module Nova.Foundation.Session

-- A "session" is just the text content of a rules file: a sequence of
-- lines `- <TypingRule>`, always either empty or newline-terminated.
--
-- Every function here is pure (String in, String/description out) so the
-- incremental checker can be driven either from the CLI (Application.idr)
-- or directly from tests, without threading IO through the core logic.
-- Replaying the whole session on every call is O(n) in its length, but
-- `step` is cheap (structural pattern matches over small sets), so this
-- stays fast for realistic session sizes and avoids needing a persistent
-- server process: the session file itself is the entire state.

import Data.List
import Data.String

import Nova.Foundation.Syntax
import Nova.Foundation.Derivation
import Nova.Foundation.Derivation.Parser
import Nova.Foundation.Parser
import Nova.Foundation.Pretty
import Nova.Foundation.Rejection.Pretty

%default covering

||| Parse a session's stored rules.
export
loadRules : String -> Either String (List TypingRule)
loadRules = runParser parseListTypingRule

describeBrokenSession : ContextualRejection -> String
describeBrokenSession cr =
  "Session file is corrupt (a previously-accepted rule no longer checks out)\n" ++
  "  At rule: " ++ prettyTypingRule cr.rule ++ "\n" ++
  "  Reason: " ++ prettyRejection cr.reason

||| Keyword used by JudgementForm's keyword-first grammar, reused here to
||| filter `dump` output by judgement kind.
kindOf : JudgementForm -> String
kindOf (JfCtxWf _)    = "ctx-wf"
kindOf (JfCtxEq _)    = "ctx-eq"
kindOf (JfSubWf _)    = "sub-wf"
kindOf (JfSubEq _)    = "sub-eq"
kindOf (JfSubNormWf _) = "sub-norm-wf"
kindOf (JfSubNormEq _) = "sub-norm-eq"
kindOf (JfTyWf _)     = "ty-wf"
kindOf (JfTyEq _)     = "ty-eq"
kindOf (JfElemWf _)   = "el-wf"
kindOf (JfElemEq _)   = "el-eq"
kindOf (JfTelWf _)    = "tel-wf"
kindOf (JfTelEq _)    = "tel-eq"
kindOf (JfSpineWf _)  = "sp-wf"
kindOf (JfSpineEq _)  = "sp-eq"

||| Outcome of applying a single candidate rule to a session.
public export
record ApplyOutcome where
  constructor MkApplyOutcome
  ||| Message to show the caller.
  message : String
  ||| New session content to persist, only on success.
  newContent : Maybe String

||| Parse and check a single candidate rule against the session so far.
||| On success, returns the new facts it derived and the updated session
||| text (existing content plus the canonically pretty-printed new line).
export
apply : (sessionContent : String) -> (ruleText : String) -> ApplyOutcome
apply sessionContent ruleText =
  case runParser parseTypingRule ruleText of
    Left err => MkApplyOutcome ("Parse error: " ++ err) Nothing
    Right rule =>
      case loadRules sessionContent of
        Left err => MkApplyOutcome ("Session file is corrupt: " ++ err) Nothing
        Right existing =>
          case generate existing of
            Left cr => MkApplyOutcome (describeBrokenSession cr) Nothing
            Right before =>
              case step rule before of
                Left reason =>
                  MkApplyOutcome
                    ("Rejected\n  At rule: " ++ prettyTypingRule rule ++
                     "\n  Reason: " ++ prettyRejection reason)
                    Nothing
                Right after =>
                  let facts = newJudgements before after
                      line  = "- " ++ prettyTypingRule rule ++ "\n"
                      factLines = case facts of
                                    [] => "  (no new facts)"
                                    _  => unlines (map (("  + " ++) . prettyJudgementForm) facts)
                  in MkApplyOutcome ("Ok\n" ++ factLines) (Just (sessionContent ++ line))

||| Check whether a target judgement is derivable from the session so far,
||| without mutating it.
export
query : (sessionContent : String) -> (targetText : String) -> String
query sessionContent targetText =
  case runParser parseJudgementForm targetText of
    Left err => "Parse error: " ++ err
    Right jf =>
      case loadRules sessionContent of
        Left err => "Session file is corrupt: " ++ err
        Right rules =>
          case generate rules of
            Left cr => describeBrokenSession cr
            Right truth => if check jf truth then "Derivable" else "NotDerivable"

||| List the facts currently in the session, optionally filtered to one
||| judgement kind (e.g. "el-wf"); `Nothing` (or `"all"`) lists everything.
export
dump : (sessionContent : String) -> (kind : Maybe String) -> String
dump sessionContent kind =
  case loadRules sessionContent of
    Left err => "Session file is corrupt: " ++ err
    Right rules =>
      case generate rules of
        Left cr => describeBrokenSession cr
        Right truth =>
          let js : List JudgementForm
              js = allJudgements truth
              selected : List JudgementForm
              selected = case kind of
                           Nothing      => js
                           Just "all"   => js
                           Just k       => filter (\j => kindOf j == k) js
          in case selected of
               [] => "(no facts)"
               _  => unlines (map prettyJudgementForm selected)

||| Drop the last rule from the session, if any.
export
undo : (sessionContent : String) -> Maybe String
undo sessionContent =
  case reverse (filter (/= "") (lines sessionContent)) of
    []            => Nothing
    (_ :: rest)   => Just (unlines (reverse rest))
