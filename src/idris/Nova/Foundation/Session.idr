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
--
-- A session may declare other sessions it builds on, so a goal like
-- vect-append never has to copy-paste plus/vect's derivation inline: put
--   depends: plus, vect
-- on its own line(s) before any `- <rule>` bullet. This is resolved by
-- Application.idr (it needs IO, to read the other session files) into a
-- `prelude : List TypingRule` that every function below expects to be
-- replayed first — see `apply`/`query`/`dump` and `splitHeader`.

import Data.List
import Data.List1
import Data.String

import Nova.Foundation.Syntax
import Nova.Foundation.Derivation
import Nova.Foundation.Derivation.NamedParser
import Nova.Foundation.Derivation.NamedPretty
import Nova.Foundation.Derivation.NamedRejectionPretty
import Nova.Foundation.Parser

%default covering

||| Parse a session's stored rules (named surface syntax — see
||| docs/NovaNamedSyntax.txt). Expects any `depends:` header to already
||| have been stripped off by `splitHeader`.
export
loadRules : String -> Either String (List TypingRule)
loadRules = runParser parseNamedListTypingRule

||| A leading block of blank lines and `depends: name1, name2` lines,
||| ending at the first line that's neither (i.e. the first `- <rule>`
||| bullet). Multiple `depends:` lines are all collected. Returns
||| (dependency names in declaration order, the header's own raw text —
||| verbatim, so callers can losslessly reattach it, the remaining content
||| unchanged).
export
splitHeader : String -> (List String, String, String)
splitHeader content =
  let (headerLines, restLines) = spanHeader (lines content)
      deps = concatMap dependsNames headerLines
  in (deps, unlines headerLines, unlines restLines)
  where
    isHeaderLine : String -> Bool
    isHeaderLine l = trim l == "" || isPrefixOf "depends:" (trim l)

    spanHeader : List String -> (List String, List String)
    spanHeader [] = ([], [])
    spanHeader (l :: ls) =
      if isHeaderLine l
        then let (h, r) = spanHeader ls in (l :: h, r)
        else ([], l :: ls)

    dependsNames : String -> List String
    dependsNames l =
      let t = trim l in
      if isPrefixOf "depends:" t
        then let rest = pack (drop (length "depends:") (unpack t))
             in filter (/= "") (map trim (forget (Data.String.split (== ',') rest)))
        else []

describeBrokenSession : ContextualRejection -> String
describeBrokenSession cr =
  "Session file is corrupt (a previously-accepted rule no longer checks out)\n" ++
  "  At rule: " ++ prettyTypingRuleN cr.rule ++ "\n" ++
  "  Reason: " ++ prettyRejectionN cr.reason

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
||| text (existing content plus the rule text as written, verbatim —
||| unlike the indexed parser's canonical re-print, this preserves
||| whatever names the caller actually chose, since those aren't
||| recoverable from the parsed (indexed) AST alone).
|||
||| `prelude` is every rule contributed by this session's `depends:`
||| header (transitively, resolved by Application.idr, since that needs
||| IO) — replayed first, ahead of `sessionContent`'s own rules, but never
||| written back here: `newContent` only ever holds `sessionContent`'s own
||| growing text, so a session file never duplicates its dependencies'
||| content.
export
apply : (prelude : List TypingRule) -> (sessionContent : String) -> (ruleText : String) -> ApplyOutcome
apply prelude sessionContent ruleText =
  case runParser parseNamedTypingRule ruleText of
    Left err => MkApplyOutcome ("Parse error: " ++ err) Nothing
    Right rule =>
      case loadRules sessionContent of
        Left err => MkApplyOutcome ("Session file is corrupt: " ++ err) Nothing
        Right existing =>
          case generate (prelude ++ existing) of
            Left cr => MkApplyOutcome (describeBrokenSession cr) Nothing
            Right before =>
              case step rule before of
                Left reason =>
                  MkApplyOutcome
                    ("Rejected\n  At rule: " ++ prettyTypingRuleN rule ++
                     "\n  Reason: " ++ prettyRejectionN reason)
                    Nothing
                Right after =>
                  let facts = newJudgements before after
                      line  = "- " ++ trim ruleText ++ "\n"
                      factLines = case facts of
                                    [] => "  (no new facts)"
                                    _  => unlines (map (("  + " ++) . prettyJudgementFormN) facts)
                  in MkApplyOutcome ("Ok\n" ++ factLines) (Just (sessionContent ++ line))

||| Check whether a target judgement is derivable from the session so far
||| (`prelude` ++ its own rules), without mutating it.
export
query : (prelude : List TypingRule) -> (sessionContent : String) -> (targetText : String) -> String
query prelude sessionContent targetText =
  case runParser parseNamedJudgementForm targetText of
    Left err => "Parse error: " ++ err
    Right jf =>
      case loadRules sessionContent of
        Left err => "Session file is corrupt: " ++ err
        Right rules =>
          case generate (prelude ++ rules) of
            Left cr => describeBrokenSession cr
            Right truth => if check jf truth then "Derivable" else "NotDerivable"

||| List the facts currently in the session (`prelude` ++ its own rules),
||| optionally filtered to one judgement kind (e.g. "el-wf"); `Nothing` (or
||| `"all"`) lists everything.
export
dump : (prelude : List TypingRule) -> (sessionContent : String) -> (kind : Maybe String) -> String
dump prelude sessionContent kind =
  case loadRules sessionContent of
    Left err => "Session file is corrupt: " ++ err
    Right rules =>
      case generate (prelude ++ rules) of
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
               _  => unlines (map prettyJudgementFormN selected)

||| Drop the last rule from the session, if any — never touches a
||| `depends:` header, only the rule bullets after it.
export
undo : (sessionContent : String) -> Maybe String
undo sessionContent =
  let (_, headerRaw, rest) = splitHeader sessionContent
  in case reverse (filter (/= "") (lines rest)) of
       []            => Nothing
       (_ :: rest')  => Just (headerRaw ++ unlines (reverse rest'))
