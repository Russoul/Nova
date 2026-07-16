module Nova.Foundation.Application

import Data.List
import Data.List1
import Data.String

import Nova.Foundation.Syntax
import Nova.Foundation.Derivation
import Nova.Foundation.Derivation.NamedParser
import Nova.Foundation.Derivation.NamedPretty
import Nova.Foundation.Derivation.NamedRejectionPretty
import Nova.Foundation.Parser
import Nova.Foundation.Session
import System
import System.File

%default covering

||| Input of the program.
record Input where
  constructor MkInput
  ||| Typing rules to generate the `Truth` table from.
  rules : List TypingRule
  ||| The judgement forms we want to check derivability of.
  targets : List JudgementForm

||| Output of the program.
||| `Ok` — all targets derived
||| `Rejected` — one of the typing rules has been rejected
||| `NoWitness` — rules are consistent but a target is not in the truth table
data Output = Ok | Rejected ContextualRejection | NoWitness Truth JudgementForm

BadInput = String
Filename = String

run : Input -> Output
run (MkInput rules targets) =
  case generate rules of
    Left rejection => Rejected rejection
    Right truth    =>
      case find (\t => not (check t truth)) targets of
        Just t  => NoWitness truth t
        Nothing => Ok

report : Output -> IO ()
report Ok = putStrLn "Ok"
report (Rejected cr) = do
  putStrLn "Rejected"
  putStrLn $ "  At rule: " ++ prettyTypingRuleN cr.rule
  putStrLn $ "  Reason: " ++ prettyRejectionN cr.reason ++ prettyNearMissesN cr.truth cr.reason
report (NoWitness truth t) = do
  putStrLn "NoWitness"
  putStrLn $ "  Target: " ++ prettyJudgementFormN t ++ prettyNearMissesN truth (jfRejection t)

||| Read a session file's content. A missing file reads as an empty session
||| (freshly started, no rules applied yet) rather than an error.
loadSession : Filename -> IO String
loadSession file = do
  Right content <- readFile file
    | Left FileNotFound => pure ""
    | Left err => die ("Cannot read session file '" ++ file ++ "': " ++ show err)
  pure content

writeSession : Filename -> String -> IO ()
writeSession file content = do
  Right () <- writeFile file content
    | Left err => die ("Cannot write session file '" ++ file ++ "': " ++ show err)
  pure ()

-- ===== Dependency resolution ("depends: name1, name2" headers) =====
--
-- A session declares its dependencies by name (matching the sibling
-- derivations/<name>/session.rules convention), not by path, so the
-- `.rules` file stays self-explanatory without hardcoding any particular
-- checkout layout. Resolving those names into an actual List TypingRule
-- needs IO (reading the other session files), which is why this lives
-- here rather than in Session.idr's otherwise-pure functions.

||| `siblingPath "derivations/vect-append/session.rules" "plus"` is
||| `"derivations/plus/session.rules"` — a dependency name resolves to a
||| session file next to (i.e. sharing the parent directory of) the file
||| that names it, so this works the same regardless of the caller's
||| working directory, as long as the sibling-folder-per-goal convention
||| holds. Falls back to a plain relative path if `currentFile` has no
||| directory components of its own (unusual — the convention assumes
||| `derivations/<goal>/session.rules`).
siblingPath : Filename -> String -> Filename
siblingPath currentFile depName =
  case reverse (forget (Data.String.split (== '/') currentFile)) of
    (_ :: _ :: parentRev) =>
      concat (intersperse "/" (reverse parentRev)) ++ "/" ++ depName ++ "/session.rules"
    _ => "../" ++ depName ++ "/session.rules"

mutual
  ||| Fully resolve `path` (a dependency's own session file — must exist
  ||| and parse) into the flat rules it and its own transitive
  ||| dependencies contribute. `visiting` guards against cycles (grows,
  ||| never shrinks — harmless, since anything already `resolved` short-
  ||| circuits before `visiting` is even checked); `resolved`/`acc` thread
  ||| the running (deduplicated, dependency-first) result.
  resolveOne : (visiting : List Filename) -> (resolved : List Filename) -> (acc : List TypingRule)
             -> Filename -> IO (Either String (List Filename, List TypingRule))
  resolveOne visiting resolved acc path =
    if path `elem` resolved
      then pure (Right (resolved, acc))
      else if path `elem` visiting
        then pure (Left ("dependency cycle detected at '" ++ path ++ "'"))
        else do
          Right content <- readFile path
            | Left err => pure (Left ("cannot read dependency file '" ++ path ++ "': " ++ show err))
          let (depNames, _, rest) = splitHeader content
          Right (resolved', acc') <- resolveMany (path :: visiting) resolved acc path depNames
            | Left err => pure (Left err)
          case runParser parseNamedListTypingRule rest of
            Left err => pure (Left ("parse error in dependency file '" ++ path ++ "': " ++ err))
            Right ownRules => pure (Right (path :: resolved', acc' ++ ownRules))

  ||| Resolve each name in `depNames` (declared by the file at `basePath`)
  ||| to its sibling session file and fold it in, in declaration order.
  resolveMany : (visiting : List Filename) -> (resolved : List Filename) -> (acc : List TypingRule)
              -> (basePath : Filename) -> (depNames : List String)
              -> IO (Either String (List Filename, List TypingRule))
  resolveMany visiting resolved acc basePath [] = pure (Right (resolved, acc))
  resolveMany visiting resolved acc basePath (name :: names) = do
    Right (resolved', acc') <- resolveOne visiting resolved acc (siblingPath basePath name)
      | Left err => pure (Left err)
    resolveMany visiting resolved' acc' basePath names

||| Resolve `file`'s own `depends:` header (if any) into the prelude of
||| TypingRules that must be replayed before `file`'s own content —
||| including every transitive dependency, deduplicated, in a valid
||| dependency-first order. `file` itself is read tolerantly (missing =
||| fresh/empty session, matching `loadSession`); each name it declares,
||| however, must resolve to a real, parseable session file. Returns the
||| prelude, the header's own verbatim text (to reattach when writing the
||| session back), and `file`'s own content with the header stripped off.
export
resolvePrelude : Filename -> IO (Either String (List TypingRule, String, String))
resolvePrelude file = do
  content <- loadSession file
  let (depNames, headerRaw, rest) = splitHeader content
  Right (_, prelude) <- resolveMany [file] [] [] file depNames
    | Left err => pure (Left err)
  pure (Right (prelude, headerRaw, rest))

parseInput : Filename -> Filename -> IO (Either BadInput Input)
parseInput rulesFile targetFile = do
  -- A missing rules file is a genuine error for `check` (unlike the
  -- incremental session commands, `resolvePrelude` tolerates a missing
  -- *top-level* file as "freshly started" — check it explicitly first).
  Right _ <- readFile rulesFile
    | Left err => pure (Left $ "Cannot read rules file '" ++ rulesFile ++ "': " ++ show err)
  Right (prelude, _, rest) <- resolvePrelude rulesFile
    | Left err => pure (Left err)
  Right targetContent <- readFile targetFile
    | Left err => pure (Left $ "Cannot read target file '" ++ targetFile ++ "': " ++ show err)
  let Right ownRules = runParser parseNamedListTypingRule rest
    | Left err => pure (Left $ "Parse error in rules file: " ++ err)
  let Right targets = runParser parseNamedListJudgementForm targetContent
    | Left err => pure (Left $ "Parse error in target file: " ++ err)
  pure (Right (MkInput (prelude ++ ownRules) targets))

usage : String
usage = unlines
  [ "Usage:"
  , "  nova-foundation-app check     <rules-file> <target-file>"
  , "  nova-foundation-app init      <session-file> [depends-on,comma,separated]"
  , "  nova-foundation-app apply     <session-file> <rule-text>"
  , "  nova-foundation-app query     <session-file> <target-text>"
  , "  nova-foundation-app dump      <session-file> [judgement-kind]"
  , "  nova-foundation-app undo      <session-file>"
  , ""
  , "A session may build on other sessions instead of copy-pasting their"
  , "derivation inline: put `depends: name1, name2` on its own line(s)"
  , "before any `- <rule>` bullet (or pass names to `init`, which writes"
  , "that line for you). Each name resolves to a sibling"
  , "<parent-dir>/<name>/session.rules, matching the derivations/<goal>/"
  , "convention, and is itself resolved transitively (a dependency's own"
  , "dependencies are pulled in too, deduplicated)."
  ]

||| `check` is the original one-shot batch mode:
|||  - List TypingRule  (rules file, one rule per line prefixed with "- ")
|||  - Target judgement forms (target file, one per line prefixed with "- ")
||| Output:
|||  - Ok: all target judgement forms are derivable
|||  - Rejected: a rule was rejected (prints the offending rule and reason)
|||  - NoWitness: rules are consistent but a target is not derived
|||
||| The other subcommands (`init`/`apply`/`query`/`dump`/`undo`) drive a
||| session incrementally: a session file is just a rules file that
||| `apply` grows one checked rule at a time, giving immediate feedback
||| (accepted + newly derived facts, or rejected + reason) without
||| resubmitting or re-deriving the whole proof by hand.
main : IO ()
main = do
  args <- getArgs
  case args of
    (_ :: "check" :: rulesFile :: targetFile :: []) => do
      Right i <- parseInput rulesFile targetFile
        | Left err => die err
      report (run i)
    (_ :: "init" :: sessionFile :: []) => do
      writeSession sessionFile ""
      putStrLn "Ok"
    (_ :: "init" :: sessionFile :: dependsArg :: []) => do
      let deps = filter (/= "") (map trim (forget (Data.String.split (== ',') dependsArg)))
      writeSession sessionFile (if deps == [] then "" else "depends: " ++ concat (intersperse ", " deps) ++ "\n")
      putStrLn "Ok"
    (_ :: "apply" :: sessionFile :: ruleText :: []) => do
      Right (prelude, headerRaw, rest) <- resolvePrelude sessionFile
        | Left err => die err
      let outcome = Session.apply prelude rest ruleText
      putStrLn outcome.message
      case outcome.newContent of
        Nothing  => pure ()
        Just new => writeSession sessionFile (headerRaw ++ new)
    (_ :: "query" :: sessionFile :: targetText :: []) => do
      Right (prelude, _, rest) <- resolvePrelude sessionFile
        | Left err => die err
      putStrLn (Session.query prelude rest targetText)
    (_ :: "dump" :: sessionFile :: []) => do
      Right (prelude, _, rest) <- resolvePrelude sessionFile
        | Left err => die err
      putStrLn (Session.dump prelude rest Nothing)
    (_ :: "dump" :: sessionFile :: kind :: []) => do
      Right (prelude, _, rest) <- resolvePrelude sessionFile
        | Left err => die err
      putStrLn (Session.dump prelude rest (Just kind))
    (_ :: "undo" :: sessionFile :: []) => do
      content <- loadSession sessionFile
      case Session.undo content of
        Nothing  => putStrLn "(nothing to undo)"
        Just new => do
          writeSession sessionFile new
          putStrLn "Ok"
    _ => die usage
