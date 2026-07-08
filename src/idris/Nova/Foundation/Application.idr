module Nova.Foundation.Application

import Data.List
import Data.String

import Nova.Foundation.Syntax
import Nova.Foundation.Derivation
import Nova.Foundation.Derivation.Parser
import Nova.Foundation.Parser
import Nova.Foundation.Pretty
import Nova.Foundation.Rejection.Pretty
import Nova.Foundation.Session
import System
import System.File

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
data Output = Ok | Rejected ContextualRejection | NoWitness JudgementForm

BadInput = String
Filename = String

run : Input -> Output
run (MkInput rules targets) =
  case generate rules of
    Left rejection => Rejected rejection
    Right truth    =>
      case find (\t => not (check t truth)) targets of
        Just t  => NoWitness t
        Nothing => Ok

report : Output -> IO ()
report Ok = putStrLn "Ok"
report (Rejected cr) = do
  putStrLn "Rejected"
  putStrLn $ "  At rule: " ++ prettyTypingRule cr.rule
  putStrLn $ "  Reason: " ++ prettyRejection cr.reason
report (NoWitness t) = do
  putStrLn "NoWitness"
  putStrLn $ "  Target: " ++ prettyJudgementForm t

parseInput : Filename -> Filename -> IO (Either BadInput Input)
parseInput rulesFile targetFile = do
  Right rulesContent <- readFile rulesFile
    | Left err => pure (Left $ "Cannot read rules file '" ++ rulesFile ++ "': " ++ show err)
  Right targetContent <- readFile targetFile
    | Left err => pure (Left $ "Cannot read target file '" ++ targetFile ++ "': " ++ show err)
  let Right rules = runParser parseListTypingRule rulesContent
    | Left err => pure (Left $ "Parse error in rules file: " ++ err)
  let Right targets = runParser parseListJudgementForm targetContent
    | Left err => pure (Left $ "Parse error in target file: " ++ err)
  pure (Right (MkInput rules targets))

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

usage : String
usage = unlines
  [ "Usage:"
  , "  nova-foundation-app check <rules-file> <target-file>"
  , "  nova-foundation-app init  <session-file>"
  , "  nova-foundation-app apply <session-file> <rule-text>"
  , "  nova-foundation-app query <session-file> <target-text>"
  , "  nova-foundation-app dump  <session-file> [judgement-kind]"
  , "  nova-foundation-app undo  <session-file>"
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
    (_ :: "apply" :: sessionFile :: ruleText :: []) => do
      content <- loadSession sessionFile
      let outcome = Session.apply content ruleText
      putStrLn outcome.message
      case outcome.newContent of
        Nothing  => pure ()
        Just new => writeSession sessionFile new
    (_ :: "query" :: sessionFile :: targetText :: []) => do
      content <- loadSession sessionFile
      putStrLn (Session.query content targetText)
    (_ :: "dump" :: sessionFile :: []) => do
      content <- loadSession sessionFile
      putStrLn (Session.dump content Nothing)
    (_ :: "dump" :: sessionFile :: kind :: []) => do
      content <- loadSession sessionFile
      putStrLn (Session.dump content (Just kind))
    (_ :: "undo" :: sessionFile :: []) => do
      content <- loadSession sessionFile
      case Session.undo content of
        Nothing  => putStrLn "(nothing to undo)"
        Just new => do
          writeSession sessionFile new
          putStrLn "Ok"
    _ => die usage
