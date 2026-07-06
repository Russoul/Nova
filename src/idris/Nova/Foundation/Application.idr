module Nova.Foundation.Application

import Data.List

import Nova.Foundation.Syntax
import Nova.Foundation.Derivation
import Nova.Foundation.Derivation.Parser
import Nova.Foundation.Parser
import Nova.Foundation.Pretty
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

||| Input:
|||  - List TypingRule  (rules file, one rule per line prefixed with "- ")
|||  - Target judgement form (target file, written as a single typing rule)
||| Output:
|||  - Ok: the target judgement form is derivable
|||  - Rejected: a rule was rejected (prints the offending rule)
|||  - NoWitness: rules are consistent but the target is not derived
main : IO ()
main = do
  args <- getArgs
  case args of
    (_ :: rulesFile :: targetFile :: []) => do
      Right i <- parseInput rulesFile targetFile
        | Left err => die err
      report (run i)
    _ => die "Usage: nova-foundation-app <rules-file> <target-file>"
