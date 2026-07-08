module Nova.Foundation.Test.Main

import System
import System.File
import Data.List
import Data.SnocList
import Test.Golden

import Nova.Foundation.Syntax
import Nova.Foundation.Parser
import Nova.Foundation.Pretty
import Nova.Foundation.Rejection.Pretty
import Nova.Foundation.Derivation
import Nova.Foundation.Derivation.Parser

-- ===== Display helpers for top-level aliases =====

showCtx : Ctx -> String
showCtx [<] = "[<]"
showCtx sx = "[< " ++ go sx ++ "]"
  where
    go : SnocList Ty -> String
    go [<] = ""
    go (rest :< ty) = case rest of
      [<] => show ty
      _   => go rest ++ ", " ++ show ty

showTel : Tel -> String
showTel [] = "[]"
showTel tys = "[" ++ joinWith ", " (map show tys) ++ "]"
  where
    joinWith : String -> List String -> String
    joinWith _ [] = ""
    joinWith _ [x] = x
    joinWith sep (x :: xs) = x ++ sep ++ joinWith sep xs

showSpine : Spine -> String
showSpine [] = "[]"
showSpine es = "[" ++ joinWith ", " (map show es) ++ "]"
  where
    joinWith : String -> List String -> String
    joinWith _ [] = ""
    joinWith _ [x] = x
    joinWith sep (x :: xs) = x ++ sep ++ joinWith sep xs

-- ===== Parser mode =====
-- Invoked as: nova-foundation-tests run PARSER INPUT

joinWith : String -> List String -> String
joinWith _ []       = ""
joinWith _ [x]      = x
joinWith sep (x :: xs) = x ++ sep ++ joinWith sep xs

runParse : String -> String -> IO ()
runParse parser input =
  case parser of
    "sub"          => putStrLn $ either (const "ERROR") show (runParser parseSub input)
    "ty"           => putStrLn $ either (const "ERROR") show (runParser parseTy input)
    "elem"         => putStrLn $ either (const "ERROR") show (runParser parseElem input)
    "ctx"          => putStrLn $ either (const "ERROR") showCtx (runParser parseCtx input)
    "tel"          => putStrLn $ either (const "ERROR") showTel (runParser parseTel input)
    "spine"        => putStrLn $ either (const "ERROR") showSpine (runParser parseSpine input)
    "compute"      => putStrLn $ either (const "ERROR") show (runParser parseComputeRule input)
    "typing"       => putStrLn $ either (const "ERROR") show (runParser parseTypingRule input)
    "typing-list"  => putStrLn $ either (const "ERROR") (joinWith "\n" . map show) (runParser parseListTypingRule input)
    _              => putStrLn "ERROR: unknown parser '\{parser}'"

-- ===== Derivation mode =====
-- Invoked as: nova-foundation-tests run derivation RULES-FILE TARGET-FILE

runDerivation : String -> String -> IO ()
runDerivation rulesFile targetFile = do
  Right rulesContent  <- readFile rulesFile
    | Left err => putStrLn "ERROR: cannot read rules file: \{show err}"
  Right targetContent <- readFile targetFile
    | Left err => putStrLn "ERROR: cannot read target file: \{show err}"
  let Right rules = runParser parseListTypingRule rulesContent
    | Left err => putStrLn "ERROR: parse error in rules file: \{err}"
  let Right targets = runParser parseListJudgementForm targetContent
    | Left err => putStrLn "ERROR: parse error in target file: \{err}"
  case generate rules of
    Left cr  => do
      putStrLn "Rejected"
      putStrLn "  At rule: \{prettyTypingRule cr.rule}"
      putStrLn "  Reason: \{prettyRejection cr.reason}"
    Right truth =>
      case find (\t => not (check t truth)) targets of
        Just t  => do
          putStrLn "NoWitness"
          putStrLn "  Target: \{prettyJudgementForm t}"
        Nothing => putStrLn "Ok"

-- ===== Test suite mode =====
-- Invoked as: nova-foundation-tests PATH_TO_SELF [golden-options...]

pools : IO (List TestPool)
pools = sequence
  [ testsInDir "tests/foundation/parser"    "Foundation Parser"
  , testsInDir "tests/foundation/derivation" "Foundation Derivation"
  ]

main : IO ()
main = do
  args <- getArgs
  case args of
    (_ :: "run" :: "derivation" :: rulesFile :: targetFile :: []) =>
      runDerivation rulesFile targetFile
    (_ :: "run" :: parser :: input :: []) => runParse parser input
    _ => do
      ps <- pools
      runner ps
