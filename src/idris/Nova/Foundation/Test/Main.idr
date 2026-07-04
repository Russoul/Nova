module Nova.Foundation.Test.Main

import System
import Data.SnocList
import Test.Golden

import Nova.Foundation.Syntax
import Nova.Foundation.Parser

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

runParse : String -> String -> IO ()
runParse parser input =
  case parser of
    "sub"   => putStrLn $ either (const "ERROR") show (runParser parseSub input)
    "ty"    => putStrLn $ either (const "ERROR") show (runParser parseTy input)
    "elem"  => putStrLn $ either (const "ERROR") show (runParser parseElem input)
    "ctx"   => putStrLn $ either (const "ERROR") showCtx (runParser parseCtx input)
    "tel"   => putStrLn $ either (const "ERROR") showTel (runParser parseTel input)
    "spine" => putStrLn $ either (const "ERROR") showSpine (runParser parseSpine input)
    _       => putStrLn "ERROR: unknown parser '\{parser}'"

-- ===== Test suite mode =====
-- Invoked as: nova-foundation-tests PATH_TO_SELF [golden-options...]

pools : IO (List TestPool)
pools = sequence
  [ testsInDir "tests/foundation/parser" "Foundation Parser"
  ]

main : IO ()
main = do
  args <- getArgs
  case args of
    (_ :: "run" :: parser :: input :: []) => runParse parser input
    _ => do
      ps <- pools
      runner ps
