module Nova.Test

import System
import System.File
import Data.List
import Data.SnocList
import Test.Golden

import Me.Russoul.Text.Range

import Nova.Kernel.Syntax
import Nova.Kernel.Parser
import Nova.Elaboration.Named
import Nova.Elaboration
import Nova.Elaboration.Loader
import Nova.Elaboration.Surface
import Nova.Elaboration.Parser

import Nova.LSP.TestClient

-- ===== Parser mode =====
-- Invoked as: nova-foundation-tests run PARSER INPUT

runParse : String -> String -> IO ()
runParse parser input =
  case parser of
    "sub"          => putStrLn $ either (const "ERROR") show (runParser parseSub input)
    "ty"           => putStrLn $ either (const "ERROR") show (runParser parseTy input)
    "elem"         => putStrLn $ either (const "ERROR") show (runParser parseElem input)
    "surface-ty"   => putStrLn $ either (const "ERROR") (show . snd) (runSurfaceParser (parseSTy [] [<]) input)
    "surface-elem" => putStrLn $ either (const "ERROR") (show . snd) (runSurfaceParser (parseSElem [] [<]) input)
    "surface-item" => putStrLn $ either (const "ERROR") (show . snd) (runSurfaceParser (parseSItem []) input)
    _              => putStrLn "ERROR: unknown parser '\{parser}'"

-- ===== Test suite mode =====
-- Invoked as: nova-foundation-tests PATH_TO_SELF [golden-options...]

pools : IO (List TestPool)
pools = sequence
  [ testsInDir "tests/nova/parser" "Nova Parser"
  , testsInDir "tests/nova/elaboration" "Nova Elaboration"
  , testsInDir "tests/nova-lsp" "Nova LSP"
  ]

main : IO ()
main = do
  args <- getArgs
  case args of
    (_ :: "run" :: parser :: input :: []) => runParse parser input
    (_ :: "elab" :: file :: []) => do
      output <- elabPath file
      putStrLn output
    (_ :: "lsp" :: lspBin :: fixture :: word :: []) => runLspTest lspBin fixture word
    _ => do
      ps <- pools
      runner ps
