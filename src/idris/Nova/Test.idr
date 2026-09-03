module Nova.Test

import System
import System.File
import Data.List
import Data.SnocList
import Test.Golden

import Me.Russoul.Text.Range

import Nova.Kernel.Syntax
import Nova.Kernel.Parser
import Nova.Kernel
import Nova.Kernel.Dormant.Tests
import Nova.Diagnostic
import Nova.Distill
import Nova.Implicitize
import Nova.Recovery
import Nova.Eliminate
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
  , testsInDir "tests/nova/derivation" "Nova Derivation"
  , testsInDir "tests/nova/elaboration" "Nova Elaboration"
  , testsInDir "tests/nova/evaluation" "Nova Evaluation"
  , testsInDir "tests/nova/distill" "Nova Distill"
  , testsInDir "tests/nova/survey" "Nova Survey"
  , testsInDir "tests/nova/implicitize" "Nova Implicitize"
  , testsInDir "tests/nova/eliminate" "Nova Eliminate"
  , testsInDir "tests/nova-lsp" "Nova LSP"
  ]

main : IO ()
main = do
  args <- getArgs
  case args of
    (_ :: "run" :: parser :: input :: []) => runParse parser input
    (_ :: "deriv" :: []) => runDerivTests
    (_ :: "elab" :: file :: []) => do
      output <- elabPath file
      putStrLn output
    -- Nova.Application's `run` command, under a different keyword here
    -- since "run" already names the parser-debugging mode above.
    (_ :: "eval" :: file :: name :: []) => do
      result <- runPath file name
      case result of
        Left err  => putStrLn (errorLine err)
        Right val => putStrLn val
    -- Nova.Application's `survey` command, for the survey goldens
    (_ :: "survey" :: file :: []) => do
      result <- sigPath file
      case result of
        Left err  => putStrLn (errorLine err)
        Right sig => putStrLn (surveyReport sig)
    -- Nova.Application's `implicitize` command, for its goldens
    (_ :: "implicitize" :: file :: outDir :: []) => do
      result <- implicitizePath file outDir
      case result of
        Left err  => putStrLn (errorLine err)
        Right msg => putStrLn msg
    -- Nova.Application's `distill` command, for the distill goldens
    (_ :: "distill" :: file :: outDir :: []) => do
      result <- distillPath file outDir
      case result of
        Left err  => putStrLn (errorLine err)
        Right msg => putStrLn msg
    -- Nova.Application's `eliminate` command, for its goldens
    (_ :: "eliminate" :: file :: loc :: var :: flags) => do
      case parseLoc loc of
        Nothing => putStrLn "eliminate: position must be LINE:COL (1-based)"
        Just (l, c) => do
          result <- eliminatePath file (l - 1) (c - 1) var (parseOpts flags)
          case result of
            Left err  => putStrLn err
            Right out => putStr out
    (_ :: "lsp" :: lspBin :: fixture :: word :: []) => runLspTest lspBin fixture word Nothing
    (_ :: "lsp" :: lspBin :: fixture :: word :: editTo :: []) =>
      runLspTest lspBin fixture word (Just editTo)
    _ => do
      ps <- pools
      runner ps
