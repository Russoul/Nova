module Nova.Application

import Data.List
import Data.String

import Nova.Distill
import Nova.Elaboration.Loader
import Nova.Profile
import System
import System.File

%default covering

usage : String
usage = unlines
  [ "Usage:"
  , "  nova elab <surface-file>"
  , "  nova run <surface-file> <name>"
  , "  nova distill <surface-file> <out-dir>"
  , ""
  , "elab: elaborates a .nova surface file (see docs/NovaElaboration.txt):"
  , "items are checked in order against the kernel's signature; the"
  , "file is accepted exactly when the run ends with zero obligations"
  , "and every item is kernel-accepted (docs/NovaPipeline.txt)."
  , ""
  , "run: elaborates the file (requiring full acceptance, zero"
  , "obligations) and prints the normal form (Nova.Compute) of the"
  , "named top-level definition."
  , ""
  , "distill: renders the file's module closure back to surface text"
  , "into <out-dir> and verifies the round trip — re-parsed ASTs"
  , "structurally identical, re-elaboration identical"
  , "(docs/NovaPerfectSurface.txt). The input must be accepted."
  ]

main : IO ()
main = do
  args <- getArgs
  case args of
    (_ :: "elab" :: surfaceFile :: []) => do
      output <- elabPath surfaceFile
      putStrLn output
      unless (isSuffixOf "Accepted." output) exitFailure
    (_ :: "run" :: surfaceFile :: name :: []) => do
      result <- runPath surfaceFile name
      case result of
        Left err  => do putStrLn "Error: \{err}"; exitFailure
        Right val => putStrLn val
    (_ :: "distill" :: surfaceFile :: outDir :: []) => do
      result <- distillPath surfaceFile outDir
      case result of
        Left err  => do putStrLn "Error: \{err}"; exitFailure
        Right msg => putStrLn msg
    _ => die usage
