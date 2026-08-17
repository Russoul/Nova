module Nova.Application

import Data.List
import Data.String

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
  , ""
  , "elab: elaborates a .nova surface file (see docs/NovaElaboration.txt):"
  , "items are checked in order against the kernel's signature; the"
  , "file is accepted exactly when the run ends with zero obligations"
  , "and every item is kernel-accepted (docs/NovaPipeline.txt)."
  , ""
  , "run: elaborates the file (requiring full acceptance, zero"
  , "obligations) and prints the normal form (Nova.Compute) of the"
  , "named top-level definition."
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
    _ => die usage
