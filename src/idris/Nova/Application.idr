module Nova.Application

import Data.List
import Data.String

import Nova.Elaboration.Loader
import System
import System.File

%default covering

usage : String
usage = unlines
  [ "Usage:"
  , "  nova elab <surface-file>"
  , ""
  , "Elaborates a .nova surface file (see docs/NovaElaboration.txt):"
  , "items are checked in order against the kernel's signature; the"
  , "file is accepted exactly when the run ends with zero obligations"
  , "and every item is kernel-accepted (docs/NovaPipeline.txt)."
  ]

main : IO ()
main = do
  args <- getArgs
  case args of
    (_ :: "elab" :: surfaceFile :: []) => do
      output <- elabPath surfaceFile
      putStrLn output
      unless (isSuffixOf "Accepted." output) exitFailure
    _ => die usage
