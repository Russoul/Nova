module Nova.Application

import Data.List
import Data.String

import Nova.Distill
import Nova.Elaboration.Loader
import Nova.Implicitize
import Nova.Kernel.Syntax
import Nova.Profile
import Nova.Recovery
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
  , ""
  , "survey: elaborates the file (requiring acceptance) and reports,"
  , "per definition, which application arguments the phase-3 recovery"
  , "oracle could reconstruct if elided (docs/NovaPerfectSurface.txt,"
  , "the sugar tiers) — the measured basis for implicit binders."
  , ""
  , "implicitize: rewrites the file's module closure into <out-dir>"
  , "with survey-approved binder positions made implicit ({x : A})"
  , "and the arguments at those positions elided at every use site —"
  , "each elision verified by a per-site recovery trial, the whole"
  , "result verified by re-elaboration with an α-identical kernel Σ"
  , "(docs/NovaPerfectSurface.txt, Phase 3c)."
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
    (_ :: "survey" :: surfaceFile :: []) => do
      result <- sigPath surfaceFile
      case result of
        Left err  => do putStrLn "Error: \{err}"; exitFailure
        Right sig => putStrLn (surveyReport sig)
    (_ :: "implicitize" :: surfaceFile :: outDir :: []) => do
      result <- implicitizePath surfaceFile outDir
      case result of
        Left err  => do putStrLn "Error: \{err}"; exitFailure
        Right msg => putStrLn msg
    _ => die usage
