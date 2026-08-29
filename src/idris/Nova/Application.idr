module Nova.Application

import Data.List
import Data.List1
import Data.Maybe
import Data.String

import Nova.Diagnostic
import Nova.Distill
import Nova.Elaboration.Loader
import Nova.Implicitize
import Nova.Kernel.Syntax
import Nova.Profile
import Nova.Recovery
import Nova.Rename
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
  , "implicitize <file> <out-dir> <def> <pos...>: TARGETED migration —"
  , "the named def's given explicit binder positions become implicit;"
  , "each use site drops the argument (per-site recovery verified by"
  , "the override trial) or keeps it as a {t} override; the result is"
  , "Σ-α-gated to a fixpoint (docs/NovaPerfectSurface.txt)."
  , ""
  , "census <file> <def...>: per named def and explicit binder"
  , "position, how many sites recover the argument (elidable), how"
  , "many already write a blank, and how many would need a {…}"
  , "override — the measured basis for a targeted migration."
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
        Left err  => do putStrLn (errorLine err); exitFailure
        Right val => putStrLn val
    (_ :: "distill" :: surfaceFile :: outDir :: []) => do
      result <- distillPath surfaceFile outDir
      case result of
        Left err  => do putStrLn (errorLine err); exitFailure
        Right msg => putStrLn msg
    (_ :: "survey" :: surfaceFile :: []) => do
      result <- sigPath surfaceFile
      case result of
        Left err  => do putStrLn (errorLine err); exitFailure
        Right sig => putStrLn (surveyReport sig)
    (_ :: "rename" :: surfaceFile :: outDir :: pairs@(_ :: _)) => do
      let rm = mapMaybe (\p => case forget (split (== '=') p) of
                                  [old, new] => Just (old, new)
                                  _ => Nothing) pairs
      result <- renamePath surfaceFile outDir rm
      case result of
        Left err  => do putStrLn (errorLine err); exitFailure
        Right msg => putStrLn msg
    (_ :: "implicitize" :: surfaceFile :: outDir :: []) => do
      result <- implicitizePath surfaceFile outDir
      case result of
        Left err  => do putStrLn (errorLine err); exitFailure
        Right msg => putStrLn msg
    -- targeted migration: one def, chosen explicit positions
    (_ :: "implicitize" :: surfaceFile :: outDir :: name :: poss@(_ :: _)) => do
      result <- migrateDefPath surfaceFile outDir name (mapMaybe parsePositive poss)
      case result of
        Left err  => do putStrLn (errorLine err); exitFailure
        Right msg => putStrLn msg
    (_ :: "census" :: surfaceFile :: names@(_ :: _)) => do
      result <- censusPath surfaceFile names
      case result of
        Left err  => do putStrLn (errorLine err); exitFailure
        Right msg => putStrLn msg
    _ => die usage
