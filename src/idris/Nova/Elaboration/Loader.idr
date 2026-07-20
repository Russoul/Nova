module Nova.Elaboration.Loader

-- The module loader: resolves a root .nova file's import graph into
-- the dependency-ordered list of modules that elabProgram consumes.
--
-- A module is a file; a dotted module name resolves against the ROOT
-- file's directory (import Data.Nat ⇝ <rootDir>/Data/Nat.nova). The
-- graph must be a DAG — cycles are reported by name — and diamonds
-- are deduplicated by module name, so a shared dependency elaborates
-- once. All file IO lives here; elaboration itself stays pure.

import Data.List
import Data.List1
import Data.String

import Nova.Kernel.Parser

import Nova.Elaboration
import Nova.Elaboration.Surface
import Nova.Elaboration.Parser

import System.File

%default covering

dirOf : String -> String
dirOf path =
  case reverse (forget (split (== '/') path)) of
    (_ :: parentRev@(_ :: _)) => joinBy "/" (reverse parentRev)
    _ => "."

modPath : (rootDir : String) -> (mname : String) -> String
modPath rootDir mname =
  rootDir ++ "/" ++ joinBy "/" (forget (split (== '.') mname)) ++ ".nova"

parseModule : (label : String) -> String -> Either String (List SImport, List SItem)
parseModule label content =
  case runSurfaceParser parseSFile content of
    Left err => Left "parse error in \{label}: \{err}"
    Right r => Right r

mutual
  ||| Resolve module `mname` and (transitively, first) its imports into
  ||| `acc`, dependency-first. `visiting` detects cycles; `done` short-circuits diamonds.
  loadOne : (rootDir : String) -> (visiting : List String) -> (done : List String)
          -> (acc : List ModUnit) -> (mname : String)
          -> IO (Either String (List String, List ModUnit))
  loadOne rootDir visiting done acc mname =
    if mname `elem` done
      then pure (Right (done, acc))
      else if mname `elem` visiting
        then pure (Left "import cycle through module '\{mname}'")
        else do
          let path = modPath rootDir mname
          Right content <- readFile path
            | Left err => pure (Left "cannot read module '\{mname}' (\{path}): \{show err}")
          let Right (imps, items) = parseModule "module \{mname} (\{path})" content
            | Left err => pure (Left err)
          Right (done', acc') <- loadMany rootDir (mname :: visiting) done acc (map (\i => i.mname) imps)
            | Left err => pure (Left err)
          pure (Right (mname :: done', acc' ++ [MkModUnit mname imps items]))

  loadMany : (rootDir : String) -> (visiting : List String) -> (done : List String)
           -> (acc : List ModUnit) -> List String
           -> IO (Either String (List String, List ModUnit))
  loadMany rootDir visiting done acc [] = pure (Right (done, acc))
  loadMany rootDir visiting done acc (m :: ms) = do
    Right (done', acc') <- loadOne rootDir visiting done acc m
      | Left err => pure (Left err)
    loadMany rootDir visiting done' acc' ms

||| Load a root file and its import graph; the result is dependency-
||| ordered with the root (module name "") last.
export
loadProgram : (rootPath : String) -> IO (Either String (List ModUnit))
loadProgram rootPath = do
  Right content <- readFile rootPath
    | Left err => pure (Left "cannot read '\{rootPath}': \{show err}")
  let Right (imps, items) = parseModule rootPath content
    | Left err => pure (Left err)
  Right (_, deps) <- loadMany (dirOf rootPath) [] [] [] (map (\i => i.mname) imps)
    | Left err => pure (Left err)
  pure (Right (deps ++ [MkModUnit "" imps items]))

||| Load and elaborate: the `elab` command's body.
export
elabPath : String -> IO String
elabPath rootPath = do
  Right units <- loadProgram rootPath
    | Left err => pure "Error: \{err}"
  pure (elabProgram units)
