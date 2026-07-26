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
import Data.SnocList
import Data.String

import Me.Russoul.Text.Range

import Nova.Kernel.Parser

import Nova.Elaboration
import Nova.Elaboration.Surface
import Nova.Elaboration.Parser

import System.File

%default covering

||| Exported for LSP consumers that need to map a loaded module's name
||| back to the file it came from (e.g. go-to-definition across an
||| import) without re-deriving this convention themselves.
export
dirOf : String -> String
dirOf path =
  case reverse (forget (split (== '/') path)) of
    (_ :: parentRev@(_ :: _)) => joinBy "/" (reverse parentRev)
    _ => "."

export
modPath : (rootDir : String) -> (mname : String) -> String
modPath rootDir mname =
  rootDir ++ "/" ++ joinBy "/" (forget (split (== '.') mname)) ++ ".nova"

||| module name → the fixities it declares (for its own operator
||| defs); an importer's initial parse table is assembled from these,
||| restricted to the operators it OPENS.
FixMap : Type
FixMap = List (String, FixTable)

importTable : FixMap -> List SImport -> FixTable
importTable fm = concatMap
  (\i => case lookup i.mname fm of
           Nothing => []
           Just tbl => filter (\(op, _) => op `elem` i.opens) tbl)

parseHeader : (label : String) -> String -> Either String (List SImport)
parseHeader label content =
  case runSurfaceParser parseSHeader content of
    Left err => Left "parse error in \{label}: \{err}"
    Right (_, r) => Right r

parseModule : (label : String) -> FixTable -> String
            -> Either String (SnocList (Range, TokenKind), List SImport, FixTable, List (Maybe Range, SItem))
parseModule label tbl content =
  case runSurfaceParser (parseSFile tbl) content of
    Left err => Left "parse error in \{label}: \{err}"
    Right (toks, (imps, tbl', items)) => Right (toks, imps, tbl', items)

mutual
  ||| Resolve module `mname` and (transitively, first) its imports into
  ||| `acc`, dependency-first. `visiting` detects cycles; `done`
  ||| short-circuits diamonds; `fixs` accumulates each module's
  ||| declared fixities for its importers.
  loadOne : (rootDir : String) -> (visiting : List String) -> (done : List String)
          -> (fixs : FixMap) -> (acc : List ModUnit) -> (mname : String)
          -> IO (Either String (List String, FixMap, List ModUnit))
  loadOne rootDir visiting done fixs acc mname =
    if mname `elem` done
      then pure (Right (done, fixs, acc))
      else if mname `elem` visiting
        then pure (Left "import cycle through module '\{mname}'")
        else do
          let path = modPath rootDir mname
          Right content <- readFile path
            | Left err => pure (Left "cannot read module '\{mname}' (\{path}): \{show err}")
          -- two-stage parse: the header names the dependencies whose
          -- fixity tables the body parse needs
          let Right hdr = parseHeader "module \{mname} (\{path})" content
            | Left err => pure (Left err)
          Right (done', fixs', acc') <- loadMany rootDir (mname :: visiting) done fixs acc (map (\i => i.mname) hdr)
            | Left err => pure (Left err)
          let tbl0 = importTable fixs' hdr
          let Right (toks, imps, decls, items) = parseModule "module \{mname} (\{path})" tbl0 content
            | Left err => pure (Left err)
          pure (Right (mname :: done', (mname, decls) :: fixs',
                       acc' ++ [MkModUnit mname imps (decls ++ tbl0) items toks]))

  loadMany : (rootDir : String) -> (visiting : List String) -> (done : List String)
           -> (fixs : FixMap) -> (acc : List ModUnit) -> List String
           -> IO (Either String (List String, FixMap, List ModUnit))
  loadMany rootDir visiting done fixs acc [] = pure (Right (done, fixs, acc))
  loadMany rootDir visiting done fixs acc (m :: ms) = do
    Right (done', fixs', acc') <- loadOne rootDir visiting done fixs acc m
      | Left err => pure (Left err)
    loadMany rootDir visiting done' fixs' acc' ms

||| Load a root file and its import graph; the result is dependency-
||| ordered with the root (module name "") last.
export
loadProgram : (rootPath : String) -> IO (Either String (List ModUnit))
loadProgram rootPath = do
  Right content <- readFile rootPath
    | Left err => pure (Left "cannot read '\{rootPath}': \{show err}")
  let Right hdr = parseHeader rootPath content
    | Left err => pure (Left err)
  Right (_, fixs, deps) <- loadMany (dirOf rootPath) [] [] [] [] (map (\i => i.mname) hdr)
    | Left err => pure (Left err)
  let tbl0 = importTable fixs hdr
  let Right (toks, imps, decls, items) = parseModule rootPath tbl0 content
    | Left err => pure (Left err)
  pure (Right (deps ++ [MkModUnit "" imps (decls ++ tbl0) items toks]))

||| Load and elaborate: the `elab` command's body.
export
elabPath : String -> IO String
elabPath rootPath = do
  Right units <- loadProgram rootPath
    | Left err => pure "Error: \{err}"
  pure (elabProgram units)
