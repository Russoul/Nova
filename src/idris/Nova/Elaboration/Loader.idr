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
import Nova.Kernel.Syntax
import Nova.Compute

import Nova.Diagnostic
import Nova.Elaboration
import Nova.Elaboration.Surface
import Nova.Elaboration.Parser
import Nova.Profile

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
  -- a root given as a bare filename has "." for its directory; a
  -- "./" prefix is noise in a diagnostic's location, and resolves
  -- identically without it
  (if rootDir == "." then "" else rootDir ++ "/") ++
  joinBy "/" (forget (split (== '.') mname)) ++ ".nova"

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

||| Overloaded operators must AGREE on fixity: the parse is shared,
||| only the elaborator's type-directed resolution distinguishes the
||| candidates (docs/NovaPerfectSurface.txt, Phase 4).
fixityConflict : FixTable -> Maybe String
fixityConflict tbl = go tbl
 where
  go : FixTable -> Maybe String
  go [] = Nothing
  go ((op, a, p) :: rest) =
    case lookup op rest of
      Just (a', p') =>
        if a == a' && p == p' then go rest
        else Just "conflicting fixities for '\{op}' among the opened imports — overloads must agree on associativity and precedence"
      Nothing => go rest

||| A load failure: everything `Nova.Diagnostic` needs to place it —
||| the failing file, its text (for the source excerpt) and the span
||| within it, when known — plus the location-free message. The LSP
||| takes the same record and publishes `lrange` as a diagnostic.
public export
record LoadErr where
  constructor MkLoadErr
  lfile : Maybe String
  lsrc : Maybe String
  lrange : Maybe Range
  lmsg : String
  lnotes : List String

plainErr : String -> LoadErr
plainErr msg = MkLoadErr Nothing Nothing Nothing msg []

||| A failure attributable to a file but not to a span within it.
fileErr : (path : String) -> (src : String) -> String -> LoadErr
fileErr path src msg = MkLoadErr (Just path) (Just src) Nothing msg []

parseErr : (path : String) -> (content : String) -> ParseFail -> LoadErr
parseErr path content pf =
  MkLoadErr (Just path) (Just content) pf.pfrange pf.pfmsg pf.pfnotes

||| The rendered form every non-LSP consumer wants: the message with
||| its location, source excerpt and notes (`Nova.Diagnostic`).
export
showLoadErr : LoadErr -> String
showLoadErr e = render (MkDiag Err e.lfile e.lsrc e.lrange e.lmsg e.lnotes)

parseHeader : (path : String) -> String -> Either LoadErr (List SImport)
parseHeader path content =
  case runSurfaceParser parseSHeader content of
    Left pf => Left (parseErr path content pf)
    Right (_, r) => Right r

parseModule : (path : String) -> FixTable -> String
            -> Either LoadErr (SnocList (Range, TokenKind), List SImport, FixTable, List (Maybe Range, SItem), List SBodyEntry)
parseModule path tbl content =
  case runSurfaceParser (parseSFile tbl) content of
    Left pf => Left (parseErr path content pf)
    Right (toks, (imps, tbl', items, body)) => Right (toks, imps, tbl', items, body)

||| Where an import came from: the importing file, its text, and the
||| import line's own span — so a failure resolving the import is
||| reported AT the `import` line rather than at the missing file (or
||| at nothing at all).
record Blame where
  constructor MkBlame
  bpath : String
  bsrc : String
  brange : Maybe Range

blamed : Maybe Blame -> String -> LoadErr
blamed Nothing msg = plainErr msg
blamed (Just b) msg = MkLoadErr (Just b.bpath) (Just b.bsrc) b.brange msg []

mutual
  ||| Resolve module `mname` and (transitively, first) its imports into
  ||| `acc`, dependency-first. `visiting` detects cycles; `done`
  ||| short-circuits diamonds; `fixs` accumulates each module's
  ||| declared fixities for its importers. `blame` is the import line
  ||| that asked for this module — the site any failure to RESOLVE it
  ||| is reported at (a failure INSIDE the module reports there).
  loadOne : (rootDir : String) -> (visiting : List String) -> (done : List String)
          -> (fixs : FixMap) -> (acc : List ModUnit) -> (blame : Maybe Blame) -> (mname : String)
          -> IO (Either LoadErr (List String, FixMap, List ModUnit))
  loadOne rootDir visiting done fixs acc blame mname =
    if mname `elem` done
      then pure (Right (done, fixs, acc))
      else if mname `elem` visiting
        then pure (Left (blamed blame "import cycle through module '\{mname}'"))
        else do
          let path = modPath rootDir mname
          Right content <- readFile path
            | Left err => pure (Left (blamed blame "cannot read module '\{mname}' (\{path}): \{show err}"))
          -- two-stage parse: the header names the dependencies whose
          -- fixity tables the body parse needs
          let Right hdr = parseHeader path content
            | Left err => pure (Left err)
          Right (done', fixs', acc') <- loadMany rootDir (mname :: visiting) done fixs acc path content hdr
            | Left err => pure (Left err)
          let tbl0 = importTable fixs' hdr
          let Nothing = fixityConflict tbl0
            | Just msg => pure (Left (fileErr path content msg))
          let Right (toks, imps, decls, items, body) = parseModule path tbl0 content
            | Left err => pure (Left err)
          pure (Right (mname :: done', (mname, decls) :: fixs',
                       acc' ++ [MkModUnit mname path imps (decls ++ tbl0) items toks body content]))

  loadMany : (rootDir : String) -> (visiting : List String) -> (done : List String)
           -> (fixs : FixMap) -> (acc : List ModUnit)
           -> (importerPath : String) -> (importerSrc : String) -> List SImport
           -> IO (Either LoadErr (List String, FixMap, List ModUnit))
  loadMany rootDir visiting done fixs acc _ _ [] = pure (Right (done, fixs, acc))
  loadMany rootDir visiting done fixs acc ipath isrc (i :: ms) = do
    Right (done', fixs', acc') <-
      loadOne rootDir visiting done fixs acc (Just (MkBlame ipath isrc i.irange)) i.mname
      | Left err => pure (Left err)
    loadMany rootDir visiting done' fixs' acc' ipath isrc ms

||| Load a root file and its import graph; the result is dependency-
||| ordered with the root (module name "") last.
export
loadProgram : (rootPath : String) -> IO (Either LoadErr (List ModUnit))
loadProgram rootPath = do
  Right content <- readFile rootPath
    | Left err => pure (Left (plainErr "cannot read '\{rootPath}': \{show err}"))
  let Right hdr = parseHeader rootPath content
    | Left err => pure (Left err)
  Right (_, fixs, deps) <- loadMany (dirOf rootPath) [] [] [] [] rootPath content hdr
    | Left err => pure (Left err)
  let tbl0 = importTable fixs hdr
  let Nothing = fixityConflict tbl0
    | Just msg => pure (Left (fileErr rootPath content msg))
  let Right (toks, imps, decls, items, body) = parseModule rootPath tbl0 content
    | Left err => pure (Left err)
  pure (Right (deps ++ [MkModUnit "" rootPath imps (decls ++ tbl0) items toks body content]))

||| Load and elaborate: the `elab` command's body.
export
elabPath : String -> IO String
elabPath rootPath = do
  let t0 = nowNs ()
  Right units <- loadProgram rootPath
    | Left err => pure (showLoadErr err)
  let t1 = bump "phase-load-parse" (nowNs () - t0) (nowNs ())
  let out = elabProgram units
  let _ = length out
  let out2 = bump "phase-elaborate" (nowNs () - t1) out
  dumpProfile
  pure out2

||| Load and elaborate to the accepted kernel Σ (requiring full
||| acceptance): the survey commands' entry point.
export
sigPath : String -> IO (Either String Sig)
sigPath rootPath = do
  Right units <- loadProgram rootPath
    | Left err => pure (Left (showLoadErr err))
  pure (elabProgramSig units)

||| Load, elaborate (requiring full acceptance — Nova.Compute assumes
||| closed, well-typed input), and compute the normal form of a named
||| top-level definition: the `run` command's body. A term definition
||| normalizes its definiens (nfElem); a type definition, its type
||| (nfTy) — both always have an empty declaration context (every
||| top-level item elaborates at Γ = ε; see Nova.Elaboration's e-def/
||| e-typedef).
export
runPath : (rootPath : String) -> (name : String) -> IO (Either String String)
runPath rootPath name = do
  Right units <- loadProgram rootPath
    | Left err => pure (Left (showLoadErr err))
  pure $ do
    sig <- elabProgramSig units
    case sigLookup name sig of
      Nothing                    => Left "'\{name}' not found"
      Just (SigDef [<] _ body _) => Right (show (nfElem sig body))
      Just (SigDef _ _ _ _)      => Left "'\{name}' has a non-empty declaration context"
      -- unreachable behind elabProgramSig's acceptance gate (a
      -- definitional Σ), but the match must cover the open entries
      Just _                     => Left "'\{name}' is not a definition"
