module Nova.LSP.Definitions

-- Go-to-definition and document symbols, both built entirely from
-- `loadProgram`'s already-parsed `List ModUnit` — no elaboration
-- needed. `SDef`/`STypeDef`/`SQDecl` carry their own name directly in
-- the surface AST, and Nova's Σ-naming scheme (qualify by module,
-- alias opened imports — see `Nova.Elaboration.resolveSigName`/
-- `emitCoreDef`) is simple enough to replicate statically here.

import Data.List
import Data.Maybe
import Data.String

import Me.Russoul.Text.Range
import Me.Russoul.Text.Position

import Language.LSP.Message.DocumentSymbols
import Language.LSP.Message.Location

import Nova.Kernel.Parser
import Nova.Elaboration
import Nova.Elaboration.Surface
import Nova.Elaboration.Clauses
import Nova.Elaboration.Loader

import Nova.LSP.Encoding

-- Aliased so every signature below doesn't have to fully qualify
-- against `Language.LSP.Message.Location`'s own (also named)
-- Range/Position — the alias itself is unambiguous, and it gives
-- Idris' elaborator an expected type to resolve MkRange/MkPosition
-- construction against.
public export
NRange : Type
NRange = Me.Russoul.Text.Range.Range

public export
NPosition : Type
NPosition = Me.Russoul.Text.Position.Position

emptyRange : NRange
emptyRange = MkRange (MkPosition 0 0) (MkPosition 0 0)

itemRange : Maybe NRange -> NRange
itemRange = fromMaybe emptyRange

||| Every name an item registers in Σ (see `Nova.Elaboration.elabItem`/
||| `emitCoreDef`) — for an `SData` literal, one name per declaration
||| (constructor/point/equation), all sharing the literal's OWN range:
||| `SQDecl` carries no sub-range of its own (see
||| `Nova.Elaboration.Parser.parseSData`), so this is item-level
||| granularity, same caveat as `ModUnit.mitems`.
itemNames : SItem -> List String
itemNames (SDef x _ _ _) = [x]
itemNames (SDeclDef _ x _) = [x]
itemNames (STypeDef x _) = [x]
itemNames (SData _ decls) = map dqname decls
itemNames (SClausalDef _ x _ eta _ cls) = clausalNames x eta cls
itemNames (SCopatternDef _ x _ _ eta _ _ _ cn) = copatternNames x cn eta

||| Σ's own qualification: bare in the root file, module-prefixed
||| otherwise (`Nova.Elaboration.emitCoreDef`'s `q`).
qualify : (mname : String) -> String -> String
qualify "" x = x
qualify m  x = "\{m}.\{x}"

||| (qualified name, defining file, item range) for every item one
||| loaded module defines. `mname == ""` is the ROOT unit (see
||| `Nova.Elaboration.Loader.loadProgram`) — its file is `rootPath`
||| itself, not something `modPath` can derive (that convention only
||| covers modules resolved by name via an `import`).
moduleEntries : (rootPath : String) -> (rootDir : String) -> ModUnit -> List (String, String, NRange)
moduleEntries rootPath rootDir unit =
  let path = if unit.mname == "" then rootPath else modPath rootDir unit.mname in
  concatMap (\(rng, item) => map (\n => (qualify unit.mname n, path, itemRange rng)) (itemNames item))
            unit.mitems

||| Every qualified name defined anywhere in the loaded program, with
||| its (file, range) — built once per document load. Duplicate names
||| are an elaboration ERROR (already surfaced as a diagnostic), so a
||| duplicate here is unremarkable best-effort "first found wins".
export
buildIndex : (rootPath : String) -> List ModUnit -> List (String, String, NRange)
buildIndex rootPath = concatMap (moduleEntries rootPath (dirOf rootPath))

||| Mirrors `Nova.Elaboration.resolveSigName`'s `vis`: the module's own
||| items (by their bare name) plus its imports' opened aliases.
export
localAliases : ModUnit -> List (String, String)
localAliases unit =
  concatMap (\(_, item) => map (\n => (n, qualify unit.mname n)) (itemNames item)) unit.mitems
  ++ concatMap (\imp => map (\o => (o, qualify imp.mname o)) imp.opens) unit.mimports

||| Resolve a written reference (as it appears at the cursor — bare,
||| alias-opened, or already dotted/qualified) to its definition site.
||| Anything not found via the current module's own aliases is assumed
||| already-qualified, exactly like `resolveSigName`'s fallback (a
||| dotted reference reaches Σ directly).
export
resolveReference : ModUnit -> List (String, String, NRange) -> String -> Maybe (String, NRange)
resolveReference root index written =
  let qualified = fromMaybe written (lookup written (localAliases root)) in
  map (\(_, file, rng) => (file, rng)) (List.find (\(n, _, _) => n == qualified) index)

export
isNameKind : TokenKind -> Bool
isNameKind Identifier = True
isNameKind Operator   = True
isNameKind _          = False

contains : NRange -> NPosition -> Bool
contains (MkRange s e) p =
  (p.line > s.line || (p.line == s.line && p.column >= s.column)) &&
  (p.line < e.line || (p.line == e.line && p.column < e.column))

export
sliceRange : List String -> NRange -> String
sliceRange lns (MkRange (MkPosition sl sc) (MkPosition el ec)) =
  if sl /= el
    then "" -- shouldn't happen: identifier/operator tokens never cross a newline
    else case drop (cast sl) lns of
           (l :: _) => substr (cast sc) (cast (ec - sc)) l
           []       => ""

||| The identifier/operator text at a (codepoint-indexed) cursor
||| position, if any — resolves to `Nothing` just as often for a
||| perfectly good reason as a bad one: the cursor might be on a
||| keyword, on whitespace, or on a LOCAL (lambda/Pi-bound) name, none
||| of which have a separate global definition site to jump to.
export
findIdentifierAt : List String -> List (NRange, TokenKind) -> NPosition -> Maybe String
findIdentifierAt lns tokens pos = do
  (rng, _) <- List.find (\(r, k) => isNameKind k && contains r pos) tokens
  pure (sliceRange lns rng)

declSymbolKind : SQRes -> SymbolKind
declSymbolKind SQResU          = Struct
declSymbolKind (SQResEl _)     = Constructor
declSymbolKind (SQResEq _ _ _) = Operator

mkSymbol : List String -> String -> SymbolKind -> NRange -> DocumentSymbol
mkSymbol lns name kind rng =
  let r = toLspRange lns rng in
  MkDocumentSymbol
    { name           = name
    , detail         = Nothing
    , kind           = kind
    , tags           = Nothing
    , deprecated     = Nothing
    , range          = r
    , selectionRange = r
    , children       = Nothing
    }

||| One `DocumentSymbol` per name an item defines (flat — an `SData`
||| literal's several declarations become several top-level symbols
||| sharing the literal's range, rather than nested `children`, to
||| avoid `DocumentSymbol.children`'s `Inf`-wrapped recursion for a
||| depth this AST never actually needs).
export
documentSymbols : (lns : List String) -> List (Maybe NRange, SItem) -> List DocumentSymbol
documentSymbols lns = concatMap toSymbols
 where
  toSymbols : (Maybe NRange, SItem) -> List DocumentSymbol
  toSymbols (rng, item) =
    let r = itemRange rng in
    case item of
      SDef x _ _ _  => [mkSymbol lns x Function r]
      SDeclDef _ x _ => [mkSymbol lns x Function r]
      STypeDef x _  => [mkSymbol lns x Class r]
      SData _ decls => map (\d => mkSymbol lns d.dqname (declSymbolKind d.dqres) r) decls
      SClausalDef _ x _ eta _ cls => map (\n => mkSymbol lns n Function r) (clausalNames x eta cls)
      SCopatternDef _ x _ _ eta _ _ _ cn => map (\n => mkSymbol lns n Function r) (copatternNames x cn eta)
