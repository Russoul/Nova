module Nova.LSP.SemanticTokens

import Data.List
import Data.String

import Me.Russoul.Text.Range
import Me.Russoul.Text.Position

import Nova.Kernel.Parser
import Nova.LSP.Capabilities
import Nova.LSP.Encoding

compareStart : (Range, a) -> (Range, a) -> Ordering
compareStart (r1, _) (r2, _) =
  case compare r1.start.line r2.start.line of
    EQ => compare r1.start.column r2.start.column
    o  => o

||| LSP's relative-delta encoding is only meaningful over a single,
||| start-position-ordered pass, so this always runs before `encode`.
sortTokens : List (Range, a) -> List (Range, a)
sortTokens = sortBy compareStart

||| [deltaLine, deltaStartChar (relative to the PREVIOUS token's start,
||| only when on the same line — otherwise absolute), length,
||| tokenType, tokenModifiers] per token, per the LSP spec's relative
||| semantic-tokens wire format.
encode : (Int, Int) -> List (Range, Int) -> List Int
encode _ [] = []
encode (relLine, relStartChar) ((MkRange (MkPosition sl sc) (MkPosition _ ec), kind) :: xs) =
     [ sl - relLine
     , if sl == relLine then sc - relStartChar else sc
     , ec - sc
     , kind
     , 0
     ] ++ encode (sl, sc) xs

||| Assumes no token spans more than one line — true for every kind
||| this server emits (see `Nova.Elaboration.Parser`'s `kw`/`kwc`/
||| `parseName`/`parseOpName`/digit-literal instrumentation: none of
||| them can consume a newline).
convertTokens : (lastLineNum : Int) -> List String -> List (Range, a) -> List (Range, a)
convertTokens _ _ [] = []
convertTokens lastLineNum ls ((MkRange (MkPosition sl sc) (MkPosition el ec), kind) :: rest) =
  case drop (cast (sl - lastLineNum)) ls of
    (line :: ls') =>
      (MkRange (MkPosition sl (codepointToUtf16 line sc)) (MkPosition el (codepointToUtf16 line ec)), kind)
        :: convertTokens sl (line :: ls') rest
    [] => [] -- must not happen: sl always indexes a real line of `source`

posLE : Position -> Position -> Bool
posLE (MkPosition l1 c1) (MkPosition l2 c2) = l1 < l2 || (l1 == l2 && c1 <= c2)

within : (inner : Range) -> (outer : Range) -> Bool
within inner outer = posLE outer.start inner.start && posLE inner.end outer.end

||| Parser kinds carry no elaboration state, so hole occurrences come
||| out as plain identifiers (plus a keyword token for a `?` sigil);
||| reclassify every token inside a hole occurrence range by the
||| hole's state instead. `holeOccs` pairs each occurrence range with
||| whether the hole is SOLVED.
overlay : List (Range, Bool) -> (Range, TokenKind) -> (Range, Int)
overlay occs (r, k) =
  case find (\(hr, _) => within r hr) occs of
    Just (_, solved) => (r, if solved then solvedHoleIndex else unsolvedHoleIndex)
    Nothing          => (r, tokenKindIndex k)

||| Encode a document's classified tokens for a `semanticTokens/full`
||| response's `data` array. Always UTF-16 code-unit offsets — the LSP
||| default when `positionEncoding` isn't negotiated (which our pinned
||| `lsp-lib` doesn't model at all), and what every mainstream client
||| (VS Code included) assumes in that case.
export
getSemanticTokens : String -> List (Range, TokenKind) -> (holeOccs : List (Range, Bool)) -> List Int
getSemanticTokens source toks holeOccs =
  let sorted = sortTokens (map (overlay holeOccs) toks)
      ls     = lines source
  in encode (0, 0) (convertTokens 0 ls sorted)
