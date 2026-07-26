module Nova.LSP.SemanticTokens

import Data.List
import Data.String

import Me.Russoul.Text.Range
import Me.Russoul.Text.Position

import Nova.Kernel.Parser
import Nova.LSP.Capabilities
import Nova.LSP.Encoding

compareStart : (Range, TokenKind) -> (Range, TokenKind) -> Ordering
compareStart (r1, _) (r2, _) =
  case compare r1.start.line r2.start.line of
    EQ => compare r1.start.column r2.start.column
    o  => o

||| LSP's relative-delta encoding is only meaningful over a single,
||| start-position-ordered pass, so this always runs before `encode`.
sortTokens : List (Range, TokenKind) -> List (Range, TokenKind)
sortTokens = sortBy compareStart

||| [deltaLine, deltaStartChar (relative to the PREVIOUS token's start,
||| only when on the same line — otherwise absolute), length,
||| tokenType, tokenModifiers] per token, per the LSP spec's relative
||| semantic-tokens wire format.
encode : (Int, Int) -> List (Range, TokenKind) -> List Int
encode _ [] = []
encode (relLine, relStartChar) ((MkRange (MkPosition sl sc) (MkPosition _ ec), kind) :: xs) =
     [ sl - relLine
     , if sl == relLine then sc - relStartChar else sc
     , ec - sc
     , tokenKindIndex kind
     , 0
     ] ++ encode (sl, sc) xs

||| Assumes no token spans more than one line — true for every kind
||| this server emits (see `Nova.Elaboration.Parser`'s `kw`/`kwc`/
||| `parseName`/`parseOpName`/digit-literal instrumentation: none of
||| them can consume a newline).
convertTokens : (lastLineNum : Int) -> List String -> List (Range, TokenKind) -> List (Range, TokenKind)
convertTokens _ _ [] = []
convertTokens lastLineNum ls ((MkRange (MkPosition sl sc) (MkPosition el ec), kind) :: rest) =
  case drop (cast (sl - lastLineNum)) ls of
    (line :: ls') =>
      (MkRange (MkPosition sl (codepointToUtf16 line sc)) (MkPosition el (codepointToUtf16 line ec)), kind)
        :: convertTokens sl (line :: ls') rest
    [] => [] -- must not happen: sl always indexes a real line of `source`

||| Encode a document's classified tokens for a `semanticTokens/full`
||| response's `data` array. Always UTF-16 code-unit offsets — the LSP
||| default when `positionEncoding` isn't negotiated (which our pinned
||| `lsp-lib` doesn't model at all), and what every mainstream client
||| (VS Code included) assumes in that case.
export
getSemanticTokens : String -> List (Range, TokenKind) -> List Int
getSemanticTokens source toks =
  let sorted = sortTokens toks
      ls     = lines source
  in encode (0, 0) (convertTokens 0 ls sorted)
