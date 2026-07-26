module Nova.LSP.Encoding

-- Our own Range/Position (Me.Russoul.Text.*) are codepoint-indexed;
-- LSP wants UTF-16 code-unit offsets whenever `positionEncoding` isn't
-- negotiated (which our pinned lsp-lib doesn't model at all — see
-- Nova.LSP.SemanticTokens). EVERY position/range we send to or read
-- from the client goes through here, not just semantic tokens, so a
-- line with a non-BMP character (𝕌, 𝟘, 𝟙) can't silently desync some
-- OTHER feature the way it briefly did for semantic tokens.

import Data.String

import Me.Russoul.Text.Range
import Me.Russoul.Text.Position

import Language.LSP.Message.Location

||| Codepoint index -> UTF-16 offset, within one line.
export
codepointToUtf16 : String -> Int -> Int
codepointToUtf16 line wantedI = go 0 0
 where
  n : Int
  n = cast (length line)
  go : Int -> Int -> Int
  go i acc =
    if i >= wantedI || i >= n
      then acc
      else go (1 + i) (acc + (if ord (assert_total (strIndex line (cast i))) <= 0xFFFF then 1 else 2))

||| UTF-16 offset -> codepoint index, within one line — the inverse,
||| needed to translate a position the CLIENT sends us (e.g. a
||| go-to-definition cursor) back into our own coordinate system.
export
utf16ToCodepoint : String -> Int -> Int
utf16ToCodepoint line wantedU16 = go 0 0
 where
  n : Int
  n = cast (length line)
  go : Int -> Int -> Int
  go i u16 =
    if u16 >= wantedU16 || i >= n
      then i
      else go (1 + i) (u16 + (if ord (assert_total (strIndex line (cast i))) <= 0xFFFF then 1 else 2))

||| One of our own (codepoint-indexed) positions -> LSP's (UTF-16
||| -indexed) Position. `lns` must be the SAME source the position was
||| computed against, indexed by (0-based) line number.
export
toLspPosition : (lns : List String) -> Me.Russoul.Text.Position.Position -> Location.Position
toLspPosition lns (Me.Russoul.Text.Position.MkPosition line col) =
  case drop (cast line) lns of
    (l :: _) => Location.MkPosition line (codepointToUtf16 l col)
    []       => Location.MkPosition line col -- shouldn't happen: line always indexes a real source line

export
toLspRange : (lns : List String) -> Me.Russoul.Text.Range.Range -> Location.Range
toLspRange lns (Me.Russoul.Text.Range.MkRange start end) = Location.MkRange (toLspPosition lns start) (toLspPosition lns end)

||| The inverse: an LSP Position (as sent by e.g. a go-to-definition
||| request) back to our own codepoint-indexed Position. Ranges span
||| potentially different lines on each end, so start/end are each
||| looked up against their OWN line independently — no single-line
||| assumption here (that one's specific to semantic tokens).
export
fromLspPosition : (lns : List String) -> Location.Position -> Me.Russoul.Text.Position.Position
fromLspPosition lns (Location.MkPosition line ch) =
  case drop (cast line) lns of
    (l :: _) => Me.Russoul.Text.Position.MkPosition line (utf16ToCodepoint l ch)
    []       => Me.Russoul.Text.Position.MkPosition line ch
