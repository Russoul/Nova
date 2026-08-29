module Nova.Diagnostic

-- Terminal rendering of a LOCATED message.
--
-- Every user-facing failure — a parse error, a loader failure, a
-- structural elaboration error — funnels through `Diag`: a message,
-- the file it is about, that file's text, and (when known) the source
-- span it points at. `render` emits the conventional
--
--     file:line:col: error: message
--       12 | def bar : ℕ ≔ foo 1
--          |           ^^^^^^^^^
--
-- header — the spelling every editor and terminal recognizes as a
-- jump target — followed by the offending source line with a caret
-- run under the span, and any secondary notes.
--
-- Positions are 0-based everywhere INSIDE the compiler (the lexer's
-- convention, shared with LSP) and 1-based on screen. This module is
-- the only place that converts.

import Data.List
import Data.String

import Me.Russoul.Text.Position
import Me.Russoul.Text.Range

%default total

public export
data Severity = Err | Warn | Note

export
sevName : Severity -> String
sevName Err = "error"
sevName Warn = "warning"
sevName Note = "note"

||| A message with everything needed to place it in a source file.
||| Both `dfile` and `dsrc` may be absent — a failure with no file to
||| point at (an import cycle, say) still renders, just without a
||| header location or an excerpt.
public export
record Diag where
  constructor MkDiag
  dsev : Severity
  ||| the file this is about, spelled as the user spelled it (so the
  ||| header stays a working jump target)
  dfile : Maybe String
  ||| that file's text — the excerpt is sliced from it
  dsrc : Maybe String
  drange : Maybe Range
  dmsg : String
  ||| secondary lines, rendered under the excerpt
  dnotes : List String

||| An unlocated message: no file, no span, no excerpt.
export
plainDiag : Severity -> String -> Diag
plainDiag sev msg = MkDiag sev Nothing Nothing Nothing msg []

||| `line:col`, 1-based — the on-screen spelling of a position.
export
showPos : Position -> String
showPos p = "\{show (p.line + 1)}:\{show (p.column + 1)}"

||| `file:line:col` — a location prefix an editor can jump to. The
||| END of the span is deliberately absent: the caret run below shows
||| the extent, and a bare start position is what tooling parses.
export
showLoc : (file : String) -> Range -> String
showLoc f r = "\{f}:\{showPos r.start}"

toNat : Int -> Nat
toNat = cast

||| The source line the span STARTS on, with a caret run under it.
||| A span reaching past that line — a whole-item range, say — is
||| clipped to the line's end: the header carries the exact start, and
||| a screenful of carets helps nobody. A zero-width span (a failure
||| AT a position rather than at a token) still gets one caret.
excerptLines : String -> Range -> List String
excerptLines src (MkRange s e) =
  case drop (toNat s.line) (lines src) of
    [] => []
    (l :: _) =>
      let width  = length l
          startC = min (toNat s.column) width
          endC   = if e.line > s.line then width else min (toNat e.column) width
          span   = max 1 (minus endC startC)
          gutter = show (s.line + 1)
          pad    = replicate (length gutter) ' '
       in [ "\{gutter} | \{l}"
          , "\{pad} | \{replicate startC ' '}\{replicate span '^'}" ]

export
render : Diag -> String
render d =
  joinBy "\n" $
    [header] ++
    (case (d.dsrc, d.drange) of
       (Just s, Just r) => excerptLines s r
       _                => []) ++
    map (\n => "  note: \{n}") d.dnotes
 where
  header : String
  header =
    (case (d.dfile, d.drange) of
       (Just f, Just r)  => "\{showLoc f r}: "
       (Just f, Nothing) => "\{f}: "
       (Nothing, Just r) => "\{showPos r.start}: "
       (Nothing, Nothing) => "") ++
    "\{sevName d.dsev}: \{d.dmsg}"

||| The failure line a command prints. Everything below `elab` funnels
||| its failure out as a plain String: some are already-rendered
||| diagnostics (they carry their own "error:" header), the rest are
||| bare messages with nothing to locate them. This gives the latter
||| the header they lack without doubling it on the former.
export
errorLine : String -> String
errorLine msg =
  if isPrefixOf "\{sevName Err}: " msg || isInfixOf ": \{sevName Err}: " msg
    then msg
    else "\{sevName Err}: \{msg}"
