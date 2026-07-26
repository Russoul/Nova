module Nova.LSP.Diagnostics

import Language.JSON
import Language.LSP.Message.Diagnostics
import Language.LSP.Message.Location

import Me.Russoul.Text.Range
import Me.Russoul.Text.Position

import Nova.Elaboration
import Nova.Elaboration.Surface

%default total

||| Just-a-Parser's Range/Position are already 0-indexed on both axes
||| (see `Me.Russoul.Text.Lexer.tokenise`'s own comment: "we count
||| starting at 0 for both axes, solely because LSP expects this
||| format") — same convention LSP uses, so this is a plain field copy.
toLspPosition : Me.Russoul.Text.Position.Position -> Location.Position
toLspPosition (Me.Russoul.Text.Position.MkPosition line col) = Location.MkPosition line col

toLspRange : Me.Russoul.Text.Range.Range -> Location.Range
toLspRange (Me.Russoul.Text.Range.MkRange start end) = Location.MkRange (toLspPosition start) (toLspPosition end)

wholeDocument : Location.Range
wholeDocument = Location.MkRange (Location.MkPosition 0 0) (Location.MkPosition 0 0)

mkDiagnostic : Location.Range -> String -> Diagnostic
mkDiagnostic range message =
  MkDiagnostic
    { range              = range
    , severity           = Just Error
    , code               = Nothing
    , codeDescription    = Nothing
    , source             = Just "nova"
    , message            = message
    , tags               = Nothing
    , relatedInformation = Nothing
    , data_              = Nothing
    }

-- an obligation/error range belonging to a module other than the
-- root ("" — see `Nova.Elaboration.Loader.loadProgram`) is a
-- position in a DIFFERENT file, not this document, so it's reported
-- at a whole-document range with the module named in the message
-- instead of silently mislocating it.
rangeFor : String -> Maybe Me.Russoul.Text.Range.Range -> Location.Range
rangeFor "" (Just r) = toLspRange r
rangeFor _  _        = wholeDocument

annotate : String -> String -> String
annotate "" msg = msg
annotate mname msg = "in module \{mname}: " ++ msg

||| A hard failure from `Nova.Elaboration.Loader.loadProgram` itself
||| (file not found, header parse error, import cycle, ...) — no
||| module/range to attribute it to at all, so it's whole-document.
export
loadErrorDiagnostic : String -> Diagnostic
loadErrorDiagnostic msg = mkDiagnostic wholeDocument msg

||| Diagnostics for one open document's `ElabReport` — see
||| `Nova.Elaboration.elabProgramReport`.
export
toDiagnostics : FixTable -> ElabReport -> List Diagnostic
toDiagnostics tbl report =
  map (\(mname, rng, o) => mkDiagnostic (rangeFor mname rng) (annotate mname (prettyObligation tbl 0 o)))
      report.obligations
  ++
  map (\(mname, rng, msg) => mkDiagnostic (rangeFor mname rng) (annotate mname msg))
      report.errors
