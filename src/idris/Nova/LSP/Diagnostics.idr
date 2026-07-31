module Nova.LSP.Diagnostics

import Data.String

import Language.JSON
import Language.LSP.Message.Diagnostics
import Language.LSP.Message.Location

import Me.Russoul.Text.Range
import Me.Russoul.Text.Position

import Nova.Elaboration
import Nova.Elaboration.Surface
import Nova.LSP.Encoding

wholeDocument : Location.Range
wholeDocument = Location.MkRange (Location.MkPosition 0 0) (Location.MkPosition 0 0)

mkDiagnosticAt : DiagnosticSeverity -> Location.Range -> String -> Diagnostic
mkDiagnosticAt sev range message =
  MkDiagnostic
    { range              = range
    , severity           = Just sev
    , code               = Nothing
    , codeDescription    = Nothing
    , source             = Just "nova"
    , message            = message
    , tags               = Nothing
    , relatedInformation = Nothing
    , data_              = Nothing
    }

mkDiagnostic : Location.Range -> String -> Diagnostic
mkDiagnostic = mkDiagnosticAt Error

-- an obligation/error range belonging to a module other than the
-- root ("" — see `Nova.Elaboration.Loader.loadProgram`) is a
-- position in a DIFFERENT file, not this document, so it's reported
-- at a whole-document range with the module named in the message
-- instead of silently mislocating it.
rangeFor : List String -> String -> Maybe Me.Russoul.Text.Range.Range -> Location.Range
rangeFor lns "" (Just r) = toLspRange lns r
rangeFor _   _  _        = wholeDocument

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
||| `Nova.Elaboration.elabProgramReport`. `source` is the open
||| document's own text — ranges need it to convert codepoint columns
||| to LSP's UTF-16 ones (see `Nova.LSP.Encoding`).
export
toDiagnostics : (source : String) -> FixTable -> ElabReport -> List Diagnostic
toDiagnostics source tbl report =
  let lns = lines source in
  map (\(mname, rng, o) => mkDiagnostic (rangeFor lns mname rng) (annotate mname (prettyObligation tbl 0 o)))
      report.obligations
  ++
  -- open holes are the WORKING state of a development, not a defect
  -- in it: acceptance is blocked, but every hole is something the
  -- user deliberately wrote — a warning, not an error
  map (\(mname, rng, h) => mkDiagnosticAt Warning (rangeFor lns mname rng) (annotate mname h))
      report.holes
  ++
  map (\(mname, rng, msg) => mkDiagnostic (rangeFor lns mname rng) (annotate mname msg))
      report.errors
