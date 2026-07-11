module Nova.Foundation.Elaboration.Test

-- Isolates the elaboration-syntax parsers from Nova.Foundation.Test.Main:
-- Nova.Foundation.Elaboration.Syntax's Ctx/Ty/Elem/Sub/SubNorm/SigIdentifier
-- share names with Nova.Foundation.Syntax's, so this module is kept from
-- ever being imported alongside that one — it only ever produces Strings.

import Nova.Foundation.Parser
import Nova.Foundation.Elaboration.Syntax
import Nova.Foundation.Elaboration.Parser

||| Dispatch a `run <tag> <input>` request for one of the elaboration-syntax
||| parsers. Returns Nothing for an unrecognized tag (so the caller can fall
||| through to its own "unknown parser" message), Just "ERROR" on a parse
||| failure, Just <shown-value> on success.
export
runElabParse : String -> String -> Maybe String
runElabParse tag input =
  case tag of
    "e-ctx"         => Just $ either (const "ERROR") show (runParser Nova.Foundation.Elaboration.Parser.parseCtx input)
    "e-ctx-eq"      => Just $ either (const "ERROR") show (runParser parseCtxEq0 input)
    "e-ty"          => Just $ either (const "ERROR") show (runParser parseTy0 input)
    "e-ty-eq"       => Just $ either (const "ERROR") show (runParser parseTyEq0 input)
    "e-sub"         => Just $ either (const "ERROR") show (runParser parseSub0 input)
    "e-sub-norm"    => Just $ either (const "ERROR") show (runParser parseSubNorm0 input)
    "e-sub-norm-eq" => Just $ either (const "ERROR") show (runParser parseSubNormEq0 input)
    "e-elem"        => Just $ either (const "ERROR") show (runParser parseElem0 input)
    "e-elem-eq"     => Just $ either (const "ERROR") show (runParser parseElemEq0 input)
    "e-sig-entry"   => Just $ either (const "ERROR") show (runParser parseSigEntry input)
    "e-sig"         => Just $ either (const "ERROR") showSig (runParser parseSig input)
    _               => Nothing
