module Nova.Foundation.Elaboration.ElaboratorTest

-- Isolates Nova.Foundation.Elaboration.Elaborator's dispatch from
-- Nova.Foundation.Test.Main the same way Nova.Foundation.Elaboration.Test
-- does for the surface parsers: this module aliases both Ctx/Ty/Elem/...
-- namesakes (Low vs Surface) itself, exactly like Elaborator.idr does, and
-- only ever exports Strings — so importing it never leaks either name to
-- a module that also wants Nova.Foundation.Syntax's own bare names.
--
-- Every elaborateX judgement is exercised by building each "given" index
-- from surface syntax via the elaborator itself (never a hand-rolled low
-- value): e.g. to test elaborateTy, first elaborateCtx the given context,
-- then elaborateTy the term under test against it. A failure while
-- building a "given" piece is a malformed test (reported as
-- PRECONDITION-ERROR), distinct from the judgement-under-test's own
-- Left/Right result (reported as "Error: ..." / "Ok: ...").

import Data.SnocList
import Nova.Foundation.Parser
import Nova.Foundation.Syntax as Low
import Nova.Foundation.Elaboration.Syntax as Surface
import Nova.Foundation.Elaboration.Parser
import Nova.Foundation.Elaboration.Elaborator

%default covering

buildSig : String -> Either String Low.Sig
buildSig s =
  case runParser Nova.Foundation.Elaboration.Parser.parseSig s of
    Left e => Left "PARSE-ERROR(sig): \{e}"
    Right surfaceSig =>
      case elaborateSig surfaceSig of
        Left err => Left "PRECONDITION-ERROR(sig): \{show err}"
        Right lowSig => Right lowSig

buildCtx : Low.Sig -> String -> Either String Low.Ctx
buildCtx sig s =
  case runParser Nova.Foundation.Elaboration.Parser.parseCtx s of
    Left e => Left "PARSE-ERROR(ctx): \{e}"
    Right surfaceCtx =>
      case elaborateCtx sig surfaceCtx of
        Left err => Left "PRECONDITION-ERROR(ctx): \{show err}"
        Right lowCtx => Right lowCtx

buildTy : Low.Sig -> Low.Ctx -> String -> Either String Low.Ty.Ty
buildTy sig ctx s =
  case runParser parseTy0 s of
    Left e => Left "PARSE-ERROR(ty): \{e}"
    Right surfaceTy =>
      case elaborateTy sig ctx surfaceTy of
        Left err => Left "PRECONDITION-ERROR(ty): \{show err}"
        Right lowTy => Right lowTy

buildElem : Low.Sig -> Low.Ctx -> Low.Ty.Ty -> String -> Either String Low.Elem.Elem
buildElem sig ctx ty s =
  case runParser parseElem0 s of
    Left e => Left "PARSE-ERROR(elem): \{e}"
    Right surfaceElem =>
      case elaborateElem sig ctx ty surfaceElem of
        Left err => Left "PRECONDITION-ERROR(elem): \{show err}"
        Right lowElem => Right lowElem

buildSubNorm : Low.Sig -> Low.Ctx -> Low.Ctx -> String -> Either String Low.SubNorm
buildSubNorm sig dom cod s =
  case runParser parseSubNorm0 s of
    Left e => Left "PARSE-ERROR(sub-norm): \{e}"
    Right surfaceSubNorm =>
      case elaborateSubNorm sig dom cod surfaceSubNorm of
        Left err => Left "PRECONDITION-ERROR(sub-norm): \{show err}"
        Right lowSubNorm => Right lowSubNorm

showResult : Show e => Show a => Either e a -> String
showResult = either (\e => "Error: \{show e}") (\v => "Ok: \{show v}")

showUnitResult : Either ElabError () -> String
showUnitResult = either (\e => "Error: \{show e}") (const "Ok")

||| Dispatch a `run elab <tag> <arg...>` request to one of the elaborator
||| judgements. Returns Nothing for an unrecognized tag/arity (so the caller
||| can fall through to its own "unknown" message).
export
runElaborate : String -> List String -> Maybe String
runElaborate "ctx" [sigStr, ctxStr] = Just $
  case buildSig sigStr of
    Left e => e
    Right sig =>
      case runParser Nova.Foundation.Elaboration.Parser.parseCtx ctxStr of
        Left e => "PARSE-ERROR: \{e}"
        Right surfaceCtx => showResult (elaborateCtx sig surfaceCtx)
runElaborate "ty" [sigStr, ctxStr, tyStr] = Just $
  case buildSig sigStr of
    Left e => e
    Right sig => case buildCtx sig ctxStr of
      Left e => e
      Right ctx =>
        case runParser parseTy0 tyStr of
          Left e => "PARSE-ERROR: \{e}"
          Right surfaceTy => showResult (elaborateTy sig ctx surfaceTy)
runElaborate "elem" [sigStr, ctxStr, tyStr, elemStr] = Just $
  case buildSig sigStr of
    Left e => e
    Right sig => case buildCtx sig ctxStr of
      Left e => e
      Right ctx => case buildTy sig ctx tyStr of
        Left e => e
        Right ty =>
          case runParser parseElem0 elemStr of
            Left e => "PARSE-ERROR: \{e}"
            Right surfaceElem => showResult (elaborateElem sig ctx ty surfaceElem)
runElaborate "sub" [sigStr, domStr, codStr, subStr] = Just $
  case buildSig sigStr of
    Left e => e
    Right sig => case buildCtx sig domStr of
      Left e => e
      Right dom => case buildCtx sig codStr of
        Left e => e
        Right cod =>
          case runParser parseSub0 subStr of
            Left e => "PARSE-ERROR: \{e}"
            Right surfaceSub => showResult (elaborateSub sig dom cod surfaceSub)
runElaborate "ctx-eq" [sigStr, ctx0Str, ctx1Str, ctxEqStr] = Just $
  case buildSig sigStr of
    Left e => e
    Right sig => case buildCtx sig ctx0Str of
      Left e => e
      Right ctx0 => case buildCtx sig ctx1Str of
        Left e => e
        Right ctx1 =>
          case runParser parseCtxEq0 ctxEqStr of
            Left e => "PARSE-ERROR: \{e}"
            Right surfaceCtxEq => showUnitResult (elaborateCtxEq sig ctx0 ctx1 surfaceCtxEq)
runElaborate "ty-eq" [sigStr, ctxStr, ty0Str, ty1Str, tyEqStr] = Just $
  case buildSig sigStr of
    Left e => e
    Right sig => case buildCtx sig ctxStr of
      Left e => e
      Right ctx => case buildTy sig ctx ty0Str of
        Left e => e
        Right ty0 => case buildTy sig ctx ty1Str of
          Left e => e
          Right ty1 =>
            case runParser parseTyEq0 tyEqStr of
              Left e => "PARSE-ERROR: \{e}"
              Right surfaceTyEq => showUnitResult (elaborateTyEq sig ctx ty0 ty1 surfaceTyEq)
runElaborate "elem-eq" [sigStr, ctxStr, tyStr, elem0Str, elem1Str, elemEqStr] = Just $
  case buildSig sigStr of
    Left e => e
    Right sig => case buildCtx sig ctxStr of
      Left e => e
      Right ctx => case buildTy sig ctx tyStr of
        Left e => e
        Right ty => case buildElem sig ctx ty elem0Str of
          Left e => e
          Right elem0 => case buildElem sig ctx ty elem1Str of
            Left e => e
            Right elem1 =>
              case runParser parseElemEq0 elemEqStr of
                Left e => "PARSE-ERROR: \{e}"
                Right surfaceElemEq => showUnitResult (elaborateElemEq sig ctx ty elem0 elem1 surfaceElemEq)
runElaborate "sub-norm" [sigStr, domStr, codStr, subNormStr] = Just $
  case buildSig sigStr of
    Left e => e
    Right sig => case buildCtx sig domStr of
      Left e => e
      Right dom => case buildCtx sig codStr of
        Left e => e
        Right cod =>
          case runParser parseSubNorm0 subNormStr of
            Left e => "PARSE-ERROR: \{e}"
            Right surfaceSubNorm => showResult (elaborateSubNorm sig dom cod surfaceSubNorm)
runElaborate "sub-norm-eq" [sigStr, domStr, codStr, sn0Str, sn1Str, subNormEqStr] = Just $
  case buildSig sigStr of
    Left e => e
    Right sig => case buildCtx sig domStr of
      Left e => e
      Right dom => case buildCtx sig codStr of
        Left e => e
        Right cod => case buildSubNorm sig dom cod sn0Str of
          Left e => e
          Right sn0 => case buildSubNorm sig dom cod sn1Str of
            Left e => e
            Right sn1 =>
              case runParser parseSubNormEq0 subNormEqStr of
                Left e => "PARSE-ERROR: \{e}"
                Right surfaceSubNormEq => showUnitResult (elaborateSubNormEq sig dom cod sn0 sn1 surfaceSubNormEq)
runElaborate "sig-entry" [sigStr, entryStr] = Just $
  case buildSig sigStr of
    Left e => e
    Right sig =>
      case runParser parseSigEntry entryStr of
        Left e => "PARSE-ERROR: \{e}"
        Right surfaceEntry => showResult (elaborateSigEntry sig surfaceEntry)
runElaborate "sig" [sigStr] = Just $
  case runParser Nova.Foundation.Elaboration.Parser.parseSig sigStr of
    Left e => "PARSE-ERROR: \{e}"
    Right surfaceSig => showResult (elaborateSig surfaceSig)
runElaborate _ _ = Nothing
