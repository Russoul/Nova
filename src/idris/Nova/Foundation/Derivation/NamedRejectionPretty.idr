module Nova.Foundation.Derivation.NamedRejectionPretty

-- Mirrors Nova.Foundation.Rejection.Pretty using the named printer.

import Nova.Foundation.Syntax
import Nova.Foundation.Derivation
import Nova.Foundation.Pretty
import Nova.Foundation.Derivation.NamedParser
import Nova.Foundation.Derivation.NamedPretty

%default covering

export
prettyRejectionN : Rejection -> String
prettyRejectionN (CtxWfNotDerivable ctx) =
  "not derivable: ctx-wf " ++ prettyCtxN ctx
prettyRejectionN (CtxEqNotDerivable ctx0 ctx1) =
  "not derivable: ctx-eq " ++ prettyCtxN ctx0 ++ " ≐ " ++ prettyCtxN ctx1
prettyRejectionN (SubWfNotDerivable sigma gamma delta) =
  "not derivable: sub-wf " ++ prettySubN (envForCtx gamma) sigma ++ " : " ++ prettyCtxN gamma ++ " ⇒ " ++ prettyCtxN delta
prettyRejectionN (SubEqNotDerivable s0 s1 gamma delta) =
  let env = envForCtx gamma
  in "not derivable: sub-eq " ++ prettySubN env s0 ++ " ≐ " ++ prettySubN env s1 ++
    " : " ++ prettyCtxN gamma ++ " ⇒ " ++ prettyCtxN delta
prettyRejectionN (SubNormWfNotDerivable sigma gamma delta) =
  "not derivable: sub-norm-wf " ++ prettySubNormN (envForCtx gamma) sigma ++ " : " ++ prettyCtxN gamma ++ " ⇒ " ++ prettyCtxN delta ++ " norm"
prettyRejectionN (SubNormEqNotDerivable s0 s1 gamma delta) =
  let env = envForCtx gamma
  in "not derivable: sub-norm-eq " ++ prettySubNormN env s0 ++ " ≐ " ++ prettySubNormN env s1 ++
    " : " ++ prettyCtxN gamma ++ " ⇒ " ++ prettyCtxN delta ++ " norm"
prettyRejectionN (TyWfNotDerivable ctx ty) =
  "not derivable: ty-wf " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTyN (envForCtx ctx) ty
prettyRejectionN (TyEqNotDerivable ctx ty0 ty1) =
  let env = envForCtx ctx
  in "not derivable: ty-eq " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTyN env ty0 ++ " ≐ " ++ prettyTyN env ty1
prettyRejectionN (ElemWfNotDerivable ctx e ty) =
  let env = envForCtx ctx
  in "not derivable: el-wf " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN env e ++ " : " ++ prettyTyN env ty
prettyRejectionN (ElemEqNotDerivable ctx e0 e1 ty) =
  let env = envForCtx ctx
  in "not derivable: el-eq " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN env e0 ++ " ≐ " ++ prettyElemN env e1 ++
    " : " ++ prettyTyN env ty
prettyRejectionN (TelWfNotDerivable ctx tel) =
  "not derivable: tel-wf " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTelN (envForCtx ctx) tel
prettyRejectionN (TelEqNotDerivable ctx tel0 tel1) =
  let env = envForCtx ctx
  in "not derivable: tel-eq " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTelN env tel0 ++ " ≐ " ++ prettyTelN env tel1
prettyRejectionN (SpineWfNotDerivable ctx spine tel) =
  let env = envForCtx ctx
  in "not derivable: sp-wf " ++ prettyCtxN ctx ++ " ⊦ " ++ prettySpineN env spine ++ " : " ++ prettyTelN env tel
prettyRejectionN (SpineEqNotDerivable ctx s0 s1 tel) =
  let env = envForCtx ctx
  in "not derivable: sp-eq " ++ prettyCtxN ctx ++ " ⊦ " ++ prettySpineN env s0 ++ " ≐ " ++ prettySpineN env s1 ++
    " : " ++ prettyTelN env tel
prettyRejectionN (SigIdentifierNotFound x) =
  "identifier not found in signature: " ++ x
prettyRejectionN (SigIdentifierAlreadyDefined x) =
  "identifier already defined in signature: " ++ x
prettyRejectionN (SigIdentifierNotATermDef x) =
  "signature identifier is not a term definition: " ++ x
prettyRejectionN (SigIdentifierNotATypeDef x) =
  "signature identifier is not a type definition: " ++ x
prettyRejectionN (PiAppInferenceFailed ctx f e) =
  "no Π-typed fact for the function (or none accepting the argument) in: " ++
    prettyCtxN ctx ++ " ⊦ " ++ prettyElemN (envForCtx ctx) (PiApp f e)

prettyRejectionN (CtxVarOutOfBounds ctx n) =
  "index out of bounds: " ++ nameAt (envForCtx ctx) n ++ " in " ++ prettyCtxN ctx
-- ===== Near-miss rendering =====

joinWith : String -> List String -> String
joinWith _ []          = ""
joinWith _ [x]         = x
joinWith sep (x :: xs) = x ++ sep ++ joinWith sep xs

export
prettyHintN : Hint -> String
prettyHintN HintQueryCtxNotWf =
  "the query's context is not derivably well-formed (some entry's type has no derivation and does not synthesize) — weakening and conversion are disabled until it is"
prettyHintN (HintCtxPrefixDerived pfx ty) =
  "longest derived prefix: " ++ prettyCtxN pfx ++ " — the next entry " ++
    prettyTyN (envForCtx pfx) ty ++ " needs ty-wf and ctx-ext"
prettyHintN (HintAtOtherTypes ctx tys) =
  let env = envForCtx ctx
  in "derived here at other type(s): " ++ joinWith " | " (map (prettyTyN env) tys) ++
     " — conversion is automatic once the queried type is derivably well-formed here and beta-equal to one of these; since this query failed, derive the queried type's ty-wf first, or bridge a non-computational equality with el-ty-coe"
prettyHintN (HintInOtherCtxs ctxs) =
  "the exact judgement holds only in other context(s): " ++ joinWith " | " (map prettyCtxN ctxs)
prettyHintN (HintEqGuardMissing side subs) =
  "the " ++ side ++ " side has no wf fact at the queried type" ++
    (case subs of
       [] => ""
       _  => " (" ++ joinWith "; " (map prettyHintN subs) ++ ")")
prettyHintN HintEqNeedsContent =
  "both sides are well-formed, but their normal forms differ and no stored equality bridges them — this equality needs real content (lemma / congruence / transitivity)"
prettyHintN HintReversedEq =
  "the reversed equality is a stored fact — one sym step away"
prettyHintN (HintElemEqEndpoints ctx eqs) =
  let env = envForCtx ctx
  in "stored equalities sharing an endpoint: " ++
     joinWith " | " (map (\(a, b) => prettyElemN env a ++ " ≐ " ++ prettyElemN env b) eqs)
prettyHintN (HintTyEqEndpoints ctx eqs) =
  let env = envForCtx ctx
  in "stored equalities sharing an endpoint: " ++
     joinWith " | " (map (\(a, b) => prettyTyN env a ++ " ≐ " ++ prettyTyN env b) eqs)
prettyHintN (HintPiArg ctx doms argTys) =
  let env = envForCtx ctx
  in "the function has Π-type(s) with domain(s): " ++ joinWith " | " (map (prettyTyN env) doms) ++
     (case argTys of
        [] => " — but the argument has no derived type at all"
        _  => " — but the argument is derived only at: " ++ joinWith " | " (map (prettyTyN env) argTys))

||| A "\n  Near misses:" block for appending after a rejection's Reason
||| line (empty string when there is nothing useful to say).
export
prettyNearMissesN : Truth -> Rejection -> String
prettyNearMissesN truth r =
  case diagnose truth r of
    [] => ""
    hs => "\n  Near misses:\n" ++ joinWith "\n" (map (\h => "    • " ++ prettyHintN h) hs)

