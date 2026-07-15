module Nova.Foundation.Rejection.Pretty

import Nova.Foundation.Syntax
import Nova.Foundation.Derivation
import Nova.Foundation.Pretty

%default covering

export
prettyRejection : Rejection -> String
prettyRejection (CtxWfNotDerivable ctx) =
  "not derivable: ctx-wf " ++ prettyCtx ctx
prettyRejection (CtxEqNotDerivable ctx0 ctx1) =
  "not derivable: ctx-eq " ++ prettyCtx ctx0 ++ " ≐ " ++ prettyCtx ctx1
prettyRejection (SubWfNotDerivable sigma gamma delta) =
  "not derivable: sub-wf " ++ prettySub sigma ++ " : " ++ prettyCtx gamma ++ " ⇒ " ++ prettyCtx delta
prettyRejection (SubEqNotDerivable s0 s1 gamma delta) =
  "not derivable: sub-eq " ++ prettySub s0 ++ " ≐ " ++ prettySub s1 ++
    " : " ++ prettyCtx gamma ++ " ⇒ " ++ prettyCtx delta
prettyRejection (SubNormWfNotDerivable sigma gamma delta) =
  "not derivable: sub-norm-wf " ++ prettySubNorm sigma ++ " : " ++ prettyCtx gamma ++ " ⇒ " ++ prettyCtx delta ++ " norm"
prettyRejection (SubNormEqNotDerivable s0 s1 gamma delta) =
  "not derivable: sub-norm-eq " ++ prettySubNorm s0 ++ " ≐ " ++ prettySubNorm s1 ++
    " : " ++ prettyCtx gamma ++ " ⇒ " ++ prettyCtx delta ++ " norm"
prettyRejection (TyWfNotDerivable ctx ty) =
  "not derivable: ty-wf " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTy ty
prettyRejection (TyEqNotDerivable ctx ty0 ty1) =
  "not derivable: ty-eq " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTy ty0 ++ " ≐ " ++ prettyTy ty1
prettyRejection (ElemWfNotDerivable ctx e ty) =
  "not derivable: el-wf " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem e ++ " : " ++ prettyTy ty
prettyRejection (ElemEqNotDerivable ctx e0 e1 ty) =
  "not derivable: el-eq " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem e0 ++ " ≐ " ++ prettyElem e1 ++
    " : " ++ prettyTy ty
prettyRejection (TelWfNotDerivable ctx tel) =
  "not derivable: tel-wf " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTel tel
prettyRejection (TelEqNotDerivable ctx tel0 tel1) =
  "not derivable: tel-eq " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTel tel0 ++ " ≐ " ++ prettyTel tel1
prettyRejection (SpineWfNotDerivable ctx spine tel) =
  "not derivable: sp-wf " ++ prettyCtx ctx ++ " ⊦ " ++ prettySpine spine ++ " : " ++ prettyTel tel
prettyRejection (SpineEqNotDerivable ctx s0 s1 tel) =
  "not derivable: sp-eq " ++ prettyCtx ctx ++ " ⊦ " ++ prettySpine s0 ++ " ≐ " ++ prettySpine s1 ++
    " : " ++ prettyTel tel
prettyRejection (SigIdentifierNotFound x) =
  "identifier not found in signature: " ++ x
prettyRejection (SigIdentifierAlreadyDefined x) =
  "identifier already defined in signature: " ++ x
prettyRejection (SigIdentifierNotATermDef x) =
  "signature identifier is not a term definition: " ++ x
prettyRejection (SigIdentifierNotATypeDef x) =
  "signature identifier is not a type definition: " ++ x
prettyRejection (CtxVarOutOfBounds ctx n) =
  "index out of bounds: " ++ prettyElemAtom (CtxVar n) ++ " in " ++ prettyCtx ctx
