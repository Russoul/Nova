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
prettyRejectionN (CtxVarOutOfBounds ctx n) =
  "index out of bounds: " ++ nameAt (envForCtx ctx) n ++ " in " ++ prettyCtxN ctx
