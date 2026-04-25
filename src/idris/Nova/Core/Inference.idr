module Nova.Core.Inference

import Nova.Control.Monad.Id

import Nova.Core.Context
import Nova.Core.Evaluation
import Nova.Core.Language

-- Every Elem has a canonical syntactic type
-- Moreover, every Elem has a unique type up to equality.

public export
inferNu : Signature -> Omega -> Context -> Elem -> EvalM Typ
inferNu sig omega ctx (PiTy str x y) = pure UniverseTy
inferNu sig omega ctx (ImplicitPiTy str x y) = pure UniverseTy
inferNu sig omega ctx (SigmaTy str x y) = pure UniverseTy
inferNu sig omega ctx (PiVal x dom cod f) = pure (PiTy x dom cod)
inferNu sig omega ctx (ImplicitPiVal x dom cod f) = pure (ImplicitPiTy x dom cod)
inferNu sig omega ctx (SigmaVal x dom cod p q) = pure (SigmaTy x dom cod)
inferNu sig omega ctx (PiElim f x dom cod e) = pure (ContextSubstElim cod (Ext Id e))
inferNu sig omega ctx (ImplicitPiElim f x dom cod e) = pure (ContextSubstElim cod (Ext Id e))
inferNu sig omega ctx (SigmaElim1 f x dom cod) = pure dom
inferNu sig omega ctx (SigmaElim2 f x dom cod) = pure (ContextSubstElim cod (Ext Id (SigmaElim1 f x dom cod)))
inferNu sig omega ctx NatVal0 = pure NatTy
inferNu sig omega ctx (NatVal1 x) = pure NatTy
inferNu sig omega ctx NatTy = pure UniverseTy
inferNu sig omega ctx (NatElim x schema z y h s t) = pure (ContextSubstElim schema (Ext Id t))
inferNu sig omega ctx (ContextSubstElim x y) = assert_total $ idris_crash "inferNu(ContextSubstElim)"
inferNu sig omega ctx (SignatureSubstElim x y) = assert_total $ idris_crash "inferNu(SignatureSubstElim)"
inferNu sig omega ctx (ContextVarElim k) = Id.do
  case lookupContext ctx k of
    Just (x, ty) => pure ty
    Nothing => assert_total $ idris_crash "inferNu(ContextVarElim)"
inferNu sig omega ctx (SignatureVarElim k tau) =
  case lookupSignature sig k of
    Just (x, e) =>
      case mbElemSignature e of
        Just (delta, ty) => pure (ContextSubstElim ty tau)
        Nothing => assert_total $ idris_crash "inferNu(SignatureVarElim(1))"
    Nothing => assert_total $ idris_crash "inferNu(SignatureVarElim(2))"
inferNu sig omega ctx (OmegaVarElim x tau) =
  case lookupOmega omega x of
    Just e =>
      case mbElemSignature e of
        Just (ctx, ty) => pure (ContextSubstElim ty tau)
        Nothing =>  assert_total $ idris_crash "inferNu(OmegaVarElim(1))"
    Nothing => assert_total $ idris_crash "inferNu(OmegaVarElim(2))"
inferNu sig omega ctx (TyEqTy x y) = pure UniverseTy
inferNu sig omega ctx (ElEqTy x y z) = pure UniverseTy
inferNu sig omega ctx (TyEqVal ty) = pure (TyEqTy ty ty)
inferNu sig omega ctx (ElEqVal ty a) = pure (ElEqTy a a ty)
inferNu sig omega ctx ZeroTy = pure UniverseTy
inferNu sig omega ctx OneTy = pure UniverseTy
inferNu sig omega ctx OneVal = pure OneTy
inferNu sig omega ctx (ZeroElim ty y) = pure ty

public export
infer : Signature -> Omega -> Context -> Elem -> EvalM Typ
infer sig omega ctx el = inferNu sig omega ctx !(openEval sig omega el)
