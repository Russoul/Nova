module Nova.Core.Inference

import Nova.Core.Context
import Nova.Core.Evaluation
import Nova.Core.Language
import Nova.Core.Monad

-- Every Elem has a canonical syntactic type
-- Moreover, every Elem has a unique type up to equality.

public export
inferNu : Signature -> Omega -> Context -> Elem -> M Typ
inferNu sig omega ctx (PiTy str x y) = return UniverseTy
inferNu sig omega ctx (ImplicitPiTy str x y) = return UniverseTy
inferNu sig omega ctx (SigmaTy str x y) = return UniverseTy
inferNu sig omega ctx (PiVal x dom cod f) = return (PiTy x dom cod)
inferNu sig omega ctx (ImplicitPiVal x dom cod f) = return (ImplicitPiTy x dom cod)
inferNu sig omega ctx (SigmaVal x dom cod p q) = return (SigmaTy x dom cod)
inferNu sig omega ctx (PiElim f x dom cod e) = return (ContextSubstElim cod (Ext Id e))
inferNu sig omega ctx (ImplicitPiElim f x dom cod e) = return (ContextSubstElim cod (Ext Id e))
inferNu sig omega ctx (SigmaElim1 f x dom cod) = return dom
inferNu sig omega ctx (SigmaElim2 f x dom cod) = return (ContextSubstElim cod (Ext Id (SigmaElim1 f x dom cod)))
inferNu sig omega ctx NatVal0 = return NatTy
inferNu sig omega ctx (NatVal1 x) = return NatTy
inferNu sig omega ctx NatTy = return UniverseTy
inferNu sig omega ctx (NatElim x schema z y h s t) = return (ContextSubstElim schema (Ext Id t))
inferNu sig omega ctx (ContextSubstElim x y) = assert_total $ idris_crash "inferNu(ContextSubstElim)"
inferNu sig omega ctx (SignatureSubstElim x y) = assert_total $ idris_crash "inferNu(SignatureSubstElim)"
inferNu sig omega ctx (ContextVarElim k) = M.do
  case lookupContext ctx k of
    Just (x, ty) => return ty
    Nothing => assert_total $ idris_crash "inferNu(ContextVarElim)"
inferNu sig omega ctx (SignatureVarElim k tau) =
  case lookupSignature sig k of
    Just (x, e) =>
      case mbElemSignature e of
        Just (delta, ty) => return (ContextSubstElim ty tau)
        Nothing => assert_total $ idris_crash "inferNu(SignatureVarElim(1))"
    Nothing => assert_total $ idris_crash "inferNu(SignatureVarElim(2))"
inferNu sig omega ctx (OmegaVarElim x tau) =
  case lookupOmega omega x of
    Just e =>
      case mbElemSignature e of
        Just (ctx, ty) => return (ContextSubstElim ty tau)
        Nothing =>  assert_total $ idris_crash "inferNu(OmegaVarElim(1))"
    Nothing => assert_total $ idris_crash "inferNu(OmegaVarElim(2))"
inferNu sig omega ctx (TyEqTy x y) = return UniverseTy
inferNu sig omega ctx (ElEqTy x y z) = return UniverseTy
inferNu sig omega ctx (TyEqVal ty) = return (TyEqTy ty ty)
inferNu sig omega ctx (ElEqVal ty a) = return (ElEqTy a a ty)
inferNu sig omega ctx ZeroTy = return UniverseTy
inferNu sig omega ctx OneTy = return UniverseTy
inferNu sig omega ctx OneVal = return OneTy
inferNu sig omega ctx (ZeroElim ty y) = return ty

public export
infer : Signature -> Omega -> Context -> Elem -> M Typ
infer sig omega ctx el = inferNu sig omega ctx !(openEval sig omega el)
