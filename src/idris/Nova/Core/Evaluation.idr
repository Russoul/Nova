module Nova.Core.Evaluation

import Data.Util
import Data.AVL

import Nova.Core.Monad
import Nova.Core.Language
import Nova.Core.Substitution

-- Closed term evaluation

lookupContextInst : ContextInst -> Nat -> M Elem
lookupContextInst [<] _ = throw "Exception in lookupContextInst"
lookupContextInst (ts :< t) 0 = return t
lookupContextInst (ts :< t) (S k) = lookupContextInst ts k

lookupSignatureInst : SignatureInst -> Nat -> M Elem
lookupSignatureInst [<] _ = throw "Exception in lookupSignatureInst"
lookupSignatureInst (ts :< t) 0 = return t
lookupSignatureInst (ts :< t) (S k) = lookupSignatureInst ts k

mutual
  ||| Σ ⊦ a ⇝ a' : A
  ||| Σ must only contain let-elem's
  public export
  closedEvalNu : Signature -> Omega -> Elem -> M Elem
  closedEvalNu sig omega NatTy = return NatTy
  closedEvalNu sig omega Universe = return Universe
  closedEvalNu sig omega (PiTy x a b) = return (PiTy x a b)
  closedEvalNu sig omega (ImplicitPiTy x a b) = return (ImplicitPiTy x a b)
  closedEvalNu sig omega (SigmaTy x a b) = return (SigmaTy x a b)
  closedEvalNu sig omega (PiVal x a b f) = return (PiVal x a b f)
  closedEvalNu sig omega (ImplicitPiVal x a b f) = return (ImplicitPiVal x a b f)
  closedEvalNu sig omega (SigmaVal a b) = return (SigmaVal a b)
  closedEvalNu sig omega (PiElim f x a b e) = M.do
    PiVal _ _ _ f <- closedEval sig omega f
      | _ => throw "closedEval(PiElim)"
    closedEval sig omega (ContextSubstElim f (Ext Terminal e))
  closedEvalNu sig omega (ImplicitPiElim f x a b e) = M.do
    ImplicitPiVal _ _ _ f <- closedEval sig omega f
      | _ => throw "closedEval(ImplicitPiElim)"
    closedEval sig omega (ContextSubstElim f (Ext Terminal e))
  closedEvalNu sig omega (SigmaElim1 f x a b) = M.do
    SigmaVal p q <- closedEval sig omega f
      | _ => throw "closedEval(SigmaElim1)"
    closedEval sig omega p
  closedEvalNu sig omega (SigmaElim2 f x a b) = M.do
    SigmaVal p q <- closedEval sig omega f
      | _ => throw "closedEval(SigmaElim2)"
    closedEval sig omega q
  closedEvalNu sig omega NatVal0 = return NatVal0
  closedEvalNu sig omega (NatVal1 t) = return (NatVal1 t)
  closedEvalNu sig omega (NatElim x schema z y h s t) = M.do
    t <- closedEval sig omega t
    case t of
      NatVal0 => closedEval sig omega z
      NatVal1 t => closedEval sig omega (ContextSubstElim s (Ext (Ext Terminal t) (NatElim x schema z y h s t)))
      _ => throw "closedEval(NatElim)"
  closedEvalNu sig omega (ContextSubstElim t sigma) = throw "closedEval(ContextSubstElim)"
  closedEvalNu sig omega (SignatureSubstElim t sigma) = throw "closedEval(SignatureSubstElim)"
  closedEvalNu sig omega (ContextVarElim x) = throw "closedEval(ContextVarElim)"
  closedEvalNu sig omega (SignatureVarElim k sigma) = M.do
    return (SignatureVarElim k sigma)
  -- Σ Ω₀ (Δ ⊦ x ≔ t : T) Ω₁ ⊦ x σ = t(σ)
  closedEvalNu sig omega (OmegaVarElim x sigma) = M.do
    case (lookup x omega) of
      Just (LetType _ rhs) => closedEval sig omega (ContextSubstElim rhs sigma)
      Just (LetElem _ rhs _) => closedEval sig omega (ContextSubstElim rhs sigma)
      _ => throw "closedEval(OmegaVarElim)"
  closedEvalNu sig omega (EqTy a0 a1 ty) = return $ EqTy a0 a1 ty
  closedEvalNu sig omega EqVal = return EqVal

  ||| Σ ⊦ a ⇝ a' : A
  ||| Σ must only contain let-elem's
  public export
  closedEval : Signature -> Omega -> Elem -> M Elem
  closedEval sig omega tm = closedEvalNu sig omega (runSubst tm)

mutual
  ||| Σ ⊦ a ⇝ a' : A
  ||| Σ must only contain let-elem's
  public export
  openEvalNu : Signature -> Omega -> Elem -> M Elem
  openEvalNu sig omega NatTy = return NatTy
  openEvalNu sig omega Universe = return Universe
  openEvalNu sig omega (PiTy x a b) = return (PiTy x a b)
  openEvalNu sig omega (ImplicitPiTy x a b) = return (ImplicitPiTy x a b)
  openEvalNu sig omega (SigmaTy x a b) = return (SigmaTy x a b)
  openEvalNu sig omega (PiVal x a b f) = return (PiVal x a b f)
  openEvalNu sig omega (ImplicitPiVal x a b f) = return (ImplicitPiVal x a b f)
  openEvalNu sig omega (SigmaVal a b) = return (SigmaVal a b)
  openEvalNu sig omega (PiElim f x a b e) = M.do
    return (PiElim f x a b e)
  openEvalNu sig omega (ImplicitPiElim f x a b e) = M.do
    return (ImplicitPiElim f x a b e)
  openEvalNu sig omega (SigmaElim1 f x a b) = M.do
    return (SigmaElim1 f x a b)
  openEvalNu sig omega (SigmaElim2 f x a b) = M.do
    return (SigmaElim2 f x a b)
  openEvalNu sig omega NatVal0 = return NatVal0
  openEvalNu sig omega (NatVal1 t) = return (NatVal1 t)
  openEvalNu sig omega (NatElim x schema z y h s t) = M.do
    return (NatElim x schema z y h s t)
  openEvalNu sig omega (ContextSubstElim t sigma) = throw "openEval(ContextSubstElim)"
  openEvalNu sig omega (SignatureSubstElim t sigma) = throw "openEval(SignatureSubstElim)"
  openEvalNu sig omega (ContextVarElim x) = return (ContextVarElim x)
  openEvalNu sig omega (SignatureVarElim k sigma) = M.do
    return (SignatureVarElim k sigma)
  -- Σ Ω₀ (Δ ⊦ x ≔ t : T) Ω₁ ⊦ x σ = t(σ)
  openEvalNu sig omega (OmegaVarElim k sigma) = M.do
    case (lookup k omega) of
      Just (LetElem _ rhs _) => openEval sig omega (ContextSubstElim rhs sigma)
      Just (LetType _ rhs) => openEval sig omega (ContextSubstElim rhs sigma)
      Just _ => return (OmegaVarElim k sigma)
      Nothing => throw "openEval(OmegaVarElim)"
  openEvalNu sig omega (EqTy a0 a1 ty) = return $ EqTy a0 a1 ty
  openEvalNu sig omega EqVal = return EqVal

  ||| Σ ⊦ a ⇝ a' : A
  ||| Computes head-normal form w.r.t. (~) relation used in unification.
  public export
  openEval : Signature -> Omega -> Elem -> M Elem
  openEval sig omega tm = openEvalNu sig omega (runSubst tm)
