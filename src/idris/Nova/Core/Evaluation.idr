module Nova.Core.Evaluation

import Data.Util
import Data.AVL

import Nova.Core.Monad
import Nova.Core.Language
import Nova.Core.Substitution

-- Closed term evaluation

mutual
  namespace Elem
    ||| Σ ⊦ a ⇝ a' : A
    ||| Σ must only contain let-elem's
    public export
    closedEvalNu : Signature -> Omega -> Elem -> M Elem
    closedEvalNu sig omega NatTy = return NatTy
    closedEvalNu sig omega ZeroTy = return ZeroTy
    closedEvalNu sig omega OneTy = return OneTy
    closedEvalNu sig omega OneVal = return OneVal
    closedEvalNu sig omega (ZeroElim ty t) = throw "closedEval(ZeroElim)"
    closedEvalNu sig omega (PiTy x a b) = return (PiTy x a b)
    closedEvalNu sig omega (ImplicitPiTy x a b) = return (ImplicitPiTy x a b)
    closedEvalNu sig omega (SigmaTy x a b) = return (SigmaTy x a b)
    closedEvalNu sig omega (PiVal x a b f) = return (PiVal x a b f)
    closedEvalNu sig omega (ImplicitPiVal x a b f) = return (ImplicitPiVal x a b f)
    closedEvalNu sig omega (SigmaVal x a b p q) = return (SigmaVal x a b p q)
    closedEvalNu sig omega (PiElim f x a b e) = M.do
      PiVal _ _ _ f <- closedEval sig omega f
        | _ => throw "closedEval(PiElim)"
      closedEval sig omega (ContextSubstElim f (Ext Terminal e))
    closedEvalNu sig omega (ImplicitPiElim f x a b e) = M.do
      ImplicitPiVal _ _ _ f <- closedEval sig omega f
        | _ => throw "closedEval(ImplicitPiElim)"
      closedEval sig omega (ContextSubstElim f (Ext Terminal e))
    closedEvalNu sig omega (SigmaElim1 f x a b) = M.do
      SigmaVal _ _ _ p q <- closedEval sig omega f
        | _ => throw "closedEval(SigmaElim1)"
      closedEval sig omega p
    closedEvalNu sig omega (SigmaElim2 f x a b) = M.do
      SigmaVal _ _ _ p q <- closedEval sig omega f
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
        Just (LetElem _ rhs _) => closedEval sig omega (ContextSubstElim rhs sigma)
        _ => throw "closedEval(OmegaVarElim)"
    closedEvalNu sig omega (TyEqTy a0 a1) = return $ TyEqTy a0 a1
    closedEvalNu sig omega (ElEqTy a0 a1 ty) = return $ ElEqTy a0 a1 ty
    closedEvalNu sig omega (TyEqVal ty) = return (TyEqVal ty)
    closedEvalNu sig omega (ElEqVal ty e) = return (ElEqVal ty e)

    ||| Σ ⊦ a ⇝ a' : A
    ||| Σ must only contain let-elem's
    public export
    closedEval : Signature -> Omega -> Elem -> M Elem
    closedEval sig omega tm = closedEvalNu sig omega (runSubst tm)

    ||| Σ ⊦ a ⇝ a' : A
    ||| Σ must only contain let-elem's
    public export
    openEvalNu : Signature -> Omega -> Elem -> M Elem
    openEvalNu sig omega ZeroTy = return ZeroTy
    openEvalNu sig omega OneTy = return OneTy
    openEvalNu sig omega NatTy = return NatTy
    openEvalNu sig omega OneVal = return OneVal
    openEvalNu sig omega (ZeroElim ty t) = M.do
      return (ZeroElim ty t)
    openEvalNu sig omega (PiTy x a b) = return (PiTy x a b)
    openEvalNu sig omega (ImplicitPiTy x a b) = return (ImplicitPiTy x a b)
    openEvalNu sig omega (SigmaTy x a b) = return (SigmaTy x a b)
    openEvalNu sig omega (PiVal x a b f) = return (PiVal x a b f)
    openEvalNu sig omega (ImplicitPiVal x a b f) = return (ImplicitPiVal x a b f)
    openEvalNu sig omega (SigmaVal x a b p q) = return (SigmaVal x a b p q)
    openEvalNu sig omega (PiElim f x a b e) = M.do
      PiVal _ _ _ f <- openEval sig omega f
        | f => return (PiElim f x a b e)
      openEval sig omega (ContextSubstElim f (Ext Id e))
    openEvalNu sig omega (ImplicitPiElim f x a b e) = M.do
      ImplicitPiVal _ _ _ f <- openEval sig omega f
        | f => return (ImplicitPiElim f x a b e)
      openEval sig omega (ContextSubstElim f (Ext Id e))
    openEvalNu sig omega (SigmaElim1 f x a b) = M.do
      SigmaVal _ _ _ p q <- openEval sig omega f
        | f => return (SigmaElim1 f x a b)
      openEval sig omega p
    openEvalNu sig omega (SigmaElim2 f x a b) = M.do
      SigmaVal _ _ _ p q <- openEval sig omega f
        | f => return (SigmaElim2 f x a b)
      openEval sig omega q
    openEvalNu sig omega NatVal0 = return NatVal0
    openEvalNu sig omega (NatVal1 t) = return (NatVal1 t)
    openEvalNu sig omega (NatElim x schema z y h s t) = M.do
      t <- openEval sig omega t
      case t of
        NatVal0 => openEval sig omega z
        NatVal1 t => openEval sig omega (ContextSubstElim s (Ext (Ext Id t) (NatElim x schema z y h s t)))
        t => return (NatElim x schema z y h s t)
    openEvalNu sig omega (ContextSubstElim t sigma) = throw "openEval(ContextSubstElim)"
    openEvalNu sig omega (SignatureSubstElim t sigma) = throw "openEval(SignatureSubstElim)"
    openEvalNu sig omega (ContextVarElim x) = return (ContextVarElim x)
    openEvalNu sig omega (SignatureVarElim k sigma) = M.do
      return (SignatureVarElim k sigma)
    -- Σ Ω₀ (Δ ⊦ x ≔ t : T) Ω₁ ⊦ x σ = t(σ)
    openEvalNu sig omega (OmegaVarElim k sigma) = M.do
      case (lookup k omega) of
        Just (LetElem _ rhs _) => openEval sig omega (ContextSubstElim rhs sigma)
        Just (MetaElem {}) => return (OmegaVarElim k sigma)
        Just (LetType {}) => throw "openEval/Elem(OmegaVarElim(LetType))"
        Just (MetaType {}) => throw "openEval/Elem(OmegaVarElim(MetaType))"
        Just (TypeConstraint {}) => throw "openEval/Elem(OmegaVarElim(TypeConstraint))"
        Just (ElemConstraint {}) => throw "openEval/Elem(OmegaVarElim(ElemConstraint))"
        Just (SubstContextConstraint {}) => throw "openEval/Elem(OmegaVarElim(SubstConstraint))"
        Nothing => throw "openEval/Elem(OmegaVarElim(Nothing))"
    openEvalNu sig omega (TyEqTy a0 a1) = return $ TyEqTy a0 a1
    openEvalNu sig omega (ElEqTy a0 a1 ty) = return $ ElEqTy a0 a1 ty
    openEvalNu sig omega (TyEqVal ty) = return (TyEqVal ty)
    openEvalNu sig omega (ElEqVal ty e) = return (ElEqVal ty e)

    ||| Σ ⊦ a ⇝ a' : A
    ||| Computes head-normal form w.r.t. (~) relation used in unification.
    public export
    openEval : Signature -> Omega -> Elem -> M Elem
    openEval sig omega tm = openEvalNu sig omega (runSubst tm)

  namespace Typ
    ||| Σ ⊦ a ⇝ a' : A
    ||| Σ must only contain let-elem's
    public export
    closedEvalNu : Signature -> Omega -> Typ -> M Typ
    closedEvalNu sig omega ZeroTy = return ZeroTy
    closedEvalNu sig omega OneTy = return OneTy
    closedEvalNu sig omega NatTy = return NatTy
    closedEvalNu sig omega UniverseTy = return UniverseTy
    closedEvalNu sig omega (El a) = M.do
      case !(closedEval sig omega a) of
        ZeroTy => closedEval sig omega ZeroTy
        OneTy => closedEval sig omega OneTy
        NatTy => closedEval sig omega NatTy
        (PiTy x a b) => closedEval sig omega (PiTy x (El a) (El b))
        (SigmaTy x a b) => closedEval sig omega (SigmaTy x (El a) (El b))
        (TyEqTy a0 a1) => closedEval sig omega (TyEqTy (El a0) (El a1))
        (ElEqTy a0 a1 ty) => closedEval sig omega (ElEqTy a0 a1 (El ty))
        a => return (El a)
    closedEvalNu sig omega (PiTy x a b) = return (PiTy x a b)
    closedEvalNu sig omega (ImplicitPiTy x a b) = return (ImplicitPiTy x a b)
    closedEvalNu sig omega (SigmaTy x a b) = return (SigmaTy x a b)
    closedEvalNu sig omega (ContextSubstElim t sigma) = throw "closedEval(ContextSubstElim)"
    closedEvalNu sig omega (SignatureSubstElim t sigma) = throw "closedEval(SignatureSubstElim)"
    -- Σ Ω₀ (Δ ⊦ x ≔ t : T) Ω₁ ⊦ x σ = t(σ)
    closedEvalNu sig omega (OmegaVarElim x sigma) = M.do
      case (lookup x omega) of
        Just (LetType _ rhs) => closedEval sig omega (ContextSubstElim rhs sigma)
        _ => throw "closedEval(OmegaVarElim)"
    closedEvalNu sig omega (TyEqTy a0 a1) = return $ TyEqTy a0 a1
    closedEvalNu sig omega (ElEqTy a0 a1 ty) = return $ ElEqTy a0 a1 ty
    closedEvalNu sig omega (SignatureVarElim idx tau) = return (SignatureVarElim idx tau)

    ||| Σ ⊦ a ⇝ a' : A
    ||| Σ must only contain let-elem's
    public export
    closedEval : Signature -> Omega -> Typ -> M Typ
    closedEval sig omega tm = closedEvalNu sig omega (runSubst tm)

    ||| Σ ⊦ a ⇝ a' : A
    ||| Σ must only contain let-elem's
    public export
    openEvalNu : Signature -> Omega -> Typ -> M Typ
    openEvalNu sig omega ZeroTy = return ZeroTy
    openEvalNu sig omega OneTy = return OneTy
    openEvalNu sig omega NatTy = return NatTy
    openEvalNu sig omega UniverseTy = return UniverseTy
    openEvalNu sig omega (El a) = M.do
      case !(openEval sig omega a) of
        ZeroTy => openEval sig omega ZeroTy
        OneTy => openEval sig omega OneTy
        NatTy => openEval sig omega NatTy
        (PiTy x a b) => openEval sig omega (PiTy x (El a) (El b))
        (SigmaTy x a b) => openEval sig omega (SigmaTy x (El a) (El b))
        (TyEqTy a0 a1) => openEval sig omega (TyEqTy (El a0) (El a1))
        (ElEqTy a0 a1 ty) => openEval sig omega (ElEqTy a0 a1 (El ty))
        a => return (El a)
    openEvalNu sig omega (PiTy x a b) = return (PiTy x a b)
    openEvalNu sig omega (ImplicitPiTy x a b) = return (ImplicitPiTy x a b)
    openEvalNu sig omega (SigmaTy x a b) = return (SigmaTy x a b)
    openEvalNu sig omega (ContextSubstElim t sigma) = throw "openEval(ContextSubstElim)"
    openEvalNu sig omega (SignatureSubstElim t sigma) = throw "openEval(SignatureSubstElim)"
    -- Σ Ω₀ (Δ ⊦ x ≔ t : T) Ω₁ ⊦ x σ = t(σ)
    openEvalNu sig omega (OmegaVarElim k sigma) = M.do
      case (lookup k omega) of
        Just (LetType _ rhs) => openEval sig omega (ContextSubstElim rhs sigma)
        Just (MetaType {}) => return (OmegaVarElim k sigma)
        Just (LetElem {}) => throw "openEval/Type(OmegaVarElim(LetElem))"
        Just (MetaElem {}) => throw "openEval/Type(OmegaVarElim(MetaElem))"
        Just (TypeConstraint {}) => throw "openEval/Type(OmegaVarElim(TypeConstraint))"
        Just (ElemConstraint {}) => throw "openEval/Type(OmegaVarElim(ElemConstraint))"
        Just (SubstContextConstraint {}) => throw "openEval/Type(OmegaVarElim(SubstConstraint))"
        Nothing => throw "openEval/Type(OmegaVarElim(Nothing))"
    openEvalNu sig omega (TyEqTy a0 a1) = return $ TyEqTy a0 a1
    openEvalNu sig omega (ElEqTy a0 a1 ty) = return $ ElEqTy a0 a1 ty
    openEvalNu sig omega (SignatureVarElim k sigma) = M.do
      return (SignatureVarElim k sigma)

    ||| Σ ⊦ a ⇝ a' : A
    ||| Computes head-normal form w.r.t. (~) relation used in unification.
    public export
    openEval : Signature -> Omega -> Typ -> M Typ
    openEval sig omega tm = openEvalNu sig omega (runSubst tm)
