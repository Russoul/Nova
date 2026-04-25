module Nova.Core.Evaluation

import Data.Util
import Data.AVL

import Nova.Control.Monad.Id

import Nova.Core.Language
import Nova.Core.Substitution
import Nova.Core.Context


-- Closed term evaluation

EvalM = Nova.Control.Monad.Id.Id

mutual
  namespace Elem
    ||| Σ ⊦ a ⇝ a' : A
    ||| Σ must only contain let-elem's
    public export
    closedEvalNu : Signature -> Omega -> Elem -> Id Elem
    closedEvalNu sig omega NatTy = pure NatTy
    closedEvalNu sig omega ZeroTy = pure ZeroTy
    closedEvalNu sig omega OneTy = pure OneTy
    closedEvalNu sig omega OneVal = pure OneVal
    closedEvalNu sig omega (ZeroElim ty t) = assert_total $ idris_crash $ "closedEval(ZeroElim)"
    closedEvalNu sig omega (PiTy x a b) = pure (PiTy x a b)
    closedEvalNu sig omega (ImplicitPiTy x a b) = pure (ImplicitPiTy x a b)
    closedEvalNu sig omega (SigmaTy x a b) = pure (SigmaTy x a b)
    closedEvalNu sig omega (PiVal x a b f) = pure (PiVal x a b f)
    closedEvalNu sig omega (ImplicitPiVal x a b f) = pure (ImplicitPiVal x a b f)
    closedEvalNu sig omega (SigmaVal x a b p q) = pure (SigmaVal x a b p q)
    closedEvalNu sig omega (PiElim f x a b e) = Id.do
      PiVal _ _ _ f <- closedEval sig omega f
        | _ => assert_total $ idris_crash "closedEval(PiElim)"
      closedEval sig omega (ContextSubstElim f (Ext Terminal e))
    closedEvalNu sig omega (ImplicitPiElim f x a b e) = Id.do
      ImplicitPiVal _ _ _ f <- closedEval sig omega f
        | _ => assert_total $ idris_crash "closedEval(ImplicitPiElim)"
      closedEval sig omega (ContextSubstElim f (Ext Terminal e))
    closedEvalNu sig omega (SigmaElim1 f x a b) = Id.do
      SigmaVal _ _ _ p q <- closedEval sig omega f
        | _ => assert_total $ idris_crash "closedEval(SigmaElim1)"
      closedEval sig omega p
    closedEvalNu sig omega (SigmaElim2 f x a b) = Id.do
      SigmaVal _ _ _ p q <- closedEval sig omega f
        | _ => assert_total $ idris_crash "closedEval(SigmaElim2)"
      closedEval sig omega q
    closedEvalNu sig omega NatVal0 = pure NatVal0
    closedEvalNu sig omega (NatVal1 t) = pure (NatVal1 t)
    closedEvalNu sig omega (NatElim x schema z y h s t) = Id.do
      t <- closedEval sig omega t
      case t of
        NatVal0 => closedEval sig omega z
        NatVal1 t => closedEval sig omega (ContextSubstElim s (Ext (Ext Terminal t) (NatElim x schema z y h s t)))
        _ => assert_total $ idris_crash "closedEval(NatElim)"
    closedEvalNu sig omega (ContextSubstElim t sigma) = assert_total $ idris_crash "closedEval(ContextSubstElim)"
    closedEvalNu sig omega (SignatureSubstElim t sigma) = assert_total $ idris_crash "closedEval(SignatureSubstElim)"
    closedEvalNu sig omega (ContextVarElim x) = assert_total $ idris_crash "closedEval(ContextVarElim)"
    closedEvalNu sig omega (SignatureVarElim k sigma) = Id.do
      (_, LetElemEntry ctx rhs _) <- lookupSignatureE sig k
        | _ => pure (SignatureVarElim k sigma)
      closedEval sig omega (ContextSubstElim rhs sigma)
    -- Σ Ω₀ (Δ ⊦ x ≔ t : T) Ω₁ ⊦ x σ = t(σ)
    closedEvalNu sig omega (OmegaVarElim x sigma) = Id.do
      case (lookup x omega) of
        Just (LetElem _ rhs _) => closedEval sig omega (ContextSubstElim rhs sigma)
        _ => assert_total $ idris_crash "closedEval(OmegaVarElim)"
    closedEvalNu sig omega (TyEqTy a0 a1) = pure $ TyEqTy a0 a1
    closedEvalNu sig omega (ElEqTy a0 a1 ty) = pure $ ElEqTy a0 a1 ty
    closedEvalNu sig omega (TyEqVal ty) = pure (TyEqVal ty)
    closedEvalNu sig omega (ElEqVal ty e) = pure (ElEqVal ty e)

    ||| Σ ⊦ a ⇝ a' : A
    ||| Σ must only contain let-elem's
    public export
    closedEval : Signature -> Omega -> Elem -> EvalM Elem
    closedEval sig omega tm = closedEvalNu sig omega (runSubst tm)

    public export
    closedNormaliseNu : Signature -> Omega -> Elem -> EvalM Elem
    closedNormaliseNu sig omega (PiTy x dom cod) = Id.do
      pure $
        PiTy x
          !(closedNormalise sig omega dom)
          !(closedNormalise sig omega cod)
    closedNormaliseNu sig omega (ImplicitPiTy x dom cod) = Id.do
      pure $
        ImplicitPiTy x
          !(closedNormalise sig omega dom)
          !(closedNormalise sig omega cod)
    closedNormaliseNu sig omega (SigmaTy x dom cod) = Id.do
      pure $
        SigmaTy x
          !(closedNormalise sig omega dom)
          !(closedNormalise sig omega cod)
    closedNormaliseNu sig omega (PiVal x a b f) = Id.do
      pure $
        PiVal x a b !(closedNormalise sig omega f)
    closedNormaliseNu sig omega (ImplicitPiVal x a b f) = Id.do
      pure $
        ImplicitPiVal x a b !(closedNormalise sig omega f)
    closedNormaliseNu sig omega (SigmaVal x a b p q) = Id.do
      pure $
        SigmaVal x a b
          !(closedNormalise sig omega p)
          !(closedNormalise sig omega q)
    closedNormaliseNu sig omega (PiElim f x a b e) = Id.do
      pure $
        PiElim
          !(closedNormalise sig omega f)
          x
          a
          b
          !(closedNormalise sig omega e)
    closedNormaliseNu sig omega (ImplicitPiElim f x a b e) = Id.do
      pure $
        ImplicitPiElim
          !(closedNormalise sig omega f)
          x
          a
          b
          !(closedNormalise sig omega e)
    closedNormaliseNu sig omega (SigmaElim1 p x a b) = Id.do
      pure $
        SigmaElim1
          !(closedNormalise sig omega p)
          x
          a
          b
    closedNormaliseNu sig omega (SigmaElim2 p x a b) = Id.do
      pure $
        SigmaElim2
          !(closedNormalise sig omega p)
          x
          a
          b
    closedNormaliseNu sig omega NatVal0 = Id.do
      pure NatVal0
    closedNormaliseNu sig omega (NatVal1 t) = Id.do
      pure $
        NatVal1
          !(closedNormalise sig omega t)
    closedNormaliseNu sig omega NatTy = Id.do
      pure NatTy
    closedNormaliseNu sig omega (NatElim x schema z y h s t) = Id.do
      pure $
        NatElim
          x
          !(closedNormalise sig omega schema) -- That's a type. Do we really want to normalise?
          !(closedNormalise sig omega z)
          y
          h
          !(closedNormalise sig omega s)
          !(closedNormalise sig omega t)
    closedNormaliseNu sig omega (ContextSubstElim x y) = assert_total $ idris_crash "closedNormaliseNu(ContextSubstElim)"
    closedNormaliseNu sig omega (SignatureSubstElim x y) = assert_total $ idris_crash "closedNormaliseNu(SignatureSubstElim)"
    closedNormaliseNu sig omega (ContextVarElim k) = assert_total $ idris_crash "closedNormaliseNu(ContextVarElim)"
    closedNormaliseNu sig omega (SignatureVarElim k x) = assert_total $ idris_crash "closedNormaliseNu(SignatureVarElim)"
    closedNormaliseNu sig omega (OmegaVarElim str x) = assert_total $ idris_crash "closedNormaliseNu(OmegaVarElim)"
    closedNormaliseNu sig omega (TyEqTy a b) = Id.do
      pure $
        TyEqTy
          !(closedNormalise sig omega a)
          !(closedNormalise sig omega b)
    closedNormaliseNu sig omega (ElEqTy a0 a1 ty) = Id.do
      pure $
        ElEqTy
          !(closedNormalise sig omega a0)
          !(closedNormalise sig omega a1)
          !(closedNormalise sig omega ty)
    closedNormaliseNu sig omega (TyEqVal a) = Id.do
      pure $
        TyEqVal
          a -- Don't care
    closedNormaliseNu sig omega (ElEqVal ty el) = Id.do
      pure $
        ElEqVal
          ty -- Don't care
          el -- Don't care
    closedNormaliseNu sig omega ZeroTy = Id.do
      pure ZeroTy
    closedNormaliseNu sig omega OneTy = Id.do
      pure OneTy
    closedNormaliseNu sig omega OneVal = Id.do
      pure OneVal
    closedNormaliseNu sig omega (ZeroElim ty t) = Id.do
      pure $
        ZeroElim
          ty -- Don't care
          !(closedNormalise sig omega t) -- Do we care? The elements are unique up to equality

    public export
    closedNormalise : Signature -> Omega -> Elem -> EvalM Elem
    closedNormalise sig omega el = closedNormaliseNu sig omega !(closedEval sig omega el)

    ||| Σ ⊦ a ⇝ a' : A
    ||| Σ must only contain let-elem's
    public export
    openEvalNu : Signature -> Omega -> Elem -> EvalM Elem
    openEvalNu sig omega ZeroTy = pure ZeroTy
    openEvalNu sig omega OneTy = pure OneTy
    openEvalNu sig omega NatTy = pure NatTy
    openEvalNu sig omega OneVal = pure OneVal
    openEvalNu sig omega (ZeroElim ty t) = Id.do
      pure (ZeroElim ty t)
    openEvalNu sig omega (PiTy x a b) = pure (PiTy x a b)
    openEvalNu sig omega (ImplicitPiTy x a b) = pure (ImplicitPiTy x a b)
    openEvalNu sig omega (SigmaTy x a b) = pure (SigmaTy x a b)
    openEvalNu sig omega (PiVal x a b f) = pure (PiVal x a b f)
    openEvalNu sig omega (ImplicitPiVal x a b f) = pure (ImplicitPiVal x a b f)
    openEvalNu sig omega (SigmaVal x a b p q) = pure (SigmaVal x a b p q)
    openEvalNu sig omega (PiElim f x a b e) = Id.do
      PiVal _ _ _ f <- openEval sig omega f
        | f => pure (PiElim f x a b e)
      openEval sig omega (ContextSubstElim f (Ext Id e))
    openEvalNu sig omega (ImplicitPiElim f x a b e) = Id.do
      ImplicitPiVal _ _ _ f <- openEval sig omega f
        | f => pure (ImplicitPiElim f x a b e)
      openEval sig omega (ContextSubstElim f (Ext Id e))
    openEvalNu sig omega (SigmaElim1 f x a b) = Id.do
      SigmaVal _ _ _ p q <- openEval sig omega f
        | f => pure (SigmaElim1 f x a b)
      openEval sig omega p
    openEvalNu sig omega (SigmaElim2 f x a b) = Id.do
      SigmaVal _ _ _ p q <- openEval sig omega f
        | f => pure (SigmaElim2 f x a b)
      openEval sig omega q
    openEvalNu sig omega NatVal0 = pure NatVal0
    openEvalNu sig omega (NatVal1 t) = pure (NatVal1 t)
    openEvalNu sig omega (NatElim x schema z y h s t) = Id.do
      t <- openEval sig omega t
      case t of
        NatVal0 => openEval sig omega z
        NatVal1 t => openEval sig omega (ContextSubstElim s (Ext (Ext Id t) (NatElim x schema z y h s t)))
        t => pure (NatElim x schema z y h s t)
    openEvalNu sig omega (ContextSubstElim t sigma) = assert_total $ idris_crash "openEval(ContextSubstElim)"
    openEvalNu sig omega (SignatureSubstElim t sigma) = assert_total $ idris_crash "openEval(SignatureSubstElim)"
    openEvalNu sig omega (ContextVarElim x) = pure (ContextVarElim x)
    openEvalNu sig omega (SignatureVarElim k sigma) = Id.do
      pure (SignatureVarElim k sigma)
    -- Σ Ω₀ (Δ ⊦ x ≔ t : T) Ω₁ ⊦ x σ = t(σ)
    openEvalNu sig omega (OmegaVarElim k sigma) = Id.do
      case (lookup k omega) of
        Just (LetElem _ rhs _) => openEval sig omega (ContextSubstElim rhs sigma)
        Just (MetaElem {}) => pure (OmegaVarElim k sigma)
        Just (LetType {}) => assert_total $ idris_crash "openEval/Elem(OmegaVarElim(LetType))"
        Just (MetaType {}) => assert_total $ idris_crash "openEval/Elem(OmegaVarElim(MetaType))"
        Just (TypeConstraint {}) => assert_total $ idris_crash "openEval/Elem(OmegaVarElim(TypeConstraint))"
        Just (ElemConstraint {}) => assert_total $ idris_crash "openEval/Elem(OmegaVarElim(ElemConstraint))"
        Just (SubstContextConstraint {}) => assert_total $ idris_crash "openEval/Elem(OmegaVarElim(SubstConstraint))"
        Nothing => assert_total $ idris_crash "openEval/Elem(OmegaVarElim(Nothing))"
    openEvalNu sig omega (TyEqTy a0 a1) = pure $ TyEqTy a0 a1
    openEvalNu sig omega (ElEqTy a0 a1 ty) = pure $ ElEqTy a0 a1 ty
    openEvalNu sig omega (TyEqVal ty) = pure (TyEqVal ty)
    openEvalNu sig omega (ElEqVal ty e) = pure (ElEqVal ty e)

    ||| Σ ⊦ a ⇝ a' : A
    ||| Computes head-normal form w.r.t. (~) relation used in unification.
    public export
    openEval : Signature -> Omega -> Elem -> EvalM Elem
    openEval sig omega tm = openEvalNu sig omega (runSubst tm)

  namespace Typ
    ||| Σ ⊦ a ⇝ a' : A
    ||| Σ must only contain let-elem's
    public export
    closedEvalNu : Signature -> Omega -> Typ -> EvalM Typ
    closedEvalNu sig omega ZeroTy = pure ZeroTy
    closedEvalNu sig omega OneTy = pure OneTy
    closedEvalNu sig omega NatTy = pure NatTy
    closedEvalNu sig omega UniverseTy = pure UniverseTy
    closedEvalNu sig omega (El a) = Id.do
      case !(closedEval sig omega a) of
        ZeroTy => closedEval sig omega ZeroTy
        OneTy => closedEval sig omega OneTy
        NatTy => closedEval sig omega NatTy
        (PiTy x a b) => closedEval sig omega (PiTy x (El a) (El b))
        (SigmaTy x a b) => closedEval sig omega (SigmaTy x (El a) (El b))
        (TyEqTy a0 a1) => closedEval sig omega (TyEqTy (El a0) (El a1))
        (ElEqTy a0 a1 ty) => closedEval sig omega (ElEqTy a0 a1 (El ty))
        a => pure (El a)
    closedEvalNu sig omega (PiTy x a b) = pure (PiTy x a b)
    closedEvalNu sig omega (ImplicitPiTy x a b) = pure (ImplicitPiTy x a b)
    closedEvalNu sig omega (SigmaTy x a b) = pure (SigmaTy x a b)
    closedEvalNu sig omega (ContextSubstElim t sigma) = assert_total $ idris_crash "closedEval(ContextSubstElim)"
    closedEvalNu sig omega (SignatureSubstElim t sigma) = assert_total $ idris_crash "closedEval(SignatureSubstElim)"
    -- Σ Ω₀ (Δ ⊦ x ≔ t : T) Ω₁ ⊦ x σ = t(σ)
    closedEvalNu sig omega (OmegaVarElim x sigma) = Id.do
      case (lookup x omega) of
        Just (LetType _ rhs) => closedEval sig omega (ContextSubstElim rhs sigma)
        _ => assert_total $ idris_crash "closedEval(OmegaVarElim)"
    closedEvalNu sig omega (TyEqTy a0 a1) = pure $ TyEqTy a0 a1
    closedEvalNu sig omega (ElEqTy a0 a1 ty) = pure $ ElEqTy a0 a1 ty
    closedEvalNu sig omega (SignatureVarElim k sigma) = Id.do
      (_, LetTypeEntry ctx rhs) <- lookupSignatureE sig k
        | _ => pure (SignatureVarElim k sigma)
      closedEval sig omega (ContextSubstElim rhs sigma)

    ||| Σ ⊦ a ⇝ a' : A
    ||| Σ must only contain let-elem's
    public export
    closedEval : Signature -> Omega -> Typ -> EvalM Typ
    closedEval sig omega tm = closedEvalNu sig omega (runSubst tm)

    public export
    closedNormaliseNu : Signature -> Omega -> Typ -> EvalM Typ
    closedNormaliseNu sig omega ZeroTy = pure ZeroTy
    closedNormaliseNu sig omega OneTy = pure OneTy
    closedNormaliseNu sig omega UniverseTy = pure UniverseTy
    closedNormaliseNu sig omega NatTy = pure NatTy
    closedNormaliseNu sig omega (PiTy x dom cod) = Id.do
      pure $
        PiTy x
          !(closedNormalise sig omega dom)
          !(closedNormalise sig omega cod)
    closedNormaliseNu sig omega (ImplicitPiTy x dom cod) = Id.do
      pure $
        ImplicitPiTy x
          !(closedNormalise sig omega dom)
          !(closedNormalise sig omega cod)
    closedNormaliseNu sig omega (SigmaTy x dom cod) = Id.do
      pure $
        SigmaTy x
          !(closedNormalise sig omega dom)
          !(closedNormalise sig omega cod)
    closedNormaliseNu sig omega (TyEqTy a b) = Id.do
      pure $
        TyEqTy
          !(closedNormalise sig omega a)
          !(closedNormalise sig omega b)
    closedNormaliseNu sig omega (ElEqTy a0 a1 ty) = Id.do
      pure $
        ElEqTy
          !(closedNormalise sig omega a0)
          !(closedNormalise sig omega a1)
          !(closedNormalise sig omega ty)
    closedNormaliseNu sig omega (El el) = Id.do
      pure $
        El !(closedNormalise sig omega el)
    closedNormaliseNu sig omega (ContextSubstElim x y) = assert_total $ idris_crash "closedNormaliseNu(ContextSubstElim)"
    closedNormaliseNu sig omega (SignatureSubstElim x y) = assert_total $ idris_crash "closedNormaliseNu(SignatureSubstElim)"
    closedNormaliseNu sig omega (OmegaVarElim x sigma) = assert_total $ idris_crash "closedNormaliseNu(OmegaVarElim)"
    closedNormaliseNu sig omega (SignatureVarElim k sigma) = assert_total $ idris_crash "closedNormaliseNu(SignatureVarElim)"

    public export
    closedNormalise : Signature -> Omega -> Typ -> EvalM Typ
    closedNormalise sig omega ty = closedNormaliseNu sig omega !(closedEval sig omega ty)

    ||| Σ ⊦ a ⇝ a' : A
    ||| Σ must only contain let-elem's
    public export
    openEvalNu : Signature -> Omega -> Typ -> EvalM Typ
    openEvalNu sig omega ZeroTy = pure ZeroTy
    openEvalNu sig omega OneTy = pure OneTy
    openEvalNu sig omega NatTy = pure NatTy
    openEvalNu sig omega UniverseTy = pure UniverseTy
    openEvalNu sig omega (El a) = Id.do
      case !(openEval sig omega a) of
        ZeroTy => openEval sig omega ZeroTy
        OneTy => openEval sig omega OneTy
        NatTy => openEval sig omega NatTy
        (PiTy x a b) => openEval sig omega (PiTy x (El a) (El b))
        (SigmaTy x a b) => openEval sig omega (SigmaTy x (El a) (El b))
        (TyEqTy a0 a1) => openEval sig omega (TyEqTy (El a0) (El a1))
        (ElEqTy a0 a1 ty) => openEval sig omega (ElEqTy a0 a1 (El ty))
        a => pure (El a)
    openEvalNu sig omega (PiTy x a b) = pure (PiTy x a b)
    openEvalNu sig omega (ImplicitPiTy x a b) = pure (ImplicitPiTy x a b)
    openEvalNu sig omega (SigmaTy x a b) = pure (SigmaTy x a b)
    openEvalNu sig omega (ContextSubstElim t sigma) = assert_total $ idris_crash "openEval(ContextSubstElim)"
    openEvalNu sig omega (SignatureSubstElim t sigma) = assert_total $ idris_crash "openEval(SignatureSubstElim)"
    -- Σ Ω₀ (Δ ⊦ x ≔ t : T) Ω₁ ⊦ x σ = t(σ)
    openEvalNu sig omega (OmegaVarElim k sigma) = Id.do
      case (lookup k omega) of
        Just (LetType _ rhs) => openEval sig omega (ContextSubstElim rhs sigma)
        Just (MetaType {}) => pure (OmegaVarElim k sigma)
        Just (LetElem {}) => assert_total $ idris_crash "openEval/Type(OmegaVarElim(LetElem(\{k})))"
        Just (MetaElem {}) => assert_total $ idris_crash "openEval/Type(OmegaVarElim(MetaElem))"
        Just (TypeConstraint {}) => assert_total $ idris_crash "openEval/Type(OmegaVarElim(TypeConstraint))"
        Just (ElemConstraint {}) => assert_total $ idris_crash "openEval/Type(OmegaVarElim(ElemConstraint))"
        Just (SubstContextConstraint {}) => assert_total $ idris_crash "openEval/Type(OmegaVarElim(SubstConstraint))"
        Nothing => assert_total $ idris_crash "openEval/Type(OmegaVarElim(Nothing))"
    openEvalNu sig omega (TyEqTy a0 a1) = pure $ TyEqTy a0 a1
    openEvalNu sig omega (ElEqTy a0 a1 ty) = pure $ ElEqTy a0 a1 ty
    openEvalNu sig omega (SignatureVarElim k sigma) = Id.do
      pure (SignatureVarElim k sigma)

    ||| Σ ⊦ a ⇝ a' : A
    ||| Computes head-normal form w.r.t. (~) relation used in unification.
    public export
    openEval : Signature -> Omega -> Typ -> EvalM Typ
    openEval sig omega tm = openEvalNu sig omega (runSubst tm)
