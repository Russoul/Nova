module Nova.Core.Evaluation

import Data.Util
import Data.AVL

import Nova.Core.Monad
import Nova.Core.Language
import Nova.Core.Substitution
import Nova.Core.Context

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
    closedEvalNu sig omega (ZeroElim ty t) = criticalError "closedEval(ZeroElim)"
    closedEvalNu sig omega (PiTy x a b) = return (PiTy x a b)
    closedEvalNu sig omega (ImplicitPiTy x a b) = return (ImplicitPiTy x a b)
    closedEvalNu sig omega (SigmaTy x a b) = return (SigmaTy x a b)
    closedEvalNu sig omega (PiVal x a b f) = return (PiVal x a b f)
    closedEvalNu sig omega (ImplicitPiVal x a b f) = return (ImplicitPiVal x a b f)
    closedEvalNu sig omega (SigmaVal x a b p q) = return (SigmaVal x a b p q)
    closedEvalNu sig omega (PiElim f x a b e) = M.do
      PiVal _ _ _ f <- closedEval sig omega f
        | _ => criticalError "closedEval(PiElim)"
      closedEval sig omega (ContextSubstElim f (Ext Terminal e))
    closedEvalNu sig omega (ImplicitPiElim f x a b e) = M.do
      ImplicitPiVal _ _ _ f <- closedEval sig omega f
        | _ => criticalError "closedEval(ImplicitPiElim)"
      closedEval sig omega (ContextSubstElim f (Ext Terminal e))
    closedEvalNu sig omega (SigmaElim1 f x a b) = M.do
      SigmaVal _ _ _ p q <- closedEval sig omega f
        | _ => criticalError "closedEval(SigmaElim1)"
      closedEval sig omega p
    closedEvalNu sig omega (SigmaElim2 f x a b) = M.do
      SigmaVal _ _ _ p q <- closedEval sig omega f
        | _ => criticalError "closedEval(SigmaElim2)"
      closedEval sig omega q
    closedEvalNu sig omega NatVal0 = return NatVal0
    closedEvalNu sig omega (NatVal1 t) = return (NatVal1 t)
    closedEvalNu sig omega (NatElim x schema z y h s t) = M.do
      t <- closedEval sig omega t
      case t of
        NatVal0 => closedEval sig omega z
        NatVal1 t => closedEval sig omega (ContextSubstElim s (Ext (Ext Terminal t) (NatElim x schema z y h s t)))
        _ => criticalError "closedEval(NatElim)"
    closedEvalNu sig omega (ContextSubstElim t sigma) = criticalError "closedEval(ContextSubstElim)"
    closedEvalNu sig omega (SignatureSubstElim t sigma) = criticalError "closedEval(SignatureSubstElim)"
    closedEvalNu sig omega (ContextVarElim x) = criticalError "closedEval(ContextVarElim)"
    closedEvalNu sig omega (SignatureVarElim k sigma) = M.do
      (_, LetElemEntry ctx rhs _) <- lookupSignatureE sig k
        | _ => return (SignatureVarElim k sigma)
      closedEval sig omega (ContextSubstElim rhs sigma)
    -- Σ Ω₀ (Δ ⊦ x ≔ t : T) Ω₁ ⊦ x σ = t(σ)
    closedEvalNu sig omega (OmegaVarElim x sigma) = M.do
      case (lookup x omega) of
        Just (LetElem _ rhs _) => closedEval sig omega (ContextSubstElim rhs sigma)
        _ => criticalError "closedEval(OmegaVarElim)"
    closedEvalNu sig omega (TyEqTy a0 a1) = return $ TyEqTy a0 a1
    closedEvalNu sig omega (ElEqTy a0 a1 ty) = return $ ElEqTy a0 a1 ty
    closedEvalNu sig omega (TyEqVal ty) = return (TyEqVal ty)
    closedEvalNu sig omega (ElEqVal ty e) = return (ElEqVal ty e)

    ||| Σ ⊦ a ⇝ a' : A
    ||| Σ must only contain let-elem's
    public export
    closedEval : Signature -> Omega -> Elem -> M Elem
    closedEval sig omega tm = closedEvalNu sig omega (runSubst tm)

    public export
    closedNormaliseNu : Signature -> Omega -> Elem -> M Elem
    closedNormaliseNu sig omega (PiTy x dom cod) = M.do
      return $
        PiTy x
          !(closedNormalise sig omega dom)
          !(closedNormalise sig omega cod)
    closedNormaliseNu sig omega (ImplicitPiTy x dom cod) = M.do
      return $
        ImplicitPiTy x
          !(closedNormalise sig omega dom)
          !(closedNormalise sig omega cod)
    closedNormaliseNu sig omega (SigmaTy x dom cod) = M.do
      return $
        SigmaTy x
          !(closedNormalise sig omega dom)
          !(closedNormalise sig omega cod)
    closedNormaliseNu sig omega (PiVal x a b f) = M.do
      return $
        PiVal x a b !(closedNormalise sig omega f)
    closedNormaliseNu sig omega (ImplicitPiVal x a b f) = M.do
      return $
        ImplicitPiVal x a b !(closedNormalise sig omega f)
    closedNormaliseNu sig omega (SigmaVal x a b p q) = M.do
      return $
        SigmaVal x a b
          !(closedNormalise sig omega p)
          !(closedNormalise sig omega q)
    closedNormaliseNu sig omega (PiElim f x a b e) = M.do
      return $
        PiElim
          !(closedNormalise sig omega f)
          x
          a
          b
          !(closedNormalise sig omega e)
    closedNormaliseNu sig omega (ImplicitPiElim f x a b e) = M.do
      return $
        ImplicitPiElim
          !(closedNormalise sig omega f)
          x
          a
          b
          !(closedNormalise sig omega e)
    closedNormaliseNu sig omega (SigmaElim1 p x a b) = M.do
      return $
        SigmaElim1
          !(closedNormalise sig omega p)
          x
          a
          b
    closedNormaliseNu sig omega (SigmaElim2 p x a b) = M.do
      return $
        SigmaElim2
          !(closedNormalise sig omega p)
          x
          a
          b
    closedNormaliseNu sig omega NatVal0 = M.do
      return NatVal0
    closedNormaliseNu sig omega (NatVal1 t) = M.do
      return $
        NatVal1
          !(closedNormalise sig omega t)
    closedNormaliseNu sig omega NatTy = M.do
      return NatTy
    closedNormaliseNu sig omega (NatElim x schema z y h s t) = M.do
      return $
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
    closedNormaliseNu sig omega (TyEqTy a b) = M.do
      return $
        TyEqTy
          !(closedNormalise sig omega a)
          !(closedNormalise sig omega b)
    closedNormaliseNu sig omega (ElEqTy a0 a1 ty) = M.do
      return $
        ElEqTy
          !(closedNormalise sig omega a0)
          !(closedNormalise sig omega a1)
          !(closedNormalise sig omega ty)
    closedNormaliseNu sig omega (TyEqVal a) = M.do
      return $
        TyEqVal
          a -- Don't care
    closedNormaliseNu sig omega (ElEqVal ty el) = M.do
      return $
        ElEqVal
          ty -- Don't care
          el -- Don't care
    closedNormaliseNu sig omega ZeroTy = M.do
      return ZeroTy
    closedNormaliseNu sig omega OneTy = M.do
      return OneTy
    closedNormaliseNu sig omega OneVal = M.do
      return OneVal
    closedNormaliseNu sig omega (ZeroElim ty t) = M.do
      return $
        ZeroElim
          ty -- Don't care
          !(closedNormalise sig omega t) -- Do we care? The elements are unique up to equality

    public export
    closedNormalise : Signature -> Omega -> Elem -> M Elem
    closedNormalise sig omega el = closedNormaliseNu sig omega !(closedEval sig omega el)

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
    openEvalNu sig omega (ContextSubstElim t sigma) = criticalError "openEval(ContextSubstElim)"
    openEvalNu sig omega (SignatureSubstElim t sigma) = criticalError "openEval(SignatureSubstElim)"
    openEvalNu sig omega (ContextVarElim x) = return (ContextVarElim x)
    openEvalNu sig omega (SignatureVarElim k sigma) = M.do
      return (SignatureVarElim k sigma)
    -- Σ Ω₀ (Δ ⊦ x ≔ t : T) Ω₁ ⊦ x σ = t(σ)
    openEvalNu sig omega (OmegaVarElim k sigma) = M.do
      case (lookup k omega) of
        Just (LetElem _ rhs _) => openEval sig omega (ContextSubstElim rhs sigma)
        Just (MetaElem {}) => return (OmegaVarElim k sigma)
        Just (LetType {}) => criticalError "openEval/Elem(OmegaVarElim(LetType))"
        Just (MetaType {}) => criticalError "openEval/Elem(OmegaVarElim(MetaType))"
        Just (TypeConstraint {}) => criticalError "openEval/Elem(OmegaVarElim(TypeConstraint))"
        Just (ElemConstraint {}) => criticalError "openEval/Elem(OmegaVarElim(ElemConstraint))"
        Just (SubstContextConstraint {}) => criticalError "openEval/Elem(OmegaVarElim(SubstConstraint))"
        Nothing => criticalError "openEval/Elem(OmegaVarElim(Nothing))"
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
    closedEvalNu sig omega (ContextSubstElim t sigma) = criticalError "closedEval(ContextSubstElim)"
    closedEvalNu sig omega (SignatureSubstElim t sigma) = criticalError "closedEval(SignatureSubstElim)"
    -- Σ Ω₀ (Δ ⊦ x ≔ t : T) Ω₁ ⊦ x σ = t(σ)
    closedEvalNu sig omega (OmegaVarElim x sigma) = M.do
      case (lookup x omega) of
        Just (LetType _ rhs) => closedEval sig omega (ContextSubstElim rhs sigma)
        _ => criticalError "closedEval(OmegaVarElim)"
    closedEvalNu sig omega (TyEqTy a0 a1) = return $ TyEqTy a0 a1
    closedEvalNu sig omega (ElEqTy a0 a1 ty) = return $ ElEqTy a0 a1 ty
    closedEvalNu sig omega (SignatureVarElim k sigma) = M.do
      (_, LetTypeEntry ctx rhs) <- lookupSignatureE sig k
        | _ => return (SignatureVarElim k sigma)
      closedEval sig omega (ContextSubstElim rhs sigma)

    ||| Σ ⊦ a ⇝ a' : A
    ||| Σ must only contain let-elem's
    public export
    closedEval : Signature -> Omega -> Typ -> M Typ
    closedEval sig omega tm = closedEvalNu sig omega (runSubst tm)

    public export
    closedNormaliseNu : Signature -> Omega -> Typ -> M Typ
    closedNormaliseNu sig omega ZeroTy = return ZeroTy
    closedNormaliseNu sig omega OneTy = return OneTy
    closedNormaliseNu sig omega UniverseTy = return UniverseTy
    closedNormaliseNu sig omega NatTy = return NatTy
    closedNormaliseNu sig omega (PiTy x dom cod) = M.do
      return $
        PiTy x
          !(closedNormalise sig omega dom)
          !(closedNormalise sig omega cod)
    closedNormaliseNu sig omega (ImplicitPiTy x dom cod) = M.do
      return $
        ImplicitPiTy x
          !(closedNormalise sig omega dom)
          !(closedNormalise sig omega cod)
    closedNormaliseNu sig omega (SigmaTy x dom cod) = M.do
      return $
        SigmaTy x
          !(closedNormalise sig omega dom)
          !(closedNormalise sig omega cod)
    closedNormaliseNu sig omega (TyEqTy a b) = M.do
      return $
        TyEqTy
          !(closedNormalise sig omega a)
          !(closedNormalise sig omega b)
    closedNormaliseNu sig omega (ElEqTy a0 a1 ty) = M.do
      return $
        ElEqTy
          !(closedNormalise sig omega a0)
          !(closedNormalise sig omega a1)
          !(closedNormalise sig omega ty)
    closedNormaliseNu sig omega (El el) = M.do
      return $
        El !(closedNormalise sig omega el)
    closedNormaliseNu sig omega (ContextSubstElim x y) = assert_total $ idris_crash "closedNormaliseNu(ContextSubstElim)"
    closedNormaliseNu sig omega (SignatureSubstElim x y) = assert_total $ idris_crash "closedNormaliseNu(SignatureSubstElim)"
    closedNormaliseNu sig omega (OmegaVarElim x sigma) = assert_total $ idris_crash "closedNormaliseNu(OmegaVarElim)"
    closedNormaliseNu sig omega (SignatureVarElim k sigma) = assert_total $ idris_crash "closedNormaliseNu(SignatureVarElim)"

    public export
    closedNormalise : Signature -> Omega -> Typ -> M Typ
    closedNormalise sig omega ty = closedNormaliseNu sig omega !(closedEval sig omega ty)

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
    openEvalNu sig omega (ContextSubstElim t sigma) = criticalError "openEval(ContextSubstElim)"
    openEvalNu sig omega (SignatureSubstElim t sigma) = criticalError "openEval(SignatureSubstElim)"
    -- Σ Ω₀ (Δ ⊦ x ≔ t : T) Ω₁ ⊦ x σ = t(σ)
    openEvalNu sig omega (OmegaVarElim k sigma) = M.do
      case (lookup k omega) of
        Just (LetType _ rhs) => openEval sig omega (ContextSubstElim rhs sigma)
        Just (MetaType {}) => return (OmegaVarElim k sigma)
        Just (LetElem {}) => criticalError "openEval/Type(OmegaVarElim(LetElem(\{k})))"
        Just (MetaElem {}) => criticalError "openEval/Type(OmegaVarElim(MetaElem))"
        Just (TypeConstraint {}) => criticalError "openEval/Type(OmegaVarElim(TypeConstraint))"
        Just (ElemConstraint {}) => criticalError "openEval/Type(OmegaVarElim(ElemConstraint))"
        Just (SubstContextConstraint {}) => criticalError "openEval/Type(OmegaVarElim(SubstConstraint))"
        Nothing => criticalError "openEval/Type(OmegaVarElim(Nothing))"
    openEvalNu sig omega (TyEqTy a0 a1) = return $ TyEqTy a0 a1
    openEvalNu sig omega (ElEqTy a0 a1 ty) = return $ ElEqTy a0 a1 ty
    openEvalNu sig omega (SignatureVarElim k sigma) = M.do
      return (SignatureVarElim k sigma)

    ||| Σ ⊦ a ⇝ a' : A
    ||| Computes head-normal form w.r.t. (~) relation used in unification.
    public export
    openEval : Signature -> Omega -> Typ -> M Typ
    openEval sig omega tm = openEvalNu sig omega (runSubst tm)
