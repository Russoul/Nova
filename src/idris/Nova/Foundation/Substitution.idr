||| Substitution normal form computation.
||| The functions below eliminate all SubstElim nodes inside a term top-to-bottom,
||| producing a term in substitution normal form (no residual SubstElim constructors).
module Nova.Foundation.Substitution

import Nova.Foundation.Syntax

||| σ⁺ ≔ σ ∘ ↑, ☐₀ : Γ₀ A(σ) ⇒ Γ₁ A
public export
Under : SubstContext -> SubstContext
Under sigma = Ext (Chain sigma Wk) (CtxVar 0)

||| UnderN n σ = σ⁺ⁿ
public export
UnderN : Nat -> SubstContext -> SubstContext
UnderN 0 sigma = sigma
UnderN (S k) sigma = UnderN k (Under sigma)

mutual
  ||| ☐ᵢ(σ)
  substContextVar : Nat -> SubstContext -> Elem
  substContextVar i Id           = CtxVar i
  substContextVar i Wk           = CtxVar (S i)
  substContextVar i (Chain s t)  = Elem.subst (substContextVar i s) t
  substContextVar 0 (Ext _ t)    = t
  substContextVar (S i) (Ext s _) = substContextVar i s
  substContextVar _ Terminal     = assert_total $ idris_crash "substContextVar: Terminal"

  namespace Typ
    ||| T(σ)
    public export
    subst : Typ -> SubstContext -> Typ
    subst UniverseTy     sigma = UniverseTy
    subst NatTy          sigma = NatTy
    subst ZeroTy         sigma = ZeroTy
    subst OneTy          sigma = OneTy
    subst (El t)         sigma = El (Elem.subst t sigma)
    subst (PiTy a b)     sigma = PiTy (subst a sigma) (subst b (Under sigma))
    subst (SigmaTy a b)  sigma = SigmaTy (subst a sigma) (subst b (Under sigma))
    subst (EqTy t0 t1 a) sigma = EqTy (Elem.subst t0 sigma) (Elem.subst t1 sigma) (subst a sigma)
    subst (SubstElim t tau) sigma = subst t (Chain tau sigma)

  namespace Elem
    ||| t(σ)
    public export
    subst : Elem -> SubstContext -> Elem
    subst (SubstElim t tau)   sigma = subst t (Chain tau sigma)
    subst (PiIntro f)         sigma = PiIntro (subst f (Under sigma))
    subst (PiElim f e)        sigma = PiElim (subst f sigma) (subst e sigma)
    subst (SigmaElim1 t)      sigma = SigmaElim1 (subst t sigma)
    subst (SigmaElim2 t)      sigma = SigmaElim2 (subst t sigma)
    subst (SigmaIntro a b)    sigma = SigmaIntro (subst a sigma) (subst b sigma)
    subst (PiTy a b)          sigma = PiTy (subst a sigma) (subst b (Under sigma))
    subst (SigmaTy a b)       sigma = SigmaTy (subst a sigma) (subst b (Under sigma))
    subst NatTy               sigma = NatTy
    subst ZeroTy              sigma = ZeroTy
    subst OneTy               sigma = OneTy
    subst (EqTy t0 t1 a)     sigma = EqTy (subst t0 sigma) (subst t1 sigma) (subst a sigma)
    subst OneIntro            sigma = OneIntro
    subst NatIntro0           sigma = NatIntro0
    subst (NatIntro1 t)       sigma = NatIntro1 (subst t sigma)
    -- motive in Γ ℕ, z in Γ, s in Γ ℕ A, t in Γ
    subst (NatElim motive z s t) sigma =
      NatElim (Typ.subst motive (Under sigma))
              (subst z sigma)
              (subst s (UnderN 2 sigma))
              (subst t sigma)
    subst (ZeroElim t)        sigma = ZeroElim (subst t sigma)
    subst (CtxVar i)          sigma = substContextVar i sigma
    subst Refl                sigma = Refl

||| Δ(σ) — defined by induction: ε(σ) = ε, (A Δ)(σ) = A(σ) Δ(σ⁺)
namespace Tel
  public export
  subst : Tel -> SubstContext -> Tel
  subst []          sigma = []
  subst (ty :: tel) sigma = Typ.subst ty sigma :: subst tel (Under sigma)

||| ē(σ) — defined by induction: ·(σ) = ·, (e ē)(σ) = e(σ) ē(σ)
namespace ElemList
  public export
  subst : ElemList -> SubstContext -> ElemList
  subst []        sigma = []
  subst (e :: es) sigma = Elem.subst e sigma :: subst es sigma
