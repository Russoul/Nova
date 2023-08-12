module ETT.Core.Substitution

import Data.List
import Data.SnocList
import Data.AVL

import ETT.Core.Language

mutual
  namespace A
    ||| τ : Σ₀ ⇒ Σ₁
    ||| Σ₁ ⊦ σ : Γ ⇒ Δ
    ||| -----------------------
    ||| Σ₀ ⊦ σ(τ) : Γ(τ) ⇒ Δ(τ)
    ||| Σ₀ ⊦ (id Γ)(τ) = id Γ(τ) : Γ(τ) ⇒ Γ(τ)
    ||| Σ₀ ⊦ (↑ Γ A)(τ) = ↑ Γ(τ) A(τ) : Γ(τ) A(τ) ⇒ Γ(τ)
    ||| Σ₀ ⊦ (σ₁ ∘ σ₀)(τ) = σ₁(τ) ∘ σ(τ) : Γ₀(τ) ⇒ Γ₂(τ)
    ||| Σ₀ ⊦ (ext σ A t)(τ) = ext σ(τ) A(τ) t(τ) : Γ(τ) ⇒ Δ(τ) A(τ)
    ||| Σ₀ ⊦ (terminal Γ)(τ) = terminal Γ(τ) : Γ(τ) ⇒ ε
    ||| Σ₀ ⊦ σ(τ₀)(τ₁) = σ(τ₀ ∘ τ₁) : ...
    -- Σ₁ Δ ⊦ A type
    -- Σ₁ Γ ⊦ t : A(σ)
    -- Σ₀ Γ(τ) ⊦ t(τ) : A(τ)(σ(τ))   [= A(σ)(τ)]
    public export
    subst : SubstContext -> SubstSignature -> SubstContext
    -- (id Γ)(σ) = id Γ(σ)
    subst Id sigma = Id
    -- (↑ Γ A)(σ) = ↑ Γ(σ) A(σ)
    subst Wk sigma = Wk
    subst (Chain tau0 tau1) sigma = Chain (SignatureSubstElim tau0 sigma) (SignatureSubstElim tau1 sigma)
    -- (τ, t : A)(σ) = τ(σ), t(σ) : A(σ)
    subst (Ext tau t) sigma = Ext (SignatureSubstElim tau sigma) (SignatureSubstElim t sigma)
    subst Terminal sigma = Terminal
    subst (SignatureSubstElim tau sigma0) sigma1 = subst tau (Chain sigma0 sigma1)

    public export
    runSubst : SubstContext -> SubstContext
    runSubst (SignatureSubstElim sigma tau) = subst sigma tau
    runSubst x = x

    ||| i ∈ Σ₂
    ||| Σ₂ ⊦ σ : Δ ⇒ Γ
    ||| Σ₂ Γ ⊦ χᵢ : A
    ||| Σ₂ Δ ⊦ χᵢ σ : A(σ)
    ||| τ₀ : Σ₁ ⇒ Σ₂
    ||| τ₁ : Σ₀ ⇒ Σ₁
    ||| --------------------------------------------
    ||| Σ₀ Δ(τ₀)(τ₁) ⊦ (χᵢ σ)(τ₀)(τ₁) : A(σ)(τ₀)(τ₁)
    ||| Σ₀ Δ(↑)(τ : Σ₀ ⇒ Σ E) ⊦ (χᵢ σ)(↑)(τ) = (χᵢ₊₁ σ(↑))(τ)(id) : A(σ)(↑)(τ)       //↑ : Σ E ⇒ Σ
    -- Σ E ⊦ σ(↑) : Δ(↑) ⇒ Γ(↑)
    -- Σ Γ ⊦ χᵢ : A
    -- Σ E Γ(↑) ⊦ χᵢ₊₁ : A(↑)
    -- Σ E Δ(↑) ⊦ χᵢ₊₁ σ(↑) : A(σ)(↑)
    -- Σ₀ Δ(↑)(τ) ⊦ (χᵢ₊₁ σ(↑))(τ) : A(σ)(↑)(τ)
    ||| Σ₀ Δ(τ₀, t)(τ₁) ⊦ (χ₀ σ)(τ₀, t)(τ₁) = t(σ(τ₀, t))(τ₁) : A(↑)(σ)(τ₀, t)(τ₁)   [= A(τ₀)(σ(τ₀, t))(τ₁)]
    -- Σ₂ (Ω ⊦ A) Ω(↑) ⊦ χ₀ : A(↑)
    -- Σ₂ (Ω ⊦ A) ⊦ σ : Δ ⇒ Ω(↑)

    -- τ₀ : Σ₁ ⇒ Σ₂
    -- Σ₁ Ω(τ₀) ⊦ t : A(τ₀)
    -- τ₀, t : Σ₁ ⇒ Σ₂ (Ω ⊦ A)

    -- Σ₁ ⊦ σ(τ₀, t) : Δ(τ₀, t) ⇒ Ω(τ₀)
    -- Σ₂ ⊦ (Ω ⊦ A) entry
    -- Σ₁ Δ(τ₀, t) ⊦ t(σ(τ₀, t)) : A(τ₀)(σ(τ₀, t))
    -- Σ₀ Δ(τ₀, t)(τ₁) ⊦ t(σ(τ₀, t))(τ₁) : A(τ₀)(σ(τ₀, t))(τ₁)
    ||| Σ₀ Δ(τ₀)(τ₁) ⊦ (χ₁₊ᵢ σ)(τ₀, t)(τ₁) = (χᵢ σ)(τ₀)(τ₁) : A(↑Σ₂₁)(σ)(τ₀)(τ₁)

    -- Σ₂₀ (Γ ⊦ A) Σ₂₁ (Ω ⊦ C) Γ(↑)(↑Σ₂₁) ⊦ χ₁₊ᵢ : A(↑)(↑Σ₂₁)
    -- Σ₂₀ (Γ ⊦ A) Σ₂₁ Γ(↑Σ₂₁) ⊦ χᵢ : A(↑Σ₂₁)
    -- τ₀ : Σ₁ ⇒ Σ₂₀ (Γ ⊦ A) Σ₂₁
    -- Σ₁ Γ(↑Σ₂₁)(τ₀) ⊦ χᵢ(τ₁) : A(↑Σ₂₁)(τ₀)
    -- Σ₁ Δ(τ₀, t) ⊦ χᵢ(τ₁)(σ) = (χᵢ σ)(τ₁) : A(↑Σ₂₁)(τ₀)(σ)
    -- Σ₂₀ (Γ ⊦ A) Σ₂₁ (Ω ⊦ C) ⊦ σ : Δ ⇒ Γ(↑)(↑Σ₂₁)
    -- Σ₁ ⊦ σ : Δ(τ₀, t) ⇒ Γ(↑Σ₂₁)(τ₀)
    public export
    substSignatureVar : Nat -> SubstSignature -> SubstSignature -> SubstContext -> Elem
    substSignatureVar x Id Id spine = SignatureVarElim x spine
    substSignatureVar x Id sigma1 spine = substSignatureVar x sigma1 Id spine
    substSignatureVar x Wk sigma1 spine = substSignatureVar (S x) sigma1 Id spine
    substSignatureVar x (Chain Id tau) sigma spine = substSignatureVar x tau sigma spine
    substSignatureVar x (Chain tau0 tau1) sigma1 spine = substSignatureVar x tau0 (Chain tau1 sigma1) spine
    -- Σ (Δ ⊦ χ : A) | Γ ⊦ χ₀(ē)[τ, t] = t(ē[τ, t])
    -- Σ (Δ ⊦ χ : A) | Γ ⊦ χ₁₊ᵢ(ē)[τ, t] = χᵢ(ē[τ, t])[τ]
    substSignatureVar 0 (Ext tau (ElemEntryInstance t)) sigma1 spine = FailSt.do
      subst (SignatureSubstElim t sigma1) spine
    substSignatureVar 0 (Ext tau (TypeEntryInstance t)) sigma1 spine =
      subst (SignatureSubstElim t sigma1) spine
    substSignatureVar (S k) (Ext tau _) sigma1 spine =
      substSignatureVar k tau sigma1 spine
    substSignatureVar 0 (Ext tau (CtxEntryInstance _)) sigma1 spine =
      assert_total $ idris_crash "Elem.substSignatureVar(CtxEntryInstance)"
    substSignatureVar 0 (Ext tau (LetEntryInstance {})) sigma1 spine =
      assert_total $ idris_crash "Elem.substSignatureVar(LetEntryInstance)"
    substSignatureVar 0 (Ext tau EqTyEntryInstance) sigma1 spine =
      assert_total $ idris_crash "Elem.substSignatureVar(EqEntryInstance)"
    substSignatureVar x Terminal sigma1 spine = assert_total $ idris_crash "substSignatureVar(Terminal)"

    ||| xᵢ(σ : Γ₁ ⇒ Γ₂)(τ : Γ₀ ⇒ Γ₁)
    substContextVarNu : Nat -> SubstContext -> SubstContext -> Elem
    substContextVarNu x Id Id = ContextVarElim x
    -- xᵢ(id : Γ ⇒ Γ)(τ : Γ₀ ⇒ Γ)
    substContextVarNu x Id tau = substContextVar x tau Id
    -- xᵢ(↑ : Γ (x : A) ⇒ Γ)(τ : Γ₀ ⇒ Γ (x : A))
    substContextVarNu x Wk tau = substContextVar (S x) tau Id
    substContextVarNu x (Chain Id sigma) tau = substContextVar x sigma tau
    substContextVarNu x (Chain sigma0 sigma1) tau = substContextVar x sigma0 (Chain sigma1 tau)
    substContextVarNu 0 (Ext sigma t) tau = subst t tau
    substContextVarNu (S k) (Ext sigma t) tau = substContextVar k sigma tau
    substContextVarNu x Terminal tau = assert_total $ idris_crash "substContextVarNu(Terminal)"
    substContextVarNu x (SignatureSubstElim {}) tau = assert_total $ idris_crash "substContextVarNu(SignatureSubstElim)"

    ||| xᵢ(σ)(τ)
    public export
    substContextVar : Nat -> SubstContext -> SubstContext -> Elem
    substContextVar x sigma tau = substContextVarNu x (runSubst sigma) tau

  namespace B
    ||| t(σ)
    public export
    subst : Elem -> SubstContext -> Elem
    -- ℕ(σ) = ℕ
    subst NatTy sigma = NatTy
    -- 𝕌(σ) = 𝕌
    subst Universe sigma = Universe
    -- (π A B)(σ) = π A(σ) B(σ⁺(El A))
    subst (PiTy x a b) sigma =
      PiTy x (ContextSubstElim a sigma) (ContextSubstElim b (Under sigma))
    subst (ImplicitPiTy x a b) sigma =
      ImplicitPiTy x (ContextSubstElim a sigma) (ContextSubstElim b (Under sigma))
    -- (π A B)(σ) = π A(σ) B(σ⁺(El A))
    subst (SigmaTy x a b) sigma =
      SigmaTy x (ContextSubstElim a sigma) (ContextSubstElim b (Under sigma))
    -- (λ A B f)(σ) = λ A B(σ⁺(A)) f(σ⁺(A))
    subst (PiVal x a b f) sigma =
      PiVal x (ContextSubstElim a sigma) (ContextSubstElim b (Under sigma)) (ContextSubstElim f (Under sigma))
    subst (ImplicitPiVal x a b f) sigma =
      ImplicitPiVal x (ContextSubstElim a sigma) (ContextSubstElim b (Under sigma)) (ContextSubstElim f (Under sigma))
    subst (SigmaVal a b) sigma =
      SigmaVal (ContextSubstElim a sigma) (ContextSubstElim b sigma)
    -- (ap f A B e)(σ) = ap f(σ) A(σ) B(σ⁺(A)) e(σ)
    subst (PiElim f x a b e) sigma =
      PiElim (ContextSubstElim f sigma)
             x
             (ContextSubstElim a sigma)
             (ContextSubstElim b (Under sigma))
             (ContextSubstElim e sigma)
    subst (ImplicitPiElim f x a b e) sigma =
      ImplicitPiElim (ContextSubstElim f sigma)
             x
             (ContextSubstElim a sigma)
             (ContextSubstElim b (Under sigma))
             (ContextSubstElim e sigma)
    subst (SigmaElim1 f x a b) sigma =
      SigmaElim1 (ContextSubstElim f sigma)
                 x
                 (ContextSubstElim a sigma)
                 (ContextSubstElim b (Under sigma))
    subst (SigmaElim2 f x a b) sigma =
      SigmaElim2 (ContextSubstElim f sigma)
                 x
                 (ContextSubstElim a sigma)
                 (ContextSubstElim b (Under sigma))
    -- 0(σ) = 0
    subst NatVal0 sigma =
      NatVal0
    -- (S t)(σ) = S t(σ)
    subst (NatVal1 t) sigma =
      NatVal1 (ContextSubstElim t sigma)
    -- (ℕ-elim A z s t)(σ) = ℕ-elim A(σ⁺(ℕ)) z(σ) s(σ⁺(ℕ A ε)) t(σ)
    subst (NatElim x schema z y h s t) sigma =
      NatElim x
              (ContextSubstElim schema (Under sigma))
              z
              y
              h
              (ContextSubstElim s (UnderN 2 sigma))
              (ContextSubstElim t sigma)
    -- t(σ₀)(σ₁) = t(σ₀ ∘ σ₁)
    subst (ContextSubstElim t tau) sigma =
      subst t (Chain tau sigma)
    -- t(σ)(τ) = t(τ)(σ)
    subst (SignatureSubstElim t tau) sigma =
      subst (subst t tau) sigma
    -- χᵢ(σ) = χᵢ(σ)(id(dom σ))
    subst (ContextVarElim k) sigma = substContextVar k sigma Id
    -- Σ Δ ⊦ χ type
    -- Σ ⊦ σ : Γ ⇒ Δ
    -- Σ Γ ⊦ χ(σ)
    -- Σ₀ Γ(τ) ⊦ χ(σ)(τ) = χ(σ ∘ τ)
    subst (SignatureVarElim k sigma) tau = SignatureVarElim k (Chain sigma tau)
    subst (OmegaVarElim k sigma) tau = OmegaVarElim k (Chain sigma tau)
    subst (EqTy a0 a1 ty) tau = EqTy (ContextSubstElim a0 tau) (ContextSubstElim a1 tau) (ContextSubstElim ty tau)
    subst EqVal tau = EqVal

  namespace C
    public export
    subst : Elem -> SubstSignature -> Elem
    subst (PiTy x a b) sigma = PiTy x (SignatureSubstElim a sigma) (SignatureSubstElim b sigma)
    subst (ImplicitPiTy x a b) sigma = ImplicitPiTy x (SignatureSubstElim a sigma) (SignatureSubstElim b sigma)
    subst (SigmaTy x a b) sigma = SigmaTy x (SignatureSubstElim a sigma) (SignatureSubstElim b sigma)
    subst (PiVal x a b f) sigma = PiVal x (SignatureSubstElim a sigma) (SignatureSubstElim b sigma) (SignatureSubstElim f sigma)
    subst (ImplicitPiVal x a b f) sigma = ImplicitPiVal x (SignatureSubstElim a sigma) (SignatureSubstElim b sigma) (SignatureSubstElim f sigma)
    subst (SigmaVal a b) sigma = SigmaVal (SignatureSubstElim a sigma) (SignatureSubstElim b sigma)
    subst (PiElim f x a b e) sigma =
      PiElim
          (SignatureSubstElim f sigma)
          x
          (SignatureSubstElim a sigma)
          (SignatureSubstElim b sigma)
          (SignatureSubstElim e sigma)
    subst (ImplicitPiElim f x a b e) sigma =
      ImplicitPiElim
          (SignatureSubstElim f sigma)
          x
          (SignatureSubstElim a sigma)
          (SignatureSubstElim b sigma)
          (SignatureSubstElim e sigma)
    subst (SigmaElim1 f x a b) sigma =
      SigmaElim1
          (SignatureSubstElim f sigma)
          x
          (SignatureSubstElim a sigma)
          (SignatureSubstElim b sigma)
    subst (SigmaElim2 f x a b) sigma =
      SigmaElim2
          (SignatureSubstElim f sigma)
          x
          (SignatureSubstElim a sigma)
          (SignatureSubstElim b sigma)
    subst NatVal0 sigma = NatVal0
    subst NatTy sigma = NatTy
    subst Universe sigma = Universe
    subst (NatVal1 t) sigma = NatVal1 (SignatureSubstElim t sigma)
    subst (NatElim x schema z y h s t) sigma =
      NatElim
         x
         (SignatureSubstElim schema sigma)
         (SignatureSubstElim z sigma)
         y
         h
         (SignatureSubstElim s sigma)
         (SignatureSubstElim t sigma)
    subst (ContextSubstElim t sigma) tau =
      subst (subst t sigma) tau
    subst (SignatureSubstElim t sigma0) sigma1 =
      subst t (Chain sigma0 sigma1)
    subst (ContextVarElim k) sigma = ContextVarElim k
    subst (OmegaVarElim k tau) sigma = OmegaVarElim k (subst tau sigma)
    subst (SignatureVarElim k tau) sigma = substSignatureVar k sigma Id (subst tau sigma)
    subst (EqTy a0 a1 ty) tau = EqTy (SignatureSubstElim a0 tau) (SignatureSubstElim a1 tau) (SignatureSubstElim ty tau)
    subst EqVal tau = EqVal

  namespace List
    public export
    subst : List -> SubstContext -> List
    subst [] sigma = []
    subst (t :: ts) sigma = ContextSubstElim t sigma :: subst ts sigma

  namespace ContextSpine
    public export
    subst : Spine -> SubstContext -> Spine
    subst [<] sigma = [<]
    subst (ts :< t) sigma = subst ts sigma :< ContextSubstElim t sigma

  namespace SignatureSpine
    public export
    subst : Spine -> SubstSignature -> Spine
    subst [<] sigma = [<]
    subst (ts :< t) sigma = subst ts sigma :< SignatureSubstElim t sigma

  namespace SignatureContext
    ||| τ : Σ₀ ⇛ Σ₁
    ||| Σ₁ ⊦ χ type
    ||| ------------
    ||| Σ₀ ⊦ χ(τ) type
    ||| Σ₀ ⊦ χ(τ) type
    public export
    substSignatureVar : Nat -> SubstSignature -> SubstSignature -> Context
    substSignatureVar x Id Id = SignatureVarElim x
    substSignatureVar x Id sigma1 = substSignatureVar x sigma1 Id
    substSignatureVar x Wk sigma1 = substSignatureVar (S x) sigma1 Id
    substSignatureVar x (Chain Id tau) sigma = substSignatureVar x tau sigma
    substSignatureVar x (Chain tau0 tau1) sigma1 = substSignatureVar x tau0 (Chain tau1 sigma1)
    --- τ : Σ₀ ⇛ Σ₁
    --- Σ₀ ⊦ Γ ctx
    --- ? ≔ (τ, Γ) : Σ₀ ⇛ Σ₁ (χ ctx)
    --- -------------------
    --- Σ₀ ⊦ χ₀(τ, Γ) = Γ ctx
    substSignatureVar 0 (Ext tau (CtxEntryInstance ctx)) sigma1 = FailSt.do
      subst ctx sigma1
    substSignatureVar (S k) (Ext tau _) sigma1 =
      substSignatureVar k tau sigma1
    substSignatureVar 0 (Ext tau _) sigma1 = assert_total $ idris_crash "Context.substSignatureVar(...)"
    substSignatureVar x Terminal sigma1 = assert_total $ idris_crash "substSignatureVar(Terminal)"

    ||| σ : Γ₀ ⇒ Γ₁
    ||| Γ₁ ⊦ A type
    |||               ↑    σ
    ||| Γ₀ (x : A(σ)) ⇒ Γ₀ ⇒ Γ₁
    ||| σ⁺(A) = ext (σ ∘ ↑(Γ₀, A(σ)), A, x) : Γ₀ (x : A(σ)) ⇒ Γ₁ (x : A)
    public export
    Under : SubstContext -> SubstContext
    Under sigma = Ext (Chain sigma Wk) (ContextVarElim 0)

    ||| σ : Γ₀ ⇒ Γ₁
    ||| Γ₁ ⊦ Δ tel
    ||| σ⁺(Δ) : Γ₀ Δ(σ) ⇒ Γ₁ Δ
    ||| σ⁺(ε) = σ
    ||| σ⁺((x : A) Δ) = (σ⁺(A))⁺(Δ) : Γ₀ (x : A(σ)) Δ(σ⁺(A)) ⇒ Γ₁ (x : A) Δ
    public export
    UnderN : Nat -> SubstContext -> SubstContext
    UnderN 0 sigma = sigma
    UnderN (S k) sigma = UnderN k (Under sigma)

    namespace Signature
      ||| σ : Σ₀ ⇒ Σ₁
      ||| Σ₁ ⊦ E sig-entry
      ||| -------------------
      ||| σ⁺(E) : Σ₀ E(σ) ⇒ Σ₁ E
      ||| σ⁺(Γ ⊦ A type) = σ ∘ ↑ : Σ₀ (Γ(σ) ⊦ A type) ⇒ Σ₁ (Γ ⊦ A type)
      -- Σ₀ (Γ(σ) ⊦ A type) Γ(σ)(↑) ⊦ χ₀ (id Γ(σ)(↑)) type
      ||| σ⁺(Γ ⊦ x : A) : Σ₀ (Γ(σ) ⊦ x : A(σ)) ⇒ Σ₁ (Γ ⊦ x : A)
      ||| σ⁺(Γ ⊦ x ≔ e : A) : Σ₀ (Γ(σ) ⊦ x ≔ e(σ) : A(σ)) ⇒ Σ₁ (Γ ⊦ x ≔ e : A)
      ||| σ⁺(Γ ⊦ A = B type) : Σ₀ (Γ(σ) ⊦ A(σ) = B(σ) type) ⇒ Σ₁ (Γ ⊦ A = B type)
      public export
      Under : SubstSignature -> SignatureEntry -> SubstSignature
      Under sigma CtxEntry = Ext (Chain sigma Wk) (CtxEntryInstance Var)
      Under sigma (TypeEntry ctx) =
        Ext (Chain sigma Wk) (TypeEntryInstance $ SignatureVarElim 0 Id)
      Under sigma (ElemEntry ctx ty) =
        Ext (Chain sigma Wk) (ElemEntryInstance $ SignatureVarElim 0 Id)
      Under sigma (LetElemEntry ctx e ty) =
        Ext (Chain sigma Wk) LetEntryInstance
      Under sigma (EqTyEntry ctx a b) =
        Ext (Chain sigma Wk) EqTyEntryInstance

      ||| σ : Σ₀ ⇒ Σ₁
      ||| Σ₁ ⊦ Δ sig
      ||| -------------------
      ||| σ⁺(Δ) : Σ₀ Δ(σ) ⇒ Σ₁ Δ
      ||| σ⁺(ε) : Σ₀ ⇒ Σ₁
      ||| σ⁺((x : E) Δ) : Σ₀ ((x : E(σ)) Δ(σ⁺(E))) ⇒ Σ₁ (x : E) Δ
      public export
      UnderN : SubstSignature -> List (VarName, SignatureEntry) -> SubstSignature
      UnderN sigma [] = sigma
      UnderN sigma ((x, e) :: es) = UnderN (Under sigma e) es


    public export
    subst : Context -> SubstSignature -> Context
    -- ε(τ) = ε
    subst Empty tau = Empty
    -- (Γ (x : A))(τ) = Γ(τ) (x : A(τ))
    subst (Ext ctx x ty) tau = Ext (subst ctx tau) x (SignatureSubstElim ty tau)
    -- χ(τ)
    subst (SignatureVarElim x) tau = substSignatureVar x tau Id

namespace SignatureEntry
  public export
  subst : SignatureEntry -> SubstSignature -> SignatureEntry
  subst CtxEntry sigma = CtxEntry
  subst (TypeEntry ctx) sigma = TypeEntry (subst ctx sigma)
  subst (ElemEntry ctx ty) sigma = ElemEntry (subst ctx sigma) (SignatureSubstElim ty sigma)
  subst (LetElemEntry ctx e ty) sigma = LetElemEntry (subst ctx sigma) (SignatureSubstElim e sigma) (SignatureSubstElim ty sigma)
  subst (EqTyEntry ctx a b) sigma = EqTyEntry (subst ctx sigma) (SignatureSubstElim a sigma) (SignatureSubstElim b sigma)

namespace EntryList
  public export
  subst : List (VarName, SignatureEntry) -> SubstSignature -> List (VarName, SignatureEntry)
  subst [] sigma = []
  subst ((x, e) :: es) sigma = (x, subst e sigma) :: subst es (Under sigma e)

namespace Signature
  public export
  subst : Signature -> SubstSignature -> Signature
  subst sig sigma = cast {to = Signature} (subst (cast {to = List _} sig) sigma)

namespace OmegaEntry
  public export
  subst : OmegaEntry -> SubstSignature -> OmegaEntry
  subst (MetaType ctx k) sigma = MetaType (subst ctx sigma) k
  subst (LetType ctx rhs) sigma = LetType (subst ctx sigma) (SignatureSubstElim rhs sigma)
  subst (MetaElem ctx ty k) sigma = MetaElem (subst ctx sigma) (SignatureSubstElim ty sigma) k
  subst (LetElem ctx rhs ty) sigma = LetElem (subst ctx sigma) (SignatureSubstElim rhs sigma) (SignatureSubstElim ty sigma)
  subst (TypeConstraint ctx a b) sigma = TypeConstraint (subst ctx sigma) (SignatureSubstElim a sigma) (SignatureSubstElim b sigma)
  subst (ElemConstraint ctx a b ty) sigma = ElemConstraint (subst ctx sigma) (SignatureSubstElim a sigma) (SignatureSubstElim b sigma) (SignatureSubstElim ty sigma)
  subst (SubstContextConstraint tau0 tau1 source target) sigma =
    SubstContextConstraint (SignatureSubstElim tau0 sigma) (SignatureSubstElim tau1 sigma) (subst source sigma) (subst target sigma)

namespace Omega
  public export
  subst : Omega -> SubstSignature -> Omega
  subst omega sigma = unsafeMap (\(x, t) => (x, subst t sigma)) omega

namespace Elem
  public export
  runSubst : Elem -> Elem
  runSubst (ContextSubstElim t sigma) = subst t sigma
  runSubst (SignatureSubstElim t sigma) = subst t sigma
  runSubst t = t

public export
toContext : SnocList (VarName, Elem) -> Context
toContext [<] = Empty
toContext (tyes :< (x, ty)) = Ext (toContext tyes) x ty

||| Γ ⊦ id : Γ
||| ε ⊦ id = · : ε
||| Γ (x : A) ⊦ id = Γ (x : A) : ε
||| n = |Γ|
idSpine : SnocList (VarName, Elem) -> Spine
idSpine [<] = [<]
idSpine (tyes :< (x, ty)) =
  subst (idSpine tyes) (the SubstContext Wk) :< ContextVarElim 0
 -- Γ ⊦ id(Γ) : Γ
 -- Γ A ⊦ id(Γ A) = id(Γ)(↑), 0 : Γ A

mutual
  ||| σ : Γ ⇒ Δ
  ||| n = |Δ|
  ||| ------------------
  ||| Γ ⊦ toSpine(σ) : Δ
  public export
  toSpineNu : SnocList (VarName, Elem) -> SubstContext -> Spine
  toSpineNu delta Id = idSpine delta
  -- ↑ : Γ (x : A) ⇒ Γ
  -- Γ (x : A) ⊦ toSpine(↑) : Γ
  toSpineNu delta Wk = ContextSpine.subst (idSpine delta) Wk
  -- σ : Γ ⇒ Δ
  -- τ : Δ ⇒ Ξ
  -- Γ ⊦ toSpine(τ)[σ] : Ξ
  -- τ : Δ ⇒ Ξ
  -- Γ ⊦ toSpine(σ ∘ τ) = toSpine(τ)[σ] : Ξ
  toSpineNu delta (Chain sigma tau) = subst (toSpine delta tau) sigma
  toSpineNu (delta :< (x, ty)) (Ext tau t) = toSpine delta tau :< t
  toSpineNu [<] (Ext {}) = assert_total $ idris_crash "toSpineNu(0, Ext)"
  toSpineNu [<] Terminal = [<]
  toSpineNu (_ :< _) Terminal = assert_total $ idris_crash "toSpineNu (S _, Terminal)"
  toSpineNu delta (SignatureSubstElim x y) = assert_total $ idris_crash "toSpineNu(SignatureSubstElim)"

  public export
  toSpine : SnocList (VarName, Elem) -> SubstContext -> Spine
  toSpine delta sigma = toSpineNu delta (runSubst sigma)

public export
quote : SubstContextNF -> SubstContext
quote Terminal = Terminal
quote (WkN k) = WkN k
quote (Ext sigma a) = Ext sigma a

-- x y z w ⊦ ·, 3, 2, 1, 0 = ↑⁴, 3, 2, 1, 0 = id : x y z w
-- ·, 4, 3, 2, 1, 0 = ↑⁵, 4, 3, 2, 1, 0 = id
-- ↑⁵
-- terminal can be always reduced to weakening but for that we need to know length of the context...
public export
eval : SubstContext -> SubstContextNF
eval Id = WkN 0
eval Wk = WkN 1
eval (Chain sigma tau) =
  case (eval sigma, eval tau) of
    (Terminal, b) => Terminal
    (WkN 0, b) => b
    (WkN (S k), Terminal) => assert_total $ idris_crash "eval" -- impossible by typing
    -- ↑ᵐ : Γ₀ Δ₀ ⇒ Γ₀
    -- Γ₀ = Γ₁ Δ₁
    -- ↑ⁿ : Γ₁ Δ₁ ⇒ Γ₁
    -- hence
    -- Γ₁ Δ₁ Δ₀
    (WkN delta1@(S _), WkN delta0) => WkN (delta1 + delta0)
    -- ↑ᵐ : Γ Δ (x : A) ⇒ Γ
    -- σ : Ω ⇒ Γ Δ (x : A)
    (WkN list@(S k), Ext sigma t) => eval (Chain (WkN k) sigma)
      -- ⟦↑ ∘ (σ, t)⟧ = ⟦id ∘ σ⟧ = ⟦σ⟧
    (Ext sigma t, _) => Ext (Chain sigma tau) (ContextSubstElim t tau)
eval (Ext sigma t) = Ext sigma t
eval Terminal = Terminal
eval tm@(SignatureSubstElim x y) = eval (runSubst tm)

public export
headNormalise : SubstContext -> SubstContext
headNormalise = quote . eval
