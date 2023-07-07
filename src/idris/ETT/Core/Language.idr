module ETT.Core.Language

import Data.SnocList

import public ETT.Core.VarName

mutual
  namespace Context
    public export
    data Context : Type where
      ||| ε
      Empty : Context
      ||| Γ (x : A)
      Ext : Context -> VarName -> TypE -> Context
      ||| χ
      SignatureVarElim : Nat -> Context

  public export
  data SignatureEntryInstance : Type where
    CtxEntryInstance : Context -> SignatureEntryInstance
    TypEEntryInstance : TypE -> SignatureEntryInstance
    ElemEntryInstance : Elem -> SignatureEntryInstance
    LetEntryInstance : SignatureEntryInstance
    EqTyEntryInstance : SignatureEntryInstance

  namespace SubstSignature
    ||| σ : Σ₀ ⇒ Σ₁
    public export
    data SubstSignature : Type where
      ||| id
      Id : SubstSignature
      ||| ↑
      Wk : SubstSignature
      ||| σ ∘ τ
      Chain : SubstSignature -> SubstSignature -> SubstSignature
      ||| σ, i
      Ext : SubstSignature -> SignatureEntryInstance -> SubstSignature
      ||| ·
      Terminal : SubstSignature

  namespace B
    ||| Σ ⊦ τ : Γ₀ ⇒ Γ₁
    public export
    data SubstContext : Type where
      ||| id : Γ ⇒ Γ
      Id : SubstContext
      ||| ↑ : Γ (x : A) ⇒ Γ
      Wk : SubstContext
      ||| σ ∘ τ
      Chain : SubstContext -> SubstContext -> SubstContext
      ||| σ : Γ₀ ⇒ Γ₁
      ||| Γ₁ ⊦ A type
      ||| Γ₀ ⊦ t : A(σ)
      ||| ext(σ, A, t)
      Ext : SubstContext -> Elem -> SubstContext
      ||| · : Γ ⇒ ε
      Terminal : SubstContext
      ||| Σ₁ ⊦ σ : Γ₀ ⇒ Γ₁
      ||| Σ₀ ⊦ σ[τ] : Γ₀(τ) ⇒ Γ₁(τ)
      SignatureSubstElim : SubstContext -> SubstSignature -> SubstContext

  namespace C
    public export
    data SubstContextNF : Type where
      ||| · : Γ ⇒ ε
      Terminal : SubstContextNF
      ||| ↑ Γ Δ : Γ Δ ⇒ Γ
      WkN : Nat -> SubstContextNF
      ||| σ : Γ₀ ⇒ Γ₁
      ||| Γ₁ ⊦ A type
      ||| Γ₀ ⊦ t : A(σ)
      ||| ext(σ, A, t)
      Ext : SubstContext -> Elem -> SubstContextNF

  namespace C
    public export
    data TypE : Type where
      ||| (x : A) → B
      PiTy : VarName -> TypE -> TypE -> TypE
      ||| A(σ)
      ContextSubstElim : TypE -> SubstContext -> TypE
      ||| A(σ)
      SignatureSubstElim : TypE -> SubstSignature -> TypE
      ||| a₀ ≡ a₁ ∈ A
      EqTy : Elem -> Elem -> TypE -> TypE
      ||| ℕ
      NatTy : TypE
      ||| 𝕌
      UniverseTy : TypE
      ||| χ
      SignatureVarElim : Nat -> SubstContext -> TypE
      ||| El e
      El : Elem -> TypE

  namespace D
    public export
    data Elem : Type where
      ||| (x : A) → B
      PiTy : VarName -> Elem -> Elem -> Elem
      ||| x ↦ f
      PiVal : VarName -> TypE -> TypE -> Elem -> Elem
      ||| (f : (x : A) → B) e
      PiElim : Elem -> VarName -> TypE -> TypE -> Elem -> Elem
      ||| 0
      NatVal0 : Elem
      ||| S t
      NatVal1 : Elem -> Elem
      ||| ℕ
      NatTy : Elem
      ||| ℕ-elim x.A z x.h.s t
      NatElim : VarName -> TypE -> Elem -> VarName -> VarName -> Elem -> Elem -> Elem
      ||| t(σ)
      ContextSubstElim : Elem -> SubstContext -> Elem
      ||| t[σ]
      SignatureSubstElim : Elem -> SubstSignature -> Elem
      ||| xᵢ
      ContextVarElim : Nat -> Elem
      ||| Xᵢ(σ)
      SignatureVarElim : Nat -> SubstContext -> Elem
      ||| a₀ ≡ a₁ ∈ A
      EqTy : Elem -> Elem -> Elem -> Elem
      ||| *
      EqVal : Elem
      ||| J A a₀ x.p.B r a₁ a
      EqElim : TypE -> Elem -> VarName -> VarName -> TypE -> Elem -> Elem -> Elem -> Elem

  public export
  Spine : Type
  Spine = SnocList Elem

  public export
  List : Type
  List = List Elem

public export
data SignatureEntry : Type where
  CtxEntry : SignatureEntry
  TypEEntry : Context -> SignatureEntry
  ElemEntry : Context -> TypE -> SignatureEntry
  LetElemEntry : Context -> Elem -> TypE -> SignatureEntry
  EqTyEntry : Context -> TypE -> TypE -> SignatureEntry

Signature = SnocList (VarName, SignatureEntry)

public export
extend : Signature -> VarName -> SignatureEntry -> Signature
extend sig x e = sig :< (x, e)

namespace TypE
  ||| Σ (Γ ⊦ A type) Γ ⊦ A type
  public export
  Var : TypE
  Var = SignatureVarElim 0 Id

  ||| Σ₀ (Γ ⊦ A type) Σ₁ Γ(↑(1 + |Σ₁|)) ⊦ A type
  public export
  VarN : Nat -> TypE
  VarN n = SignatureVarElim n Id

namespace Context
  public export
  Var : Context
  Var = SignatureVarElim 0

namespace Elem
  public export
  VarN : Nat -> Elem
  VarN = ContextVarElim

  public export
  CtxVar : Elem
  CtxVar = ContextVarElim 0

  public export
  SigVar : Elem
  SigVar = SignatureVarElim 0 Id

  public export
  SigVarN : Nat -> Elem
  SigVarN n = SignatureVarElim n Id

namespace Context
  public export
  VarN : Nat -> Context
  VarN = SignatureVarElim

namespace Context
  ||| ↑(Γ, Δ) : Γ Δ ⇒ Γ
  ||| ↑(Γ, ε) = id(Γ) : Γ ⇒ Γ
  ||| ↑(Γ, (x : A) Δ) = ↑(Γ, A) ∘ ↑(Γ (x : A), Δ) : Γ (x : A) Δ ⇒ Γ
  public export
  WkN : Nat -> SubstContext
  WkN 0 = Id
  WkN (S k) = Chain Wk (WkN k)

namespace Signature
  public export
  WkN : Nat -> SubstSignature
  WkN 0 = Id
  WkN (S x) = Chain (WkN x) Wk

public export
SignatureInst : Type
SignatureInst = SnocList Elem

public export
ContextInst : Type
ContextInst = SnocList Elem
