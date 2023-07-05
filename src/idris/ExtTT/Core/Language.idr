module ExtTT.Core.Language

import Data.SnocList

import public ExtTT.Core.VarName

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
      ||| σ, Γ
      ExtCtx : SubstSignature -> Context -> SubstSignature
      ||| σ, A
      ExtTypE : SubstSignature -> TypE -> SubstSignature
      ||| σ, t
      ExtElem : SubstSignature -> Elem -> SubstSignature
      ||| σ, *
      ExtEqTy : SubstSignature -> SubstSignature
      ||| ·
      Terminal : SubstSignature

  namespace B
    ||| Σ ⊦ τ : Γ₀ ⇒ Γ₁
    public export
    data SubstContext : Type where
      ||| id : Γ ⇒ Γ
      Id : Context -> SubstContext
      ||| ↑ : Γ (x : A) ⇒ Γ
      Wk : Context -> TypE -> SubstContext
      ||| σ ∘ τ
      Chain : SubstContext -> SubstContext -> SubstContext
      ||| σ : Γ₀ ⇒ Γ₁
      ||| Γ₁ ⊦ A type
      ||| Γ₀ ⊦ t : A(σ)
      ||| ext(σ, A, t)
      Ext : SubstContext -> TypE -> Elem -> SubstContext
      ||| · : Γ ⇒ ε
      Terminal : Context -> SubstContext
      ||| Σ₁ ⊦ σ : Γ₀ ⇒ Γ₁
      ||| Σ₀ ⊦ σ[τ] : Γ₀(τ) ⇒ Γ₁(τ)
      SignatureSubstElim : SubstContext -> SubstSignature -> SubstContext

  namespace C
    public export
    data SubstContextNF : Type where
      ||| · : Γ ⇒ ε
      Terminal : Context -> SubstContextNF
      ||| ↑ Γ Δ : Γ Δ ⇒ Γ
      WkN : Context -> List (VarName, TypE) -> SubstContextNF
      ||| σ : Γ₀ ⇒ Γ₁
      ||| Γ₁ ⊦ A type
      ||| Γ₀ ⊦ t : A(σ)
      ||| ext(σ, A, t)
      Ext : SubstContext -> TypE -> Elem -> SubstContextNF

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
      ||| Refl (a : A)
      EqVal : Elem -> TypE -> Elem
      ||| J A a₀ x.p.B r a₁ a
      EqElim : TypE -> Elem -> VarName -> VarName -> TypE -> Elem -> Elem -> Elem -> Elem

  public export
  Spine : Type
  Spine = SnocList Elem

  public export
  List : Type
  List = List Elem

namespace Signature
  public export
  data Signature : Type where
    ||| ε
    Empty : Signature
    ||| Σ (χ ctx)
    ExtCtx : Signature -> VarName -> Signature
    ||| Σ (Γ ⊦ χ type)
    ExtTypE : Signature -> Context -> VarName -> Signature
    ||| Σ (Γ ⊦ χ : A)
    ExtElem : Signature -> Context -> VarName -> TypE -> Signature
    ||| Σ (Γ ⊦ χ ≔ a : A)
    ExtLetElem : Signature -> Context -> VarName -> Elem -> TypE -> Signature
    ||| Σ (Γ ⊦ A = B type)
    ExtEqTy : Signature -> Context -> VarName -> TypE -> TypE -> Signature

public export
data SignatureEntry : Type where
  CtxEntry : SignatureEntry
  TypEEntry : Context -> SignatureEntry
  ElemEntry : Context -> TypE -> SignatureEntry
  LetElemEntry : Context -> Elem -> TypE -> SignatureEntry
  EqTyEntry : Context -> TypE -> TypE -> SignatureEntry

public export
toSnocList : Signature -> SnocList (VarName, SignatureEntry)
toSnocList Empty = [<]
toSnocList (ExtCtx sig x) = toSnocList sig :< (x, CtxEntry)
toSnocList (ExtTypE sig ctx x) = toSnocList sig :< (x, TypEEntry ctx)
toSnocList (ExtElem sig ctx x ty) = toSnocList sig :< (x, ElemEntry ctx ty)
toSnocList (ExtLetElem sig ctx x e ty) = toSnocList sig :< (x, LetElemEntry ctx e ty)
toSnocList (ExtEqTy sig ctx x a b) = toSnocList sig :< (x, EqTyEntry ctx a b)

public export
toList : Signature -> List (VarName, SignatureEntry)
toList sig = cast (toSnocList sig)

public export
fromSnocList : SnocList (VarName, SignatureEntry) -> Signature
fromSnocList [<] = Empty
fromSnocList (xs :< (x, CtxEntry)) = ExtCtx (fromSnocList xs) x
fromSnocList (xs :< (x, (TypEEntry ctx))) = ExtTypE (fromSnocList xs) ctx x
fromSnocList (xs :< (x, (ElemEntry ctx ty))) = ExtElem (fromSnocList xs) ctx x ty
fromSnocList (xs :< (x, (LetElemEntry ctx e ty))) = ExtLetElem (fromSnocList xs) ctx x e ty
fromSnocList (xs :< (x, EqTyEntry ctx a b)) = ExtEqTy (fromSnocList xs) ctx x a b

public export
fromList : List (VarName, SignatureEntry) -> Signature
fromList xs = fromSnocList (cast xs)

public export
extend : Signature -> VarName -> SignatureEntry -> Signature
extend sig x CtxEntry = ExtCtx sig x
extend sig x (TypEEntry ctx) = ExtTypE sig ctx x
extend sig x (ElemEntry ctx ty) = ExtElem sig ctx x ty
extend sig x (LetElemEntry ctx e ty) = ExtLetElem sig ctx x e ty
extend sig x (EqTyEntry ctx a b) = ExtEqTy sig ctx x a b

public export
(++) : Signature -> Signature -> Signature
sig ++ Empty = sig
sig0 ++ ExtCtx sig1 x = ExtCtx (sig0 ++ sig1) x
sig0 ++ ExtTypE sig1 ctx x = ExtTypE (sig0 ++ sig1) ctx x
sig0 ++ ExtElem sig1 ctx x ty = ExtElem (sig0 ++ sig1) ctx x ty
sig0 ++ ExtLetElem sig1 ctx x e ty = ExtLetElem (sig0 ++ sig1) ctx x e ty
sig0 ++ ExtEqTy sig1 ctx x a b = ExtEqTy (sig0 ++ sig1) ctx x a b

namespace TypE
  ||| Σ (Γ ⊦ A type) Γ ⊦ A type
  public export
  Var : Context -> TypE
  Var gamma = SignatureVarElim 0 (Id gamma)

namespace Context
  public export
  Var : Context
  Var = SignatureVarElim 0

namespace Elem
  public export
  VarN : Nat -> Elem
  VarN = ContextVarElim

namespace Context
  public export
  VarN : Nat -> Context
  VarN = SignatureVarElim

namespace Context
  ||| ↑(Γ, Δ) : Γ Δ ⇒ Γ
  ||| ↑(Γ, ε) = id(Γ) : Γ ⇒ Γ
  ||| ↑(Γ, (x : A) Δ) = ↑(Γ, A) ∘ ↑(Γ (x : A), Δ) : Γ (x : A) Δ ⇒ Γ
  public export
  WkN : Context -> List (VarName, TypE) -> SubstContext
  WkN ctx [] = Id ctx
  WkN ctx ((x, ty) :: tyes) = Chain (Wk ctx ty) (WkN ctx tyes)

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
