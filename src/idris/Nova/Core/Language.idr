module Nova.Core.Language

import Data.SnocList
import Data.AVL

import public Nova.Core.Name

mutual
  public export
  data SignatureEntryInstance : Type where
    ElemEntryInstance : Elem -> SignatureEntryInstance
    LetEntryInstance : SignatureEntryInstance

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

  namespace D
    public export
    data Typ : Type where
      ||| 𝟘
      ZeroTy : Typ
      ||| 𝟙
      OneTy : Typ
      ||| 𝕌
      UniverseTy : Typ
      ||| ℕ
      NatTy : Typ
      ||| (x : A) → B
      PiTy : VarName -> Typ -> Typ -> Typ
      ||| {x : A} → B
      ImplicitPiTy : VarName -> Typ -> Typ -> Typ
      ||| (x : A) ⨯ B
      SigmaTy : VarName -> Typ -> Typ -> Typ
      ||| A ≡ B
      TyEqTy : Typ -> Typ -> Typ
      ||| a₀ ≡ a₁ ∈ A
      ElEqTy : Elem -> Elem -> Typ -> Typ
      ||| El A
      El : Elem -> Typ
      ||| t(σ)
      ContextSubstElim : Typ -> SubstContext -> Typ
      ||| t(σ)
      SignatureSubstElim : Typ -> SubstSignature -> Typ
      ||| Xᵢ(σ)
      OmegaVarElim : OmegaName -> SubstContext -> Typ

  namespace E
    public export
    data Elem : Type where
      ||| (x : A) → B
      PiTy : VarName -> Elem -> Elem -> Elem
      ||| {x : A} → B
      ImplicitPiTy : VarName -> Elem -> Elem -> Elem
      ||| (x : A) ⨯ B
      SigmaTy : VarName -> Elem -> Elem -> Elem
      ||| x ↦ f
      PiVal : VarName -> Typ -> Typ -> Elem -> Elem
      ||| {x} ↦ f
      ImplicitPiVal : VarName -> Typ -> Typ -> Elem -> Elem
      ||| (a, b)
      SigmaVal : Elem -> Elem -> Elem
      ||| (f : (x : A) → B) e
      PiElim : Elem -> VarName -> Typ -> Typ -> Elem -> Elem
      ||| {f : {x : A} → B} e
      ImplicitPiElim : Elem -> VarName -> Typ -> Typ -> Elem -> Elem
      ||| (p : (x : A) ⨯ B) .π₁
      SigmaElim1 : Elem -> VarName -> Typ -> Typ -> Elem
      ||| (p : (x : A) ⨯ B) .π₁
      SigmaElim2 : Elem -> VarName -> Typ -> Typ -> Elem
      ||| 0
      NatVal0 : Elem
      ||| S t
      NatVal1 : Elem -> Elem
      ||| ℕ
      NatTy : Elem
      ||| ℕ-elim x.A z x.h.s t
      NatElim : VarName -> Typ -> Elem -> VarName -> VarName -> Elem -> Elem -> Elem
      ||| t(σ)
      ContextSubstElim : Elem -> SubstContext -> Elem
      ||| t[σ]
      SignatureSubstElim : Elem -> SubstSignature -> Elem
      ||| xᵢ
      ContextVarElim : Nat -> Elem
      ||| Xᵢ(σ)
      SignatureVarElim : Nat -> SubstContext -> Elem
      ||| Xᵢ(σ)
      OmegaVarElim : OmegaName -> SubstContext -> Elem
      ||| A ≡ B
      TyEqTy : Elem -> Elem -> Elem
      ||| a₀ ≡ a₁ ∈ A
      ElEqTy : Elem -> Elem -> Elem -> Elem
      ||| Refl
      TyEqVal : Elem
      ||| Refl
      ElEqVal : Elem
      ||| 𝟘
      ZeroTy : Elem
      ||| 𝟙
      OneTy : Elem
      ||| ()
      OneVal : Elem
      ||| 𝟘-elim t
      ZeroElim : Elem -> Elem

  public export
  Context : Type
  Context = SnocList (VarName, Typ)

  public export
  Spine : Type
  Spine = SnocList Elem

  public export
  List : Type
  List = List Elem

public export
data SignatureEntry : Type where
  ||| Γ ⊦ A
  ElemEntry : Context -> Typ -> SignatureEntry
  ||| Γ ⊦ a : A
  LetElemEntry : Context -> Elem -> Typ -> SignatureEntry

Signature = SnocList (VarName, SignatureEntry)

public export
data MetaKind = NoSolve | SolveByUnification | SolveByElaboration

namespace OmegaEntry
  public export
  data OmegaEntry : Type where
    ||| Γ ⊦ type
    MetaType : Context -> MetaKind -> OmegaEntry
    ||| Γ ⊦ T
    LetType : Context -> (rhs : Typ) -> OmegaEntry
    ||| Γ ⊦ T type
    MetaElem : Context -> Typ -> MetaKind -> OmegaEntry
    ||| Γ ⊦ t : T
    LetElem : Context -> (rhs : Elem) -> (ty : Typ) -> OmegaEntry
    ||| Σ Ω Γ ⊦ A₀ ~ A₁ type
    TypeConstraint : Context -> Typ -> Typ -> OmegaEntry
    ||| Γ ⊦ a₀ ~ a₁ : A
    ElemConstraint : Context -> Elem -> Elem -> Typ -> OmegaEntry
    ||| σ₀ ~ σ₁ : Γ ⇒ Δ
    SubstContextConstraint : SubstContext -> SubstContext -> Context -> Context -> OmegaEntry

Omega = OrdTree (OmegaName, OmegaEntry) ByFst

namespace ConstraintEntry
  public export
  data ConstraintEntry : Type where
    ||| Σ Ω Γ ⊦ A₀ ~ A₁ type
    TypeConstraint : Context -> Typ -> Typ -> ConstraintEntry
    ||| Σ Ω Γ ⊦ a₀ ~ a₁ : A
    ElemConstraint : Context -> Elem -> Elem -> Typ -> ConstraintEntry
    ||| Σ Ω ⊦ σ₀ ~ σ₁ : Γ ⇒ Δ
    SubstContextConstraint : SubstContext -> SubstContext -> Context -> Context -> ConstraintEntry

Constraints = SnocList ConstraintEntry

public export
toOmegaEntry : ConstraintEntry -> OmegaEntry
toOmegaEntry (TypeConstraint x y z) = TypeConstraint x y z
toOmegaEntry (ElemConstraint x y z w) = ElemConstraint x y z w
toOmegaEntry (SubstContextConstraint x y z w) = SubstContextConstraint x y z w

public export
mbConstraintEntry : OmegaEntry -> Maybe ConstraintEntry
mbConstraintEntry (MetaType x y) = Nothing
mbConstraintEntry (LetType x rhs) = Nothing
mbConstraintEntry (MetaElem x y k) = Nothing
mbConstraintEntry (LetElem x rhs ty) = Nothing
mbConstraintEntry (ElemConstraint x y z w) = Just (ElemConstraint x y z w)
mbConstraintEntry (TypeConstraint x y z) = Just (TypeConstraint x y z)
mbConstraintEntry (SubstContextConstraint x y z w) = Just (SubstContextConstraint x y z w)

public export
mbTypingEntry : OmegaEntry -> Maybe ConstraintEntry

public export
extend : Signature -> VarName -> SignatureEntry -> Signature
extend sig x e = sig :< (x, e)

namespace Elem
  public export
  CtxVar : Elem
  CtxVar = ContextVarElim 0

  public export
  SigVar : Elem
  SigVar = SignatureVarElim 0 Id

  public export
  SigVarN : Nat -> Elem
  SigVarN n = SignatureVarElim n Id

  public export
  CtxVarN : Nat -> Elem
  CtxVarN n = ContextVarElim n

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
SignatureInst = SnocList SignatureEntryInstance

public export
ContextInst : Type
ContextInst = SnocList Elem

public export
isImplicitPi : Elem -> Bool
isImplicitPi (ImplicitPiTy str x y) = True
isImplicitPi _ = False

public export
isMetaType : OmegaEntry -> Bool
isMetaType (MetaType {}) = True
isMetaType _ = False

public export
isMetaElem : OmegaEntry -> Bool
isMetaElem (MetaElem {}) = True
isMetaElem _ = False
