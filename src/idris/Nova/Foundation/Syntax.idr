module Nova.Foundation.Syntax

import Data.SnocList

mutual
  namespace SubstContext
    ||| Typing context substitution
    ||| σ, τ ::= · | σ, t | σ ∘ τ | id | ↑
    public export
    data SubstContext : Type where
      ||| ·  (unique substitution into the empty context)
      Terminal : SubstContext
      ||| σ, t  (substitution into an extended context)
      Ext : SubstContext -> Elem -> SubstContext
      ||| σ ∘ τ  (composition of substitutions)
      Chain : SubstContext -> SubstContext -> SubstContext
      ||| id  (identity substitution)
      Id : SubstContext
      ||| ↑  (weakening substitution)
      Wk : SubstContext

  namespace Typ
    ||| Type
    ||| T ::= 𝕌 | T → T | T ⨯ T | t ≡ t ∈ T | ℕ | 𝟘 | 𝟙 | El t | T(σ)
    public export
    data Typ : Type where
      ||| 𝕌
      UniverseTy : Typ
      ||| T → T  (dependent product type, Π)
      PiTy : Typ -> Typ -> Typ
      ||| T ⨯ T  (dependent sum type, Σ)
      SigmaTy : Typ -> Typ -> Typ
      ||| t ≡ t ∈ T  (extensional equality type)
      EqTy : Elem -> Elem -> Typ -> Typ
      ||| ℕ
      NatTy : Typ
      ||| 𝟘
      ZeroTy : Typ
      ||| 𝟙
      OneTy : Typ
      ||| El t  (every element of the universe is a type)
      El : Elem -> Typ
      ||| T(σ)  (context substitution applied to a type)
      SubstElim : Typ -> SubstContext -> Typ

  namespace Elem
    ||| Element
    ||| t ::= t(σ) | λ t | t t | t .π₁ | t .π₂ | t , t
    |||       | t → t | t ⨯ t | ℕ | 𝟘 | 𝟙 | t ≡ t ∈ t
    |||       | () | Z | S t | ℕ-elim T t t t | 𝟘-elim t
    |||       | ☐ᵢ | Refl | x
    public export
    data Elem : Type where
      ||| t(σ)  (context substitution)
      SubstElim : Elem -> SubstContext -> Elem
      ||| λ t  (pi introduction)
      PiIntro : Elem -> Elem
      ||| t t  (pi elimination / application)
      PiElim : Elem -> Elem -> Elem
      ||| t .π₁  (sigma elimination, first projection)
      SigmaElim1 : Elem -> Elem
      ||| t .π₂  (sigma elimination, second projection)
      SigmaElim2 : Elem -> Elem
      ||| t , t  (sigma introduction / pair)
      SigmaIntro : Elem -> Elem -> Elem
      ||| t → t  (universe element encoding Π)
      PiTy : Elem -> Elem -> Elem
      ||| t ⨯ t  (universe element encoding Σ)
      SigmaTy : Elem -> Elem -> Elem
      ||| ℕ  (universe element)
      NatTy : Elem
      ||| 𝟘  (universe element)
      ZeroTy : Elem
      ||| 𝟙  (universe element)
      OneTy : Elem
      ||| t ≡ t ∈ t  (universe element encoding equality)
      EqTy : Elem -> Elem -> Elem -> Elem
      ||| ()  (unit introduction)
      OneIntro : Elem
      ||| Z  (zero)
      NatIntro0 : Elem
      ||| S t  (successor)
      NatIntro1 : Elem -> Elem
      ||| ℕ-elim T z s t  (natural number elimination)
      NatElim : Typ -> Elem -> Elem -> Elem -> Elem
      ||| 𝟘-elim t  (empty type elimination)
      ZeroElim : Elem -> Elem
      ||| ☐ᵢ  (i-th de Bruijn context variable)
      CtxVar : Nat -> Elem
      ||| Refl  (reflexivity)
      Refl : Elem

||| Typing context: Γ ::= ε | Γ T
public export
Ctx : Type
Ctx = SnocList Typ

||| Type telescope: Δ ::= ε | T Δ
public export
Tel : Type
Tel = List Typ

||| Element list: ē ::= · | e ē
public export
ElemList : Type
ElemList = List Elem
