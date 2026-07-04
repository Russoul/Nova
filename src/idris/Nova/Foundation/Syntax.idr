module Nova.Foundation.Syntax

import Data.SnocList

mutual
  namespace Sub
    public export
    data Sub : Type where
      ||| ·  (unique substitution into the empty context)
      Terminal : Sub
      ||| σ, t  (substitution into an extended context)
      Ext : Sub -> Elem -> Sub
      ||| σ ∘ τ  (composition of substitutions)
      Chain : Sub -> Sub -> Sub
      ||| id  (identity substitution)
      Id : Sub
      ||| ↑  (weakening substitution)
      Wk : Sub

  namespace Ty
    public export
    data Ty : Type where
      ||| A(σ)  (context substitution applied to a type)
      SubstElim : Ty -> Sub -> Ty
      ||| 𝟘
      ZeroTy : Ty
      ||| 𝟙
      OneTy : Ty
      ||| ℕ
      NatTy : Ty
      ||| 𝕌
      UniverseTy : Ty
      ||| T → T  (dependent product type, Π)
      PiTy : Ty -> Ty -> Ty
      ||| T ⨯ T  (dependent sum type, Σ)
      SigmaTy : Ty -> Ty -> Ty
      ||| t ≡ t ∈ T  (extensional equality type)
      EqTy : Elem -> Elem -> Ty -> Ty
      ||| El t  (every element of the universe is a type)
      El : Elem -> Ty

  namespace Elem
    public export
    data Elem : Type where
      ||| t(σ)  (context substitution)
      SubstElim : Elem -> Sub -> Elem
      ||| ☐
      CtxVar : Elem
      ||| 𝟘-elim t (empty type elimination)
      ZeroElim : Elem -> Elem
      ||| ()  (unit introduction)
      OneIntro : Elem
      ||| Z  (zero)
      NatIntro0 : Elem
      ||| S t  (successor)
      NatIntro1 : Elem -> Elem
      ||| ℕ-elim z s t (natural number elimination)
      NatElim : Elem -> Elem -> Elem -> Elem
      ||| λ t (pi introduction)
      PiIntro : Elem -> Elem
      ||| t @
      PiElim : Elem -> Elem
      ||| t , t (sigma introduction / pair)
      SigmaIntro : Elem -> Elem -> Elem
      ||| t .π₁  (sigma elimination, first projection)
      SigmaElim1 : Elem -> Elem
      ||| t .π₂  (sigma elimination, second projection)
      SigmaElim2 : Elem -> Elem
      ||| 𝟘  (universe element)
      ZeroTy : Elem
      ||| 𝟙  (universe element)
      OneTy : Elem
      ||| ℕ  (universe element)
      NatTy : Elem
      ||| t → t  (universe element encoding Π)
      PiTy : Elem -> Elem -> Elem
      ||| t ⨯ t  (universe element encoding Σ)
      SigmaTy : Elem -> Elem -> Elem
      ||| t ≡ t ∈ t  (universe element encoding equality)
      EqTy : Elem -> Elem -> Elem -> Elem
      ||| Refl  (reflexivity)
      Refl : Elem

||| Tying context: Γ ::= ε | Γ ᐅ T
public export
Ctx : Type
Ctx = SnocList Ty

||| Tye telescope: Δ ::= ε | T ◁ Δ
public export
Tel : Type
Tel = List Ty

||| Spine: ē ::= · | e, ē
public export
Spine : Type
Spine = List Elem

||| σ⁺ ≜ σ∘↑, ☐
public export
under : Sub -> Sub
under sigma = Ext (Chain sigma Wk) CtxVar

mutual
  public export
  covering
  Eq Sub where

  public export
  covering
  Eq Ty where

  public export
  covering
  Eq Elem where

mutual
  public export
  covering
  Show Sub where
    show Terminal = "Terminal"
    show (Ext s e) = "Ext (\{show s}) (\{show e})"
    show (Chain s t) = "Chain (\{show s}) (\{show t})"
    show Id = "Id"
    show Wk = "Wk"

  public export
  covering
  Show Ty where
    show (SubstElim ty s) = "SubstElim (\{show ty}) (\{show s})"
    show ZeroTy = "ZeroTy"
    show OneTy = "OneTy"
    show NatTy = "NatTy"
    show UniverseTy = "UniverseTy"
    show (PiTy a b) = "PiTy (\{show a}) (\{show b})"
    show (SigmaTy a b) = "SigmaTy (\{show a}) (\{show b})"
    show (EqTy e0 e1 a) = "EqTy (\{show e0}) (\{show e1}) (\{show a})"
    show (El e) = "El (\{show e})"

  public export
  covering
  Show Elem where
    show (SubstElim e s) = "SubstElim (\{show e}) (\{show s})"
    show CtxVar = "CtxVar"
    show (ZeroElim e) = "ZeroElim (\{show e})"
    show OneIntro = "OneIntro"
    show NatIntro0 = "NatIntro0"
    show (NatIntro1 e) = "NatIntro1 (\{show e})"
    show (NatElim z s t) = "NatElim (\{show z}) (\{show s}) (\{show t})"
    show (PiIntro e) = "PiIntro (\{show e})"
    show (PiElim e) = "PiElim (\{show e})"
    show (SigmaIntro e1 e2) = "SigmaIntro (\{show e1}) (\{show e2})"
    show (SigmaElim1 e) = "SigmaElim1 (\{show e})"
    show (SigmaElim2 e) = "SigmaElim2 (\{show e})"
    show Elem.ZeroTy = "ZeroTy"
    show Elem.OneTy = "OneTy"
    show Elem.NatTy = "NatTy"
    show (Elem.PiTy e1 e2) = "PiTy (\{show e1}) (\{show e2})"
    show (Elem.SigmaTy e1 e2) = "SigmaTy (\{show e1}) (\{show e2})"
    show (Elem.EqTy e0 e1 e2) = "EqTy (\{show e0}) (\{show e1}) (\{show e2})"
    show Refl = "Refl"
