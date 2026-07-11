module Nova.Foundation.Elaboration.Syntax

import Data.SnocList

-- Proof-term surface syntax, as specified in docs/NovaSurfaceSyntax.txt.
-- Every constructor here corresponds to a named proof-term constructor
-- documented alongside a rule in docs/NovaFoundation.txt: elaborating a
-- value of one of these types should produce a derivation in the
-- low-level TypingRule language (Nova.Foundation.Derivation).
--
-- Naming mirrors docs/NovaSurfaceSyntax.txt's own nonterminal names:
--   Γ    -> Ctx         Γ⁼  -> CtxEq
--   T    -> Ty          T⁼  -> TyEq
--   σ    -> Sub
--   t˲   -> SubNorm     t˲⁼ -> SubNormEq
--   t    -> Elem        t⁼  -> ElemEq
-- These are distinct types from Nova.Foundation.Syntax's Ctx/Ty/Elem/Sub —
-- the ones here are proof terms (not yet checked), the ones there are the
-- checked object-language terms a proof term elaborates to.

public export
SigIdentifier : Type
SigIdentifier = String

mutual
  namespace Ctx
    ||| Γ ::= ε | Γ ᐅ T
    public export
    data Ctx : Type where
      ||| ε
      Empty : Ctx
      ||| Γ ᐅ T
      Ext : Ctx -> Ty -> Ctx

  namespace CtxEq
    ||| Γ⁼ ::= ε | refl | Γ⁼ ⁻¹ | Γ⁼ ᐅ T⁼ | Γ⁼ · Γ⁼ via Γ
    public export
    data CtxEq : Type where
      ||| ε
      Empty : CtxEq
      ||| refl
      Refl : CtxEq
      ||| Γ⁼ ⁻¹
      Sym : CtxEq -> CtxEq
      ||| Γ⁼ ᐅ T⁼
      Ext : CtxEq -> TyEq -> CtxEq
      ||| Γ⁼ · Γ⁼ via Γ
      Trans : CtxEq -> CtxEq -> Ctx -> CtxEq

  namespace Ty
    ||| T ::= 𝟘 | 𝟙 | ℕ | 𝕌
    |||     | (Γ ⊦ T)[σ]
    |||     | El t | coe-ctx T via (Γ, Γ⁼)
    |||     | T → T | T ⨯ T | T / T
    |||     | t ≡ t ∈ T
    public export
    data Ty : Type where
      ZeroTy : Ty
      OneTy : Ty
      NatTy : Ty
      UniverseTy : Ty
      ||| (Γ ⊦ T)[σ]
      Subst : Ctx -> Ty -> Sub -> Ty
      ||| El t
      El : Elem -> Ty
      ||| coe-ctx T via (Γ, Γ⁼)
      CoeCtx : Ty -> Ctx -> CtxEq -> Ty
      ||| T → T
      PiTy : Ty -> Ty -> Ty
      ||| T ⨯ T
      SigmaTy : Ty -> Ty -> Ty
      ||| T / T
      Quotient : Ty -> Ty -> Ty
      ||| t ≡ t ∈ T
      EqTy : Elem -> Elem -> Ty -> Ty

  namespace TyEq
    ||| T⁼ ::= 𝟘 | 𝟙 | ℕ | 𝕌 | refl
    |||      | T⁼ ⁻¹ | (Γ ⊦ T⁼ of T = T)[σ]
    |||      | El t⁼ | coe-ctx T⁼ via (Γ, Γ⁼) | 𝟘-elim t
    |||      | T⁼ → T⁼ | T⁼ ⨯ T⁼ | T⁼ / T⁼
    |||      | t⁼ ≡ t⁼ ∈ T⁼ | T⁼ · T⁼ via T
    public export
    data TyEq : Type where
      ZeroTy : TyEq
      OneTy : TyEq
      NatTy : TyEq
      UniverseTy : TyEq
      ||| refl
      Refl : TyEq
      ||| T⁼ ⁻¹
      Sym : TyEq -> TyEq
      ||| (Γ ⊦ T⁼ of T = T)[σ]
      Subst : Ctx -> TyEq -> Ty -> Ty -> Sub -> TyEq
      ||| El t⁼
      El : ElemEq -> TyEq
      ||| coe-ctx T⁼ via (Γ, Γ⁼)
      CoeCtx : TyEq -> Ctx -> CtxEq -> TyEq
      ||| 𝟘-elim t   (type equality from absurdity)
      ZeroElim : Elem -> TyEq
      ||| T⁼ → T⁼
      PiTy : TyEq -> TyEq -> TyEq
      ||| T⁼ ⨯ T⁼
      SigmaTy : TyEq -> TyEq -> TyEq
      ||| T⁼ / T⁼
      Quotient : TyEq -> TyEq -> TyEq
      ||| t⁼ ≡ t⁼ ∈ T⁼
      EqTy : ElemEq -> ElemEq -> TyEq -> TyEq
      ||| T⁼ · T⁼ via T
      Trans : TyEq -> TyEq -> Ty -> TyEq

  namespace Sub
    ||| σ ::= · | id | ↑ | σ ∘ σ via Γ | σ, t
    public export
    data Sub : Type where
      ||| ·
      Terminal : Sub
      ||| id
      Id : Sub
      ||| ↑
      Wk : Sub
      ||| σ ∘ σ via Γ
      Chain : Sub -> Sub -> Ctx -> Sub
      ||| σ, t
      Ext : Sub -> Elem -> Sub

  namespace SubNorm
    ||| t˲ ::= · | coe-dom t˲ via (Γ, Γ⁼) | coe-codom t˲ via (Γ, Γ⁼)
    |||       | t˲, t | t˲ ∘ σ via Γ
    public export
    data SubNorm : Type where
      ||| ·
      Terminal : SubNorm
      ||| coe-dom t˲ via (Γ, Γ⁼)
      CoeDom : SubNorm -> Ctx -> CtxEq -> SubNorm
      ||| coe-codom t˲ via (Γ, Γ⁼)
      CoeCodom : SubNorm -> Ctx -> CtxEq -> SubNorm
      ||| t˲, t
      Ext : SubNorm -> Elem -> SubNorm
      ||| t˲ ∘ σ via Γ
      Chain : SubNorm -> Sub -> Ctx -> SubNorm

  namespace SubNormEq
    ||| t˲⁼ ::= · | refl | t˲⁼ ⁻¹
    |||        | coe-dom t˲⁼ via (Γ, Γ⁼) | coe-codom t˲⁼ via (Γ, Γ⁼)
    |||        | t˲⁼, t⁼ | t˲⁼ ∘ σ via Γ | t˲⁼ · t˲⁼ via t˲
    public export
    data SubNormEq : Type where
      ||| ·
      Terminal : SubNormEq
      ||| refl
      Refl : SubNormEq
      ||| t˲⁼ ⁻¹
      Sym : SubNormEq -> SubNormEq
      ||| coe-dom t˲⁼ via (Γ, Γ⁼)
      CoeDom : SubNormEq -> Ctx -> CtxEq -> SubNormEq
      ||| coe-codom t˲⁼ via (Γ, Γ⁼)
      CoeCodom : SubNormEq -> Ctx -> CtxEq -> SubNormEq
      ||| t˲⁼, t⁼
      Ext : SubNormEq -> ElemEq -> SubNormEq
      ||| t˲⁼ ∘ σ via Γ
      Chain : SubNormEq -> Sub -> Ctx -> SubNormEq
      ||| t˲⁼ · t˲⁼ via t˲
      Trans : SubNormEq -> SubNormEq -> SubNorm -> SubNormEq

  namespace Elem
    ||| t ::= ☐ₙ | () | Z | Refl | 𝟘 | 𝟙 | ℕ | x
    |||     | (Γ ⊦ t)[σ]
    |||     | (t : T → T) t | (t : T ⨯ T) .π₁ | (t : T ⨯ T) .π₂
    |||     | λ t | 𝟘-elim t | S t
    |||     | ℕ-elim t t t motive T
    |||     | class t
    |||     | quote-elim (T / T) t t⁼ t motive T
    |||     | coe-ctx t via (Γ, Γ⁼) | coe-ty t via (T, T⁼)
    |||     | t → t | t ⨯ t | t ≡ t ∈ t
    |||     | t , t
    public export
    data Elem : Type where
      ||| ☐ₙ
      CtxVar : Nat -> Elem
      ||| ()
      OneIntro : Elem
      ||| Z
      NatIntro0 : Elem
      ||| Refl
      Refl : Elem
      ||| 𝟘  (universe code)
      ZeroTy : Elem
      ||| 𝟙  (universe code)
      OneTy : Elem
      ||| ℕ  (universe code)
      NatTy : Elem
      ||| x
      Var : SigIdentifier -> Elem
      ||| (Γ ⊦ t)[σ]
      Subst : Ctx -> Elem -> Sub -> Elem
      ||| (t : T → T) t
      App : Elem -> Ty -> Ty -> Elem -> Elem
      ||| (t : T ⨯ T) .π₁
      Proj1 : Elem -> Ty -> Ty -> Elem
      ||| (t : T ⨯ T) .π₂
      Proj2 : Elem -> Ty -> Ty -> Elem
      ||| λ t
      PiIntro : Elem -> Elem
      ||| 𝟘-elim t
      ZeroElim : Elem -> Elem
      ||| S t
      NatIntro1 : Elem -> Elem
      ||| ℕ-elim z s t motive T
      NatElim : Elem -> Elem -> Elem -> Ty -> Elem
      ||| class t
      Class : Elem -> Elem
      ||| quote-elim (A / R) f f⁼ q motive B
      ||| (f⁼ : A ᐅ f respects R, i.e. the ElemEq coherence witness)
      QuotElim : Ty -> Ty -> Elem -> ElemEq -> Elem -> Ty -> Elem
      ||| coe-ctx t via (Γ, Γ⁼)
      CoeCtx : Elem -> Ctx -> CtxEq -> Elem
      ||| coe-ty t via (T, T⁼)
      CoeTy : Elem -> Ty -> TyEq -> Elem
      ||| t → t  (universe code)
      PiTyCode : Elem -> Elem -> Elem
      ||| t ⨯ t  (universe code)
      SigmaTyCode : Elem -> Elem -> Elem
      ||| t ≡ t ∈ t  (universe code)
      EqTyCode : Elem -> Elem -> Elem -> Elem
      ||| t , t
      SigmaIntro : Elem -> Elem -> Elem

  namespace ElemEq
    ||| t⁼ ::= ☐ₙ | () | Z | 𝟘 | 𝟙 | ℕ | refl | x | x-β
    |||      | t⁼ ⁻¹ | (Γ ⊦ t⁼ of t = t : T)[σ]
    |||      | (t⁼ : T → T) t⁼ | (t⁼ : T ⨯ T) .π₁ | (t⁼ : T ⨯ T) .π₂
    |||      | S t⁼ | λ t⁼ | class t⁼ | class⁼ t | 𝟘-elim t
    |||      | ℕ-elim z⁼ s⁼ t⁼ motive T
    |||      | ℕ-elim-η z s f⁼ f₀⁼ f₁⁼ t motive t = t : T
    |||      | quote-elim (T / T) f⁼ resp₀ resp₁ q⁼ motive T
    |||      | reflect t | coe-ctx t⁼ via (Γ, Γ⁼) | coe-ty t⁼ via (T, T⁼)
    |||      | t⁼ → t⁼ | t⁼ ⨯ t⁼ | t⁼ ≡ t⁼ ∈ t⁼
    |||      | t⁼ , t⁼ | t⁼ · t⁼ via t
    public export
    data ElemEq : Type where
      ||| ☐ₙ
      CtxVar : Nat -> ElemEq
      ||| ()
      OneIntro : ElemEq
      ||| Z
      NatIntro0 : ElemEq
      ||| 𝟘  (universe code)
      ZeroTy : ElemEq
      ||| 𝟙  (universe code)
      OneTy : ElemEq
      ||| ℕ  (universe code)
      NatTy : ElemEq
      ||| refl
      Refl : ElemEq
      ||| x
      Var : SigIdentifier -> ElemEq
      ||| x-β
      Unfold : SigIdentifier -> ElemEq
      ||| t⁼ ⁻¹
      Sym : ElemEq -> ElemEq
      ||| (Γ ⊦ t⁼ of t = t : T)[σ]
      Subst : Ctx -> ElemEq -> Elem -> Elem -> Ty -> Sub -> ElemEq
      ||| (t⁼ : T → T) t⁼
      App : ElemEq -> Ty -> Ty -> ElemEq -> ElemEq
      ||| (t⁼ : T ⨯ T) .π₁
      Proj1 : ElemEq -> Ty -> Ty -> ElemEq
      ||| (t⁼ : T ⨯ T) .π₂
      Proj2 : ElemEq -> Ty -> Ty -> ElemEq
      ||| S t⁼
      NatIntro1 : ElemEq -> ElemEq
      ||| λ t⁼
      PiIntro : ElemEq -> ElemEq
      ||| class t⁼  (congruence)
      Class : ElemEq -> ElemEq
      ||| class⁼ t  (the R a b witness r)
      ClassEq : Elem -> ElemEq
      ||| 𝟘-elim t  (element congruence via absurdity)
      ZeroElim : Elem -> ElemEq
      ||| ℕ-elim z⁼ s⁼ t⁼ motive T
      NatElim : ElemEq -> ElemEq -> ElemEq -> Ty -> ElemEq
      ||| ℕ-elim-η z s f⁼ f₀⁼ f₁⁼ t motive f₀ = f₁ : T
      NatElimEta : Elem -> Elem -> ElemEq -> ElemEq -> ElemEq -> Elem -> Elem -> Elem -> Ty -> ElemEq
      ||| quote-elim (A / R) f⁼ resp₀ resp₁ q⁼ motive B
      QuotElim : Ty -> Ty -> ElemEq -> ElemEq -> ElemEq -> ElemEq -> Ty -> ElemEq
      ||| reflect t
      Reflect : Elem -> ElemEq
      ||| coe-ctx t⁼ via (Γ, Γ⁼)
      CoeCtx : ElemEq -> Ctx -> CtxEq -> ElemEq
      ||| coe-ty t⁼ via (T, T⁼)
      CoeTy : ElemEq -> Ty -> TyEq -> ElemEq
      ||| t⁼ → t⁼  (universe code congruence)
      PiTyCode : ElemEq -> ElemEq -> ElemEq
      ||| t⁼ ⨯ t⁼  (universe code congruence)
      SigmaTyCode : ElemEq -> ElemEq -> ElemEq
      ||| t⁼ ≡ t⁼ ∈ t⁼  (universe code congruence)
      EqTyCode : ElemEq -> ElemEq -> ElemEq -> ElemEq
      ||| t⁼ , t⁼
      SigmaIntro : ElemEq -> ElemEq -> ElemEq
      ||| t⁼ · t⁼ via t
      Trans : ElemEq -> ElemEq -> Elem -> ElemEq

||| A signature entry: Γ ⊦ x ≔ t : A  (a top-level reusable definition).
public export
data SigEntry : Type where
  MkSigEntry : Ctx -> SigIdentifier -> Elem -> Ty -> SigEntry

||| Σ ::= ε | Σ SigEntry  (a program: a snoclist of top-level definitions).
public export
Sig : Type
Sig = SnocList SigEntry

mutual
  public export
  covering
  Show Ctx where
    show Ctx.Empty = "Empty"
    show (Ctx.Ext g a) = "Ext (\{show g}) (\{show a})"

  public export
  covering
  Show CtxEq where
    show CtxEq.Empty = "Empty"
    show CtxEq.Refl = "Refl"
    show (CtxEq.Sym g) = "Sym (\{show g})"
    show (CtxEq.Ext g a) = "Ext (\{show g}) (\{show a})"
    show (CtxEq.Trans g0 g1 g) = "Trans (\{show g0}) (\{show g1}) (\{show g})"

  public export
  covering
  Show Ty where
    show Ty.ZeroTy = "ZeroTy"
    show Ty.OneTy = "OneTy"
    show Ty.NatTy = "NatTy"
    show Ty.UniverseTy = "UniverseTy"
    show (Ty.Subst g a s) = "Subst (\{show g}) (\{show a}) (\{show s})"
    show (Ty.El e) = "El (\{show e})"
    show (Ty.CoeCtx a g geq) = "CoeCtx (\{show a}) (\{show g}) (\{show geq})"
    show (Ty.PiTy a b) = "PiTy (\{show a}) (\{show b})"
    show (Ty.SigmaTy a b) = "SigmaTy (\{show a}) (\{show b})"
    show (Ty.Quotient a r) = "Quotient (\{show a}) (\{show r})"
    show (Ty.EqTy a b t) = "EqTy (\{show a}) (\{show b}) (\{show t})"

  public export
  covering
  Show TyEq where
    show TyEq.ZeroTy = "ZeroTy"
    show TyEq.OneTy = "OneTy"
    show TyEq.NatTy = "NatTy"
    show TyEq.UniverseTy = "UniverseTy"
    show TyEq.Refl = "Refl"
    show (TyEq.Sym a) = "Sym (\{show a})"
    show (TyEq.Subst g a t0 t1 s) = "Subst (\{show g}) (\{show a}) (\{show t0}) (\{show t1}) (\{show s})"
    show (TyEq.El e) = "El (\{show e})"
    show (TyEq.CoeCtx a g geq) = "CoeCtx (\{show a}) (\{show g}) (\{show geq})"
    show (TyEq.ZeroElim e) = "ZeroElim (\{show e})"
    show (TyEq.PiTy a b) = "PiTy (\{show a}) (\{show b})"
    show (TyEq.SigmaTy a b) = "SigmaTy (\{show a}) (\{show b})"
    show (TyEq.Quotient a r) = "Quotient (\{show a}) (\{show r})"
    show (TyEq.EqTy a b t) = "EqTy (\{show a}) (\{show b}) (\{show t})"
    show (TyEq.Trans a0 a1 a) = "Trans (\{show a0}) (\{show a1}) (\{show a})"

  public export
  covering
  Show Sub where
    show Sub.Terminal = "Terminal"
    show Sub.Id = "Id"
    show Sub.Wk = "Wk"
    show (Sub.Chain s t g) = "Chain (\{show s}) (\{show t}) (\{show g})"
    show (Sub.Ext s e) = "Ext (\{show s}) (\{show e})"

  public export
  covering
  Show SubNorm where
    show SubNorm.Terminal = "Terminal"
    show (SubNorm.CoeDom s g geq) = "CoeDom (\{show s}) (\{show g}) (\{show geq})"
    show (SubNorm.CoeCodom s g geq) = "CoeCodom (\{show s}) (\{show g}) (\{show geq})"
    show (SubNorm.Ext s e) = "Ext (\{show s}) (\{show e})"
    show (SubNorm.Chain s t g) = "Chain (\{show s}) (\{show t}) (\{show g})"

  public export
  covering
  Show SubNormEq where
    show SubNormEq.Terminal = "Terminal"
    show SubNormEq.Refl = "Refl"
    show (SubNormEq.Sym s) = "Sym (\{show s})"
    show (SubNormEq.CoeDom s g geq) = "CoeDom (\{show s}) (\{show g}) (\{show geq})"
    show (SubNormEq.CoeCodom s g geq) = "CoeCodom (\{show s}) (\{show g}) (\{show geq})"
    show (SubNormEq.Ext s e) = "Ext (\{show s}) (\{show e})"
    show (SubNormEq.Chain s t g) = "Chain (\{show s}) (\{show t}) (\{show g})"
    show (SubNormEq.Trans s0 s1 s) = "Trans (\{show s0}) (\{show s1}) (\{show s})"

  public export
  covering
  Show Elem where
    show (Elem.CtxVar n) = "CtxVar \{show n}"
    show Elem.OneIntro = "OneIntro"
    show Elem.NatIntro0 = "NatIntro0"
    show Elem.Refl = "Refl"
    show Elem.ZeroTy = "ZeroTy"
    show Elem.OneTy = "OneTy"
    show Elem.NatTy = "NatTy"
    show (Elem.Var x) = "Var \{show x}"
    show (Elem.Subst g e s) = "Subst (\{show g}) (\{show e}) (\{show s})"
    show (Elem.App f a b e) = "App (\{show f}) (\{show a}) (\{show b}) (\{show e})"
    show (Elem.Proj1 e a b) = "Proj1 (\{show e}) (\{show a}) (\{show b})"
    show (Elem.Proj2 e a b) = "Proj2 (\{show e}) (\{show a}) (\{show b})"
    show (Elem.PiIntro e) = "PiIntro (\{show e})"
    show (Elem.ZeroElim e) = "ZeroElim (\{show e})"
    show (Elem.NatIntro1 e) = "NatIntro1 (\{show e})"
    show (Elem.NatElim z s t a) = "NatElim (\{show z}) (\{show s}) (\{show t}) (\{show a})"
    show (Elem.Class a) = "Class (\{show a})"
    show (Elem.QuotElim a r f fEq q b) = "QuotElim (\{show a}) (\{show r}) (\{show f}) (\{show fEq}) (\{show q}) (\{show b})"
    show (Elem.CoeCtx e g geq) = "CoeCtx (\{show e}) (\{show g}) (\{show geq})"
    show (Elem.CoeTy e a aeq) = "CoeTy (\{show e}) (\{show a}) (\{show aeq})"
    show (Elem.PiTyCode a b) = "PiTyCode (\{show a}) (\{show b})"
    show (Elem.SigmaTyCode a b) = "SigmaTyCode (\{show a}) (\{show b})"
    show (Elem.EqTyCode a b t) = "EqTyCode (\{show a}) (\{show b}) (\{show t})"
    show (Elem.SigmaIntro a b) = "SigmaIntro (\{show a}) (\{show b})"

  public export
  covering
  Show ElemEq where
    show (ElemEq.CtxVar n) = "CtxVar \{show n}"
    show ElemEq.OneIntro = "OneIntro"
    show ElemEq.NatIntro0 = "NatIntro0"
    show ElemEq.ZeroTy = "ZeroTy"
    show ElemEq.OneTy = "OneTy"
    show ElemEq.NatTy = "NatTy"
    show ElemEq.Refl = "Refl"
    show (ElemEq.Var x) = "Var \{show x}"
    show (ElemEq.Unfold x) = "Unfold \{show x}"
    show (ElemEq.Sym e) = "Sym (\{show e})"
    show (ElemEq.Subst g e t0 t1 a s) = "Subst (\{show g}) (\{show e}) (\{show t0}) (\{show t1}) (\{show a}) (\{show s})"
    show (ElemEq.App f a b e) = "App (\{show f}) (\{show a}) (\{show b}) (\{show e})"
    show (ElemEq.Proj1 e a b) = "Proj1 (\{show e}) (\{show a}) (\{show b})"
    show (ElemEq.Proj2 e a b) = "Proj2 (\{show e}) (\{show a}) (\{show b})"
    show (ElemEq.NatIntro1 e) = "NatIntro1 (\{show e})"
    show (ElemEq.PiIntro e) = "PiIntro (\{show e})"
    show (ElemEq.Class a) = "Class (\{show a})"
    show (ElemEq.ClassEq r) = "ClassEq (\{show r})"
    show (ElemEq.ZeroElim e) = "ZeroElim (\{show e})"
    show (ElemEq.NatElim z s t a) = "NatElim (\{show z}) (\{show s}) (\{show t}) (\{show a})"
    show (ElemEq.NatElimEta z s fEq f0Eq f1Eq t f0 f1 a) =
      "NatElimEta (\{show z}) (\{show s}) (\{show fEq}) (\{show f0Eq}) (\{show f1Eq}) (\{show t}) (\{show f0}) (\{show f1}) (\{show a})"
    show (ElemEq.QuotElim a r fEq resp0 resp1 qEq b) =
      "QuotElim (\{show a}) (\{show r}) (\{show fEq}) (\{show resp0}) (\{show resp1}) (\{show qEq}) (\{show b})"
    show (ElemEq.Reflect e) = "Reflect (\{show e})"
    show (ElemEq.CoeCtx e g geq) = "CoeCtx (\{show e}) (\{show g}) (\{show geq})"
    show (ElemEq.CoeTy e a aeq) = "CoeTy (\{show e}) (\{show a}) (\{show aeq})"
    show (ElemEq.PiTyCode a b) = "PiTyCode (\{show a}) (\{show b})"
    show (ElemEq.SigmaTyCode a b) = "SigmaTyCode (\{show a}) (\{show b})"
    show (ElemEq.EqTyCode a b t) = "EqTyCode (\{show a}) (\{show b}) (\{show t})"
    show (ElemEq.SigmaIntro a b) = "SigmaIntro (\{show a}) (\{show b})"
    show (ElemEq.Trans a0 a1 a) = "Trans (\{show a0}) (\{show a1}) (\{show a})"

public export
covering
Show SigEntry where
  show (MkSigEntry g x t a) = "MkSigEntry (\{show g}) \{show x} (\{show t}) (\{show a})"

public export
covering
showSig : Sig -> String
showSig [<] = "[<]"
showSig sx = "[< " ++ go sx ++ "]"
  where
    covering
    go : Sig -> String
    go [<] = ""
    go (rest :< e) = case rest of
      [<] => show e
      _   => go rest ++ ", " ++ show e
