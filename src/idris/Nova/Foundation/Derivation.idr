module Nova.Foundation.Derivation

import Data.Either
import Data.List
import Data.SnocList
import Nova.Foundation.Syntax
import Nova.Foundation.Subst
import Nova.Foundation.Beta

import Data.SortedSet

%default covering

||| Γ ctx
public export
CtxWf : Type
CtxWf = Ctx

||| Γ₀ ≐ Γ₁ ctx
public export
CtxEq : Type
CtxEq = (Ctx, Ctx)

||| Γ ⊦ A type
public export
TyWf : Type
TyWf = (Ctx, Ty)

||| Γ ⊦ A₀ ≐ A₁ type
public export
TyEq : Type
TyEq = (Ctx, Ty, Ty)

||| σ : Γ ⇒ Δ
public export
SubWf : Type
SubWf = (Sub, Ctx, Ctx)

||| σ₀ ≐ σ₁ : Γ ⇒ Δ
public export
SubEq : Type
SubEq = (Sub, Sub, Ctx, Ctx)

||| e˲ : Γ ⇒ Δ norm
public export
SubNormWf : Type
SubNormWf = (SubNorm, Ctx, Ctx)

||| e˲₀ ≐ e˲₁ : Γ ⇒ Δ norm
public export
SubNormEq : Type
SubNormEq = (SubNorm, SubNorm, Ctx, Ctx)

||| Γ ⊦ a : A
public export
ElemWf : Type
ElemWf = (Ctx, Elem, Ty)

||| Γ ⊦ a₀ ≐ a₁ : A
public export
ElemEq : Type
ElemEq = (Ctx, Elem, Elem, Ty)

||| Γ ⊦ Δ tel
public export
TelWf : Type
TelWf = (Ctx, Tel)

||| Γ ⊦ Δ₀ ≐ Δ₁ tel
public export
TelEq : Type
TelEq = (Ctx, Tel, Tel)

||| Γ ⊦ ē : Δ
public export
SpineWf : Type
SpineWf = (Ctx, Spine, Tel)

||| Γ ⊦ ē₀ ≐ ē₁ : Δ
public export
SpineEq : Type
SpineEq = (Ctx, Spine, Spine, Tel)

public export
data JudgementForm = JfCtxWf CtxWf
                   | JfCtxEq CtxEq
                   | JfSubWf SubWf
                   | JfSubEq SubEq
                   | JfSubNormWf SubNormWf
                   | JfSubNormEq SubNormEq
                   | JfTyWf TyWf
                   | JfTyEq TyEq
                   | JfElemWf ElemWf
                   | JfElemEq ElemEq
                   | JfTelWf TelWf
                   | JfTelEq TelEq
                   | JfSpineWf SpineWf
                   | JfSpineEq SpineEq

||| Private!
|||
||| Every fact is stored twice: raw (exactly as the rule concluded it) and
||| beta-normalized (Beta.idr). Both stores are legitimate: a conclusion is
||| derivable by construction, and normalizing a *derivable* judgement is
||| licensed by subject reduction. Normalization is never applied to
||| unvalidated input — see the derivability checks below.
export
record Truth where
  constructor MkTruth
  sig : Sig
  ctxWfRaw : SortedSet CtxWf
  ctxWfNorm : SortedSet CtxWf
  ctxEqRaw : SortedSet CtxEq
  ctxEqNorm : SortedSet CtxEq
  tyWfRaw : SortedSet TyWf
  tyWfNorm : SortedSet TyWf
  tyEqRaw : SortedSet TyEq
  tyEqNorm : SortedSet TyEq
  subWfRaw : SortedSet SubWf
  subWfNorm : SortedSet SubWf
  subEqRaw : SortedSet SubEq
  subEqNorm : SortedSet SubEq
  subNormWfRaw : SortedSet SubNormWf
  subNormWfNorm : SortedSet SubNormWf
  subNormEqRaw : SortedSet SubNormEq
  subNormEqNorm : SortedSet SubNormEq
  elemWfRaw : SortedSet ElemWf
  elemWfNorm : SortedSet ElemWf
  elemEqRaw : SortedSet ElemEq
  elemEqNorm : SortedSet ElemEq
  telWfRaw : SortedSet TelWf
  telWfNorm : SortedSet TelWf
  telEqRaw : SortedSet TelEq
  telEqNorm : SortedSet TelEq
  spineWfRaw : SortedSet SpineWf
  spineWfNorm : SortedSet SpineWf
  spineEqRaw : SortedSet SpineEq
  spineEqNorm : SortedSet SpineEq

export
trivial : Truth
trivial = MkTruth [<]
  empty empty empty empty empty empty empty empty empty empty empty empty empty empty
  empty empty empty empty empty empty empty empty empty empty empty empty empty empty


public export
data TypingRule : Type where
  ||| ε ctx
  CtxWfEmpty : TypingRule
  ||| Γ ᐅ A ctx
  CtxWfExt : Ctx -> Ty -> TypingRule
  ||| Γ ⊦ 𝟘 type
  TyWfZero : Ctx -> TypingRule
  ||| Γ ⊦ 𝟙 type
  TyWfOne : Ctx -> TypingRule
  ||| Γ ⊦ ℕ type
  TyWfNat : Ctx -> TypingRule
  ||| Γ ⊦ 𝕌 type
  TyWfUniverse : Ctx -> TypingRule
  ||| Γ ⊦ A → B type
  TyWfPi : Ctx -> Ty -> Ty -> TypingRule
  ||| Γ ⊦ A ⨯ B type
  TyWfSigma : Ctx -> Ty -> Ty -> TypingRule
  ||| Γ ⊦ t ≡ t ∈ T type
  TyWfEq : Ctx -> Elem -> Elem -> Ty -> TypingRule
  ||| Γ ⊦ El t type
  TyWfEl : Ctx -> Elem -> TypingRule
  ||| Γ ⊦ A type
  ||| Γ ᐅ A ᐅ A[↑] ⊦ R type
  ||| ================
  ||| Γ ⊦ A / R type
  TyWfQuotient : Ctx -> Ty -> Ty -> TypingRule
  ||| Γ₁ ⊦ A type
  ||| σ : Γ₀ ⇒ Γ₁
  ||| ----------------
  ||| Γ₀ ⊦ A[σ] type
  TyWfSubst : Ctx -> Ctx -> Sub -> Ty -> TypingRule
  ||| (Γ ⊦ x ≔ A type) ∈ Σ
  ||| e˲ : Δ ⇒ Γ norm
  ||| -------------------
  ||| Σ Δ ⊦ x[e˲] type
  TyWfSigVar : Ctx -> SubNorm -> SigIdentifier -> TypingRule
  ||| Γ ⊦ ☐ₙ : Γ‖ₙ
  ElemWfVar : Ctx -> Nat -> TypingRule
  ||| Γ ⊦ 𝟘-elim t : A
  ElemWfZeroElim : Ctx -> Elem -> Ty -> TypingRule
  ||| Γ ⊦ ()
  ElemWfOneIntro : Ctx -> TypingRule
  ||| Γ ⊦ Z
  ElemWfZeroIntro : Ctx -> TypingRule
  ||| Γ ⊦ S t
  ElemWfSucIntro : Ctx -> Elem -> TypingRule
  ||| Γ ⊦ ℕ-elim t t t : T
  ElemWfNatElim : Ctx -> Elem -> Elem -> Elem -> Ty -> TypingRule
  ||| Γ ⊦ A type
  ||| Γ ᐅ A ᐅ A[↑] ⊦ R type
  ||| -----------------------
  ||| Γ ⊦ a : A
  ||| =======================
  ||| Γ ⊦ class a : A / R
  ElemWfClass : Ctx -> Elem -> Ty -> Ty -> TypingRule
  ||| Γ ⊦ A type
  ||| Γ ᐅ A ᐅ A[↑] ⊦ R type
  ||| Γ ᐅ (A / R) ⊦ B type
  ||| ---------------------------------------------------------------------
  ||| Γ ᐅ A ⊦ f : B[↑, class ☐₀]
  ||| Γ ᐅ A ᐅ A[↑] ᐅ R ⊦ f[↑∘↑∘↑, ☐₂] ≐ f[↑∘↑∘↑, ☐₁] : B[↑∘↑∘↑, class ☐₂]
  ||| Γ ⊦ q : A / R
  ||| =======================================================================
  ||| Γ ⊦ quot-elim f q : B[id, q]
  ElemWfQuotElim : Ctx -> Ty -> Ty -> Ty -> Elem -> Elem -> TypingRule
  ||| Γ₁ ⊦ t : A
  ||| σ : Γ₀ ⇒ Γ₁
  ||| ----------------
  ||| Γ₀ ⊦ t[σ] : A[σ]
  ElemWfSubst : Ctx -> Ctx -> Sub -> Elem -> Ty -> TypingRule
  ||| Γ ⊦ λ t : T → T
  ElemWfPiIntro : Ctx -> Elem -> Ty -> Ty -> TypingRule
  ||| Γ ⊦ (f : A -> B) e
  ElemWfPiApp : Ctx -> Elem -> Ty -> Ty -> Elem -> TypingRule
  ||| Γ ⊦ f e — like ElemWfPiApp, but f's Π-type is looked up in the
  ||| derived-facts table instead of restated: for every stored
  ||| (weakening-visible) fact Γ ⊦ f : A → B whose domain accepts e, the
  ||| conclusion Γ ⊦ f e : B[id, e] is derived. If no Π-typed fact for f
  ||| exists yet and f is itself an application, f is inferred first
  ||| recursively — one rule can check a whole application spine.
  ElemWfPiAppInfer : Ctx -> Elem -> Elem -> TypingRule
  ||| Γ ⊦ t , t : T ⨯ T
  ElemWfSigmaIntro : Ctx -> Elem -> Elem -> Ty -> Ty -> TypingRule
  ||| Γ ⊦ (t : T ⨯ T) .π₁
  ElemWfSigmaElim1 : Ctx -> Elem -> Ty -> Ty -> TypingRule
  ||| Γ ⊦ (t : T ⨯ T) .π₂
  ElemWfSigmaElim2 : Ctx -> Elem -> Ty -> Ty -> TypingRule
  ||| Γ ⊦ 𝟘
  ElemWfZeroTy : Ctx -> TypingRule
  ||| Γ ⊦ 𝟙
  ElemWfOneTy : Ctx -> TypingRule
  ||| Γ ⊦ ℕ
  ElemWfNatTy : Ctx -> TypingRule
  ||| Γ ⊦ t → t
  ElemWfPiTy : Ctx -> Elem -> Elem -> TypingRule
  ||| Γ ⊦ t ⨯ t
  ElemWfSigmaTy : Ctx -> Elem -> Elem -> TypingRule
  ||| Γ ⊦ t ≡ t ∈ t
  ElemWfEqTy : Ctx -> Elem -> Elem -> Elem -> TypingRule
  ||| Γ ⊦ Refl : (a ≡ a : A)
  ElemWfRefl : Ctx -> Elem -> Ty -> TypingRule
  ||| Γ ⊦ a : A₀
  ||| Γ ⊦ A₀ ≐ A₁ type
  ||| ---------------- (Γ ⊦ a : A₀ ≐ A₁)
  ||| Γ ⊦ a : A₁
  ElemWfTyCoe : Ctx -> Elem -> Ty -> Ty -> TypingRule
  ||| Γ₀ ⊦ a : A₀
  ||| Γ₀ ≐ Γ₁ ctx
  ||| ---------------- (Γ₀ ≐ Γ₁ ⊦ a : A)
  ||| Γ₁ ⊦ a : A
  ElemWfCtxCoe : Ctx -> Ctx -> Elem -> Ty -> TypingRule
  ||| (Γ ⊦ x ≔ a : A) ∈ Σ
  ||| σ : Δ ⇒ Γ norm
  ||| -------------------
  ||| Σ Δ ⊦ x[σ] : A[σ]
  ElemWfSigVar : Ctx -> SubNorm -> SigIdentifier -> TypingRule
  -- Context equality
  CtxEqRefl  : Ctx -> TypingRule
  CtxEqSym   : Ctx -> Ctx -> TypingRule
  CtxEqTrans : Ctx -> Ctx -> Ctx -> TypingRule
  -- Substitution well-formedness
  ||| · : Γ ⇒ ε
  SubWfTerminal : Ctx -> TypingRule
  ||| (σ, e) : Γ ⇒ (Δ ᐅ A)  given σ : Γ ⇒ Δ
  SubWfExt : Sub -> Elem -> Ctx -> Ctx -> Ty -> TypingRule
  -- Substitution equality
  SubEqRefl  : Sub -> Ctx -> Ctx -> TypingRule
  SubEqSym   : Sub -> Sub -> Ctx -> Ctx -> TypingRule
  SubEqTrans : Sub -> Sub -> Sub -> Ctx -> Ctx -> TypingRule
  -- Normal substitution well-formedness
  ||| · : Γ ⇒ ε norm
  SubNormWfTerminal : Ctx -> TypingRule
  ||| (e˲, t) : Γ₀ ⇒ (Γ₁ ᐅ A) norm  given e˲ : Γ₀ ⇒ Γ₁ norm
  SubNormWfExt : SubNorm -> Elem -> Ctx -> Ctx -> Ty -> TypingRule
  -- Normal substitution equality
  SubNormEqRefl  : SubNorm -> Ctx -> Ctx -> TypingRule
  SubNormEqSym   : SubNorm -> SubNorm -> Ctx -> Ctx -> TypingRule
  SubNormEqTrans : SubNorm -> SubNorm -> SubNorm -> Ctx -> Ctx -> TypingRule
  ||| e˲₀, t₀ ≐ e˲₁, t₁ : Γ₀ ⇒ (Γ₁ ᐅ A) norm  given e˲₀ ≐ e˲₁ : Γ₀ ⇒ Γ₁ norm
  SubNormEqExt : SubNorm -> SubNorm -> Elem -> Elem -> Ctx -> Ctx -> Ty -> TypingRule
  -- Type equality
  TyEqRefl  : Ctx -> Ty -> TypingRule
  TyEqSym   : Ctx -> Ty -> Ty -> TypingRule
  TyEqTrans : Ctx -> Ty -> Ty -> Ty -> TypingRule
  ||| Γ ⊦ T₀ ≐ T₁ type
  ||| Γ ⊦ a₀ ≐ a₁ : T₁
  ||| Γ ⊦ b₀ ≐ b₁ : T₁
  ||| ========================================
  ||| Γ ⊦ (a₀ ≡ b₀ ∈ T₀) ≐ (a₁ ≡ b₁ ∈ T₁) type
  TyEqCongEqTy : Ctx -> Elem -> Elem -> Ty -> Elem -> Elem -> Ty -> TypingRule
  ||| Γ ⊦ t₀ ≐ t₁ : 𝕌
  ||| ===================
  ||| Γ ⊦ El t₀ ≐ El t₁ type
  TyEqCongEl : Ctx -> Elem -> Elem -> TypingRule
  ||| Γ₁ ⊦ A₀ ≐ A₁ type
  ||| σ₀ ≐ σ₁ : Γ₀ ⇒ Γ₁
  ||| -----------------------
  ||| Γ₀ ⊦ A₀[σ₀] ≐ A₁[σ₁] type
  TyEqSubst : Ctx -> Ctx -> Sub -> Sub -> Ty -> Ty -> TypingRule
  -- Element equality
  ElemEqRefl  : Ctx -> Elem -> Ty -> TypingRule
  ElemEqSym   : Ctx -> Elem -> Elem -> Ty -> TypingRule
  ElemEqTrans : Ctx -> Elem -> Elem -> Elem -> Ty -> TypingRule
  ||| Γ ⊦ a : (a₀ ≡ a₁ ∈ A)
  ||| -------------------------
  ||| Γ ⊦ a₀ ≐ a₁ : A
  ElemEqReflection : Ctx -> Elem -> Elem -> Elem -> Ty -> TypingRule
  ||| Γ ⊦ t₀ ≐ t₁ : ℕ
  ||| ===================
  ||| Γ ⊦ S t₀ ≐ S t₁ : ℕ
  ElemEqCongSuc : Ctx -> Elem -> Elem -> TypingRule
  ||| Γ ⊦ f₀ ≐ f₁ : A → B
  ||| Γ ⊦ a₀ ≐ a₁ : A
  ||| ==========================
  ||| Γ ⊦ f₀ a₀ ≐ f₁ a₁ : B[a₁]
  ElemEqCongPiApp : Ctx -> Elem -> Elem -> Ty -> Ty -> Elem -> Elem -> TypingRule
  ||| Γ ⊦ A type
  ||| Γ ᐅ A ᐅ A[↑] ⊦ R type
  ||| -----------------------
  ||| Γ ⊦ a : A
  ||| Γ ⊦ b : A
  ||| Γ ⊦ r : R[id, a, b]
  ||| -----------------------------------
  ||| Γ ⊦ class a ≐ class b : A / R
  ElemEqQuotient : Ctx -> Ty -> Ty -> Elem -> Elem -> Elem -> TypingRule
  ||| Γ ⊦ A type
  ||| Γ ᐅ A ᐅ A[↑] ⊦ R type
  ||| --------------------
  ||| Γ ⊦ a₀ ≐ a₁ : A
  ||| ====================
  ||| Γ ⊦ class a₀ ≐ class a₁ : A / R
  ElemEqCongClass : Ctx -> Ty -> Ty -> Elem -> Elem -> TypingRule
  ||| Γ₁ ⊦ A type
  ||| Γ₁ ⊦ t₀ ≐ t₁ : A
  ||| σ₀ ≐ σ₁ : Γ₀ ⇒ Γ₁
  ||| -------------------------
  ||| Γ₀ ⊦ t₀[σ₀] ≐ t₁[σ₁] : A[σ₁]
  ElemEqSubst : Ctx -> Ctx -> Sub -> Sub -> Elem -> Elem -> Ty -> TypingRule
  ||| Γ ⊦ a ≐ b : A₀
  ||| Γ ⊦ A₀ ≐ A₁ type
  ||| -----------------
  ||| Γ ⊦ a ≐ b : A₁
  ElemEqTyCoe : Ctx -> Elem -> Elem -> Ty -> Ty -> TypingRule
  ||| Σ sig, Σ ⊦ Γ ctx, Σ Γ ⊦ A type, Σ Γ ⊦ a : A, x ∉ Σ
  ||| -------------------------------------------------------
  ||| Σ (Γ ⊦ x ≔ a : A) sig
  SigExt : Ctx -> SigIdentifier -> Elem -> Ty -> TypingRule
  ||| Σ sig, Σ ⊦ Γ ctx, Σ Γ ⊦ A type, x ∉ Σ
  ||| --------------------------------------
  ||| Σ (Γ ⊦ x ≔ A type) sig
  SigExtTy : Ctx -> SigIdentifier -> Ty -> TypingRule
  -- Telescope equality
  TelEqRefl  : Ctx -> Tel -> TypingRule
  TelEqSym   : Ctx -> Tel -> Tel -> TypingRule
  TelEqTrans : Ctx -> Tel -> Tel -> Tel -> TypingRule
  -- Spine equality
  SpineEqRefl  : Ctx -> Spine -> Tel -> TypingRule
  SpineEqSym   : Ctx -> Spine -> Spine -> Tel -> TypingRule
  SpineEqTrans : Ctx -> Spine -> Spine -> Spine -> Tel -> TypingRule

covering
showCtxRep : Ctx -> String
showCtxRep [<] = "[<]"
showCtxRep (rest :< ty) = "(\{showCtxRep rest} :< \{show ty})"

export covering
Show TypingRule where
  show CtxWfEmpty                    = "CtxWfEmpty"
  show (CtxWfExt g ty)               = "CtxWfExt (\{showCtxRep g}) (\{show ty})"
  show (TyWfZero ctx)                = "TyWfZero (\{showCtxRep ctx})"
  show (TyWfOne ctx)                 = "TyWfOne (\{showCtxRep ctx})"
  show (TyWfNat ctx)                 = "TyWfNat (\{showCtxRep ctx})"
  show (TyWfUniverse ctx)            = "TyWfUniverse (\{showCtxRep ctx})"
  show (TyWfPi ctx a b)              = "TyWfPi (\{showCtxRep ctx}) (\{show a}) (\{show b})"
  show (TyWfSigma ctx a b)           = "TyWfSigma (\{showCtxRep ctx}) (\{show a}) (\{show b})"
  show (TyWfEq ctx l r ty)           = "TyWfEq (\{showCtxRep ctx}) (\{show l}) (\{show r}) (\{show ty})"
  show (TyWfEl ctx e)                = "TyWfEl (\{showCtxRep ctx}) (\{show e})"
  show (TyWfQuotient ctx a r)        = "TyWfQuotient (\{showCtxRep ctx}) (\{show a}) (\{show r})"
  show (TyWfSubst gamma0 gamma1 sigma a) = "TyWfSubst (\{showCtxRep gamma0}) (\{showCtxRep gamma1}) (\{show sigma}) (\{show a})"
  show (TyWfSigVar ctx sigma x)      = "TyWfSigVar (\{showCtxRep ctx}) (\{show sigma}) \{show x}"
  show (ElemWfVar g n)               = "ElemWfVar (\{showCtxRep g}) (\{show n})"
  show (ElemWfZeroElim ctx e ty)     = "ElemWfZeroElim (\{showCtxRep ctx}) (\{show e}) (\{show ty})"
  show (ElemWfOneIntro ctx)          = "ElemWfOneIntro (\{showCtxRep ctx})"
  show (ElemWfZeroIntro ctx)         = "ElemWfZeroIntro (\{showCtxRep ctx})"
  show (ElemWfSucIntro ctx e)        = "ElemWfSucIntro (\{showCtxRep ctx}) (\{show e})"
  show (ElemWfNatElim ctx z s t ty)  = "ElemWfNatElim (\{showCtxRep ctx}) (\{show z}) (\{show s}) (\{show t}) (\{show ty})"
  show (ElemWfClass ctx a ty r)      = "ElemWfClass (\{showCtxRep ctx}) (\{show a}) (\{show ty}) (\{show r})"
  show (ElemWfQuotElim ctx ty r motive f q) = "ElemWfQuotElim (\{showCtxRep ctx}) (\{show ty}) (\{show r}) (\{show motive}) (\{show f}) (\{show q})"
  show (ElemWfSubst gamma0 gamma1 sigma t a) = "ElemWfSubst (\{showCtxRep gamma0}) (\{showCtxRep gamma1}) (\{show sigma}) (\{show t}) (\{show a})"
  show (ElemWfPiIntro ctx f a b)     = "ElemWfPiIntro (\{showCtxRep ctx}) (\{show f}) (\{show a}) (\{show b})"
  show (ElemWfPiApp g a f e b)       = "ElemWfPiApp (\{showCtxRep g}) (\{show a}) (\{show f}) (\{show e}) (\{show b})"
  show (ElemWfPiAppInfer g f e)      = "ElemWfPiAppInfer (\{showCtxRep g}) (\{show f}) (\{show e})"
  show (ElemWfSigmaIntro ctx u v a b) = "ElemWfSigmaIntro (\{showCtxRep ctx}) (\{show u}) (\{show v}) (\{show a}) (\{show b})"
  show (ElemWfSigmaElim1 ctx e a b)  = "ElemWfSigmaElim1 (\{showCtxRep ctx}) (\{show e}) (\{show a}) (\{show b})"
  show (ElemWfSigmaElim2 ctx e a b)  = "ElemWfSigmaElim2 (\{showCtxRep ctx}) (\{show e}) (\{show a}) (\{show b})"
  show (ElemWfZeroTy ctx)            = "ElemWfZeroTy (\{showCtxRep ctx})"
  show (ElemWfOneTy ctx)             = "ElemWfOneTy (\{showCtxRep ctx})"
  show (ElemWfNatTy ctx)             = "ElemWfNatTy (\{showCtxRep ctx})"
  show (ElemWfPiTy ctx a b)          = "ElemWfPiTy (\{showCtxRep ctx}) (\{show a}) (\{show b})"
  show (ElemWfSigmaTy ctx a b)       = "ElemWfSigmaTy (\{showCtxRep ctx}) (\{show a}) (\{show b})"
  show (ElemWfEqTy ctx l r ty)       = "ElemWfEqTy (\{showCtxRep ctx}) (\{show l}) (\{show r}) (\{show ty})"
  show (ElemWfRefl ctx e ty)         = "ElemWfRefl (\{showCtxRep ctx}) (\{show e}) (\{show ty})"
  show (ElemWfTyCoe ctx e ty0 ty1)   = "ElemWfTyCoe (\{showCtxRep ctx}) (\{show e}) (\{show ty0}) (\{show ty1})"
  show (ElemWfCtxCoe ctx0 ctx1 e ty) = "ElemWfCtxCoe (\{showCtxRep ctx0}) (\{showCtxRep ctx1}) (\{show e}) (\{show ty})"
  show (ElemWfSigVar ctx sigma x)     = "ElemWfSigVar (\{showCtxRep ctx}) (\{show sigma}) \{show x}"
  show (ElemEqTyCoe ctx a b ty0 ty1)  = "ElemEqTyCoe (\{showCtxRep ctx}) (\{show a}) (\{show b}) (\{show ty0}) (\{show ty1})"
  show (SigExt gamma x a ty)          = "SigExt (\{showCtxRep gamma}) \{show x} (\{show a}) (\{show ty})"
  show (SigExtTy gamma x ty)          = "SigExtTy (\{showCtxRep gamma}) \{show x} (\{show ty})"
  show (CtxEqRefl ctx)               = "CtxEqRefl (\{showCtxRep ctx})"
  show (CtxEqSym ctx0 ctx1)          = "CtxEqSym (\{showCtxRep ctx0}) (\{showCtxRep ctx1})"
  show (CtxEqTrans ctx0 ctx1 ctx2)   = "CtxEqTrans (\{showCtxRep ctx0}) (\{showCtxRep ctx1}) (\{showCtxRep ctx2})"
  show (SubWfTerminal ctx)             = "SubWfTerminal (\{showCtxRep ctx})"
  show (SubWfExt sigma e gamma delta ty) = "SubWfExt (\{show sigma}) (\{show e}) (\{showCtxRep gamma}) (\{showCtxRep delta}) (\{show ty})"
  show (SubEqRefl s g d)             = "SubEqRefl (\{show s}) (\{showCtxRep g}) (\{showCtxRep d})"
  show (SubEqSym s0 s1 g d)          = "SubEqSym (\{show s0}) (\{show s1}) (\{showCtxRep g}) (\{showCtxRep d})"
  show (SubEqTrans s0 s1 s2 g d)     = "SubEqTrans (\{show s0}) (\{show s1}) (\{show s2}) (\{showCtxRep g}) (\{showCtxRep d})"
  show (SubNormWfTerminal ctx)             = "SubNormWfTerminal (\{showCtxRep ctx})"
  show (SubNormWfExt sigma e gamma delta ty) = "SubNormWfExt (\{show sigma}) (\{show e}) (\{showCtxRep gamma}) (\{showCtxRep delta}) (\{show ty})"
  show (SubNormEqRefl s g d)             = "SubNormEqRefl (\{show s}) (\{showCtxRep g}) (\{showCtxRep d})"
  show (SubNormEqSym s0 s1 g d)          = "SubNormEqSym (\{show s0}) (\{show s1}) (\{showCtxRep g}) (\{showCtxRep d})"
  show (SubNormEqTrans s0 s1 s2 g d)     = "SubNormEqTrans (\{show s0}) (\{show s1}) (\{show s2}) (\{showCtxRep g}) (\{showCtxRep d})"
  show (SubNormEqExt s0 s1 t0 t1 gamma0 gamma1 ty) = "SubNormEqExt (\{show s0}) (\{show s1}) (\{show t0}) (\{show t1}) (\{showCtxRep gamma0}) (\{showCtxRep gamma1}) (\{show ty})"
  show (TyEqRefl ctx ty)             = "TyEqRefl (\{showCtxRep ctx}) (\{show ty})"
  show (TyEqSym ctx ty0 ty1)         = "TyEqSym (\{showCtxRep ctx}) (\{show ty0}) (\{show ty1})"
  show (TyEqTrans ctx ty0 ty1 ty2)   = "TyEqTrans (\{showCtxRep ctx}) (\{show ty0}) (\{show ty1}) (\{show ty2})"
  show (TyEqCongEqTy ctx a0 b0 ty0 a1 b1 ty1) = "TyEqCongEqTy (\{showCtxRep ctx}) (\{show a0}) (\{show b0}) (\{show ty0}) (\{show a1}) (\{show b1}) (\{show ty1})"
  show (TyEqCongEl ctx t0 t1) = "TyEqCongEl (\{showCtxRep ctx}) (\{show t0}) (\{show t1})"
  show (TyEqSubst gamma0 gamma1 sigma0 sigma1 a0 a1) = "TyEqSubst (\{showCtxRep gamma0}) (\{showCtxRep gamma1}) (\{show sigma0}) (\{show sigma1}) (\{show a0}) (\{show a1})"
  show (ElemEqRefl ctx e ty)         = "ElemEqRefl (\{showCtxRep ctx}) (\{show e}) (\{show ty})"
  show (ElemEqSym ctx e0 e1 ty)      = "ElemEqSym (\{showCtxRep ctx}) (\{show e0}) (\{show e1}) (\{show ty})"
  show (ElemEqTrans ctx e0 e1 e2 ty) = "ElemEqTrans (\{showCtxRep ctx}) (\{show e0}) (\{show e1}) (\{show e2}) (\{show ty})"
  show (ElemEqReflection ctx a a0 a1 ty) = "ElemEqReflection (\{showCtxRep ctx}) (\{show a}) (\{show a0}) (\{show a1}) (\{show ty})"
  show (ElemEqCongSuc ctx t0 t1) = "ElemEqCongSuc (\{showCtxRep ctx}) (\{show t0}) (\{show t1})"
  show (ElemEqCongPiApp ctx f0 f1 a b a0 a1) = "ElemEqCongPiApp (\{showCtxRep ctx}) (\{show f0}) (\{show f1}) (\{show a}) (\{show b}) (\{show a0}) (\{show a1})"
  show (ElemEqQuotient ctx ty r a b witness) = "ElemEqQuotient (\{showCtxRep ctx}) (\{show ty}) (\{show r}) (\{show a}) (\{show b}) (\{show witness})"
  show (ElemEqCongClass ctx ty r a0 a1) = "ElemEqCongClass (\{showCtxRep ctx}) (\{show ty}) (\{show r}) (\{show a0}) (\{show a1})"
  show (ElemEqSubst gamma0 gamma1 sigma0 sigma1 t0 t1 a) = "ElemEqSubst (\{showCtxRep gamma0}) (\{showCtxRep gamma1}) (\{show sigma0}) (\{show sigma1}) (\{show t0}) (\{show t1}) (\{show a})"
  show (TelEqRefl ctx tel)           = "TelEqRefl (\{showCtxRep ctx}) (\{show tel})"
  show (TelEqSym ctx tel0 tel1)      = "TelEqSym (\{showCtxRep ctx}) (\{show tel0}) (\{show tel1})"
  show (TelEqTrans ctx tel0 tel1 tel2) = "TelEqTrans (\{showCtxRep ctx}) (\{show tel0}) (\{show tel1}) (\{show tel2})"
  show (SpineEqRefl ctx spine tel)       = "SpineEqRefl (\{showCtxRep ctx}) (\{show spine}) (\{show tel})"
  show (SpineEqSym ctx s0 s1 tel)        = "SpineEqSym (\{showCtxRep ctx}) (\{show s0}) (\{show s1}) (\{show tel})"
  show (SpineEqTrans ctx s0 s1 s2 tel)   = "SpineEqTrans (\{showCtxRep ctx}) (\{show s0}) (\{show s1}) (\{show s2}) (\{show tel})"

public export
data Rejection : Type where
  CtxWfNotDerivable : Ctx -> Rejection
  CtxEqNotDerivable : Ctx -> Ctx -> Rejection
  SubWfNotDerivable : Sub -> Ctx -> Ctx -> Rejection
  SubEqNotDerivable : Sub -> Sub -> Ctx -> Ctx -> Rejection
  SubNormWfNotDerivable : SubNorm -> Ctx -> Ctx -> Rejection
  SubNormEqNotDerivable : SubNorm -> SubNorm -> Ctx -> Ctx -> Rejection
  TyWfNotDerivable : Ctx -> Ty -> Rejection
  TyEqNotDerivable : Ctx -> Ty -> Ty -> Rejection
  ElemWfNotDerivable : Ctx -> Elem -> Ty -> Rejection
  ElemEqNotDerivable : Ctx -> Elem -> Elem -> Ty -> Rejection
  TelWfNotDerivable : Ctx -> Tel -> Rejection
  TelEqNotDerivable : Ctx -> Tel -> Tel -> Rejection
  SpineWfNotDerivable : Ctx -> Spine -> Tel -> Rejection
  SpineEqNotDerivable : Ctx -> Spine -> Spine -> Tel -> Rejection
  SigIdentifierNotFound : SigIdentifier -> Rejection
  SigIdentifierAlreadyDefined : SigIdentifier -> Rejection
  SigIdentifierNotATermDef : SigIdentifier -> Rejection
  SigIdentifierNotATypeDef : SigIdentifier -> Rejection
  ||| el-pi-e's inferring form found no Π-typed fact for the function (or
  ||| none whose domain accepts the argument).
  PiAppInferenceFailed : Ctx -> Elem -> Elem -> Rejection
  CtxVarOutOfBounds : Ctx -> Nat -> Rejection

||| A near-miss explanation attached to a rejection or a NotDerivable
||| answer: what the derived-facts table *does* contain that is close to
||| the failed query. Purely advisory — computed only when a rejection is
||| rendered, never inserted anywhere, and never normalizes the
||| (unvalidated) query.
public export
data Hint : Type where
  ||| The query's own context has no ctx-wf fact, so weakening from
  ||| prefix contexts was disabled.
  HintQueryCtxNotWf : Hint
  ||| ctx-wf miss: this (longest) prefix is derived; the next entry's
  ||| type is what needs ty-wf and ctx-ext.
  HintCtxPrefixDerived : Ctx -> Ty -> Hint
  ||| wf miss: the same expression is derived here (possibly via
  ||| weakening) at these other types — likely an el-ty-coe away.
  HintAtOtherTypes : Ctx -> List Ty -> Hint
  ||| wf miss: the exact judgement holds, but only in these other
  ||| contexts (which weakening cannot reach).
  HintInOtherCtxs : List Ctx -> Hint
  ||| eq miss: the named side has no wf fact at the queried type — the
  ||| guard failed there; the sub-hints explain that side's wf miss.
  HintEqGuardMissing : String -> List Hint -> Hint
  ||| eq miss: both sides are well-formed at the queried type, but their
  ||| normal forms differ and no stored equality bridges them — the
  ||| equality needs real content (lemma/congruence/transitivity chain).
  HintEqNeedsContent : Hint
  ||| eq miss: the reversed equality is a stored fact — one sym away.
  HintReversedEq : Hint
  ||| eq miss: stored equalities at the queried type sharing an endpoint
  ||| with the query — transitivity-chain material.
  HintElemEqEndpoints : Ctx -> List (Elem, Elem) -> Hint
  HintTyEqEndpoints : Ctx -> List (Ty, Ty) -> Hint
  ||| el-pi-e inference miss: the function does have Π-types (their
  ||| domains listed), but the argument's derived types don't match.
  HintPiArg : Ctx -> (domains : List Ty) -> (argTypes : List Ty) -> Hint

rejectUnless : Rejection -> Bool -> Either Rejection ()
rejectUnless _ True = Right ()
rejectUnless r False = Left r

-- Normalization discipline: beta-normalizing (Beta.idr — every Π/Σ/ℕ-elim/
-- quot-elim/x-β redex and El-of-universe-code decoding) is only ever
-- applied to judgements already known derivable, never to unvalidated
-- candidates. Two uses are licensed:
--
--   1. A conclusion at insertion (insertXxx): its premises were just found
--      in the table, so it's derivable by the rule, and subject reduction
--      makes its normal form derivable too. Hence the dual store — every
--      fact lands in both the raw and the normalized set.
--   2. An equality query whose *guard* passed: both sides raw-derivable
--      well-formed at the queried type — exactly the well-formedness
--      premises the ≜-computation rules carry. Only then is the query
--      normalized and matched against the normalized store.
--
-- Well-formedness queries are matched raw only (up to automatic
-- weakening — see the weakening-aware membership section below): subject
-- *expansion* does not hold (reduction can discard an ill-formed subterm
-- — e.g. `(λ Z) (S ())` normalizes to `Z`), so "normalize the candidate,
-- then look it up" would accept underivable judgements; operationally it
-- could also crash or diverge on ill-formed input. These normXxx
-- functions all need Σ, since unfolding a signature reference (x-β) does.
normCtxWf : Sig -> CtxWf -> CtxWf
normCtxWf = betaCtx

normCtxEq : Sig -> CtxEq -> CtxEq
normCtxEq sig (ctx0, ctx1) = (betaCtx sig ctx0, betaCtx sig ctx1)

normSubWf : Sig -> SubWf -> SubWf
normSubWf sig (sigma, gamma, delta) = (betaSub sig sigma, betaCtx sig gamma, betaCtx sig delta)

normSubEq : Sig -> SubEq -> SubEq
normSubEq sig (s0, s1, g, d) = (betaSub sig s0, betaSub sig s1, betaCtx sig g, betaCtx sig d)

normSubNormWf : Sig -> SubNormWf -> SubNormWf
normSubNormWf sig (sigma, gamma, delta) = (betaSubNorm sig sigma, betaCtx sig gamma, betaCtx sig delta)

normSubNormEq : Sig -> SubNormEq -> SubNormEq
normSubNormEq sig (s0, s1, g, d) = (betaSubNorm sig s0, betaSubNorm sig s1, betaCtx sig g, betaCtx sig d)

normTyWf : Sig -> TyWf -> TyWf
normTyWf sig (ctx, ty) = (betaCtx sig ctx, betaTy sig ty)

normTyEq : Sig -> TyEq -> TyEq
normTyEq sig (ctx, ty0, ty1) = (betaCtx sig ctx, betaTy sig ty0, betaTy sig ty1)

normElemWf : Sig -> ElemWf -> ElemWf
normElemWf sig (ctx, elem, ty) = (betaCtx sig ctx, betaElem sig elem, betaTy sig ty)

normElemEq : Sig -> ElemEq -> ElemEq
normElemEq sig (ctx, e0, e1, ty) = (betaCtx sig ctx, betaElem sig e0, betaElem sig e1, betaTy sig ty)

normTelWf : Sig -> TelWf -> TelWf
normTelWf sig (ctx, tel) = (betaCtx sig ctx, betaTel sig tel)

normTelEq : Sig -> TelEq -> TelEq
normTelEq sig (ctx, t0, t1) = (betaCtx sig ctx, betaTel sig t0, betaTel sig t1)

normSpineWf : Sig -> SpineWf -> SpineWf
normSpineWf sig (ctx, spine, tel) = (betaCtx sig ctx, betaSpine sig spine, betaTel sig tel)

normSpineEq : Sig -> SpineEq -> SpineEq
normSpineEq sig (ctx, s0, s1, tel) = (betaCtx sig ctx, betaSpine sig s0, betaSpine sig s1, betaTel sig tel)

-- Each insertXxx records a just-derived conclusion in both stores: raw as
-- concluded, and beta-normalized (licensed — the fact is derivable).

insertCtxWf : CtxWf -> Truth -> Truth
insertCtxWf x sp = {ctxWfRaw $= insert x, ctxWfNorm $= insert (normCtxWf sp.sig x)} sp

insertCtxEq : CtxEq -> Truth -> Truth
insertCtxEq x sp = {ctxEqRaw $= insert x, ctxEqNorm $= insert (normCtxEq sp.sig x)} sp

insertSubWf : SubWf -> Truth -> Truth
insertSubWf x sp = {subWfRaw $= insert x, subWfNorm $= insert (normSubWf sp.sig x)} sp

insertSubEq : SubEq -> Truth -> Truth
insertSubEq x sp = {subEqRaw $= insert x, subEqNorm $= insert (normSubEq sp.sig x)} sp

insertSubNormWf : SubNormWf -> Truth -> Truth
insertSubNormWf x sp = {subNormWfRaw $= insert x, subNormWfNorm $= insert (normSubNormWf sp.sig x)} sp

insertSubNormEq : SubNormEq -> Truth -> Truth
insertSubNormEq x sp = {subNormEqRaw $= insert x, subNormEqNorm $= insert (normSubNormEq sp.sig x)} sp

insertTyWf : TyWf -> Truth -> Truth
insertTyWf x sp = {tyWfRaw $= insert x, tyWfNorm $= insert (normTyWf sp.sig x)} sp

insertTyEq : TyEq -> Truth -> Truth
insertTyEq x sp = {tyEqRaw $= insert x, tyEqNorm $= insert (normTyEq sp.sig x)} sp

insertElemWf : ElemWf -> Truth -> Truth
insertElemWf x sp = {elemWfRaw $= insert x, elemWfNorm $= insert (normElemWf sp.sig x)} sp

insertElemEq : ElemEq -> Truth -> Truth
insertElemEq x sp = {elemEqRaw $= insert x, elemEqNorm $= insert (normElemEq sp.sig x)} sp

insertTelWf : TelWf -> Truth -> Truth
insertTelWf x sp = {telWfRaw $= insert x, telWfNorm $= insert (normTelWf sp.sig x)} sp

insertTelEq : TelEq -> Truth -> Truth
insertTelEq x sp = {telEqRaw $= insert x, telEqNorm $= insert (normTelEq sp.sig x)} sp

insertSpineWf : SpineWf -> Truth -> Truth
insertSpineWf x sp = {spineWfRaw $= insert x, spineWfNorm $= insert (normSpineWf sp.sig x)} sp

insertSpineEq : SpineEq -> Truth -> Truth
insertSpineEq x sp = {spineEqRaw $= insert x, spineEqNorm $= insert (normSpineEq sp.sig x)} sp

-- ===== Weakening-aware membership =====
--
-- Weakening is admissible: a fact derived in Γ holds, weakened, in any
-- extension Γ ᐅ A ᐅ ... whose context is itself derivable — inversion of
-- the extension's ctx-wf makes each ↑ a well-formed substitution, and the
-- substitution rules transport the judgement. So a lookup that misses
-- tries to *strengthen* the query (undo one ↑ — possible exactly when the
-- payload never mentions the innermost variable) and retries in the
-- prefix context, provided the query's own context is raw-derivable
-- well-formed (`ctxOk`). Without that guard a rule could smuggle in an
-- extension whose entry type was never checked (e.g. ty-pi's premise
-- context). Every strengthening step is verified by weakening back — a
-- strengthening bug then crashes loudly instead of silently
-- manufacturing facts.

roundtripCrash : String -> a
roundtripCrash what =
  assert_total $ idris_crash "weakening-aware lookup: strengthen/weaken round-trip failed on a \{what}"

strTy : Ty -> Maybe Ty
strTy ty = do
  ty' <- strengthenTy 0 ty
  if substTy ty' Wk == ty then Just ty' else roundtripCrash "type"

strElem : Elem -> Maybe Elem
strElem e = do
  e' <- strengthenElem 0 e
  if substElem e' Wk == e then Just e' else roundtripCrash "element"

strSub : Sub -> Maybe Sub
strSub s = do
  s' <- strengthenSub 0 s
  if weakenSub s' == s then Just s' else roundtripCrash "substitution"

strSubNorm : SubNorm -> Maybe SubNorm
strSubNorm s = do
  s' <- strengthenSubNorm 0 s
  if substSubNorm s' Wk == s then Just s' else roundtripCrash "normal substitution"

strTel : Tel -> Maybe Tel
strTel t = do
  t' <- strengthenTel 0 t
  if substTel t' Wk == t then Just t' else roundtripCrash "telescope"

strSpine : Spine -> Maybe Spine
strSpine s = do
  s' <- strengthenSpine 0 s
  if substSpine s' Wk == s then Just s' else roundtripCrash "spine"

||| Membership up to weakening: the query is in the set as written, or —
||| if `ctxOk` — some strengthening of it into a prefix context is.
wkMember : Ord a => SortedSet a -> (strengthen1 : a -> Maybe a) -> (ctxOk : Bool) -> a -> Bool
wkMember raw str1 ctxOk q = contains q raw || (ctxOk && go (str1 q))
  where
    go : Maybe a -> Bool
    go Nothing   = False
    go (Just q') = contains q' raw || go (str1 q')

-- One strengthening step per judgement class: drop the innermost entry of
-- the (domain) context and strengthen every payload component with it.

str1TyWf : TyWf -> Maybe TyWf
str1TyWf (rest :< _, ty) = (\ty' => (rest, ty')) <$> strTy ty
str1TyWf ([<], _) = Nothing

str1TyEq : TyEq -> Maybe TyEq
str1TyEq (rest :< _, t0, t1) = (\a, b => (rest, a, b)) <$> strTy t0 <*> strTy t1
str1TyEq ([<], _, _) = Nothing

str1ElemWf : ElemWf -> Maybe ElemWf
str1ElemWf (rest :< _, e, ty) = (\e', ty' => (rest, e', ty')) <$> strElem e <*> strTy ty
str1ElemWf ([<], _, _) = Nothing

str1ElemEq : ElemEq -> Maybe ElemEq
str1ElemEq (rest :< _, e0, e1, ty) =
  (\a, b, c => (rest, a, b, c)) <$> strElem e0 <*> strElem e1 <*> strTy ty
str1ElemEq ([<], _, _, _) = Nothing

str1SubWf : SubWf -> Maybe SubWf
str1SubWf (s, rest :< _, cod) = (\s' => (s', rest, cod)) <$> strSub s
str1SubWf (_, [<], _) = Nothing

str1SubEq : SubEq -> Maybe SubEq
str1SubEq (s0, s1, rest :< _, cod) = (\a, b => (a, b, rest, cod)) <$> strSub s0 <*> strSub s1
str1SubEq (_, _, [<], _) = Nothing

str1SubNormWf : SubNormWf -> Maybe SubNormWf
str1SubNormWf (s, rest :< _, cod) = (\s' => (s', rest, cod)) <$> strSubNorm s
str1SubNormWf (_, [<], _) = Nothing

str1SubNormEq : SubNormEq -> Maybe SubNormEq
str1SubNormEq (s0, s1, rest :< _, cod) = (\a, b => (a, b, rest, cod)) <$> strSubNorm s0 <*> strSubNorm s1
str1SubNormEq (_, _, [<], _) = Nothing

str1TelWf : TelWf -> Maybe TelWf
str1TelWf (rest :< _, tel) = (\tel' => (rest, tel')) <$> strTel tel
str1TelWf ([<], _) = Nothing

str1TelEq : TelEq -> Maybe TelEq
str1TelEq (rest :< _, t0, t1) = (\a, b => (rest, a, b)) <$> strTel t0 <*> strTel t1
str1TelEq ([<], _, _) = Nothing

str1SpineWf : SpineWf -> Maybe SpineWf
str1SpineWf (rest :< _, spn, tel) = (\a, b => (rest, a, b)) <$> strSpine spn <*> strTel tel
str1SpineWf ([<], _, _) = Nothing

str1SpineEq : SpineEq -> Maybe SpineEq
str1SpineEq (rest :< _, s0, s1, tel) =
  (\a, b, c => (rest, a, b, c)) <$> strSpine s0 <*> strSpine s1 <*> strTel tel
str1SpineEq ([<], _, _, _) = Nothing

||| Every type the derived-facts table assigns to `e` in `gamma`,
||| including facts from prefix contexts weakened into `gamma` (same
||| discipline and ctx-wf guard as wkMember; strengthening is only used to
||| build lookup keys). Purely a query — each returned type is a component
||| of a stored derivable fact, weakened back to `gamma`.
elemTypesFor : Truth -> Ctx -> Elem -> List Ty
elemTypesFor sp gamma e = go 0 gamma e
  where
    weakenBy : Nat -> Ty -> Ty
    weakenBy Z     ty = ty
    weakenBy (S k) ty = weakenBy k (substTy ty Wk)

    exact : Ctx -> Elem -> List Ty
    exact ctx g = mapMaybe
      (\(c, h, ty) => if c == ctx && h == g then Just ty else Nothing)
      (Prelude.toList sp.elemWfRaw)

    go : Nat -> Ctx -> Elem -> List Ty
    go k ctx g =
      let here = map (weakenBy k) (exact ctx g)
          deeper = case ctx of
                     [<] => []
                     rest :< _ =>
                       if k == 0 && not (contains gamma sp.ctxWfRaw)
                         then []
                         else case strElem g of
                                Nothing => []
                                Just g' => go (S k) rest g'
      in here ++ deeper

||| The Π-types among elemTypesFor, split into domain and codomain.
piCandidates : Truth -> Ctx -> Elem -> List (Ty, Ty)
piCandidates sp gamma f =
  mapMaybe (\ty => case ty of
                     PiTy a b => Just (a, b)
                     _        => Nothing)
           (elemTypesFor sp gamma f)

-- Derivability checks. Well-formedness queries match the raw store, up to
-- weakening — the expression must have been derived in exactly the form
-- written, but possibly in a prefix context. Equality queries match raw,
-- or — once the guard passes (both sides raw-derivable well-formed at the
-- queried type, licensing normalization) — by computation or against the
-- normalized store (again up to weakening). The by-computation disjunct
-- (the two sides' normal forms coincide) needs no stored equality fact at
-- all: with both endpoints well-formed, every ≜-step out of them is a
-- derivable equality (subject reduction supplies the intermediate wf
-- premises), and equal normal forms make the two chains meet — the
-- conclusion follows by symmetry/transitivity. (&&)/(||) are lazy in
-- their right argument, so nothing is normalized unless its guard already
-- succeeded.

export
ctxWfDerivable : Ctx -> Truth -> Either Rejection ()
ctxWfDerivable ctx sp = rejectUnless (CtxWfNotDerivable ctx) $ contains ctx sp.ctxWfRaw

export
subWfDerivable : Sub -> Ctx -> Ctx -> Truth -> Either Rejection ()
subWfDerivable sigma gamma delta sp =
  rejectUnless (SubWfNotDerivable sigma gamma delta) $
    wkMember sp.subWfRaw str1SubWf (contains gamma sp.ctxWfRaw) (sigma, gamma, delta)

export
subNormWfDerivable : SubNorm -> Ctx -> Ctx -> Truth -> Either Rejection ()
subNormWfDerivable sigma gamma delta sp =
  rejectUnless (SubNormWfNotDerivable sigma gamma delta) $
    wkMember sp.subNormWfRaw str1SubNormWf (contains gamma sp.ctxWfRaw) (sigma, gamma, delta)

export
tyWfDerivable : Ctx -> Ty -> Truth -> Either Rejection ()
tyWfDerivable ctx ty sp =
  rejectUnless (TyWfNotDerivable ctx ty) $
    wkMember sp.tyWfRaw str1TyWf (contains ctx sp.ctxWfRaw) (ctx, ty)

export
elemWfDerivable : Ctx -> Elem -> Ty -> Truth -> Either Rejection ()
elemWfDerivable ctx elem ty sp =
  rejectUnless (ElemWfNotDerivable ctx elem ty) $
    wkMember sp.elemWfRaw str1ElemWf (contains ctx sp.ctxWfRaw) (ctx, elem, ty)

export
telWfDerivable : Ctx -> Tel -> Truth -> Either Rejection ()
telWfDerivable ctx tel sp =
  rejectUnless (TelWfNotDerivable ctx tel) $
    wkMember sp.telWfRaw str1TelWf (contains ctx sp.ctxWfRaw) (ctx, tel)

export
spineWfDerivable : Ctx -> Spine -> Tel -> Truth -> Either Rejection ()
spineWfDerivable ctx spine tel sp =
  rejectUnless (SpineWfNotDerivable ctx spine tel) $
    wkMember sp.spineWfRaw str1SpineWf (contains ctx sp.ctxWfRaw) (ctx, spine, tel)

export
ctxEqDerivable : Ctx -> Ctx -> Truth -> Either Rejection ()
ctxEqDerivable ctx0 ctx1 sp =
  rejectUnless (CtxEqNotDerivable ctx0 ctx1) $
    contains (ctx0, ctx1) sp.ctxEqRaw
    || (contains ctx0 sp.ctxWfRaw && contains ctx1 sp.ctxWfRaw
        && (betaCtx sp.sig ctx0 == betaCtx sp.sig ctx1
            || contains (normCtxEq sp.sig (ctx0, ctx1)) sp.ctxEqNorm))

export
tyEqDerivable : Ctx -> Ty -> Ty -> Truth -> Either Rejection ()
tyEqDerivable ctx ty0 ty1 sp =
  rejectUnless (TyEqNotDerivable ctx ty0 ty1) $
    let ctxOk = contains ctx sp.ctxWfRaw in
    wkMember sp.tyEqRaw str1TyEq ctxOk (ctx, ty0, ty1)
    || (wkMember sp.tyWfRaw str1TyWf ctxOk (ctx, ty0)
        && wkMember sp.tyWfRaw str1TyWf ctxOk (ctx, ty1)
        && (betaTy sp.sig ty0 == betaTy sp.sig ty1
            || wkMember sp.tyEqNorm str1TyEq ctxOk (normTyEq sp.sig (ctx, ty0, ty1))))

export
subEqDerivable : Sub -> Sub -> Ctx -> Ctx -> Truth -> Either Rejection ()
subEqDerivable s0 s1 g d sp =
  rejectUnless (SubEqNotDerivable s0 s1 g d) $
    let ctxOk = contains g sp.ctxWfRaw in
    wkMember sp.subEqRaw str1SubEq ctxOk (s0, s1, g, d)
    || (wkMember sp.subWfRaw str1SubWf ctxOk (s0, g, d)
        && wkMember sp.subWfRaw str1SubWf ctxOk (s1, g, d)
        && (betaSub sp.sig s0 == betaSub sp.sig s1
            || wkMember sp.subEqNorm str1SubEq ctxOk (normSubEq sp.sig (s0, s1, g, d))))

export
subNormEqDerivable : SubNorm -> SubNorm -> Ctx -> Ctx -> Truth -> Either Rejection ()
subNormEqDerivable s0 s1 g d sp =
  rejectUnless (SubNormEqNotDerivable s0 s1 g d) $
    let ctxOk = contains g sp.ctxWfRaw in
    wkMember sp.subNormEqRaw str1SubNormEq ctxOk (s0, s1, g, d)
    || (wkMember sp.subNormWfRaw str1SubNormWf ctxOk (s0, g, d)
        && wkMember sp.subNormWfRaw str1SubNormWf ctxOk (s1, g, d)
        && (betaSubNorm sp.sig s0 == betaSubNorm sp.sig s1
            || wkMember sp.subNormEqNorm str1SubNormEq ctxOk (normSubNormEq sp.sig (s0, s1, g, d))))

export
elemEqDerivable : Ctx -> Elem -> Elem -> Ty -> Truth -> Either Rejection ()
elemEqDerivable ctx e0 e1 ty sp =
  rejectUnless (ElemEqNotDerivable ctx e0 e1 ty) $
    let ctxOk = contains ctx sp.ctxWfRaw in
    wkMember sp.elemEqRaw str1ElemEq ctxOk (ctx, e0, e1, ty)
    || (wkMember sp.elemWfRaw str1ElemWf ctxOk (ctx, e0, ty)
        && wkMember sp.elemWfRaw str1ElemWf ctxOk (ctx, e1, ty)
        && (betaElem sp.sig e0 == betaElem sp.sig e1
            || wkMember sp.elemEqNorm str1ElemEq ctxOk (normElemEq sp.sig (ctx, e0, e1, ty))))

export
telEqDerivable : Ctx -> Tel -> Tel -> Truth -> Either Rejection ()
telEqDerivable ctx t0 t1 sp =
  rejectUnless (TelEqNotDerivable ctx t0 t1) $
    let ctxOk = contains ctx sp.ctxWfRaw in
    wkMember sp.telEqRaw str1TelEq ctxOk (ctx, t0, t1)
    || (wkMember sp.telWfRaw str1TelWf ctxOk (ctx, t0)
        && wkMember sp.telWfRaw str1TelWf ctxOk (ctx, t1)
        && (betaTel sp.sig t0 == betaTel sp.sig t1
            || wkMember sp.telEqNorm str1TelEq ctxOk (normTelEq sp.sig (ctx, t0, t1))))

export
spineEqDerivable : Ctx -> Spine -> Spine -> Tel -> Truth -> Either Rejection ()
spineEqDerivable ctx s0 s1 tel sp =
  rejectUnless (SpineEqNotDerivable ctx s0 s1 tel) $
    let ctxOk = contains ctx sp.ctxWfRaw in
    wkMember sp.spineEqRaw str1SpineEq ctxOk (ctx, s0, s1, tel)
    || (wkMember sp.spineWfRaw str1SpineWf ctxOk (ctx, s0, tel)
        && wkMember sp.spineWfRaw str1SpineWf ctxOk (ctx, s1, tel)
        && (betaSpine sp.sig s0 == betaSpine sp.sig s1
            || wkMember sp.spineEqNorm str1SpineEq ctxOk (normSpineEq sp.sig (ctx, s0, s1, tel))))

||| Γ‖ₙ : the type ☐ₙ has in Γ, weakening by one extra ↑ at every step of
||| the lookup (so the result already accounts for every extension between
||| it and the front of Γ).
ctxLookup : Ctx -> Nat -> Maybe Ty
ctxLookup [<]          _     = Nothing
ctxLookup (rest :< ty) Z     = Just (substTy ty Wk)
ctxLookup (rest :< ty) (S n) = map (\t => substTy t Wk) (ctxLookup rest n)

||| Checks the closure of the typing rule, meaning
||| if the typing rule depends on existence of a derivation of some judgement form it won't be presumed.
||| E.g. To check all at once:
|||
||| Γ ctx
||| Γ ⊦ A type
||| Γ ᐅ A ⊦ B type
||| Γ ⊦ λ f : A → B
|||
||| It's enough to check:
||| Γ ctx
||| Γ ⊦ A type
||| Γ ᐅ A ⊦ B type
||| Γ ᐅ B ⊦ f : B

||| To check:
|||
||| Γ ctx
||| Γ ⊦ ℕ type
|||
||| It's necessary and sufficient to check:
||| Γ ctx
export
step : TypingRule -> Truth -> Either Rejection Truth
step CtxWfEmpty sp = Right $ insertCtxWf [<] sp
step (CtxWfExt gamma ty) sp = do
  tyWfDerivable gamma ty sp
  Right $ insertCtxWf (gamma :< ty) sp
step (TyWfZero gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ insertTyWf (gamma, ZeroTy) sp
step (TyWfOne gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ insertTyWf (gamma, OneTy) sp
step (TyWfNat gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ insertTyWf (gamma, NatTy) sp
step (TyWfUniverse gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ insertTyWf (gamma, UniverseTy) sp
step (TyWfPi gamma a b) sp = do
  tyWfDerivable (gamma :< a) b sp
  Right $ insertTyWf (gamma, PiTy a b) sp
step (TyWfSigma gamma a b) sp = do
  tyWfDerivable (gamma :< a) b sp
  Right $ insertTyWf (gamma, SigmaTy a b) sp
step (TyWfEq gamma left right ty) sp = do
  elemWfDerivable gamma left ty sp
  elemWfDerivable gamma right ty sp
  Right $ insertTyWf (gamma, EqTy left right ty) sp
step (TyWfEl gamma t) sp = do
  elemWfDerivable gamma t UniverseTy sp
  Right $ insertTyWf (gamma, El t) sp
step (TyWfQuotient gamma a r) sp = do
  tyWfDerivable gamma a sp
  tyWfDerivable (gamma :< a :< substTy a Wk) r sp
  Right $ insertTyWf (gamma, Quotient a r) sp
step (TyWfSubst gamma0 gamma1 sigma a) sp = do
  subWfDerivable sigma gamma0 gamma1 sp
  tyWfDerivable gamma1 a sp
  Right $ insertTyWf (gamma0, substTy a sigma) sp
step (TyWfSigVar delta sigma x) sp = do
  ctxWfDerivable delta sp
  case sigLookup x sp.sig of
    Just (SigTyDef gamma _ _) => do
      subNormWfDerivable sigma delta gamma sp
      Right $ insertTyWf (delta, Ty.SigVar x sigma) sp
    Just (SigDef _ _ _ _) => Left (SigIdentifierNotATypeDef x)
    Nothing => Left (SigIdentifierNotFound x)
step (ElemWfVar gamma n) sp = do
  ctxWfDerivable gamma sp
  case ctxLookup gamma n of
    Nothing => Left (CtxVarOutOfBounds gamma n)
    Just ty => Right $ insertElemWf (gamma, CtxVar n, ty) sp
step (ElemWfZeroElim gamma t ty) sp = do
  tyWfDerivable gamma ty sp
  elemWfDerivable gamma t ZeroTy sp
  Right $ insertElemWf (gamma, ZeroElim t, ty) sp
step (ElemWfOneIntro gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ insertElemWf (gamma, OneIntro, OneTy) sp
step (ElemWfZeroIntro gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ insertElemWf (gamma, NatIntro0, NatTy) sp
step (ElemWfSucIntro gamma t) sp = do
  elemWfDerivable gamma t NatTy sp
  Right $ insertElemWf (gamma, NatIntro1 t, NatTy) sp
step (ElemWfNatElim gamma z s t a) sp = do
  tyWfDerivable (gamma :< NatTy) a sp
  elemWfDerivable gamma z (substTy a (Ext Id NatIntro0)) sp
  elemWfDerivable (gamma :< NatTy :< a) s (substTy a (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk)) sp
  elemWfDerivable gamma t NatTy sp
  Right $ insertElemWf (gamma, NatElim z s t, substTy a (Ext Id t)) sp
step (ElemWfClass gamma a ty r) sp = do
  elemWfDerivable gamma a ty sp
  tyWfDerivable (gamma :< ty :< substTy ty Wk) r sp
  Right $ insertElemWf (gamma, Class a, Quotient ty r) sp
step (ElemWfQuotElim gamma ty r motive f q) sp = do
  let wk3 = Chain Wk (Chain Wk Wk)
  tyWfDerivable (gamma :< ty :< substTy ty Wk) r sp
  tyWfDerivable (gamma :< Quotient ty r) motive sp
  elemWfDerivable (gamma :< ty) f (substTy motive (Ext Wk (Class (CtxVar 0)))) sp
  elemEqDerivable (gamma :< ty :< substTy ty Wk :< r)
    (substElem f (Ext wk3 (CtxVar 2))) (substElem f (Ext wk3 (CtxVar 1)))
    (substTy motive (Ext wk3 (Class (CtxVar 2)))) sp
  elemWfDerivable gamma q (Quotient ty r) sp
  Right $ insertElemWf (gamma, QuotElim f q, substTy motive (Ext Id q)) sp
step (ElemWfSubst gamma0 gamma1 sigma t a) sp = do
  subWfDerivable sigma gamma0 gamma1 sp
  elemWfDerivable gamma1 t a sp
  Right $ insertElemWf (gamma0, substElem t sigma, substTy a sigma) sp
step (ElemWfPiIntro gamma f a b) sp = do
  elemWfDerivable (gamma :< a) f b sp
  Right $ insertElemWf (gamma, PiIntro f, PiTy a b) sp
step (ElemWfPiApp gamma f a b e) sp = do
  elemWfDerivable gamma f (PiTy a b) sp
  elemWfDerivable gamma e a sp
  Right $ insertElemWf (gamma, PiApp f e, substTy b (Ext Id e)) sp
step (ElemWfPiAppInfer gamma f e) sp =
  -- First opportunistically infer any application nested in the function
  -- or the argument (failures are swallowed — the fact may already exist
  -- via another route, e.g. a coercion; the final check below decides).
  let sp = tryInfer f (tryInfer e sp) in
  case filter (\(a, _) => isRight (elemWfDerivable gamma e a sp)) (piCandidates sp gamma f) of
    []    => Left (PiAppInferenceFailed gamma f e)
    cands => Right $ foldl (\acc, (a, b) => insertElemWf (gamma, PiApp f e, substTy b (Ext Id e)) acc) sp cands
  where
    tryInfer : Elem -> Truth -> Truth
    tryInfer (PiApp g x) truth = either (const truth) id (step (ElemWfPiAppInfer gamma g x) truth)
    tryInfer _ truth = truth
step (ElemWfSigmaIntro gamma u v a b) sp = do
  tyWfDerivable (gamma :< a) b sp
  elemWfDerivable gamma u a sp
  elemWfDerivable gamma v (substTy b (Ext Id u)) sp
  Right $ insertElemWf (gamma, SigmaIntro u v, SigmaTy a b) sp
step (ElemWfSigmaElim1 gamma t a b) sp = do
  elemWfDerivable gamma t (SigmaTy a b) sp
  Right $ insertElemWf (gamma, SigmaElim1 t, a) sp
step (ElemWfSigmaElim2 gamma t a b) sp = do
  elemWfDerivable gamma t (SigmaTy a b) sp
  Right $ insertElemWf (gamma, SigmaElim2 t, substTy b (Ext Id (SigmaElim1 t))) sp
step (ElemWfZeroTy gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ insertElemWf (gamma, ZeroTy, UniverseTy) sp
step (ElemWfOneTy gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ insertElemWf (gamma, OneTy, UniverseTy) sp
step (ElemWfNatTy gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ insertElemWf (gamma, NatTy, UniverseTy) sp
step (ElemWfPiTy gamma a b) sp = do
  elemWfDerivable gamma a UniverseTy sp
  elemWfDerivable (gamma :< El a) b UniverseTy sp
  Right $ insertElemWf (gamma, PiTy a b, UniverseTy) sp
step (ElemWfSigmaTy gamma a b) sp = do
  elemWfDerivable gamma a UniverseTy sp
  elemWfDerivable (gamma :< El a) b UniverseTy sp
  Right $ insertElemWf (gamma, SigmaTy a b, UniverseTy) sp
step (ElemWfEqTy gamma l r ty) sp = do
  elemWfDerivable gamma ty UniverseTy sp
  elemWfDerivable gamma l (El ty) sp
  elemWfDerivable gamma r (El ty) sp
  Right $ insertElemWf (gamma, EqTy l r ty, UniverseTy) sp
step (ElemWfRefl gamma e ty) sp = do
  elemWfDerivable gamma e ty sp
  Right $ insertElemWf (gamma, Refl, EqTy e e ty) sp
-- Γ ⊦ a : A₀
-- Γ ⊦ A₀ = A₁ type
-- ----------------
-- Γ ⊦ a : A₁
step (ElemWfTyCoe ctx e ty0 ty1) sp = do
  elemWfDerivable ctx e ty0 sp
  tyEqDerivable ctx ty0 ty1 sp
  Right $ insertElemWf (ctx, e, ty1) sp
-- Γ₀ ⊦ a : A
-- Γ₀ = Γ₁ ctx
-- ------------
-- Γ₁ ⊦ a : A
step (ElemWfCtxCoe ctx0 ctx1 e ty) sp = do
  elemWfDerivable ctx0 e ty sp
  ctxEqDerivable ctx0 ctx1 sp
  Right $ insertElemWf (ctx1, e, ty) sp
step (ElemWfSigVar delta sigma x) sp = do
  ctxWfDerivable delta sp
  case sigLookup x sp.sig of
    Just (SigDef gamma _ _ ty) => do
      subNormWfDerivable sigma delta gamma sp
      Right $ insertElemWf (delta, SigVar x sigma, substTy ty (embed sigma)) sp
    Just (SigTyDef _ _ _) => Left (SigIdentifierNotATermDef x)
    Nothing => Left (SigIdentifierNotFound x)
-- Γ ⊦ a = b : A₀
-- Γ ⊦ A₀ = A₁ type
-- -----------------
-- Γ ⊦ a = b : A₁
step (ElemEqTyCoe ctx a b ty0 ty1) sp = do
  elemEqDerivable ctx a b ty0 sp
  tyEqDerivable ctx ty0 ty1 sp
  Right $ insertElemEq (ctx, a, b, ty1) sp
step (SigExt gamma x a ty) sp = do
  elemWfDerivable gamma a ty sp
  case sigLookup x sp.sig of
    Just _  => Left (SigIdentifierAlreadyDefined x)
    Nothing => Right $ {sig $= (:< SigDef gamma x a ty)} sp
step (SigExtTy gamma x ty) sp = do
  tyWfDerivable gamma ty sp
  case sigLookup x sp.sig of
    Just _  => Left (SigIdentifierAlreadyDefined x)
    Nothing => Right $ {sig $= (:< SigTyDef gamma x ty)} sp
step (CtxEqRefl ctx) sp = do
  ctxWfDerivable ctx sp
  Right $ insertCtxEq (ctx, ctx) sp
step (CtxEqSym ctx0 ctx1) sp = do
  ctxEqDerivable ctx0 ctx1 sp
  Right $ insertCtxEq (ctx1, ctx0) sp
step (CtxEqTrans ctx0 ctx1 ctx2) sp = do
  ctxEqDerivable ctx0 ctx1 sp
  ctxEqDerivable ctx1 ctx2 sp
  Right $ insertCtxEq (ctx0, ctx2) sp
step (SubWfTerminal gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ insertSubWf (Terminal, gamma, [<]) sp
step (SubWfExt sigma e gamma delta ty) sp = do
  subWfDerivable sigma gamma delta sp
  tyWfDerivable delta ty sp
  elemWfDerivable gamma e (substTy ty sigma) sp
  Right $ insertSubWf (Ext sigma e, gamma, delta :< ty) sp
step (SubEqRefl s g d) sp = do
  subWfDerivable s g d sp
  Right $ insertSubEq (s, s, g, d) sp
step (SubEqSym s0 s1 g d) sp = do
  subEqDerivable s0 s1 g d sp
  Right $ insertSubEq (s1, s0, g, d) sp
step (SubEqTrans s0 s1 s2 g d) sp = do
  subEqDerivable s0 s1 g d sp
  subEqDerivable s1 s2 g d sp
  Right $ insertSubEq (s0, s2, g, d) sp
step (SubNormWfTerminal gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ insertSubNormWf ([<], gamma, [<]) sp
step (SubNormWfExt sigma e gamma delta ty) sp = do
  subNormWfDerivable sigma gamma delta sp
  tyWfDerivable delta ty sp
  elemWfDerivable gamma e (substTy ty (embed sigma)) sp
  Right $ insertSubNormWf (sigma :< e, gamma, delta :< ty) sp
step (SubNormEqRefl s g d) sp = do
  subNormWfDerivable s g d sp
  Right $ insertSubNormEq (s, s, g, d) sp
step (SubNormEqSym s0 s1 g d) sp = do
  subNormEqDerivable s0 s1 g d sp
  Right $ insertSubNormEq (s1, s0, g, d) sp
step (SubNormEqTrans s0 s1 s2 g d) sp = do
  subNormEqDerivable s0 s1 g d sp
  subNormEqDerivable s1 s2 g d sp
  Right $ insertSubNormEq (s0, s2, g, d) sp
step (SubNormEqExt s0 s1 t0 t1 gamma0 gamma1 ty) sp = do
  subNormEqDerivable s0 s1 gamma0 gamma1 sp
  tyWfDerivable gamma1 ty sp
  elemEqDerivable gamma0 t0 t1 (substTy ty (embed s1)) sp
  Right $ insertSubNormEq (s0 :< t0, s1 :< t1, gamma0, gamma1 :< ty) sp
step (TyEqRefl ctx ty) sp = do
  tyWfDerivable ctx ty sp
  Right $ insertTyEq (ctx, ty, ty) sp
step (TyEqSym ctx ty0 ty1) sp = do
  tyEqDerivable ctx ty0 ty1 sp
  Right $ insertTyEq (ctx, ty1, ty0) sp
step (TyEqTrans ctx ty0 ty1 ty2) sp = do
  tyEqDerivable ctx ty0 ty1 sp
  tyEqDerivable ctx ty1 ty2 sp
  Right $ insertTyEq (ctx, ty0, ty2) sp
step (TyEqCongEqTy gamma a0 b0 ty0 a1 b1 ty1) sp = do
  tyEqDerivable gamma ty0 ty1 sp
  elemEqDerivable gamma a0 a1 ty1 sp
  elemEqDerivable gamma b0 b1 ty1 sp
  Right $ insertTyEq (gamma, EqTy a0 b0 ty0, EqTy a1 b1 ty1) sp
step (TyEqCongEl gamma t0 t1) sp = do
  elemEqDerivable gamma t0 t1 UniverseTy sp
  Right $ insertTyEq (gamma, El t0, El t1) sp
step (TyEqSubst gamma0 gamma1 sigma0 sigma1 a0 a1) sp = do
  subEqDerivable sigma0 sigma1 gamma0 gamma1 sp
  tyEqDerivable gamma1 a0 a1 sp
  Right $ insertTyEq (gamma0, substTy a0 sigma0, substTy a1 sigma1) sp
step (ElemEqRefl ctx e ty) sp = do
  elemWfDerivable ctx e ty sp
  Right $ insertElemEq (ctx, e, e, ty) sp
step (ElemEqSym ctx e0 e1 ty) sp = do
  elemEqDerivable ctx e0 e1 ty sp
  Right $ insertElemEq (ctx, e1, e0, ty) sp
step (ElemEqTrans ctx e0 e1 e2 ty) sp = do
  elemEqDerivable ctx e0 e1 ty sp
  elemEqDerivable ctx e1 e2 ty sp
  Right $ insertElemEq (ctx, e0, e2, ty) sp
step (ElemEqReflection ctx a a0 a1 ty) sp = do
  elemWfDerivable ctx a (EqTy a0 a1 ty) sp
  Right $ insertElemEq (ctx, a0, a1, ty) sp
step (ElemEqCongSuc ctx t0 t1) sp = do
  elemEqDerivable ctx t0 t1 NatTy sp
  Right $ insertElemEq (ctx, NatIntro1 t0, NatIntro1 t1, NatTy) sp
step (ElemEqCongPiApp gamma f0 f1 a b a0 a1) sp = do
  elemEqDerivable gamma f0 f1 (PiTy a b) sp
  elemEqDerivable gamma a0 a1 a sp
  Right $ insertElemEq (gamma, PiApp f0 a0, PiApp f1 a1, substTy b (Ext Id a1)) sp
step (ElemEqQuotient gamma ty r a b witness) sp = do
  tyWfDerivable (gamma :< ty :< substTy ty Wk) r sp
  elemWfDerivable gamma a ty sp
  elemWfDerivable gamma b ty sp
  elemWfDerivable gamma witness (substTy r (Ext (Ext Id a) b)) sp
  Right $ insertElemEq (gamma, Class a, Class b, Quotient ty r) sp
step (ElemEqCongClass gamma ty r a0 a1) sp = do
  tyWfDerivable (gamma :< ty :< substTy ty Wk) r sp
  elemEqDerivable gamma a0 a1 ty sp
  Right $ insertElemEq (gamma, Class a0, Class a1, Quotient ty r) sp
step (ElemEqSubst gamma0 gamma1 sigma0 sigma1 t0 t1 a) sp = do
  subEqDerivable sigma0 sigma1 gamma0 gamma1 sp
  elemEqDerivable gamma1 t0 t1 a sp
  Right $ insertElemEq (gamma0, substElem t0 sigma0, substElem t1 sigma1, substTy a sigma1) sp
step (TelEqRefl ctx tel) sp = do
  telWfDerivable ctx tel sp
  Right $ insertTelEq (ctx, tel, tel) sp
step (TelEqSym ctx tel0 tel1) sp = do
  telEqDerivable ctx tel0 tel1 sp
  Right $ insertTelEq (ctx, tel1, tel0) sp
step (TelEqTrans ctx tel0 tel1 tel2) sp = do
  telEqDerivable ctx tel0 tel1 sp
  telEqDerivable ctx tel1 tel2 sp
  Right $ insertTelEq (ctx, tel0, tel2) sp
step (SpineEqRefl ctx spine tel) sp = do
  spineWfDerivable ctx spine tel sp
  Right $ insertSpineEq (ctx, spine, spine, tel) sp
step (SpineEqSym ctx s0 s1 tel) sp = do
  spineEqDerivable ctx s0 s1 tel sp
  Right $ insertSpineEq (ctx, s1, s0, tel) sp
step (SpineEqTrans ctx s0 s1 s2 tel) sp = do
  spineEqDerivable ctx s0 s1 tel sp
  spineEqDerivable ctx s1 s2 tel sp
  Right $ insertSpineEq (ctx, s0, s2, tel) sp

public export
record ContextualRejection where
  constructor MkContextualRejection
  truth : Truth
  rule : TypingRule
  reason : Rejection

export
steps : List TypingRule -> Truth -> Either ContextualRejection Truth
steps [] truth = Right truth
steps (s :: ss) truth = do
  truth <- mapFst (MkContextualRejection truth s) $ step s truth
  steps ss truth

export
generate : List TypingRule -> Either ContextualRejection Truth
generate ss = steps ss trivial

||| Target-judgement checking follows the exact same discipline as the
||| premise checks in `step` (raw for well-formedness, guarded
||| normalization for equalities) — a `.target` line is just as much an
||| unvalidated candidate as a rule premise is.
export
check : JudgementForm -> Truth -> Bool
check (JfCtxWf ctx)                  t = isRight $ ctxWfDerivable ctx t
check (JfCtxEq (c0, c1))             t = isRight $ ctxEqDerivable c0 c1 t
check (JfTyWf (ctx, ty))             t = isRight $ tyWfDerivable ctx ty t
check (JfTyEq (ctx, ty0, ty1))       t = isRight $ tyEqDerivable ctx ty0 ty1 t
check (JfSubWf (s, g, d))            t = isRight $ subWfDerivable s g d t
check (JfSubEq (s0, s1, g, d))       t = isRight $ subEqDerivable s0 s1 g d t
check (JfSubNormWf (s, g, d))        t = isRight $ subNormWfDerivable s g d t
check (JfSubNormEq (s0, s1, g, d))   t = isRight $ subNormEqDerivable s0 s1 g d t
check (JfElemWf (ctx, e, ty))        t = isRight $ elemWfDerivable ctx e ty t
check (JfElemEq (ctx, e0, e1, ty))   t = isRight $ elemEqDerivable ctx e0 e1 ty t
check (JfTelWf (ctx, tel))           t = isRight $ telWfDerivable ctx tel t
check (JfTelEq (ctx, t0, t1))        t = isRight $ telEqDerivable ctx t0 t1 t
check (JfSpineWf (ctx, spn, tel))    t = isRight $ spineWfDerivable ctx spn tel t
check (JfSpineEq (ctx, s0, s1, tel)) t = isRight $ spineEqDerivable ctx s0 s1 tel t

||| The Rejection a judgement form fails with — lets `diagnose` explain a
||| NotDerivable query/check target the same way as a rejected premise.
export
jfRejection : JudgementForm -> Rejection
jfRejection (JfCtxWf ctx)                  = CtxWfNotDerivable ctx
jfRejection (JfCtxEq (c0, c1))             = CtxEqNotDerivable c0 c1
jfRejection (JfTyWf (ctx, ty))             = TyWfNotDerivable ctx ty
jfRejection (JfTyEq (ctx, t0, t1))         = TyEqNotDerivable ctx t0 t1
jfRejection (JfSubWf (s, g, d))            = SubWfNotDerivable s g d
jfRejection (JfSubEq (s0, s1, g, d))       = SubEqNotDerivable s0 s1 g d
jfRejection (JfSubNormWf (s, g, d))        = SubNormWfNotDerivable s g d
jfRejection (JfSubNormEq (s0, s1, g, d))   = SubNormEqNotDerivable s0 s1 g d
jfRejection (JfElemWf (ctx, e, ty))        = ElemWfNotDerivable ctx e ty
jfRejection (JfElemEq (ctx, e0, e1, ty))   = ElemEqNotDerivable ctx e0 e1 ty
jfRejection (JfTelWf (ctx, tel))           = TelWfNotDerivable ctx tel
jfRejection (JfTelEq (ctx, t0, t1))        = TelEqNotDerivable ctx t0 t1
jfRejection (JfSpineWf (ctx, spn, tel))    = SpineWfNotDerivable ctx spn tel
jfRejection (JfSpineEq (ctx, s0, s1, tel)) = SpineEqNotDerivable ctx s0 s1 tel

-- ===== Near-miss diagnostics =====
--
-- diagnose explains a rejection by reporting what the raw stores DO
-- contain that is close to the failed query: the same term at other
-- types, the same fact in unreachable contexts, a failing eq-guard side
-- (with the reason recursed one level), a reversed equality, the longest
-- derived prefix of an underived context, ... Purely advisory: it never
-- inserts anything and never beta-normalizes the unvalidated query — the
-- only terms it renders or compares are raw query syntax and components
-- of stored (derivable) facts.

hintCap : Nat
hintCap = 3

diagElemWfCore : Truth -> Ctx -> Elem -> Ty -> List Hint
diagElemWfCore sp ctx e ty =
  let others = filter (/= ty) (nub (elemTypesFor sp ctx e)) in
  if not (null others)
    then [HintAtOtherTypes ctx (take hintCap others)]
    else
      let elsewhere = nub (mapMaybe
            (\(c, h, t) => if h == e && t == ty && c /= ctx then Just c else Nothing)
            (Prelude.toList sp.elemWfRaw))
      in if null elsewhere then [] else [HintInOtherCtxs (take hintCap elsewhere)]

diagTyWfCore : Truth -> Ctx -> Ty -> List Hint
diagTyWfCore sp ctx ty =
  let elsewhere = nub (mapMaybe
        (\(c, t) => if t == ty && c /= ctx then Just c else Nothing)
        (Prelude.toList sp.tyWfRaw))
  in if null elsewhere then [] else [HintInOtherCtxs (take hintCap elsewhere)]

ctxHint : Truth -> Ctx -> List Hint
ctxHint sp ctx = if contains ctx sp.ctxWfRaw then [] else [HintQueryCtxNotWf]

export
diagnose : Truth -> Rejection -> List Hint
diagnose sp (CtxWfNotDerivable ctx) = go ctx
  where
    go : Ctx -> List Hint
    go [<] = []
    go (rest :< t) =
      if contains rest sp.ctxWfRaw then [HintCtxPrefixDerived rest t] else go rest
diagnose sp (TyWfNotDerivable ctx ty) =
  ctxHint sp ctx ++ diagTyWfCore sp ctx ty
diagnose sp (ElemWfNotDerivable ctx e ty) =
  ctxHint sp ctx ++ diagElemWfCore sp ctx e ty
diagnose sp (TyEqNotDerivable ctx t0 t1) =
  let ctxOk = contains ctx sp.ctxWfRaw
      lhsOk = wkMember sp.tyWfRaw str1TyWf ctxOk (ctx, t0)
      rhsOk = wkMember sp.tyWfRaw str1TyWf ctxOk (ctx, t1)
      guardHints =
           (if lhsOk then [] else [HintEqGuardMissing "left" (diagTyWfCore sp ctx t0)])
        ++ (if rhsOk then [] else [HintEqGuardMissing "right" (diagTyWfCore sp ctx t1)])
      contentHints =
        if lhsOk && rhsOk
          then if wkMember sp.tyEqRaw str1TyEq ctxOk (ctx, t1, t0)
                 then [HintReversedEq]
                 else HintEqNeedsContent ::
                      (let eps = take hintCap (mapMaybe
                             (\(c, a, b) =>
                               if c == ctx && not (a == t0 && b == t1)
                                  && (a == t0 || b == t0 || a == t1 || b == t1)
                                 then Just (a, b) else Nothing)
                             (Prelude.toList sp.tyEqRaw))
                       in if null eps then [] else [HintTyEqEndpoints ctx eps])
          else []
  in ctxHint sp ctx ++ guardHints ++ contentHints
diagnose sp (ElemEqNotDerivable ctx e0 e1 ty) =
  let ctxOk = contains ctx sp.ctxWfRaw
      lhsOk = wkMember sp.elemWfRaw str1ElemWf ctxOk (ctx, e0, ty)
      rhsOk = wkMember sp.elemWfRaw str1ElemWf ctxOk (ctx, e1, ty)
      guardHints =
           (if lhsOk then [] else [HintEqGuardMissing "left" (diagElemWfCore sp ctx e0 ty)])
        ++ (if rhsOk then [] else [HintEqGuardMissing "right" (diagElemWfCore sp ctx e1 ty)])
      contentHints =
        if lhsOk && rhsOk
          then if wkMember sp.elemEqRaw str1ElemEq ctxOk (ctx, e1, e0, ty)
                 then [HintReversedEq]
                 else HintEqNeedsContent ::
                      (let eps = take hintCap (mapMaybe
                             (\(c, a, b, t) =>
                               if c == ctx && t == ty && not (a == e0 && b == e1)
                                  && (a == e0 || b == e0 || a == e1 || b == e1)
                                 then Just (a, b) else Nothing)
                             (Prelude.toList sp.elemEqRaw))
                       in if null eps then [] else [HintElemEqEndpoints ctx eps])
          else []
  in ctxHint sp ctx ++ guardHints ++ contentHints
diagnose sp (PiAppInferenceFailed ctx f e) =
  ctxHint sp ctx ++
  (case piCandidates sp ctx f of
     []   => let fTys = nub (elemTypesFor sp ctx f)
             in if null fTys then [] else [HintAtOtherTypes ctx (take hintCap fTys)]
     doms => [HintPiArg ctx (take hintCap (nub (map fst doms)))
                            (take hintCap (nub (elemTypesFor sp ctx e)))])
diagnose sp _ = []

||| Every judgement currently recorded in a `Truth`, in its raw form — the
||| form later rules can reference verbatim (wf premises match raw).
export
allJudgements : Truth -> List JudgementForm
allJudgements t =
     map JfCtxWf      (Prelude.toList t.ctxWfRaw)
  ++ map JfCtxEq      (Prelude.toList t.ctxEqRaw)
  ++ map JfSubWf      (Prelude.toList t.subWfRaw)
  ++ map JfSubEq      (Prelude.toList t.subEqRaw)
  ++ map JfSubNormWf  (Prelude.toList t.subNormWfRaw)
  ++ map JfSubNormEq  (Prelude.toList t.subNormEqRaw)
  ++ map JfTyWf       (Prelude.toList t.tyWfRaw)
  ++ map JfTyEq       (Prelude.toList t.tyEqRaw)
  ++ map JfElemWf     (Prelude.toList t.elemWfRaw)
  ++ map JfElemEq     (Prelude.toList t.elemEqRaw)
  ++ map JfTelWf      (Prelude.toList t.telWfRaw)
  ++ map JfTelEq      (Prelude.toList t.telEqRaw)
  ++ map JfSpineWf    (Prelude.toList t.spineWfRaw)
  ++ map JfSpineEq    (Prelude.toList t.spineEqRaw)

||| Judgements present in `after` but not in `before` (raw forms), per
||| judgement form.
export
newJudgements : (before, after : Truth) -> List JudgementForm
newJudgements before after =
     map JfCtxWf      (Prelude.toList $ difference after.ctxWfRaw      before.ctxWfRaw)
  ++ map JfCtxEq      (Prelude.toList $ difference after.ctxEqRaw      before.ctxEqRaw)
  ++ map JfSubWf      (Prelude.toList $ difference after.subWfRaw      before.subWfRaw)
  ++ map JfSubEq      (Prelude.toList $ difference after.subEqRaw      before.subEqRaw)
  ++ map JfSubNormWf  (Prelude.toList $ difference after.subNormWfRaw  before.subNormWfRaw)
  ++ map JfSubNormEq  (Prelude.toList $ difference after.subNormEqRaw  before.subNormEqRaw)
  ++ map JfTyWf       (Prelude.toList $ difference after.tyWfRaw       before.tyWfRaw)
  ++ map JfTyEq       (Prelude.toList $ difference after.tyEqRaw       before.tyEqRaw)
  ++ map JfElemWf     (Prelude.toList $ difference after.elemWfRaw     before.elemWfRaw)
  ++ map JfElemEq     (Prelude.toList $ difference after.elemEqRaw     before.elemEqRaw)
  ++ map JfTelWf      (Prelude.toList $ difference after.telWfRaw      before.telWfRaw)
  ++ map JfTelEq      (Prelude.toList $ difference after.telEqRaw      before.telEqRaw)
  ++ map JfSpineWf    (Prelude.toList $ difference after.spineWfRaw    before.spineWfRaw)
  ++ map JfSpineEq    (Prelude.toList $ difference after.spineEqRaw    before.spineEqRaw)
