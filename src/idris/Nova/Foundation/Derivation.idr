module Nova.Foundation.Derivation

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
export
record Truth where
  constructor MkTruth
  sig : Sig
  ctxWf : SortedSet CtxWf
  ctxEq : SortedSet CtxEq
  tyWf : SortedSet TyWf
  tyEq : SortedSet TyEq
  subWf : SortedSet SubWf
  subEq : SortedSet SubEq
  subNormWf : SortedSet SubNormWf
  subNormEq : SortedSet SubNormEq
  elemWf : SortedSet ElemWf
  elemEq : SortedSet ElemEq
  telWf : SortedSet TelWf
  telEq : SortedSet TelEq
  spineWf : SortedSet SpineWf
  spineEq : SortedSet SpineEq

export
trivial : Truth
trivial = MkTruth [<] empty empty empty empty empty empty empty empty empty empty empty empty empty empty


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
  ||| Γ ⊦ t / t
  ElemWfQuotTy : Ctx -> Elem -> Elem -> TypingRule
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
  ||| Γ ⊦ A type
  ||| Γ ᐅ A ᐅ A[↑] ⊦ R type
  ||| Γ ᐅ (A / R) ⊦ B type
  ||| ---------------------------------------------------------------------
  ||| Γ ᐅ A ⊦ f₀ : B[↑, class ☐₀]
  ||| Γ ᐅ A ⊦ f₁ : B[↑, class ☐₀]
  ||| Γ ᐅ A ᐅ A[↑] ᐅ R ⊦ f₀[↑∘↑∘↑, ☐₂] ≐ f₀[↑∘↑∘↑, ☐₁] : B[↑∘↑∘↑, class ☐₂]
  ||| Γ ᐅ A ᐅ A[↑] ᐅ R ⊦ f₁[↑∘↑∘↑, ☐₂] ≐ f₁[↑∘↑∘↑, ☐₁] : B[↑∘↑∘↑, class ☐₂]
  ||| Γ ⊦ q₀ : A / R
  ||| Γ ⊦ q₁ : A / R
  ||| Γ ᐅ A ⊦ f₀ ≐ f₁ : B[↑, class ☐₀]
  ||| Γ ⊦ q₀ ≐ q₁ : A / R
  ||| =======================================================================
  ||| Γ ⊦ quot-elim f₀ q₀ ≐ quot-elim f₁ q₁ : B[id, q₁]
  ElemEqCongQuotElim : Ctx -> Ty -> Ty -> Ty -> Elem -> Elem -> Elem -> Elem -> TypingRule
  ||| Γ₁ ⊦ A type
  ||| Γ₁ ⊦ t₀ ≐ t₁ : A
  ||| σ₀ ≐ σ₁ : Γ₀ ⇒ Γ₁
  ||| -------------------------
  ||| Γ₀ ⊦ t₀[σ₀] ≐ t₁[σ₁] : A[σ₁]
  ElemEqSubst : Ctx -> Ctx -> Sub -> Sub -> Elem -> Elem -> Ty -> TypingRule
  ||| (Γ ⊦ x ≔ a : A) ∈ Σ
  ||| e˲ : Δ ⇒ Γ norm
  ||| ---------------------------
  ||| Σ Δ ⊦ x[e˲] ≐ a[e˲] : A[e˲]
  ElemEqSigVar : Ctx -> SubNorm -> SigIdentifier -> TypingRule
  ||| Γ ⊦ a ≐ b : A₀
  ||| Γ ⊦ A₀ ≐ A₁ type
  ||| -----------------
  ||| Γ ⊦ a ≐ b : A₁
  ElemEqTyCoe : Ctx -> Elem -> Elem -> Ty -> Ty -> TypingRule
  ||| Σ sig, Σ ⊦ Γ ctx, Σ Γ ⊦ A type, Σ Γ ⊦ a : A, x ∉ Σ
  ||| -------------------------------------------------------
  ||| Σ (Γ ⊦ x ≔ a : A) sig
  SigExt : Ctx -> SigIdentifier -> Elem -> Ty -> TypingRule
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
  show (ElemWfSigmaIntro ctx u v a b) = "ElemWfSigmaIntro (\{showCtxRep ctx}) (\{show u}) (\{show v}) (\{show a}) (\{show b})"
  show (ElemWfSigmaElim1 ctx e a b)  = "ElemWfSigmaElim1 (\{showCtxRep ctx}) (\{show e}) (\{show a}) (\{show b})"
  show (ElemWfSigmaElim2 ctx e a b)  = "ElemWfSigmaElim2 (\{showCtxRep ctx}) (\{show e}) (\{show a}) (\{show b})"
  show (ElemWfZeroTy ctx)            = "ElemWfZeroTy (\{showCtxRep ctx})"
  show (ElemWfOneTy ctx)             = "ElemWfOneTy (\{showCtxRep ctx})"
  show (ElemWfNatTy ctx)             = "ElemWfNatTy (\{showCtxRep ctx})"
  show (ElemWfPiTy ctx a b)          = "ElemWfPiTy (\{showCtxRep ctx}) (\{show a}) (\{show b})"
  show (ElemWfSigmaTy ctx a b)       = "ElemWfSigmaTy (\{showCtxRep ctx}) (\{show a}) (\{show b})"
  show (ElemWfEqTy ctx l r ty)       = "ElemWfEqTy (\{showCtxRep ctx}) (\{show l}) (\{show r}) (\{show ty})"
  show (ElemWfQuotTy ctx a r)        = "ElemWfQuotTy (\{showCtxRep ctx}) (\{show a}) (\{show r})"
  show (ElemWfRefl ctx e ty)         = "ElemWfRefl (\{showCtxRep ctx}) (\{show e}) (\{show ty})"
  show (ElemWfTyCoe ctx e ty0 ty1)   = "ElemWfTyCoe (\{showCtxRep ctx}) (\{show e}) (\{show ty0}) (\{show ty1})"
  show (ElemWfCtxCoe ctx0 ctx1 e ty) = "ElemWfCtxCoe (\{showCtxRep ctx0}) (\{showCtxRep ctx1}) (\{show e}) (\{show ty})"
  show (ElemWfSigVar ctx sigma x)     = "ElemWfSigVar (\{showCtxRep ctx}) (\{show sigma}) \{show x}"
  show (ElemEqSigVar ctx sigma x)     = "ElemEqSigVar (\{showCtxRep ctx}) (\{show sigma}) \{show x}"
  show (ElemEqTyCoe ctx a b ty0 ty1)  = "ElemEqTyCoe (\{showCtxRep ctx}) (\{show a}) (\{show b}) (\{show ty0}) (\{show ty1})"
  show (SigExt gamma x a ty)          = "SigExt (\{showCtxRep gamma}) \{show x} (\{show a}) (\{show ty})"
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
  show (ElemEqCongQuotElim ctx ty r motive f0 f1 q0 q1) = "ElemEqCongQuotElim (\{showCtxRep ctx}) (\{show ty}) (\{show r}) (\{show motive}) (\{show f0}) (\{show f1}) (\{show q0}) (\{show q1})"
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
  CtxVarOutOfBounds : Ctx -> Nat -> Rejection

rejectUnless : Rejection -> Bool -> Either Rejection ()
rejectUnless _ True = Right ()
rejectUnless r False = Left r

-- The Truth table only ever stores beta-normal terms (Beta.idr's betaTy/
-- betaElem/etc. — every Π/Σ/ℕ-elim/quot-elim/x-β redex and El-of-universe-
-- code decoding). These normXxx functions are the single place that
-- normalizes a judgement's payload before it's either inserted (insertXxx,
-- used throughout `step`) or looked up (the derivable-checks below, and
-- `check`) — so every derivability check is, in effect, "beta-normalize the
-- input, then see if the (already beta-normal) Truth table contains it".
-- All of them need Σ, since unfolding a signature reference (x-β) does.
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

insertCtxWf : Sig -> CtxWf -> SortedSet CtxWf -> SortedSet CtxWf
insertCtxWf sig x = insert (normCtxWf sig x)

insertCtxEq : Sig -> CtxEq -> SortedSet CtxEq -> SortedSet CtxEq
insertCtxEq sig x = insert (normCtxEq sig x)

insertSubWf : Sig -> SubWf -> SortedSet SubWf -> SortedSet SubWf
insertSubWf sig x = insert (normSubWf sig x)

insertSubEq : Sig -> SubEq -> SortedSet SubEq -> SortedSet SubEq
insertSubEq sig x = insert (normSubEq sig x)

insertSubNormWf : Sig -> SubNormWf -> SortedSet SubNormWf -> SortedSet SubNormWf
insertSubNormWf sig x = insert (normSubNormWf sig x)

insertSubNormEq : Sig -> SubNormEq -> SortedSet SubNormEq -> SortedSet SubNormEq
insertSubNormEq sig x = insert (normSubNormEq sig x)

insertTyWf : Sig -> TyWf -> SortedSet TyWf -> SortedSet TyWf
insertTyWf sig x = insert (normTyWf sig x)

insertTyEq : Sig -> TyEq -> SortedSet TyEq -> SortedSet TyEq
insertTyEq sig x = insert (normTyEq sig x)

insertElemWf : Sig -> ElemWf -> SortedSet ElemWf -> SortedSet ElemWf
insertElemWf sig x = insert (normElemWf sig x)

insertElemEq : Sig -> ElemEq -> SortedSet ElemEq -> SortedSet ElemEq
insertElemEq sig x = insert (normElemEq sig x)

insertTelWf : Sig -> TelWf -> SortedSet TelWf -> SortedSet TelWf
insertTelWf sig x = insert (normTelWf sig x)

insertTelEq : Sig -> TelEq -> SortedSet TelEq -> SortedSet TelEq
insertTelEq sig x = insert (normTelEq sig x)

insertSpineWf : Sig -> SpineWf -> SortedSet SpineWf -> SortedSet SpineWf
insertSpineWf sig x = insert (normSpineWf sig x)

insertSpineEq : Sig -> SpineEq -> SortedSet SpineEq -> SortedSet SpineEq
insertSpineEq sig x = insert (normSpineEq sig x)

export
ctxWfDerivable : Ctx -> Truth -> Either Rejection ()
ctxWfDerivable ctx sp = rejectUnless (CtxWfNotDerivable ctx) $ contains (normCtxWf sp.sig ctx) sp.ctxWf

export
subWfDerivable : Sub -> Ctx -> Ctx -> Truth -> Either Rejection ()
subWfDerivable sigma gamma delta sp =
  rejectUnless (SubWfNotDerivable sigma gamma delta) $ contains (normSubWf sp.sig (sigma, gamma, delta)) sp.subWf

export
subNormWfDerivable : SubNorm -> Ctx -> Ctx -> Truth -> Either Rejection ()
subNormWfDerivable sigma gamma delta sp =
  rejectUnless (SubNormWfNotDerivable sigma gamma delta) $ contains (normSubNormWf sp.sig (sigma, gamma, delta)) sp.subNormWf

export
tyWfDerivable : Ctx -> Ty -> Truth -> Either Rejection ()
tyWfDerivable ctx ty sp = rejectUnless (TyWfNotDerivable ctx ty) $ contains (normTyWf sp.sig (ctx, ty)) sp.tyWf

export
elemWfDerivable : Ctx -> Elem -> Ty -> Truth -> Either Rejection ()
elemWfDerivable ctx elem ty sp =
  rejectUnless (ElemWfNotDerivable ctx elem ty) $ contains (normElemWf sp.sig (ctx, elem, ty)) sp.elemWf

export
tyEqDerivable : Ctx -> Ty -> Ty -> Truth -> Either Rejection ()
tyEqDerivable ctx ty0 ty1 sp =
  rejectUnless (TyEqNotDerivable ctx ty0 ty1) $ contains (normTyEq sp.sig (ctx, ty0, ty1)) sp.tyEq

export
ctxEqDerivable : Ctx -> Ctx -> Truth -> Either Rejection ()
ctxEqDerivable ctx0 ctx1 sp =
  rejectUnless (CtxEqNotDerivable ctx0 ctx1) $ contains (normCtxEq sp.sig (ctx0, ctx1)) sp.ctxEq

export
subEqDerivable : Sub -> Sub -> Ctx -> Ctx -> Truth -> Either Rejection ()
subEqDerivable s0 s1 g d sp =
  rejectUnless (SubEqNotDerivable s0 s1 g d) $ contains (normSubEq sp.sig (s0, s1, g, d)) sp.subEq

export
subNormEqDerivable : SubNorm -> SubNorm -> Ctx -> Ctx -> Truth -> Either Rejection ()
subNormEqDerivable s0 s1 g d sp =
  rejectUnless (SubNormEqNotDerivable s0 s1 g d) $ contains (normSubNormEq sp.sig (s0, s1, g, d)) sp.subNormEq

export
elemEqDerivable : Ctx -> Elem -> Elem -> Ty -> Truth -> Either Rejection ()
elemEqDerivable ctx e0 e1 ty sp =
  rejectUnless (ElemEqNotDerivable ctx e0 e1 ty) $ contains (normElemEq sp.sig (ctx, e0, e1, ty)) sp.elemEq

export
telWfDerivable : Ctx -> Tel -> Truth -> Either Rejection ()
telWfDerivable ctx tel sp = rejectUnless (TelWfNotDerivable ctx tel) $ contains (normTelWf sp.sig (ctx, tel)) sp.telWf

export
telEqDerivable : Ctx -> Tel -> Tel -> Truth -> Either Rejection ()
telEqDerivable ctx t0 t1 sp =
  rejectUnless (TelEqNotDerivable ctx t0 t1) $ contains (normTelEq sp.sig (ctx, t0, t1)) sp.telEq

export
spineWfDerivable : Ctx -> Spine -> Tel -> Truth -> Either Rejection ()
spineWfDerivable ctx spine tel sp =
  rejectUnless (SpineWfNotDerivable ctx spine tel) $ contains (normSpineWf sp.sig (ctx, spine, tel)) sp.spineWf

export
spineEqDerivable : Ctx -> Spine -> Spine -> Tel -> Truth -> Either Rejection ()
spineEqDerivable ctx s0 s1 tel sp =
  rejectUnless (SpineEqNotDerivable ctx s0 s1 tel) $ contains (normSpineEq sp.sig (ctx, s0, s1, tel)) sp.spineEq

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
step CtxWfEmpty sp = Right $ {ctxWf $= insertCtxWf sp.sig [<]} sp
step (CtxWfExt gamma ty) sp = do
  tyWfDerivable gamma ty sp
  Right $ {ctxWf $= insertCtxWf sp.sig (gamma :< ty)} sp
step (TyWfZero gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {tyWf $= insertTyWf sp.sig (gamma, ZeroTy)} sp
step (TyWfOne gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {tyWf $= insertTyWf sp.sig (gamma, OneTy)} sp
step (TyWfNat gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {tyWf $= insertTyWf sp.sig (gamma, NatTy)} sp
step (TyWfUniverse gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {tyWf $= insertTyWf sp.sig (gamma, UniverseTy)} sp
step (TyWfPi gamma a b) sp = do
  tyWfDerivable (gamma :< a) b sp
  Right $ {tyWf $= insertTyWf sp.sig (gamma, PiTy a b)} sp
step (TyWfSigma gamma a b) sp = do
  tyWfDerivable (gamma :< a) b sp
  Right $ {tyWf $= insertTyWf sp.sig (gamma, SigmaTy a b)} sp
step (TyWfEq gamma left right ty) sp = do
  elemWfDerivable gamma left ty sp
  elemWfDerivable gamma right ty sp
  Right $ {tyWf $= insertTyWf sp.sig (gamma, EqTy left right ty)} sp
step (TyWfEl gamma t) sp = do
  elemWfDerivable gamma t UniverseTy sp
  Right $ {tyWf $= insertTyWf sp.sig (gamma, El t)} sp
step (TyWfQuotient gamma a r) sp = do
  tyWfDerivable gamma a sp
  tyWfDerivable (gamma :< a :< substTy a Wk) r sp
  Right $ {tyWf $= insertTyWf sp.sig (gamma, Quotient a r)} sp
step (TyWfSubst gamma0 gamma1 sigma a) sp = do
  subWfDerivable sigma gamma0 gamma1 sp
  tyWfDerivable gamma1 a sp
  Right $ {tyWf $= insertTyWf sp.sig (gamma0, substTy a sigma)} sp
step (ElemWfVar gamma n) sp = do
  ctxWfDerivable gamma sp
  case ctxLookup gamma n of
    Nothing => Left (CtxVarOutOfBounds gamma n)
    Just ty => Right $ {elemWf $= insertElemWf sp.sig (gamma, CtxVar n, ty)} sp
step (ElemWfZeroElim gamma t ty) sp = do
  tyWfDerivable gamma ty sp
  elemWfDerivable gamma t ZeroTy sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma, ZeroElim t, ty)} sp
step (ElemWfOneIntro gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma, OneIntro, OneTy)} sp
step (ElemWfZeroIntro gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma, NatIntro0, NatTy)} sp
step (ElemWfSucIntro gamma t) sp = do
  elemWfDerivable gamma t NatTy sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma, NatIntro1 t, NatTy)} sp
step (ElemWfNatElim gamma z s t a) sp = do
  -- tyWfDerivable (gamma :< NatTy) a sp
  elemWfDerivable gamma z (substTy a (Ext Id NatIntro0)) sp
  elemWfDerivable (gamma :< NatTy :< a) s (substTy a (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk)) sp
  elemWfDerivable gamma t NatTy sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma, NatElim z s t, substTy a (Ext Id t))} sp
step (ElemWfClass gamma a ty r) sp = do
  elemWfDerivable gamma a ty sp
  tyWfDerivable (gamma :< ty :< substTy ty Wk) r sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma, Class a, Quotient ty r)} sp
step (ElemWfQuotElim gamma ty r motive f q) sp = do
  let wk3 = Chain Wk (Chain Wk Wk)
  tyWfDerivable (gamma :< ty :< substTy ty Wk) r sp
  tyWfDerivable (gamma :< Quotient ty r) motive sp
  elemWfDerivable (gamma :< ty) f (substTy motive (Ext Wk (Class (CtxVar 0)))) sp
  elemEqDerivable (gamma :< ty :< substTy ty Wk :< r)
    (substElem f (Ext wk3 (CtxVar 2))) (substElem f (Ext wk3 (CtxVar 1)))
    (substTy motive (Ext wk3 (Class (CtxVar 2)))) sp
  elemWfDerivable gamma q (Quotient ty r) sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma, QuotElim f q, substTy motive (Ext Id q))} sp
step (ElemWfSubst gamma0 gamma1 sigma t a) sp = do
  subWfDerivable sigma gamma0 gamma1 sp
  elemWfDerivable gamma1 t a sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma0, substElem t sigma, substTy a sigma)} sp
step (ElemWfPiIntro gamma f a b) sp = do
  elemWfDerivable (gamma :< a) f b sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma, PiIntro f, PiTy a b)} sp
step (ElemWfPiApp gamma f a b e) sp = do
  elemWfDerivable gamma f (PiTy a b) sp
  elemWfDerivable gamma e a sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma, PiApp f e, substTy b (Ext Id e))} sp
step (ElemWfSigmaIntro gamma u v a b) sp = do
  tyWfDerivable (gamma :< a) b sp
  elemWfDerivable gamma u a sp
  elemWfDerivable gamma v (substTy b (Ext Id u)) sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma, SigmaIntro u v, SigmaTy a b)} sp
step (ElemWfSigmaElim1 gamma t a b) sp = do
  elemWfDerivable gamma t (SigmaTy a b) sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma, SigmaElim1 t, a)} sp
step (ElemWfSigmaElim2 gamma t a b) sp = do
  elemWfDerivable gamma t (SigmaTy a b) sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma, SigmaElim2 t, substTy b (Ext Id (SigmaElim1 t)))} sp
step (ElemWfZeroTy gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma, ZeroTy, UniverseTy)} sp
step (ElemWfOneTy gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma, OneTy, UniverseTy)} sp
step (ElemWfNatTy gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma, NatTy, UniverseTy)} sp
step (ElemWfPiTy gamma a b) sp = do
  elemWfDerivable gamma a UniverseTy sp
  elemWfDerivable (gamma :< El a) b UniverseTy sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma, PiTy a b, UniverseTy)} sp
step (ElemWfSigmaTy gamma a b) sp = do
  elemWfDerivable gamma a UniverseTy sp
  elemWfDerivable (gamma :< El a) b UniverseTy sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma, SigmaTy a b, UniverseTy)} sp
step (ElemWfEqTy gamma l r ty) sp = do
  elemWfDerivable gamma ty UniverseTy sp
  elemWfDerivable gamma l (El ty) sp
  elemWfDerivable gamma r (El ty) sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma, EqTy l r ty, UniverseTy)} sp
step (ElemWfQuotTy gamma a r) sp = do
  elemWfDerivable gamma a UniverseTy sp
  elemWfDerivable (gamma :< El a :< substTy (El a) Wk) r UniverseTy sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma, QuotTy a r, UniverseTy)} sp
step (ElemWfRefl gamma e ty) sp = do
  elemWfDerivable gamma e ty sp
  Right $ {elemWf $= insertElemWf sp.sig (gamma, Refl, EqTy e e ty)} sp
-- Γ ⊦ a : A₀
-- Γ ⊦ A₀ = A₁ type
-- ----------------
-- Γ ⊦ a : A₁
step (ElemWfTyCoe ctx e ty0 ty1) sp = do
  elemWfDerivable ctx e ty0 sp
  tyEqDerivable ctx ty0 ty1 sp
  Right $ {elemWf $= insertElemWf sp.sig (ctx, e, ty1)} sp
-- Γ₀ ⊦ a : A
-- Γ₀ = Γ₁ ctx
-- ------------
-- Γ₁ ⊦ a : A
step (ElemWfCtxCoe ctx0 ctx1 e ty) sp = do
  elemWfDerivable ctx0 e ty sp
  ctxEqDerivable ctx0 ctx1 sp
  Right $ {elemWf $= insertElemWf sp.sig (ctx1, e, ty)} sp
step (ElemWfSigVar delta sigma x) sp = do
  ctxWfDerivable delta sp
  case sigLookup x sp.sig of
    Nothing => Left (SigIdentifierNotFound x)
    Just (gamma, _, _, ty) => do
      subNormWfDerivable sigma delta gamma sp
      Right $ {elemWf $= insertElemWf sp.sig (delta, SigVar x sigma, substTy ty (embed sigma))} sp
step (ElemEqSigVar delta sigma x) sp = do
  ctxWfDerivable delta sp
  case sigLookup x sp.sig of
    Nothing => Left (SigIdentifierNotFound x)
    Just (gamma, _, a, ty) => do
      subNormWfDerivable sigma delta gamma sp
      Right $ {elemEq $= insertElemEq sp.sig (delta, SigVar x sigma, substElem a (embed sigma), substTy ty (embed sigma))} sp
-- Γ ⊦ a = b : A₀
-- Γ ⊦ A₀ = A₁ type
-- -----------------
-- Γ ⊦ a = b : A₁
step (ElemEqTyCoe ctx a b ty0 ty1) sp = do
  elemEqDerivable ctx a b ty0 sp
  tyEqDerivable ctx ty0 ty1 sp
  Right $ {elemEq $= insertElemEq sp.sig (ctx, a, b, ty1)} sp
step (SigExt gamma x a ty) sp = do
  elemWfDerivable gamma a ty sp
  case sigLookup x sp.sig of
    Just _  => Left (SigIdentifierAlreadyDefined x)
    Nothing => Right $ {sig $= (:< (gamma, x, a, ty))} sp
step (CtxEqRefl ctx) sp = do
  ctxWfDerivable ctx sp
  Right $ {ctxEq $= insertCtxEq sp.sig (ctx, ctx)} sp
step (CtxEqSym ctx0 ctx1) sp = do
  ctxEqDerivable ctx0 ctx1 sp
  Right $ {ctxEq $= insertCtxEq sp.sig (ctx1, ctx0)} sp
step (CtxEqTrans ctx0 ctx1 ctx2) sp = do
  ctxEqDerivable ctx0 ctx1 sp
  ctxEqDerivable ctx1 ctx2 sp
  Right $ {ctxEq $= insertCtxEq sp.sig (ctx0, ctx2)} sp
step (SubWfTerminal gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {subWf $= insertSubWf sp.sig (Terminal, gamma, [<])} sp
step (SubWfExt sigma e gamma delta ty) sp = do
  subWfDerivable sigma gamma delta sp
  tyWfDerivable delta ty sp
  elemWfDerivable gamma e (substTy ty sigma) sp
  Right $ {subWf $= insertSubWf sp.sig (Ext sigma e, gamma, delta :< ty)} sp
step (SubEqRefl s g d) sp = do
  subWfDerivable s g d sp
  Right $ {subEq $= insertSubEq sp.sig (s, s, g, d)} sp
step (SubEqSym s0 s1 g d) sp = do
  subEqDerivable s0 s1 g d sp
  Right $ {subEq $= insertSubEq sp.sig (s1, s0, g, d)} sp
step (SubEqTrans s0 s1 s2 g d) sp = do
  subEqDerivable s0 s1 g d sp
  subEqDerivable s1 s2 g d sp
  Right $ {subEq $= insertSubEq sp.sig (s0, s2, g, d)} sp
step (SubNormWfTerminal gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {subNormWf $= insertSubNormWf sp.sig ([<], gamma, [<])} sp
step (SubNormWfExt sigma e gamma delta ty) sp = do
  subNormWfDerivable sigma gamma delta sp
  tyWfDerivable delta ty sp
  elemWfDerivable gamma e (substTy ty (embed sigma)) sp
  Right $ {subNormWf $= insertSubNormWf sp.sig (sigma :< e, gamma, delta :< ty)} sp
step (SubNormEqRefl s g d) sp = do
  subNormWfDerivable s g d sp
  Right $ {subNormEq $= insertSubNormEq sp.sig (s, s, g, d)} sp
step (SubNormEqSym s0 s1 g d) sp = do
  subNormEqDerivable s0 s1 g d sp
  Right $ {subNormEq $= insertSubNormEq sp.sig (s1, s0, g, d)} sp
step (SubNormEqTrans s0 s1 s2 g d) sp = do
  subNormEqDerivable s0 s1 g d sp
  subNormEqDerivable s1 s2 g d sp
  Right $ {subNormEq $= insertSubNormEq sp.sig (s0, s2, g, d)} sp
step (SubNormEqExt s0 s1 t0 t1 gamma0 gamma1 ty) sp = do
  subNormEqDerivable s0 s1 gamma0 gamma1 sp
  elemEqDerivable gamma0 t0 t1 (substTy ty (embed s1)) sp
  Right $ {subNormEq $= insertSubNormEq sp.sig (s0 :< t0, s1 :< t1, gamma0, gamma1 :< ty)} sp
step (TyEqRefl ctx ty) sp = do
  tyWfDerivable ctx ty sp
  Right $ {tyEq $= insertTyEq sp.sig (ctx, ty, ty)} sp
step (TyEqSym ctx ty0 ty1) sp = do
  tyEqDerivable ctx ty0 ty1 sp
  Right $ {tyEq $= insertTyEq sp.sig (ctx, ty1, ty0)} sp
step (TyEqTrans ctx ty0 ty1 ty2) sp = do
  tyEqDerivable ctx ty0 ty1 sp
  tyEqDerivable ctx ty1 ty2 sp
  Right $ {tyEq $= insertTyEq sp.sig (ctx, ty0, ty2)} sp
step (TyEqCongEqTy gamma a0 b0 ty0 a1 b1 ty1) sp = do
  tyEqDerivable gamma ty0 ty1 sp
  elemEqDerivable gamma a0 a1 ty1 sp
  elemEqDerivable gamma b0 b1 ty1 sp
  Right $ {tyEq $= insertTyEq sp.sig (gamma, EqTy a0 b0 ty0, EqTy a1 b1 ty1)} sp
step (TyEqCongEl gamma t0 t1) sp = do
  elemEqDerivable gamma t0 t1 UniverseTy sp
  Right $ {tyEq $= insertTyEq sp.sig (gamma, El t0, El t1)} sp
step (TyEqSubst gamma0 gamma1 sigma0 sigma1 a0 a1) sp = do
  subEqDerivable sigma0 sigma1 gamma0 gamma1 sp
  tyEqDerivable gamma1 a0 a1 sp
  Right $ {tyEq $= insertTyEq sp.sig (gamma0, substTy a0 sigma0, substTy a1 sigma1)} sp
step (ElemEqRefl ctx e ty) sp = do
  elemWfDerivable ctx e ty sp
  Right $ {elemEq $= insertElemEq sp.sig (ctx, e, e, ty)} sp
step (ElemEqSym ctx e0 e1 ty) sp = do
  elemEqDerivable ctx e0 e1 ty sp
  Right $ {elemEq $= insertElemEq sp.sig (ctx, e1, e0, ty)} sp
step (ElemEqTrans ctx e0 e1 e2 ty) sp = do
  elemEqDerivable ctx e0 e1 ty sp
  elemEqDerivable ctx e1 e2 ty sp
  Right $ {elemEq $= insertElemEq sp.sig (ctx, e0, e2, ty)} sp
step (ElemEqReflection ctx a a0 a1 ty) sp = do
  elemWfDerivable ctx a (EqTy a0 a1 ty) sp
  Right $ {elemEq $= insertElemEq sp.sig (ctx, a0, a1, ty)} sp
step (ElemEqCongSuc ctx t0 t1) sp = do
  elemEqDerivable ctx t0 t1 NatTy sp
  Right $ {elemEq $= insertElemEq sp.sig (ctx, NatIntro1 t0, NatIntro1 t1, NatTy)} sp
step (ElemEqCongPiApp gamma f0 f1 a b a0 a1) sp = do
  elemEqDerivable gamma f0 f1 (PiTy a b) sp
  elemEqDerivable gamma a0 a1 a sp
  Right $ {elemEq $= insertElemEq sp.sig (gamma, PiApp f0 a0, PiApp f1 a1, substTy b (Ext Id a1))} sp
step (ElemEqQuotient gamma ty r a b witness) sp = do
  tyWfDerivable (gamma :< ty :< substTy ty Wk) r sp
  elemWfDerivable gamma a ty sp
  elemWfDerivable gamma b ty sp
  elemWfDerivable gamma witness (substTy r (Ext (Ext Id a) b)) sp
  Right $ {elemEq $= insertElemEq sp.sig (gamma, Class a, Class b, Quotient ty r)} sp
step (ElemEqCongClass gamma ty r a0 a1) sp = do
  tyWfDerivable (gamma :< ty :< substTy ty Wk) r sp
  elemEqDerivable gamma a0 a1 ty sp
  Right $ {elemEq $= insertElemEq sp.sig (gamma, Class a0, Class a1, Quotient ty r)} sp
step (ElemEqCongQuotElim gamma ty r motive f0 f1 q0 q1) sp = do
  let wk3 = Chain Wk (Chain Wk Wk)
  tyWfDerivable (gamma :< ty :< substTy ty Wk) r sp
  tyWfDerivable (gamma :< Quotient ty r) motive sp
  elemWfDerivable (gamma :< ty) f0 (substTy motive (Ext Wk (Class (CtxVar 0)))) sp
  elemWfDerivable (gamma :< ty) f1 (substTy motive (Ext Wk (Class (CtxVar 0)))) sp
  elemEqDerivable (gamma :< ty :< substTy ty Wk :< r)
    (substElem f0 (Ext wk3 (CtxVar 2))) (substElem f0 (Ext wk3 (CtxVar 1)))
    (substTy motive (Ext wk3 (Class (CtxVar 2)))) sp
  elemEqDerivable (gamma :< ty :< substTy ty Wk :< r)
    (substElem f1 (Ext wk3 (CtxVar 2))) (substElem f1 (Ext wk3 (CtxVar 1)))
    (substTy motive (Ext wk3 (Class (CtxVar 2)))) sp
  elemWfDerivable gamma q0 (Quotient ty r) sp
  elemWfDerivable gamma q1 (Quotient ty r) sp
  elemEqDerivable (gamma :< ty) f0 f1 (substTy motive (Ext Wk (Class (CtxVar 0)))) sp
  elemEqDerivable gamma q0 q1 (Quotient ty r) sp
  Right $ {elemEq $= insertElemEq sp.sig (gamma, QuotElim f0 q0, QuotElim f1 q1, substTy motive (Ext Id q1))} sp
step (ElemEqSubst gamma0 gamma1 sigma0 sigma1 t0 t1 a) sp = do
  subEqDerivable sigma0 sigma1 gamma0 gamma1 sp
  elemEqDerivable gamma1 t0 t1 a sp
  Right $ {elemEq $= insertElemEq sp.sig (gamma0, substElem t0 sigma0, substElem t1 sigma1, substTy a sigma1)} sp
step (TelEqRefl ctx tel) sp = do
  telWfDerivable ctx tel sp
  Right $ {telEq $= insertTelEq sp.sig (ctx, tel, tel)} sp
step (TelEqSym ctx tel0 tel1) sp = do
  telEqDerivable ctx tel0 tel1 sp
  Right $ {telEq $= insertTelEq sp.sig (ctx, tel1, tel0)} sp
step (TelEqTrans ctx tel0 tel1 tel2) sp = do
  telEqDerivable ctx tel0 tel1 sp
  telEqDerivable ctx tel1 tel2 sp
  Right $ {telEq $= insertTelEq sp.sig (ctx, tel0, tel2)} sp
step (SpineEqRefl ctx spine tel) sp = do
  spineWfDerivable ctx spine tel sp
  Right $ {spineEq $= insertSpineEq sp.sig (ctx, spine, spine, tel)} sp
step (SpineEqSym ctx s0 s1 tel) sp = do
  spineEqDerivable ctx s0 s1 tel sp
  Right $ {spineEq $= insertSpineEq sp.sig (ctx, s1, s0, tel)} sp
step (SpineEqTrans ctx s0 s1 s2 tel) sp = do
  spineEqDerivable ctx s0 s1 tel sp
  spineEqDerivable ctx s1 s2 tel sp
  Right $ {spineEq $= insertSpineEq sp.sig (ctx, s0, s2, tel)} sp

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

export
check : JudgementForm -> Truth -> Bool
check (JfCtxWf ctx)       t = contains (normCtxWf t.sig ctx) t.ctxWf
check (JfCtxEq ctxeq)     t = contains (normCtxEq t.sig ctxeq) t.ctxEq
check (JfTyWf tywf)       t = contains (normTyWf t.sig tywf) t.tyWf
check (JfTyEq tyeq)       t = contains (normTyEq t.sig tyeq) t.tyEq
check (JfSubWf subwf)     t = contains (normSubWf t.sig subwf) t.subWf
check (JfSubEq subeq)     t = contains (normSubEq t.sig subeq) t.subEq
check (JfSubNormWf subwf) t = contains (normSubNormWf t.sig subwf) t.subNormWf
check (JfSubNormEq subeq) t = contains (normSubNormEq t.sig subeq) t.subNormEq
check (JfElemWf ewf)      t = contains (normElemWf t.sig ewf) t.elemWf
check (JfElemEq eeq)      t = contains (normElemEq t.sig eeq) t.elemEq
check (JfTelWf telwf)     t = contains (normTelWf t.sig telwf) t.telWf
check (JfTelEq teleq)     t = contains (normTelEq t.sig teleq) t.telEq
check (JfSpineWf spinewf) t = contains (normSpineWf t.sig spinewf) t.spineWf
check (JfSpineEq spineeq) t = contains (normSpineEq t.sig spineeq) t.spineEq

||| Every judgement currently recorded in a `Truth`.
export
allJudgements : Truth -> List JudgementForm
allJudgements t =
     map JfCtxWf      (Prelude.toList t.ctxWf)
  ++ map JfCtxEq      (Prelude.toList t.ctxEq)
  ++ map JfSubWf      (Prelude.toList t.subWf)
  ++ map JfSubEq      (Prelude.toList t.subEq)
  ++ map JfSubNormWf  (Prelude.toList t.subNormWf)
  ++ map JfSubNormEq  (Prelude.toList t.subNormEq)
  ++ map JfTyWf       (Prelude.toList t.tyWf)
  ++ map JfTyEq       (Prelude.toList t.tyEq)
  ++ map JfElemWf     (Prelude.toList t.elemWf)
  ++ map JfElemEq     (Prelude.toList t.elemEq)
  ++ map JfTelWf      (Prelude.toList t.telWf)
  ++ map JfTelEq      (Prelude.toList t.telEq)
  ++ map JfSpineWf    (Prelude.toList t.spineWf)
  ++ map JfSpineEq    (Prelude.toList t.spineEq)

||| Judgements present in `after` but not in `before`, per judgement form.
export
newJudgements : (before, after : Truth) -> List JudgementForm
newJudgements before after =
     map JfCtxWf      (Prelude.toList $ difference after.ctxWf      before.ctxWf)
  ++ map JfCtxEq      (Prelude.toList $ difference after.ctxEq      before.ctxEq)
  ++ map JfSubWf      (Prelude.toList $ difference after.subWf      before.subWf)
  ++ map JfSubEq      (Prelude.toList $ difference after.subEq      before.subEq)
  ++ map JfSubNormWf  (Prelude.toList $ difference after.subNormWf  before.subNormWf)
  ++ map JfSubNormEq  (Prelude.toList $ difference after.subNormEq  before.subNormEq)
  ++ map JfTyWf       (Prelude.toList $ difference after.tyWf       before.tyWf)
  ++ map JfTyEq       (Prelude.toList $ difference after.tyEq       before.tyEq)
  ++ map JfElemWf     (Prelude.toList $ difference after.elemWf     before.elemWf)
  ++ map JfElemEq     (Prelude.toList $ difference after.elemEq     before.elemEq)
  ++ map JfTelWf      (Prelude.toList $ difference after.telWf      before.telWf)
  ++ map JfTelEq      (Prelude.toList $ difference after.telEq      before.telEq)
  ++ map JfSpineWf    (Prelude.toList $ difference after.spineWf    before.spineWf)
  ++ map JfSpineEq    (Prelude.toList $ difference after.spineEq    before.spineEq)
