module Nova.Foundation.Derivation

import Data.SnocList
import Nova.Foundation.Syntax

import Data.SortedSet

%default covering

||| Γ ctx
public export
CtxWf : Type
CtxWf = Ctx

||| Γ₀ = Γ₁ ctx
public export
CtxEq : Type
CtxEq = (Ctx, Ctx)

||| Γ ⊦ A type
public export
TyWf : Type
TyWf = (Ctx, Ty)

||| Γ ⊦ A₀ = A₁ type
public export
TyEq : Type
TyEq = (Ctx, Ty, Ty)

||| σ : Γ ⇒ Δ
public export
SubWf : Type
SubWf = (Sub, Ctx, Ctx)

||| σ₀ = σ₁ : Γ ⇒ Δ
public export
SubEq : Type
SubEq = (Sub, Sub, Ctx, Ctx)

||| Γ ⊦ a : A
public export
ElemWf : Type
ElemWf = (Ctx, Elem, Ty)

||| Γ ⊦ a₀ = a₁ : A
public export
ElemEq : Type
ElemEq = (Ctx, Elem, Elem, Ty)

||| Γ ⊦ Δ tel
public export
TelWf : Type
TelWf = (Ctx, Tel)

||| Γ ⊦ Δ₀ = Δ₁ tel
public export
TelEq : Type
TelEq = (Ctx, Tel, Tel)

||| Γ ⊦ ē : Δ
public export
SpineWf : Type
SpineWf = (Ctx, Spine, Tel)

||| Γ ⊦ ē₀ = ē₁ : Δ
public export
SpineEq : Type
SpineEq = (Ctx, Spine, Spine, Tel)

public export
data JudgementForm = JfCtxWf CtxWf
                   | JfCtxEq CtxEq
                   | JfSubWf SubWf
                   | JfSubEq SubEq
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
  elemWf : SortedSet ElemWf
  elemEq : SortedSet ElemEq
  telWf : SortedSet TelWf
  telEq : SortedSet TelEq
  spineWf : SortedSet SpineWf
  spineEq : SortedSet SpineEq

export
trivial : Truth
trivial = MkTruth [<] empty empty empty empty empty empty empty empty empty empty empty empty

||| α
public export
data ComputeRule =
                 -- ↓
                 Here
                 -- id
               | Id
                 -- α; α
               | Composition ComputeRule ComputeRule
                 -- α [β]
               | InSubstElim ComputeRule ComputeRule
                 -- 𝟘-elim α
               | InZeroElim ComputeRule
                 -- S α
               | InNatIntro1 ComputeRule
                 -- ℕ-elim α α α
               | InNatElim ComputeRule ComputeRule ComputeRule
                 --  λ α
               | InPiIntro ComputeRule
                 -- α α
               | InPiApp ComputeRule ComputeRule
                 -- α , α
               | InSigmaIntro ComputeRule ComputeRule
                 -- α .π₁
               | InSigmaElim1 ComputeRule
                 -- α .π₂
               | InSigmaElim2 ComputeRule
                 -- α → α
               | InPiTy ComputeRule ComputeRule
                 -- α ⨯ α
               | InSigmaTy ComputeRule ComputeRule
                 -- α ≡ α ∈ α
               | InEqTy ComputeRule ComputeRule ComputeRule
                 -- El α
               | InEl ComputeRule
                 -- α ᐅ α
               | InExt ComputeRule ComputeRule

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
  ||| Γ ᐅ A ⊦ ☐
  ElemWfVar : Ctx -> Ty -> TypingRule
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
  ||| Γ ⊦ Refl : (a ≡ a : A)
  ElemWfRefl : Ctx -> Elem -> Ty -> TypingRule
  ||| (a : A) (σ : Γ ⇒ Δ)
  ElemWfSubElim : Elem -> Ty -> Sub -> Ctx -> Ctx -> TypingRule
  ||| Γ | α
  CtxWfCompute : Ctx -> ComputeRule -> TypingRule
  ||| Γ | α ⊦ A | α type
  TyWfCompute : Ctx -> ComputeRule -> Ty -> ComputeRule -> TypingRule
  ||| Γ | α ⊦ a | α : A | α type
  ElemWfCompute : Ctx -> ComputeRule -> Elem -> ComputeRule -> Ty -> ComputeRule -> TypingRule
  ||| Γ ⊦ a : A₀
  ||| Γ ⊦ A₀ = A₁ type
  ||| ---------------- (Γ ⊦ a : A₀ = A₁)
  ||| Γ ⊦ a : A₁
  ElemWfTyCoe : Ctx -> Elem -> Ty -> Ty -> TypingRule
  ||| Γ₀ ⊦ a : A₀
  ||| Γ₀ = Γ₁ ctx
  ||| ---------------- (Γ₀ = Γ₁ ⊦ a : A)
  ||| Γ₁ ⊦ a : A
  ElemWfCtxCoe : Ctx -> Ctx -> Elem -> Ty -> TypingRule
  ||| (Γ ⊦ x ≔ t : A) ∈ Σ
  ||| -------------------
  ||| Σ Γ ⊦ x : A
  ElemWfSigVar : SigIdentifier -> TypingRule
  -- Context equality
  CtxEqRefl  : Ctx -> TypingRule
  CtxEqSym   : Ctx -> Ctx -> TypingRule
  CtxEqTrans : Ctx -> Ctx -> Ctx -> TypingRule
  -- Substitution well-formedness
  ||| · : Γ ⇒ ε
  SubWfTerminal : Ctx -> TypingRule
  ||| id : Γ ⇒ Γ
  SubWfId : Ctx -> TypingRule
  ||| ↑ : (Γ ᐅ A) ⇒ Γ
  SubWfWk : Ctx -> Ty -> TypingRule
  ||| (σ, e) : Γ ⇒ (Δ ᐅ A)  given σ : Γ ⇒ Δ
  SubWfExt : Sub -> Elem -> Ctx -> Ctx -> Ty -> TypingRule
  ||| σ ∘ τ : Γ ⇒ Δ  given σ : Γ ⇒ Θ and τ : Θ ⇒ Δ
  SubWfChain : Sub -> Sub -> Ctx -> Ctx -> Ctx -> TypingRule
  -- Substitution equality
  SubEqRefl  : Sub -> Ctx -> Ctx -> TypingRule
  SubEqSym   : Sub -> Sub -> Ctx -> Ctx -> TypingRule
  SubEqTrans : Sub -> Sub -> Sub -> Ctx -> Ctx -> TypingRule
  -- Type equality
  TyEqRefl  : Ctx -> Ty -> TypingRule
  TyEqSym   : Ctx -> Ty -> Ty -> TypingRule
  TyEqTrans : Ctx -> Ty -> Ty -> Ty -> TypingRule
  -- Element equality
  ElemEqRefl  : Ctx -> Elem -> Ty -> TypingRule
  ElemEqSym   : Ctx -> Elem -> Elem -> Ty -> TypingRule
  ElemEqTrans : Ctx -> Elem -> Elem -> Elem -> Ty -> TypingRule
  ||| Γ ⊦ a : (a₀ ≡ a₁ ∈ A)
  ||| -------------------------
  ||| Γ ⊦ a₀ = a₁ : A
  ElemEqReflection : Ctx -> Elem -> Elem -> Elem -> Ty -> TypingRule
  ||| (Γ ⊦ x ≔ t : A) ∈ Σ
  ||| -------------------
  ||| Σ Γ ⊦ x = t : A
  ElemEqSigVar : SigIdentifier -> TypingRule
  ||| Γ ⊦ a = b : A
  ||| σ : Δ ⇒ Γ
  ||| -------------------------
  ||| Δ ⊦ a(σ) = b(σ) : A(σ)
  ElemEqSubstCong : Ctx -> Ctx -> Sub -> Elem -> Elem -> Ty -> TypingRule
  ||| Γ ⊦ a = b : A₀
  ||| Γ ⊦ A₀ = A₁ type
  ||| -----------------
  ||| Γ ⊦ a = b : A₁
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
Show ComputeRule where
  show Here                    = "Here"
  show Id                      = "Id"
  show (InSubstElim a b)       = "InSubstElim (\{show a}) (\{show b})"
  show (InZeroElim a)          = "InZeroElim (\{show a})"
  show (InNatIntro1 a)         = "InNatIntro1 (\{show a})"
  show (InNatElim a b c)       = "InNatElim (\{show a}) (\{show b}) (\{show c})"
  show (InPiIntro a)           = "InPiIntro (\{show a})"
  show (InPiApp a b)           = "InPiApp (\{show a}) (\{show b})"
  show (InSigmaIntro a b)      = "InSigmaIntro (\{show a}) (\{show b})"
  show (InSigmaElim1 a)        = "InSigmaElim1 (\{show a})"
  show (InSigmaElim2 a)        = "InSigmaElim2 (\{show a})"
  show (InPiTy a b)            = "InPiTy (\{show a}) (\{show b})"
  show (InSigmaTy a b)         = "InSigmaTy (\{show a}) (\{show b})"
  show (InEqTy a b c)          = "InEqTy (\{show a}) (\{show b}) (\{show c})"
  show (InEl a)                = "InEl (\{show a})"
  show (InExt a b)             = "InExt (\{show a}) (\{show b})"
  show (Composition a b)       = "Composition (\{show a}) (\{show b})"

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
  show (ElemWfVar g ty)              = "ElemWfVar (\{showCtxRep g}) (\{show ty})"
  show (ElemWfZeroElim ctx e ty)     = "ElemWfZeroElim (\{showCtxRep ctx}) (\{show e}) (\{show ty})"
  show (ElemWfOneIntro ctx)          = "ElemWfOneIntro (\{showCtxRep ctx})"
  show (ElemWfZeroIntro ctx)         = "ElemWfZeroIntro (\{showCtxRep ctx})"
  show (ElemWfSucIntro ctx e)        = "ElemWfSucIntro (\{showCtxRep ctx}) (\{show e})"
  show (ElemWfNatElim ctx z s t ty)  = "ElemWfNatElim (\{showCtxRep ctx}) (\{show z}) (\{show s}) (\{show t}) (\{show ty})"
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
  show (ElemWfRefl ctx e ty)         = "ElemWfRefl (\{showCtxRep ctx}) (\{show e}) (\{show ty})"
  show (ElemWfSubElim t ty sigma gamma delta) = "ElemWfSubElim (\{show t}) (\{show ty}) (\{show sigma}) (\{showCtxRep gamma}) (\{showCtxRep delta})"
  show (ElemWfTyCoe ctx e ty0 ty1)   = "ElemWfTyCoe (\{showCtxRep ctx}) (\{show e}) (\{show ty0}) (\{show ty1})"
  show (ElemWfCtxCoe ctx0 ctx1 e ty) = "ElemWfCtxCoe (\{showCtxRep ctx0}) (\{showCtxRep ctx1}) (\{show e}) (\{show ty})"
  show (ElemWfSigVar x)               = "ElemWfSigVar \{show x}"
  show (ElemEqSigVar x)               = "ElemEqSigVar \{show x}"
  show (ElemEqSubstCong gamma delta sigma a b ty) = "ElemEqSubstCong (\{showCtxRep gamma}) (\{showCtxRep delta}) (\{show sigma}) (\{show a}) (\{show b}) (\{show ty})"
  show (ElemEqTyCoe ctx a b ty0 ty1)  = "ElemEqTyCoe (\{showCtxRep ctx}) (\{show a}) (\{show b}) (\{show ty0}) (\{show ty1})"
  show (SigExt gamma x a ty)          = "SigExt (\{showCtxRep gamma}) \{show x} (\{show a}) (\{show ty})"
  show (CtxWfCompute ctx cr)         = "CtxWfCompute (\{showCtxRep ctx}) (\{show cr})"
  show (TyWfCompute ctx a ty b)      = "TyWfCompute (\{showCtxRep ctx}) (\{show a}) (\{show ty}) (\{show b})"
  show (ElemWfCompute ctx a e b ty c) = "ElemWfCompute (\{showCtxRep ctx}) (\{show a}) (\{show e}) (\{show b}) (\{show ty}) (\{show c})"
  show (CtxEqRefl ctx)               = "CtxEqRefl (\{showCtxRep ctx})"
  show (CtxEqSym ctx0 ctx1)          = "CtxEqSym (\{showCtxRep ctx0}) (\{showCtxRep ctx1})"
  show (CtxEqTrans ctx0 ctx1 ctx2)   = "CtxEqTrans (\{showCtxRep ctx0}) (\{showCtxRep ctx1}) (\{showCtxRep ctx2})"
  show (SubWfTerminal ctx)             = "SubWfTerminal (\{showCtxRep ctx})"
  show (SubWfId ctx)                   = "SubWfId (\{showCtxRep ctx})"
  show (SubWfWk ctx ty)                = "SubWfWk (\{showCtxRep ctx}) (\{show ty})"
  show (SubWfExt sigma e gamma delta ty) = "SubWfExt (\{show sigma}) (\{show e}) (\{showCtxRep gamma}) (\{showCtxRep delta}) (\{show ty})"
  show (SubWfChain sigma tau gamma theta delta) = "SubWfChain (\{show sigma}) (\{show tau}) (\{showCtxRep gamma}) (\{showCtxRep theta}) (\{showCtxRep delta})"
  show (SubEqRefl s g d)             = "SubEqRefl (\{show s}) (\{showCtxRep g}) (\{showCtxRep d})"
  show (SubEqSym s0 s1 g d)          = "SubEqSym (\{show s0}) (\{show s1}) (\{showCtxRep g}) (\{showCtxRep d})"
  show (SubEqTrans s0 s1 s2 g d)     = "SubEqTrans (\{show s0}) (\{show s1}) (\{show s2}) (\{showCtxRep g}) (\{showCtxRep d})"
  show (TyEqRefl ctx ty)             = "TyEqRefl (\{showCtxRep ctx}) (\{show ty})"
  show (TyEqSym ctx ty0 ty1)         = "TyEqSym (\{showCtxRep ctx}) (\{show ty0}) (\{show ty1})"
  show (TyEqTrans ctx ty0 ty1 ty2)   = "TyEqTrans (\{showCtxRep ctx}) (\{show ty0}) (\{show ty1}) (\{show ty2})"
  show (ElemEqRefl ctx e ty)         = "ElemEqRefl (\{showCtxRep ctx}) (\{show e}) (\{show ty})"
  show (ElemEqSym ctx e0 e1 ty)      = "ElemEqSym (\{showCtxRep ctx}) (\{show e0}) (\{show e1}) (\{show ty})"
  show (ElemEqTrans ctx e0 e1 e2 ty) = "ElemEqTrans (\{showCtxRep ctx}) (\{show e0}) (\{show e1}) (\{show e2}) (\{show ty})"
  show (ElemEqReflection ctx a a0 a1 ty) = "ElemEqReflection (\{showCtxRep ctx}) (\{show a}) (\{show a0}) (\{show a1}) (\{show ty})"
  show (TelEqRefl ctx tel)           = "TelEqRefl (\{showCtxRep ctx}) (\{show tel})"
  show (TelEqSym ctx tel0 tel1)      = "TelEqSym (\{showCtxRep ctx}) (\{show tel0}) (\{show tel1})"
  show (TelEqTrans ctx tel0 tel1 tel2) = "TelEqTrans (\{showCtxRep ctx}) (\{show tel0}) (\{show tel1}) (\{show tel2})"
  show (SpineEqRefl ctx spine tel)       = "SpineEqRefl (\{showCtxRep ctx}) (\{show spine}) (\{show tel})"
  show (SpineEqSym ctx s0 s1 tel)        = "SpineEqSym (\{showCtxRep ctx}) (\{show s0}) (\{show s1}) (\{show tel})"
  show (SpineEqTrans ctx s0 s1 s2 tel)   = "SpineEqTrans (\{showCtxRep ctx}) (\{show s0}) (\{show s1}) (\{show s2}) (\{show tel})"

Rejection : Type
Rejection = ()

rejectUnless : Bool -> Either Rejection ()
rejectUnless True = Right ()
rejectUnless False = Left ()

export
ctxWfDerivable : Ctx -> Truth -> Either Rejection ()
ctxWfDerivable ctx sp = rejectUnless $ contains ctx sp.ctxWf

export
subWfDerivable : Sub -> Ctx -> Ctx -> Truth -> Either Rejection ()
subWfDerivable sigma gamma delta sp = rejectUnless $ contains (sigma, gamma, delta) sp.subWf

export
tyWfDerivable : Ctx -> Ty -> Truth -> Either Rejection ()
tyWfDerivable ctx ty sp = rejectUnless $ contains (ctx, ty) sp.tyWf

export
elemWfDerivable : Ctx -> Elem -> Ty -> Truth -> Either Rejection ()
elemWfDerivable ctx elem ty sp = rejectUnless $ contains (ctx, elem, ty) sp.elemWf

export
tyEqDerivable : Ctx -> Ty -> Ty -> Truth -> Either Rejection ()
tyEqDerivable ctx ty0 ty1 sp = rejectUnless $ contains (ctx, ty0, ty1) sp.tyEq

export
ctxEqDerivable : Ctx -> Ctx -> Truth -> Either Rejection ()
ctxEqDerivable ctx0 ctx1 sp = rejectUnless $ contains (ctx0, ctx1) sp.ctxEq

export
subEqDerivable : Sub -> Sub -> Ctx -> Ctx -> Truth -> Either Rejection ()
subEqDerivable s0 s1 g d sp = rejectUnless $ contains (s0, s1, g, d) sp.subEq

export
elemEqDerivable : Ctx -> Elem -> Elem -> Ty -> Truth -> Either Rejection ()
elemEqDerivable ctx e0 e1 ty sp = rejectUnless $ contains (ctx, e0, e1, ty) sp.elemEq

export
telWfDerivable : Ctx -> Tel -> Truth -> Either Rejection ()
telWfDerivable ctx tel sp = rejectUnless $ contains (ctx, tel) sp.telWf

export
telEqDerivable : Ctx -> Tel -> Tel -> Truth -> Either Rejection ()
telEqDerivable ctx t0 t1 sp = rejectUnless $ contains (ctx, t0, t1) sp.telEq

export
spineWfDerivable : Ctx -> Spine -> Tel -> Truth -> Either Rejection ()
spineWfDerivable ctx spine tel sp = rejectUnless $ contains (ctx, spine, tel) sp.spineWf

export
spineEqDerivable : Ctx -> Spine -> Spine -> Tel -> Truth -> Either Rejection ()
spineEqDerivable ctx s0 s1 tel sp = rejectUnless $ contains (ctx, s0, s1, tel) sp.spineEq

mutual
  sigLookup : SigIdentifier -> Sig -> Maybe SigEntry
  sigLookup _ [<] = Nothing
  sigLookup x (rest :< entry@(_, name, _, _)) =
    if name == x then Just entry else sigLookup x rest

  computeCtx : Sig -> ComputeRule -> Ctx -> Either Rejection Ctx
  computeCtx sig Id x = Right x
  computeCtx sig (InExt alpha beta) (gamma :< ty) = [| computeCtx sig alpha gamma :< computeTy sig beta ty |]
  computeCtx sig (Composition alpha beta) x = computeCtx sig alpha x >>= computeCtx sig beta
  computeCtx sig _ _ = Left ()

  computeTy : Sig -> ComputeRule -> Ty -> Either Rejection Ty
  computeTy sig Here (SubstElim ZeroTy _) = Right ZeroTy
  computeTy sig Here (SubstElim OneTy _) = Right OneTy
  computeTy sig Here (SubstElim NatTy _) = Right NatTy
  computeTy sig Here (SubstElim UniverseTy _) = Right UniverseTy
  computeTy sig Here (El ZeroTy) = Right ZeroTy
  computeTy sig Here (El OneTy) = Right OneTy
  computeTy sig Here (El NatTy) = Right NatTy
  computeTy sig Here (El (PiTy a b)) = Right (PiTy (El a) (El b))
  computeTy sig Here (El (SigmaTy a b)) = Right (SigmaTy (El a) (El b))
  computeTy sig Here (El (EqTy a b t)) = Right (EqTy a b (El t))
  computeTy sig Id x = Right x
  computeTy sig (InSubstElim alpha beta) (SubstElim ty sigma) = [| SubstElim (computeTy sig alpha ty) (computeSub sig beta sigma) |]
  computeTy sig (InPiTy alpha beta) (PiTy a b) = [| PiTy (computeTy sig alpha a) (computeTy sig beta b) |]
  computeTy sig (InSigmaTy alpha beta) (SigmaTy a b) = [| SigmaTy (computeTy sig alpha a) (computeTy sig beta b) |]
  computeTy sig (InEqTy alpha beta gamma) (EqTy l r ty) = [| EqTy (computeElem sig alpha l) (computeElem sig beta r) (computeTy sig gamma ty) |]
  computeTy sig (InEl alpha) (El ty) = [| El (computeElem sig alpha ty) |]
  computeTy sig (Composition alpha beta) x = computeTy sig alpha x >>= computeTy sig beta
  computeTy sig _ _ = Left ()

  computeSub : Sig -> ComputeRule -> Sub -> Either Rejection Sub
  computeSub sig Id sigma = Right sigma
  -- ↑ ∘ (σ, e) = σ
  computeSub sig Here (Chain Wk (Ext sigma _)) = Right sigma
  computeSub sig (Composition alpha beta) x = computeSub sig alpha x >>= computeSub sig beta
  computeSub sig _ _ = Left ()

  computeElem : Sig -> ComputeRule -> Elem -> Either Rejection Elem
  computeElem sig Id x = Right x
  computeElem sig Here (PiApp (PiIntro f) e)      = Right (SubstElim f (Ext Id e))
  computeElem sig Here (PiIntro (PiApp (SubstElim f Wk) CtxVar)) = Right f
  computeElem sig Here (NatElim z _ NatIntro0)     = Right z
  computeElem sig Here (NatElim z s (NatIntro1 t)) = Right (SubstElim s (Ext (Ext Id t) (NatElim z s t)))
  computeElem sig Here (SigmaElim1 (SigmaIntro a _)) = Right a
  computeElem sig Here (SigmaElim2 (SigmaIntro _ b)) = Right b
  computeElem sig Here (SigmaIntro (SigmaElim1 u) (SigmaElim2 v)) = do
    rejectUnless (u == v)
    Right u
  computeElem sig Here (SubstElim CtxVar (Ext _ t)) = Right t
  computeElem sig Here (SubstElim t Id) = Right t
  computeElem sig Here (SubstElim (SubstElim t sigma) tau) = Right (SubstElim t (Chain sigma tau))
  computeElem sig Here (SubstElim t (Chain sigma tau)) = Right (SubstElim (SubstElim t sigma) tau)
  computeElem sig Here (SubstElim (ZeroElim t) sigma) = Right (ZeroElim (SubstElim t sigma))
  computeElem sig Here (SubstElim OneIntro sigma) = Right OneIntro
  computeElem sig Here (SubstElim NatIntro0 sigma) = Right NatIntro0
  computeElem sig Here (SubstElim (NatIntro1 t) sigma) = Right (NatIntro1 (SubstElim t sigma))
  computeElem sig Here (SubstElim (NatElim z s t) sigma) =
    Right (NatElim (SubstElim z sigma) (SubstElim s (under (under sigma))) (SubstElim t sigma))
  computeElem sig Here (SubstElim (PiIntro f) sigma) = Right (PiIntro (SubstElim f (under sigma)))
  computeElem sig Here (SubstElim (PiApp f e) sigma) = Right (PiApp (SubstElim f sigma) (SubstElim e sigma))
  computeElem sig Here (SubstElim (SigmaIntro a b) sigma) = Right (SigmaIntro (SubstElim a sigma) (SubstElim b sigma))
  computeElem sig Here (SubstElim (SigmaElim1 t) sigma) = Right (SigmaElim1 (SubstElim t sigma))
  computeElem sig Here (SubstElim (SigmaElim2 t) sigma) = Right (SigmaElim2 (SubstElim t sigma))
  computeElem sig Here (SubstElim ZeroTy sigma) = Right ZeroTy
  computeElem sig Here (SubstElim OneTy sigma) = Right OneTy
  computeElem sig Here (SubstElim NatTy sigma) = Right NatTy
  computeElem sig Here (SubstElim (PiTy a b) sigma) = Right (PiTy (SubstElim a sigma) (SubstElim b (under sigma)))
  computeElem sig Here (SubstElim (SigmaTy a b) sigma) = Right (SigmaTy (SubstElim a sigma) (SubstElim b (under sigma)))
  computeElem sig Here (SubstElim (EqTy l r ty) sigma) = Right (EqTy (SubstElim l sigma) (SubstElim r sigma) (SubstElim ty sigma))
  computeElem sig Here (SubstElim Refl sigma) = Right Refl
  computeElem sig Here (SigVar x) =
    case sigLookup x sig of
      Nothing => Left ()
      Just (_, _, a, _) => Right a
  computeElem sig (InSubstElim alpha beta) (SubstElim t sigma) = [| SubstElim (computeElem sig alpha t) (computeSub sig beta sigma) |]
  computeElem sig (InZeroElim alpha) (ZeroElim t) = [| ZeroElim (computeElem sig alpha t) |]
  computeElem sig (InNatIntro1 alpha) (NatIntro1 t) = [| NatIntro1 (computeElem sig alpha t) |]
  computeElem sig (InNatElim alpha beta gamma) (NatElim z s t) = [| NatElim (computeElem sig alpha z) (computeElem sig beta s) (computeElem sig gamma t) |]
  computeElem sig (InPiIntro alpha) (PiIntro f) = [| PiIntro (computeElem sig alpha f) |]
  computeElem sig (InPiApp alpha beta) (PiApp f e) = [| PiApp (computeElem sig alpha f) (computeElem sig beta e) |]
  computeElem sig (InSigmaIntro alpha beta) (SigmaIntro a b) = [| SigmaIntro (computeElem sig alpha a) (computeElem sig beta b) |]
  computeElem sig (InSigmaElim1 alpha) (SigmaElim1 t) = [| SigmaElim1 (computeElem sig alpha t) |]
  computeElem sig (InSigmaElim2 alpha) (SigmaElim2 t) = [| SigmaElim2 (computeElem sig alpha t) |]
  computeElem sig (InPiTy alpha beta) (PiTy a b) = [| PiTy (computeElem sig alpha a) (computeElem sig beta b) |]
  computeElem sig (InSigmaTy alpha beta) (SigmaTy a b) = [| SigmaTy (computeElem sig alpha a) (computeElem sig beta b) |]
  computeElem sig (InEqTy alpha beta gamma) (EqTy l r ty) = [| EqTy (computeElem sig alpha l) (computeElem sig beta r) (computeElem sig gamma ty) |]
  computeElem sig (Composition alpha beta) x = computeElem sig alpha x >>= computeElem sig beta
  computeElem sig _ _ = Left ()

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
step CtxWfEmpty sp = Right $ {ctxWf $= insert [<]} sp
step (CtxWfExt gamma ty) sp = do
  tyWfDerivable gamma ty sp
  Right $ {ctxWf $= insert (gamma :< ty)} sp
step (CtxWfCompute gamma rule) sp = do
  ctxWfDerivable gamma sp
  gamma' <- computeCtx sp.sig rule gamma
  Right $ {ctxWf $= insert gamma', ctxEq $= insert (gamma, gamma')} sp
step (TyWfCompute gamma alpha ty beta) sp = do
  tyWfDerivable gamma ty sp
  gamma' <- computeCtx sp.sig alpha gamma
  ty' <- computeTy sp.sig beta ty
  Right $ {ctxWf $= insert gamma', ctxEq $= insert (gamma, gamma'),
           tyWf $= insert (gamma', ty'), tyEq $= insert (gamma', ty, ty')} sp
step (ElemWfCompute gamma alpha t beta ty zeta) sp = do
  elemWfDerivable gamma t ty sp
  gamma' <- computeCtx sp.sig alpha gamma
  t' <- computeElem sp.sig beta t
  ty' <- computeTy sp.sig zeta ty
  Right $ {ctxWf $= insert gamma', ctxEq $= insert (gamma, gamma'),
           tyWf $= insert (gamma', ty'), tyEq $= insert (gamma', ty, ty'),
           elemWf $= insert (gamma', t', ty'), elemEq $= insert (gamma', t, t', ty')} sp
step (TyWfZero gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {tyWf $= insert (gamma, ZeroTy)} sp
step (TyWfOne gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {tyWf $= insert (gamma, OneTy)} sp
step (TyWfNat gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {tyWf $= insert (gamma, NatTy)} sp
step (TyWfUniverse gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {tyWf $= insert (gamma, UniverseTy)} sp
step (TyWfPi gamma a b) sp = do
  tyWfDerivable (gamma :< a) b sp
  Right $ {tyWf $= insert (gamma, PiTy a b)} sp
step (TyWfSigma gamma a b) sp = do
  tyWfDerivable (gamma :< a) b sp
  Right $ {tyWf $= insert (gamma, SigmaTy a b)} sp
step (TyWfEq gamma left right ty) sp = do
  elemWfDerivable gamma left ty sp
  elemWfDerivable gamma right ty sp
  Right $ {tyWf $= insert (gamma, EqTy left right ty)} sp
step (TyWfEl gamma t) sp = do
  elemWfDerivable gamma t UniverseTy sp
  Right $ {tyWf $= insert (gamma, El t)} sp
step (ElemWfVar gamma ty) sp = do
  tyWfDerivable gamma ty sp
  Right $ {elemWf $= insert (gamma :< ty, CtxVar, SubstElim ty Wk)} sp
step (ElemWfZeroElim gamma t ty) sp = do
  tyWfDerivable gamma ty sp
  elemWfDerivable gamma t ZeroTy sp
  Right $ {elemWf $= insert (gamma, ZeroElim t, ty)} sp
step (ElemWfOneIntro gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {elemWf $= insert (gamma, OneIntro, OneTy)} sp
step (ElemWfZeroIntro gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {elemWf $= insert (gamma, NatIntro0, NatTy)} sp
step (ElemWfSucIntro gamma t) sp = do
  elemWfDerivable gamma t NatTy sp
  Right $ {elemWf $= insert (gamma, NatIntro1 t, NatTy)} sp
step (ElemWfNatElim gamma z s t a) sp = do
  -- tyWfDerivable (gamma :< NatTy) a sp
  elemWfDerivable gamma z (SubstElim a (Ext Id NatIntro0)) sp
  elemWfDerivable (gamma :< NatTy :< a) s (SubstElim a (Chain (Ext Wk (NatIntro1 CtxVar)) Wk)) sp
  elemWfDerivable gamma t NatTy sp
  Right $ {elemWf $= insert (gamma, NatElim z s t, SubstElim a (Ext Id t))} sp
step (ElemWfPiIntro gamma f a b) sp = do
  elemWfDerivable (gamma :< a) f b sp
  Right $ {elemWf $= insert (gamma, PiIntro f, PiTy a b)} sp
step (ElemWfPiApp gamma f a b e) sp = do
  elemWfDerivable gamma f (PiTy a b) sp
  elemWfDerivable gamma e a sp
  Right $ {elemWf $= insert (gamma, PiApp f e, SubstElim b (Ext Id e))} sp
step (ElemWfSigmaIntro gamma u v a b) sp = do
  elemWfDerivable gamma u a sp
  elemWfDerivable gamma v (SubstElim b (Ext Id u)) sp
  Right $ {elemWf $= insert (gamma, SigmaIntro u v, PiTy a b)} sp
step (ElemWfSigmaElim1 gamma t a b) sp = do
  elemWfDerivable gamma t (SigmaTy a b) sp
  Right $ {elemWf $= insert (gamma, SigmaElim1 t, a)} sp
step (ElemWfSigmaElim2 gamma t a b) sp = do
  elemWfDerivable gamma t (SigmaTy a b) sp
  Right $ {elemWf $= insert (gamma, SigmaElim2 t, SubstElim b (Ext Id (SigmaElim1 t)))} sp
step (ElemWfZeroTy gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {elemWf $= insert (gamma, ZeroTy, UniverseTy)} sp
step (ElemWfOneTy gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {elemWf $= insert (gamma, OneTy, UniverseTy)} sp
step (ElemWfNatTy gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {elemWf $= insert (gamma, NatTy, UniverseTy)} sp
step (ElemWfPiTy gamma a b) sp = do
  elemWfDerivable (gamma :< El a) b UniverseTy sp
  Right $ {elemWf $= insert (gamma, PiTy a b, UniverseTy)} sp
step (ElemWfSigmaTy gamma a b) sp = do
  elemWfDerivable (gamma :< El a) b UniverseTy sp
  Right $ {elemWf $= insert (gamma, SigmaTy a b, UniverseTy)} sp
step (ElemWfEqTy gamma l r ty) sp = do
  elemWfDerivable gamma l (El ty) sp
  elemWfDerivable gamma r (El ty) sp
  Right $ {elemWf $= insert (gamma, EqTy l r ty, UniverseTy)} sp
step (ElemWfRefl gamma e ty) sp = do
  elemWfDerivable gamma e ty sp
  Right $ {elemWf $= insert (gamma, Refl, EqTy e e ty)} sp
-- Δ ⊦ t : A
-- σ : Γ ⇒ Δ
-- ---------------
-- Γ ⊦ t(σ) : A(σ)
step (ElemWfSubElim t ty sigma gamma delta) sp = do
  subWfDerivable sigma gamma delta sp
  elemWfDerivable delta t ty sp
  Right $ {elemWf $= insert (gamma, SubstElim t sigma, SubstElim ty sigma)} sp
-- Γ ⊦ a : A₀
-- Γ ⊦ A₀ = A₁ type
-- ----------------
-- Γ ⊦ a : A₁
step (ElemWfTyCoe ctx e ty0 ty1) sp = do
  elemWfDerivable ctx e ty0 sp
  tyEqDerivable ctx ty0 ty1 sp
  Right $ {elemWf $= insert (ctx, e, ty1)} sp
-- Γ₀ ⊦ a : A
-- Γ₀ = Γ₁ ctx
-- ------------
-- Γ₁ ⊦ a : A
step (ElemWfCtxCoe ctx0 ctx1 e ty) sp = do
  elemWfDerivable ctx0 e ty sp
  ctxEqDerivable ctx0 ctx1 sp
  Right $ {elemWf $= insert (ctx1, e, ty)} sp
step (ElemWfSigVar x) sp =
  case sigLookup x sp.sig of
    Nothing => Left ()
    Just (gamma, _, _, ty) => Right $ {elemWf $= insert (gamma, SigVar x, ty)} sp
step (ElemEqSigVar x) sp =
  case sigLookup x sp.sig of
    Nothing => Left ()
    Just (gamma, _, a, ty) => Right $ {elemEq $= insert (gamma, SigVar x, a, ty)} sp
-- Γ ⊦ a = b : A
-- σ : Δ ⇒ Γ
-- -------------------------
-- Δ ⊦ a(σ) = b(σ) : A(σ)
step (ElemEqSubstCong gamma delta sigma a b ty) sp = do
  subWfDerivable sigma delta gamma sp
  elemEqDerivable gamma a b ty sp
  Right $ {elemEq $= insert (delta, SubstElim a sigma, SubstElim b sigma, SubstElim ty sigma)} sp
-- Γ ⊦ a = b : A₀
-- Γ ⊦ A₀ = A₁ type
-- -----------------
-- Γ ⊦ a = b : A₁
step (ElemEqTyCoe ctx a b ty0 ty1) sp = do
  elemEqDerivable ctx a b ty0 sp
  tyEqDerivable ctx ty0 ty1 sp
  Right $ {elemEq $= insert (ctx, a, b, ty1)} sp
step (SigExt gamma x a ty) sp = do
  elemWfDerivable gamma a ty sp
  case sigLookup x sp.sig of
    Just _  => Left ()
    Nothing => Right $ {sig $= (:< (gamma, x, a, ty))} sp
step (CtxEqRefl ctx) sp = do
  ctxWfDerivable ctx sp
  Right $ {ctxEq $= insert (ctx, ctx)} sp
step (CtxEqSym ctx0 ctx1) sp = do
  ctxEqDerivable ctx0 ctx1 sp
  Right $ {ctxEq $= insert (ctx1, ctx0)} sp
step (CtxEqTrans ctx0 ctx1 ctx2) sp = do
  ctxEqDerivable ctx0 ctx1 sp
  ctxEqDerivable ctx1 ctx2 sp
  Right $ {ctxEq $= insert (ctx0, ctx2)} sp
step (SubWfTerminal gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {subWf $= insert (Terminal, gamma, [<])} sp
step (SubWfId gamma) sp = do
  ctxWfDerivable gamma sp
  Right $ {subWf $= insert (Id, gamma, gamma)} sp
step (SubWfWk gamma ty) sp = do
  tyWfDerivable gamma ty sp
  Right $ {subWf $= insert (Wk, gamma :< ty, gamma)} sp
step (SubWfExt sigma e gamma delta ty) sp = do
  subWfDerivable sigma gamma delta sp
  tyWfDerivable delta ty sp
  elemWfDerivable gamma e (SubstElim ty sigma) sp
  Right $ {subWf $= insert (Ext sigma e, gamma, delta :< ty)} sp
step (SubWfChain sigma tau gamma theta delta) sp = do
  subWfDerivable sigma gamma theta sp
  subWfDerivable tau theta delta sp
  Right $ {subWf $= insert (Chain sigma tau, gamma, delta)} sp
step (SubEqRefl s g d) sp = do
  subWfDerivable s g d sp
  Right $ {subEq $= insert (s, s, g, d)} sp
step (SubEqSym s0 s1 g d) sp = do
  subEqDerivable s0 s1 g d sp
  Right $ {subEq $= insert (s1, s0, g, d)} sp
step (SubEqTrans s0 s1 s2 g d) sp = do
  subEqDerivable s0 s1 g d sp
  subEqDerivable s1 s2 g d sp
  Right $ {subEq $= insert (s0, s2, g, d)} sp
step (TyEqRefl ctx ty) sp = do
  tyWfDerivable ctx ty sp
  Right $ {tyEq $= insert (ctx, ty, ty)} sp
step (TyEqSym ctx ty0 ty1) sp = do
  tyEqDerivable ctx ty0 ty1 sp
  Right $ {tyEq $= insert (ctx, ty1, ty0)} sp
step (TyEqTrans ctx ty0 ty1 ty2) sp = do
  tyEqDerivable ctx ty0 ty1 sp
  tyEqDerivable ctx ty1 ty2 sp
  Right $ {tyEq $= insert (ctx, ty0, ty2)} sp
step (ElemEqRefl ctx e ty) sp = do
  elemWfDerivable ctx e ty sp
  Right $ {elemEq $= insert (ctx, e, e, ty)} sp
step (ElemEqSym ctx e0 e1 ty) sp = do
  elemEqDerivable ctx e0 e1 ty sp
  Right $ {elemEq $= insert (ctx, e1, e0, ty)} sp
step (ElemEqTrans ctx e0 e1 e2 ty) sp = do
  elemEqDerivable ctx e0 e1 ty sp
  elemEqDerivable ctx e1 e2 ty sp
  Right $ {elemEq $= insert (ctx, e0, e2, ty)} sp
step (ElemEqReflection ctx a a0 a1 ty) sp = do
  elemWfDerivable ctx a (EqTy a0 a1 ty) sp
  Right $ {elemEq $= insert (ctx, a0, a1, ty)} sp
step (TelEqRefl ctx tel) sp = do
  telWfDerivable ctx tel sp
  Right $ {telEq $= insert (ctx, tel, tel)} sp
step (TelEqSym ctx tel0 tel1) sp = do
  telEqDerivable ctx tel0 tel1 sp
  Right $ {telEq $= insert (ctx, tel1, tel0)} sp
step (TelEqTrans ctx tel0 tel1 tel2) sp = do
  telEqDerivable ctx tel0 tel1 sp
  telEqDerivable ctx tel1 tel2 sp
  Right $ {telEq $= insert (ctx, tel0, tel2)} sp
step (SpineEqRefl ctx spine tel) sp = do
  spineWfDerivable ctx spine tel sp
  Right $ {spineEq $= insert (ctx, spine, spine, tel)} sp
step (SpineEqSym ctx s0 s1 tel) sp = do
  spineEqDerivable ctx s0 s1 tel sp
  Right $ {spineEq $= insert (ctx, s1, s0, tel)} sp
step (SpineEqTrans ctx s0 s1 s2 tel) sp = do
  spineEqDerivable ctx s0 s1 tel sp
  spineEqDerivable ctx s1 s2 tel sp
  Right $ {spineEq $= insert (ctx, s0, s2, tel)} sp

public export
record ContextualRejection where
  constructor MkContextualRejection
  truth : Truth
  rule : TypingRule

export
steps : List TypingRule -> Truth -> Either ContextualRejection Truth
steps [] truth = Right truth
steps (s :: ss) truth = do
  truth <- mapFst (const $ MkContextualRejection truth s) $ step s truth
  steps ss truth

export
generate : List TypingRule -> Either ContextualRejection Truth
generate ss = steps ss trivial

export
check : JudgementForm -> Truth -> Bool
check (JfCtxWf ctx)       t = contains ctx t.ctxWf
check (JfCtxEq ctxeq)     t = contains ctxeq t.ctxEq
check (JfTyWf tywf)       t = contains tywf t.tyWf
check (JfTyEq tyeq)       t = contains tyeq t.tyEq
check (JfSubWf subwf)     t = contains subwf t.subWf
check (JfSubEq subeq)     t = contains subeq t.subEq
check (JfElemWf ewf)      t = contains ewf t.elemWf
check (JfElemEq eeq)      t = contains eeq t.elemEq
check (JfTelWf telwf)     t = contains telwf t.telWf
check (JfTelEq teleq)     t = contains teleq t.telEq
check (JfSpineWf spinewf) t = contains spinewf t.spineWf
check (JfSpineEq spineeq) t = contains spineeq t.spineEq
