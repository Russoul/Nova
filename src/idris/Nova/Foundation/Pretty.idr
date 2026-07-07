module Nova.Foundation.Pretty

import Data.SnocList
import Nova.Foundation.Syntax
import Nova.Foundation.Derivation

%default covering

-- ===== Sub and Elem (mutually recursive) =====

mutual
  export
  prettySub : Sub -> String
  prettySub (Ext s e) = prettySub s ++ ", " ++ prettyElemNoComma e
  prettySub s = prettySubChain s

  prettySubChain : Sub -> String
  prettySubChain (Chain s t) = prettySubAtom s ++ " ∘ " ++ prettySubChain t
  prettySubChain s = prettySubAtom s

  prettySubAtom : Sub -> String
  prettySubAtom Terminal = "·"
  prettySubAtom Id = "id"
  prettySubAtom Wk = "↑"
  prettySubAtom s = "(" ++ prettySub s ++ ")"

  export
  prettyElem : Elem -> String
  prettyElem (SigmaIntro e e') = prettyElemNoComma e ++ ", " ++ prettyElem e'
  prettyElem e = prettyElemNoComma e

  export
  prettyElemNoComma : Elem -> String
  prettyElemNoComma (Elem.PiTy e e') = prettyElemPrefix e ++ " → " ++ prettyElemNoComma e'
  prettyElemNoComma (Elem.SigmaTy e e') = prettyElemPrefix e ++ " ⨯ " ++ prettyElemNoComma e'
  prettyElemNoComma (Elem.EqTy e0 e1 e2) =
    prettyElemPrefix e0 ++ " ≡ " ++ prettyElemPrefix e1 ++ " ∈ " ++ prettyElemPrefix e2
  prettyElemNoComma e = prettyElemPrefix e

  prettyElemPrefix : Elem -> String
  prettyElemPrefix (PiIntro e) = "λ " ++ prettyElemAtom e
  prettyElemPrefix (ZeroElim e) = "𝟘-elim " ++ prettyElemAtom e
  prettyElemPrefix (NatIntro1 e) = "S " ++ prettyElemAtom e
  prettyElemPrefix (NatElim z s t) =
    "ℕ-elim " ++ prettyElemAtom z ++ " " ++ prettyElemAtom s ++ " " ++ prettyElemAtom t
  prettyElemPrefix e = prettyElemPostfix e

  prettyElemPostfix : Elem -> String
  prettyElemPostfix (SigmaElim1 e) = prettyElemPostfix e ++ " .π₁"
  prettyElemPostfix (SigmaElim2 e) = prettyElemPostfix e ++ " .π₂"
  prettyElemPostfix (PiElim e) = prettyElemPostfix e ++ " @"
  prettyElemPostfix (SubstElim e s) = prettyElemPostfix e ++ "[" ++ prettySub s ++ "]"
  prettyElemPostfix e = prettyElemAtom e

  export
  prettyElemAtom : Elem -> String
  prettyElemAtom CtxVar = "☐"
  prettyElemAtom OneIntro = "()"
  prettyElemAtom NatIntro0 = "Z"
  prettyElemAtom Refl = "Refl"
  prettyElemAtom Elem.ZeroTy = "𝟘"
  prettyElemAtom Elem.OneTy = "𝟙"
  prettyElemAtom Elem.NatTy = "ℕ"
  prettyElemAtom (SigVar x) = x
  prettyElemAtom e = "(" ++ prettyElem e ++ ")"

-- ===== Ty =====

mutual
  export
  prettyTy : Ty -> String
  prettyTy (Ty.EqTy e0 e1 a) =
    prettyElemAtom e0 ++ " ≡ " ++ prettyElemAtom e1 ++ " ∈ " ++ prettyTyArrow a
  prettyTy ty = prettyTyArrow ty

  prettyTyArrow : Ty -> String
  prettyTyArrow (Ty.PiTy a b) = prettyTyEl a ++ " → " ++ prettyTyArrow b
  prettyTyArrow (Ty.SigmaTy a b) = prettyTyEl a ++ " ⨯ " ++ prettyTyArrow b
  prettyTyArrow ty = prettyTyEl ty

  prettyTyEl : Ty -> String
  prettyTyEl (El e) = "El " ++ prettyElemAtom e
  prettyTyEl ty = prettyTyPostfix ty

  prettyTyPostfix : Ty -> String
  prettyTyPostfix (Ty.SubstElim ty s) = prettyTyPostfix ty ++ "[" ++ prettySub s ++ "]"
  prettyTyPostfix ty = prettyTyAtom ty

  prettyTyAtom : Ty -> String
  prettyTyAtom Ty.ZeroTy = "𝟘"
  prettyTyAtom Ty.OneTy = "𝟙"
  prettyTyAtom Ty.NatTy = "ℕ"
  prettyTyAtom Ty.UniverseTy = "𝕌"
  prettyTyAtom ty = "(" ++ prettyTy ty ++ ")"

-- ===== Ctx, Tel, Spine =====

export
prettyCtx : Ctx -> String
prettyCtx [<] = "ε"
prettyCtx ctx = go ctx
  where
    go : Ctx -> String
    go [<] = "ε"
    go (g :< ty) = go g ++ " ᐅ " ++ prettyTy ty

export
prettyTel : Tel -> String
prettyTel [] = "ε"
prettyTel (ty :: rest) = prettyTy ty ++ " ◁ " ++ prettyTel rest

export
prettySpine : Spine -> String
prettySpine [] = "·"
prettySpine (e :: es) = prettyElemNoComma e ++ go es
  where
    go : Spine -> String
    go [] = ""
    go (e' :: es') = ", " ++ prettyElemNoComma e' ++ go es'

-- ===== ComputeRule =====

mutual
  export
  prettyComputeRule : ComputeRule -> String
  prettyComputeRule (Composition a b) = prettyComputeRule a ++ "; " ++ prettyComputeRule b
  prettyComputeRule (InSigmaIntro a b) = prettyComputeNoComma a ++ ", " ++ prettyComputeRule b
  prettyComputeRule cr = prettyComputeNoComma cr

  prettyComputeNoComma : ComputeRule -> String
  prettyComputeNoComma (InPiTy a b) = prettyComputePrefix a ++ " → " ++ prettyComputeNoComma b
  prettyComputeNoComma (InSigmaTy a b) = prettyComputePrefix a ++ " ⨯ " ++ prettyComputeNoComma b
  prettyComputeNoComma (InEqTy a b c) =
    prettyComputePrefix a ++ " ≡ " ++ prettyComputePostfix b ++ " ∈ " ++ prettyComputePostfix c
  prettyComputeNoComma (InExt a b) = prettyComputePrefix a ++ " ᐅ " ++ prettyComputeNoComma b
  prettyComputeNoComma cr = prettyComputePrefix cr

  prettyComputePrefix : ComputeRule -> String
  prettyComputePrefix (InPiIntro a) = "λ " ++ prettyComputeAtom a
  prettyComputePrefix (InZeroElim a) = "𝟘-elim " ++ prettyComputeAtom a
  prettyComputePrefix (InNatIntro1 a) = "S " ++ prettyComputeAtom a
  prettyComputePrefix (InNatElim a b c) =
    "ℕ-elim " ++ prettyComputeAtom a ++ " " ++ prettyComputeAtom b ++ " " ++ prettyComputeAtom c
  prettyComputePrefix (InEl a) = "El " ++ prettyComputeAtom a
  prettyComputePrefix cr = prettyComputePostfix cr

  prettyComputePostfix : ComputeRule -> String
  prettyComputePostfix (InSigmaElim1 a) = prettyComputePostfix a ++ " .π₁"
  prettyComputePostfix (InSigmaElim2 a) = prettyComputePostfix a ++ " .π₂"
  prettyComputePostfix (InPiElim a) = prettyComputePostfix a ++ " @"
  prettyComputePostfix (InSubstElim a b) = prettyComputePostfix a ++ " [" ++ prettyComputeRule b ++ "]"
  prettyComputePostfix cr = prettyComputeAtom cr

  prettyComputeAtom : ComputeRule -> String
  prettyComputeAtom Here = "↓"
  prettyComputeAtom Id = "id"
  prettyComputeAtom cr = "(" ++ prettyComputeRule cr ++ ")"

-- ===== Judgement forms =====
-- (Use concrete underlying types since Idris2 does not reduce type aliases for unification.)

export
prettyCtxWf : Ctx -> String
prettyCtxWf ctx = prettyCtx ctx ++ " ctx"

export
prettyCtxEq : (Ctx, Ctx) -> String
prettyCtxEq (g0, g1) = prettyCtx g0 ++ " = " ++ prettyCtx g1 ++ " ctx"

export
prettyTyWf : (Ctx, Ty) -> String
prettyTyWf (ctx, ty) = prettyCtx ctx ++ " ⊦ " ++ prettyTy ty ++ " type"

export
prettyTyEq : (Ctx, Ty, Ty) -> String
prettyTyEq (ctx, a, b) = prettyCtx ctx ++ " ⊦ " ++ prettyTy a ++ " = " ++ prettyTy b ++ " type"

export
prettySubWf : (Sub, Ctx, Ctx) -> String
prettySubWf (s, g, d) = prettySub s ++ " : " ++ prettyCtx g ++ " ⇒ " ++ prettyCtx d

export
prettySubEq : (Sub, Sub, Ctx, Ctx) -> String
prettySubEq (s0, s1, g, d) =
  prettySub s0 ++ " = " ++ prettySub s1 ++ " : " ++ prettyCtx g ++ " ⇒ " ++ prettyCtx d

export
prettyElemWf : (Ctx, Elem, Ty) -> String
prettyElemWf (ctx, e, ty) = prettyCtx ctx ++ " ⊦ " ++ prettyElem e ++ " : " ++ prettyTy ty

export
prettyElemEq : (Ctx, Elem, Elem, Ty) -> String
prettyElemEq (ctx, e0, e1, ty) =
  prettyCtx ctx ++ " ⊦ " ++ prettyElem e0 ++ " = " ++ prettyElem e1 ++ " : " ++ prettyTy ty

export
prettyTelWf : (Ctx, Tel) -> String
prettyTelWf (ctx, tel) = prettyCtx ctx ++ " ⊦ " ++ prettyTel tel ++ " tel"

export
prettyTelEq : (Ctx, Tel, Tel) -> String
prettyTelEq (ctx, t0, t1) =
  prettyCtx ctx ++ " ⊦ " ++ prettyTel t0 ++ " = " ++ prettyTel t1 ++ " tel"

export
prettySpineWf : (Ctx, Spine, Tel) -> String
prettySpineWf (ctx, spine, tel) =
  prettyCtx ctx ++ " ⊦ " ++ prettySpine spine ++ " : " ++ prettyTel tel

export
prettySpineEq : (Ctx, Spine, Spine, Tel) -> String
prettySpineEq (ctx, s0, s1, tel) =
  prettyCtx ctx ++ " ⊦ " ++ prettySpine s0 ++ " = " ++ prettySpine s1 ++ " : " ++ prettyTel tel

-- ===== TypingRule =====

export
prettyTypingRule : TypingRule -> String
prettyTypingRule CtxWfEmpty =
  "ε ctx"
prettyTypingRule (CtxWfExt g ty) =
  prettyCtx (g :< ty) ++ " ctx"
prettyTypingRule (TyWfZero ctx) =
  prettyCtx ctx ++ " ⊦ 𝟘 type"
prettyTypingRule (TyWfOne ctx) =
  prettyCtx ctx ++ " ⊦ 𝟙 type"
prettyTypingRule (TyWfNat ctx) =
  prettyCtx ctx ++ " ⊦ ℕ type"
prettyTypingRule (TyWfUniverse ctx) =
  prettyCtx ctx ++ " ⊦ 𝕌 type"
prettyTypingRule (TyWfPi ctx a b) =
  prettyCtx ctx ++ " ⊦ " ++ prettyTy (PiTy a b) ++ " type"
prettyTypingRule (TyWfSigma ctx a b) =
  prettyCtx ctx ++ " ⊦ " ++ prettyTy (SigmaTy a b) ++ " type"
prettyTypingRule (TyWfEq ctx l r ty) =
  prettyCtx ctx ++ " ⊦ " ++ prettyTy (EqTy l r ty) ++ " type"
prettyTypingRule (TyWfEl ctx e) =
  prettyCtx ctx ++ " ⊦ " ++ prettyTy (El e) ++ " type"
prettyTypingRule (ElemWfVar g ty) =
  prettyCtx (g :< ty) ++ " ⊦ ☐"
prettyTypingRule (ElemWfZeroElim ctx e ty) =
  prettyCtx ctx ++ " ⊦ " ++ prettyElem (ZeroElim e) ++ " : " ++ prettyTy ty
prettyTypingRule (ElemWfOneIntro ctx) =
  prettyCtx ctx ++ " ⊦ ()"
prettyTypingRule (ElemWfZeroIntro ctx) =
  prettyCtx ctx ++ " ⊦ Z"
prettyTypingRule (ElemWfSucIntro ctx e) =
  prettyCtx ctx ++ " ⊦ " ++ prettyElem (NatIntro1 e)
prettyTypingRule (ElemWfNatElim ctx z s t ty) =
  prettyCtx ctx ++ " ⊦ " ++ prettyElem (NatElim z s t) ++ " : " ++ prettyTy ty
prettyTypingRule (ElemWfPiIntro ctx f a b) =
  prettyCtx ctx ++ " ⊦ " ++ prettyElem (PiIntro f) ++ " : " ++ prettyTy (PiTy a b)
prettyTypingRule (ElemWfPiElim g a f b) =
  prettyCtx (g :< a) ++ " ⊦ " ++ prettyElem (PiElim f) ++ " : " ++ prettyTy b
prettyTypingRule (ElemWfSigmaIntro ctx u v a b) =
  prettyCtx ctx ++ " ⊦ " ++ prettyElem (SigmaIntro u v) ++ " : " ++ prettyTy (SigmaTy a b)
prettyTypingRule (ElemWfSigmaElim1 ctx e a b) =
  prettyCtx ctx ++ " ⊦ (" ++ prettyElem e ++ " : " ++ prettyTy (SigmaTy a b) ++ ") .π₁"
prettyTypingRule (ElemWfSigmaElim2 ctx e a b) =
  prettyCtx ctx ++ " ⊦ (" ++ prettyElem e ++ " : " ++ prettyTy (SigmaTy a b) ++ ") .π₂"
prettyTypingRule (ElemWfZeroTy ctx) =
  prettyCtx ctx ++ " ⊦ 𝟘"
prettyTypingRule (ElemWfOneTy ctx) =
  prettyCtx ctx ++ " ⊦ 𝟙"
prettyTypingRule (ElemWfNatTy ctx) =
  prettyCtx ctx ++ " ⊦ ℕ"
prettyTypingRule (ElemWfPiTy ctx a b) =
  prettyCtx ctx ++ " ⊦ " ++ prettyElem (Elem.PiTy a b)
prettyTypingRule (ElemWfSigmaTy ctx a b) =
  prettyCtx ctx ++ " ⊦ " ++ prettyElem (Elem.SigmaTy a b)
prettyTypingRule (ElemWfEqTy ctx l r ty) =
  prettyCtx ctx ++ " ⊦ " ++ prettyElem (Elem.EqTy l r ty)
prettyTypingRule (ElemWfRefl ctx e ty) =
  prettyCtx ctx ++ " ⊦ Refl : " ++ prettyElemAtom e ++ " ∈ " ++ prettyTy ty
prettyTypingRule (ElemWfSubElim t ty sigma gamma delta) =
  prettyCtx gamma ++ " ⊦ " ++ prettyElem (SubstElim t sigma) ++ " : " ++ prettyTy ty ++ " from " ++ prettyCtx delta
prettyTypingRule (ElemWfTyCoe ctx e ty0 ty1) =
  prettyCtx ctx ++ " ⊦ " ++ prettyElem e ++ " : " ++ prettyTy ty0 ++ " ↝ " ++ prettyTy ty1
prettyTypingRule (ElemWfCtxCoe ctx0 ctx1 e ty) =
  prettyCtx ctx0 ++ " = " ++ prettyCtx ctx1 ++ " ⊦ " ++ prettyElem e ++ " : " ++ prettyTy ty
prettyTypingRule (ElemWfSigVar x) = x
prettyTypingRule (ElemEqSigVar x) = x ++ " ="
prettyTypingRule (ElemEqSubstCong gamma delta sigma a b ty) =
  prettyCtx delta ++ " ⊦ " ++ prettyElem (SubstElim a sigma) ++ " = " ++ prettyElem (SubstElim b sigma) ++ " : " ++ prettyTy (SubstElim ty sigma) ++ " from " ++ prettyCtx gamma
prettyTypingRule (ElemEqTyCoe ctx a b ty0 ty1) =
  prettyCtx ctx ++ " ⊦ " ++ prettyElem a ++ " = " ++ prettyElem b ++ " : " ++ prettyTy ty0 ++ " ↝ " ++ prettyTy ty1
prettyTypingRule (SigExt gamma x a ty) =
  prettyCtx gamma ++ " ⊦ " ++ x ++ " ≔ " ++ prettyElem a ++ " : " ++ prettyTy ty
prettyTypingRule (CtxWfCompute ctx alpha) =
  prettyCtx ctx ++ " | " ++ prettyComputeRule alpha ++ " ctx"
prettyTypingRule (TyWfCompute ctx alpha ty beta) =
  prettyCtx ctx ++ " | " ++ prettyComputeRule alpha ++
  " ⊦ " ++ prettyTy ty ++ " | " ++ prettyComputeRule beta ++ " type"
prettyTypingRule (ElemWfCompute ctx alpha e beta ty gamma) =
  prettyCtx ctx ++ " | " ++ prettyComputeRule alpha ++
  " ⊦ " ++ prettyElem e ++ " | " ++ prettyComputeRule beta ++
  " : " ++ prettyTy ty ++ " | " ++ prettyComputeRule gamma ++ " type"
prettyTypingRule (CtxEqRefl ctx) =
  prettyCtx ctx ++ " = " ++ prettyCtx ctx ++ " ctx"
prettyTypingRule (CtxEqSym ctx0 ctx1) =
  prettyCtx ctx1 ++ " = " ++ prettyCtx ctx0 ++ " ctx"
prettyTypingRule (CtxEqTrans ctx0 ctx1 ctx2) =
  prettyCtx ctx0 ++ " = " ++ prettyCtx ctx2 ++ " ctx via " ++ prettyCtx ctx1
prettyTypingRule (SubWfTerminal ctx) =
  prettyCtx ctx ++ " ⊦ · sub-wf"
prettyTypingRule (SubWfId ctx) =
  prettyCtx ctx ++ " ⊦ id sub-wf"
prettyTypingRule (SubWfWk gamma ty) =
  prettyCtx (gamma :< ty) ++ " ⊦ ↑ sub-wf"
prettyTypingRule (SubWfExt sigma e gamma delta ty) =
  prettyCtx gamma ++ " ⊦ " ++ prettySub (Ext sigma e) ++ " sub-wf to " ++ prettyCtx (delta :< ty)
prettyTypingRule (SubWfChain sigma tau gamma theta delta) =
  prettyCtx gamma ++ " ⊦ " ++ prettySub (Chain sigma tau) ++ " sub-wf to " ++ prettyCtx delta ++ " via " ++ prettyCtx theta
prettyTypingRule (SubEqRefl s g d) =
  prettyCtx g ++ " ⊦ " ++ prettySub s ++ " = " ++ prettySub s ++ " : " ++ prettyCtx d
prettyTypingRule (SubEqSym s0 s1 g d) =
  prettyCtx g ++ " ⊦ " ++ prettySub s1 ++ " = " ++ prettySub s0 ++ " : " ++ prettyCtx d
prettyTypingRule (SubEqTrans s0 s1 s2 g d) =
  prettyCtx g ++ " ⊦ " ++ prettySub s0 ++ " = " ++ prettySub s2 ++ " : " ++ prettyCtx d ++ " via " ++ prettySub s1
prettyTypingRule (TyEqRefl ctx ty) =
  prettyCtx ctx ++ " ⊦ " ++ prettyTy ty ++ " = " ++ prettyTy ty ++ " type"
prettyTypingRule (TyEqSym ctx ty0 ty1) =
  prettyCtx ctx ++ " ⊦ " ++ prettyTy ty1 ++ " = " ++ prettyTy ty0 ++ " type"
prettyTypingRule (TyEqTrans ctx ty0 ty1 ty2) =
  prettyCtx ctx ++ " ⊦ " ++ prettyTy ty0 ++ " = " ++ prettyTy ty2 ++ " type via " ++ prettyTy ty1
prettyTypingRule (ElemEqRefl ctx e ty) =
  prettyCtx ctx ++ " ⊦ " ++ prettyElem e ++ " = " ++ prettyElem e ++ " : " ++ prettyTy ty
prettyTypingRule (ElemEqSym ctx e0 e1 ty) =
  prettyCtx ctx ++ " ⊦ " ++ prettyElem e1 ++ " = " ++ prettyElem e0 ++ " : " ++ prettyTy ty
prettyTypingRule (ElemEqTrans ctx e0 e1 e2 ty) =
  prettyCtx ctx ++ " ⊦ " ++ prettyElem e0 ++ " = " ++ prettyElem e2 ++ " : " ++ prettyTy ty ++ " via " ++ prettyElem e1
prettyTypingRule (ElemEqReflection ctx a a0 a1 ty) =
  prettyCtx ctx ++ " ⊦ " ++ prettyElem a ++ " : (" ++ prettyTy (EqTy a0 a1 ty) ++ ") reflect"
prettyTypingRule (TelEqRefl ctx tel) =
  prettyCtx ctx ++ " ⊦ " ++ prettyTel tel ++ " = " ++ prettyTel tel ++ " tel"
prettyTypingRule (TelEqSym ctx tel0 tel1) =
  prettyCtx ctx ++ " ⊦ " ++ prettyTel tel1 ++ " = " ++ prettyTel tel0 ++ " tel"
prettyTypingRule (TelEqTrans ctx tel0 tel1 tel2) =
  prettyCtx ctx ++ " ⊦ " ++ prettyTel tel0 ++ " = " ++ prettyTel tel2 ++ " tel via " ++ prettyTel tel1
prettyTypingRule (SpineEqRefl ctx spine tel) =
  prettyCtx ctx ++ " ⊦ " ++ prettySpine spine ++ " = " ++ prettySpine spine ++ " : " ++ prettyTel tel
prettyTypingRule (SpineEqSym ctx s0 s1 tel) =
  prettyCtx ctx ++ " ⊦ " ++ prettySpine s1 ++ " = " ++ prettySpine s0 ++ " : " ++ prettyTel tel
prettyTypingRule (SpineEqTrans ctx s0 s1 s2 tel) =
  prettyCtx ctx ++ " ⊦ " ++ prettySpine s0 ++ " = " ++ prettySpine s2 ++ " : " ++ prettyTel tel ++ " via " ++ prettySpine s1

export
prettyJudgementForm : JudgementForm -> String
prettyJudgementForm (JfCtxWf ctx)       = prettyCtxWf ctx
prettyJudgementForm (JfCtxEq p)         = prettyCtxEq p
prettyJudgementForm (JfTyWf p)          = prettyTyWf p
prettyJudgementForm (JfTyEq p)          = prettyTyEq p
prettyJudgementForm (JfSubWf p)         = prettySubWf p
prettyJudgementForm (JfSubEq p)         = prettySubEq p
prettyJudgementForm (JfElemWf p)        = prettyElemWf p
prettyJudgementForm (JfElemEq p)        = prettyElemEq p
prettyJudgementForm (JfTelWf p)         = prettyTelWf p
prettyJudgementForm (JfTelEq p)         = prettyTelEq p
prettyJudgementForm (JfSpineWf p)       = prettySpineWf p
prettyJudgementForm (JfSpineEq p)       = prettySpineEq p
