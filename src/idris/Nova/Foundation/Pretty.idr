module Nova.Foundation.Pretty

import Data.SnocList
import Nova.Foundation.Syntax
import Nova.Foundation.Derivation

%default covering

subscriptDigitChar : Char -> Char
subscriptDigitChar '0' = '₀'
subscriptDigitChar '1' = '₁'
subscriptDigitChar '2' = '₂'
subscriptDigitChar '3' = '₃'
subscriptDigitChar '4' = '₄'
subscriptDigitChar '5' = '₅'
subscriptDigitChar '6' = '₆'
subscriptDigitChar '7' = '₇'
subscriptDigitChar '8' = '₈'
subscriptDigitChar '9' = '₉'
subscriptDigitChar c   = c

||| n rendered as Unicode subscript digits, e.g. 12 -> "₁₂"
natToSubscript : Nat -> String
natToSubscript n = pack (map subscriptDigitChar (unpack (show n)))

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
  prettyElemPrefix (Class a) = "class " ++ prettyElemAtom a
  prettyElemPrefix (QuotElim f q) = "quot-elim " ++ prettyElemAtom f ++ " " ++ prettyElemAtom q
  prettyElemPrefix e = prettyElemPostfix e

  prettyElemPostfix : Elem -> String
  prettyElemPostfix (SigmaElim1 e) = prettyElemPostfix e ++ " .π₁"
  prettyElemPostfix (SigmaElim2 e) = prettyElemPostfix e ++ " .π₂"
  prettyElemPostfix (PiApp f e) = prettyElemPostfix f ++ " " ++ prettyElemAtom e
  prettyElemPostfix e = prettyElemAtom e

  export
  prettyElemAtom : Elem -> String
  prettyElemAtom (CtxVar n) = "☐" ++ natToSubscript n
  prettyElemAtom OneIntro = "()"
  prettyElemAtom NatIntro0 = "Z"
  prettyElemAtom Refl = "Refl"
  prettyElemAtom Elem.ZeroTy = "𝟘"
  prettyElemAtom Elem.OneTy = "𝟙"
  prettyElemAtom Elem.NatTy = "ℕ"
  prettyElemAtom (SigVar x es) = x ++ "[" ++ prettySubNorm es ++ "]"
  prettyElemAtom e = "(" ++ prettyElem e ++ ")"

  ||| t˲ ::= · | t˲ , t
  export
  prettySubNorm : SubNorm -> String
  prettySubNorm [<] = "·"
  prettySubNorm (es :< e) = prettySubNorm es ++ ", " ++ prettyElemNoComma e

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
  prettyTyArrow (Ty.Quotient a r) = prettyTyEl a ++ " / " ++ prettyTyArrow r
  prettyTyArrow ty = prettyTyEl ty

  prettyTyEl : Ty -> String
  prettyTyEl (El e) = "El " ++ prettyElemAtom e
  prettyTyEl ty = prettyTyAtom ty

  prettyTyAtom : Ty -> String
  prettyTyAtom Ty.ZeroTy = "𝟘"
  prettyTyAtom Ty.OneTy = "𝟙"
  prettyTyAtom Ty.NatTy = "ℕ"
  prettyTyAtom Ty.UniverseTy = "𝕌"
  prettyTyAtom (Ty.SigVar x es) = x ++ "[" ++ prettySubNorm es ++ "]"
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

-- ===== Judgement forms =====
-- (Use concrete underlying types since Idris2 does not reduce type aliases for unification.)

export
prettyCtxWf : Ctx -> String
prettyCtxWf ctx = "ctx-wf " ++ prettyCtx ctx

export
prettyCtxEq : (Ctx, Ctx) -> String
prettyCtxEq (g0, g1) = "ctx-eq " ++ prettyCtx g0 ++ " ≐ " ++ prettyCtx g1

export
prettyTyWf : (Ctx, Ty) -> String
prettyTyWf (ctx, ty) = "ty-wf " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTy ty

export
prettyTyEq : (Ctx, Ty, Ty) -> String
prettyTyEq (ctx, a, b) = "ty-eq " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTy a ++ " ≐ " ++ prettyTy b

export
prettySubWf : (Sub, Ctx, Ctx) -> String
prettySubWf (s, g, d) = "sub-wf " ++ prettySub s ++ " : " ++ prettyCtx g ++ " ⇒ " ++ prettyCtx d

export
prettySubEq : (Sub, Sub, Ctx, Ctx) -> String
prettySubEq (s0, s1, g, d) =
  "sub-eq " ++ prettySub s0 ++ " ≐ " ++ prettySub s1 ++ " : " ++ prettyCtx g ++ " ⇒ " ++ prettyCtx d

export
prettySubNormWf : (SubNorm, Ctx, Ctx) -> String
prettySubNormWf (s, g, d) = "sub-norm-wf " ++ prettySubNorm s ++ " : " ++ prettyCtx g ++ " ⇒ " ++ prettyCtx d ++ " norm"

export
prettySubNormEq : (SubNorm, SubNorm, Ctx, Ctx) -> String
prettySubNormEq (s0, s1, g, d) =
  "sub-norm-eq " ++ prettySubNorm s0 ++ " ≐ " ++ prettySubNorm s1 ++ " : " ++ prettyCtx g ++ " ⇒ " ++ prettyCtx d ++ " norm"

export
prettyElemWf : (Ctx, Elem, Ty) -> String
prettyElemWf (ctx, e, ty) = "el-wf " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem e ++ " : " ++ prettyTy ty

export
prettyElemEq : (Ctx, Elem, Elem, Ty) -> String
prettyElemEq (ctx, e0, e1, ty) =
  "el-eq " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem e0 ++ " ≐ " ++ prettyElem e1 ++ " : " ++ prettyTy ty

export
prettyTelWf : (Ctx, Tel) -> String
prettyTelWf (ctx, tel) = "tel-wf " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTel tel

export
prettyTelEq : (Ctx, Tel, Tel) -> String
prettyTelEq (ctx, t0, t1) =
  "tel-eq " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTel t0 ++ " ≐ " ++ prettyTel t1

export
prettySpineWf : (Ctx, Spine, Tel) -> String
prettySpineWf (ctx, spine, tel) =
  "sp-wf " ++ prettyCtx ctx ++ " ⊦ " ++ prettySpine spine ++ " : " ++ prettyTel tel

export
prettySpineEq : (Ctx, Spine, Spine, Tel) -> String
prettySpineEq (ctx, s0, s1, tel) =
  "sp-eq " ++ prettyCtx ctx ++ " ⊦ " ++ prettySpine s0 ++ " ≐ " ++ prettySpine s1 ++ " : " ++ prettyTel tel

-- ===== TypingRule =====

export
prettyTypingRule : TypingRule -> String
prettyTypingRule CtxWfEmpty =
  "ctx-emp"
prettyTypingRule (CtxWfExt g ty) =
  "ctx-ext " ++ prettyCtx (g :< ty)
prettyTypingRule (CtxEqRefl ctx) =
  "ctx-refl " ++ prettyCtx ctx
prettyTypingRule (CtxEqSym ctx0 ctx1) =
  "ctx-sym " ++ prettyCtx ctx1 ++ " ≐ " ++ prettyCtx ctx0
prettyTypingRule (CtxEqTrans ctx0 ctx1 ctx2) =
  "ctx-trans " ++ prettyCtx ctx0 ++ " ≐ " ++ prettyCtx ctx2 ++ " via " ++ prettyCtx ctx1
prettyTypingRule (SubWfTerminal ctx) =
  "sub-term " ++ prettyCtx ctx ++ " ⊦ ·"
prettyTypingRule (SubWfExt sigma e gamma delta ty) =
  "sub-ext " ++ prettyCtx gamma ++ " ⊦ " ++ prettySub (Ext sigma e) ++ " to " ++ prettyCtx (delta :< ty)
prettyTypingRule (SubEqRefl s g d) =
  "sub-refl " ++ prettyCtx g ++ " ⊦ " ++ prettySub s ++ " : " ++ prettyCtx d
prettyTypingRule (SubEqSym s0 s1 g d) =
  "sub-sym " ++ prettyCtx g ++ " ⊦ " ++ prettySub s1 ++ " ≐ " ++ prettySub s0 ++ " : " ++ prettyCtx d
prettyTypingRule (SubEqTrans s0 s1 s2 g d) =
  "sub-trans " ++ prettyCtx g ++ " ⊦ " ++ prettySub s0 ++ " ≐ " ++ prettySub s2 ++ " : " ++ prettyCtx d ++ " via " ++ prettySub s1
prettyTypingRule (SubNormWfTerminal ctx) =
  "sub-norm-term " ++ prettyCtx ctx ++ " ⊦ ·"
prettyTypingRule (SubNormWfExt sigma e gamma delta ty) =
  "sub-norm-ext " ++ prettyCtx gamma ++ " ⊦ " ++ prettySubNorm (sigma :< e) ++ " to " ++ prettyCtx (delta :< ty)
prettyTypingRule (SubNormEqRefl s g d) =
  "sub-norm-refl " ++ prettyCtx g ++ " ⊦ " ++ prettySubNorm s ++ " : " ++ prettyCtx d
prettyTypingRule (SubNormEqSym s0 s1 g d) =
  "sub-norm-sym " ++ prettyCtx g ++ " ⊦ " ++ prettySubNorm s1 ++ " ≐ " ++ prettySubNorm s0 ++ " : " ++ prettyCtx d
prettyTypingRule (SubNormEqTrans s0 s1 s2 g d) =
  "sub-norm-trans " ++ prettyCtx g ++ " ⊦ " ++ prettySubNorm s0 ++ " ≐ " ++ prettySubNorm s2 ++ " : " ++ prettyCtx d ++ " via " ++ prettySubNorm s1
prettyTypingRule (SubNormEqExt s0 s1 t0 t1 gamma0 gamma1 ty) =
  "sub-norm-ext-eq " ++ prettyCtx gamma0 ++ " ⊦ " ++ prettySubNorm (s0 :< t0) ++ " ≐ " ++ prettySubNorm (s1 :< t1) ++ " : " ++ prettyCtx (gamma1 :< ty)
prettyTypingRule (TyWfZero ctx) =
  "ty-zero " ++ prettyCtx ctx ++ " ⊦ 𝟘"
prettyTypingRule (TyWfOne ctx) =
  "ty-one " ++ prettyCtx ctx ++ " ⊦ 𝟙"
prettyTypingRule (TyWfNat ctx) =
  "ty-nat " ++ prettyCtx ctx ++ " ⊦ ℕ"
prettyTypingRule (TyWfUniverse ctx) =
  "ty-univ " ++ prettyCtx ctx ++ " ⊦ 𝕌"
prettyTypingRule (TyWfPi ctx a b) =
  "ty-pi " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTy (PiTy a b)
prettyTypingRule (TyWfSigma ctx a b) =
  "ty-sigma " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTy (SigmaTy a b)
prettyTypingRule (TyWfEq ctx l r ty) =
  "ty-eq-form " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTy (EqTy l r ty)
prettyTypingRule (TyWfEl ctx e) =
  "ty-el " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTy (El e)
prettyTypingRule (TyWfQuotient ctx a r) =
  "ty-quotient " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTy (Quotient a r)
prettyTypingRule (TyWfSigVar ctx sigma x) =
  "ty-sig-var " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTy (Ty.SigVar x sigma)
prettyTypingRule (TyEqRefl ctx ty) =
  "ty-refl " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTy ty
prettyTypingRule (TyEqSym ctx ty0 ty1) =
  "ty-sym " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTy ty1 ++ " ≐ " ++ prettyTy ty0
prettyTypingRule (TyEqTrans ctx ty0 ty1 ty2) =
  "ty-trans " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTy ty0 ++ " ≐ " ++ prettyTy ty2 ++ " via " ++ prettyTy ty1
prettyTypingRule (TyEqCongEqTy ctx a0 b0 ty0 a1 b1 ty1) =
  "ty-eq-cong " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTy (EqTy a0 b0 ty0) ++ " ≐ " ++ prettyTy (EqTy a1 b1 ty1)
prettyTypingRule (TyEqCongEl ctx t0 t1) =
  "ty-el-cong " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTy (El t0) ++ " ≐ " ++ prettyTy (El t1)
prettyTypingRule (TyWfSubst gamma0 gamma1 sigma a) =
  "ty-wf-subst " ++ prettyCtx gamma0 ++ " ⊦ " ++ prettySub sigma ++ " to " ++ prettyCtx gamma1 ++ " ⊦ " ++ prettyTy a
prettyTypingRule (TyEqSubst gamma0 gamma1 sigma0 sigma1 a0 a1) =
  "ty-eq-subst " ++ prettyCtx gamma0 ++ " ⊦ " ++ prettySub sigma0 ++ " ≐ " ++ prettySub sigma1 ++ " to " ++ prettyCtx gamma1 ++ " ⊦ " ++ prettyTy a0 ++ " ≐ " ++ prettyTy a1
prettyTypingRule (ElemWfVar g n) =
  "el-var " ++ prettyCtx g ++ " ⊦ " ++ prettyElemAtom (CtxVar n)
prettyTypingRule (ElemWfOneIntro ctx) =
  "el-one " ++ prettyCtx ctx ++ " ⊦ ()"
prettyTypingRule (ElemWfZeroIntro ctx) =
  "el-zero " ++ prettyCtx ctx ++ " ⊦ Z"
prettyTypingRule (ElemWfSucIntro ctx e) =
  "el-suc " ++ prettyCtx ctx ++ " ⊦ S " ++ prettyElemAtom e
prettyTypingRule (ElemWfPiIntro ctx f a b) =
  "el-pi-i " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem (PiIntro f) ++ " : " ++ prettyTy (PiTy a b)
prettyTypingRule (ElemWfPiApp gamma f a b e) =
  "el-pi-e " ++ prettyCtx gamma ++ " ⊦ (" ++ prettyElem f ++ " : " ++ prettyTy (PiTy a b) ++ ") " ++ prettyElemAtom e
prettyTypingRule (ElemWfSigmaIntro ctx u v a b) =
  "el-sigma-i " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem (SigmaIntro u v) ++ " : " ++ prettyTy (SigmaTy a b)
prettyTypingRule (ElemWfSigmaElim1 ctx e a b) =
  "el-sigma-e1 " ++ prettyCtx ctx ++ " ⊦ (" ++ prettyElem e ++ " : " ++ prettyTy (SigmaTy a b) ++ ") .π₁"
prettyTypingRule (ElemWfSigmaElim2 ctx e a b) =
  "el-sigma-e2 " ++ prettyCtx ctx ++ " ⊦ (" ++ prettyElem e ++ " : " ++ prettyTy (SigmaTy a b) ++ ") .π₂"
prettyTypingRule (ElemWfZeroElim ctx e ty) =
  "el-zero-e " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem (ZeroElim e) ++ " : " ++ prettyTy ty
prettyTypingRule (ElemWfNatElim ctx z s t ty) =
  "el-nat-e " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem (NatElim z s t) ++ " motive " ++ prettyTy ty
prettyTypingRule (ElemWfClass ctx a ty r) =
  "el-class " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem (Class a) ++ " : " ++ prettyTy (Quotient ty r)
prettyTypingRule (ElemWfQuotElim ctx ty r motive f q) =
  "el-quot-elim " ++ prettyCtx ctx ++ " ⊦ quot-elim " ++ prettyElemAtom f ++ " (" ++ prettyElem q ++ " : " ++ prettyTy (Quotient ty r) ++ ") motive " ++ prettyTy motive
prettyTypingRule (ElemWfSubst gamma0 gamma1 sigma t a) =
  "el-wf-subst " ++ prettyCtx gamma0 ++ " ⊦ " ++ prettySub sigma ++ " to " ++ prettyCtx gamma1 ++ " ⊦ " ++ prettyElem t ++ " : " ++ prettyTy a
prettyTypingRule (ElemEqReflection ctx a a0 a1 ty) =
  "el-reflect " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem a ++ " : (" ++ prettyTy (EqTy a0 a1 ty) ++ ") reflect"
prettyTypingRule (ElemEqCongSuc ctx t0 t1) =
  "el-suc-cong " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem (NatIntro1 t0) ++ " ≐ " ++ prettyElem (NatIntro1 t1)
prettyTypingRule (ElemEqCongPiApp ctx f0 f1 a b a0 a1) =
  "el-app-cong " ++ prettyCtx ctx ++ " ⊦ (" ++ prettyElem f0 ++ " ≐ " ++ prettyElem f1 ++ " : " ++ prettyTy (PiTy a b) ++ ") " ++ prettyElemAtom a0 ++ " ≐ " ++ prettyElemAtom a1
prettyTypingRule (ElemEqCongClass ctx ty r a0 a1) =
  "el-class-cong " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem (Class a0) ++ " ≐ " ++ prettyElem (Class a1) ++ " : " ++ prettyTy (Quotient ty r)
prettyTypingRule (ElemEqQuotient ctx ty r a b witness) =
  "el-quot-eq " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem (Class a) ++ " ≐ " ++ prettyElem (Class b) ++ " : " ++ prettyTy (Quotient ty r) ++ " via " ++ prettyElem witness
prettyTypingRule (ElemEqSubst gamma0 gamma1 sigma0 sigma1 t0 t1 a) =
  "el-eq-subst " ++ prettyCtx gamma0 ++ " ⊦ " ++ prettySub sigma0 ++ " ≐ " ++ prettySub sigma1 ++ " to " ++ prettyCtx gamma1 ++ " ⊦ " ++ prettyElem t0 ++ " ≐ " ++ prettyElem t1 ++ " : " ++ prettyTy a
prettyTypingRule (ElemWfRefl ctx e ty) =
  "el-refl " ++ prettyCtx ctx ++ " ⊦ Refl : " ++ prettyElemAtom e ++ " ∈ " ++ prettyTy ty
prettyTypingRule (ElemEqTyCoe ctx a b ty0 ty1) =
  "el-ty-coe-eq " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem a ++ " ≐ " ++ prettyElem b ++ " : " ++ prettyTy ty0 ++ " ↝ " ++ prettyTy ty1
prettyTypingRule (ElemWfTyCoe ctx e ty0 ty1) =
  "el-ty-coe " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem e ++ " : " ++ prettyTy ty0 ++ " ↝ " ++ prettyTy ty1
prettyTypingRule (ElemWfCtxCoe ctx0 ctx1 e ty) =
  "el-ctx-coe " ++ prettyCtx ctx0 ++ " ≐ " ++ prettyCtx ctx1 ++ " ⊦ " ++ prettyElem e ++ " : " ++ prettyTy ty
prettyTypingRule (ElemWfZeroTy ctx) =
  "el-zero-ty " ++ prettyCtx ctx ++ " ⊦ 𝟘 : 𝕌"
prettyTypingRule (ElemWfOneTy ctx) =
  "el-one-ty " ++ prettyCtx ctx ++ " ⊦ 𝟙 : 𝕌"
prettyTypingRule (ElemWfNatTy ctx) =
  "el-nat-ty " ++ prettyCtx ctx ++ " ⊦ ℕ : 𝕌"
prettyTypingRule (ElemWfPiTy ctx a b) =
  "el-pi-ty " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem (Elem.PiTy a b) ++ " : 𝕌"
prettyTypingRule (ElemWfSigmaTy ctx a b) =
  "el-sigma-ty " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem (Elem.SigmaTy a b) ++ " : 𝕌"
prettyTypingRule (ElemWfEqTy ctx l r ty) =
  "el-eq-ty " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem (Elem.EqTy l r ty) ++ " : 𝕌"
prettyTypingRule (ElemWfSigVar ctx sigma x) =
  "sig-var " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElemAtom (SigVar x sigma)
prettyTypingRule (SigExt gamma x a ty) =
  "sig " ++ prettyCtx gamma ++ " ⊦ " ++ x ++ " ≔ " ++ prettyElem a ++ " : " ++ prettyTy ty
prettyTypingRule (SigExtTy gamma x a) =
  "sig-ty " ++ prettyCtx gamma ++ " ⊦ " ++ x ++ " ≔ " ++ prettyTy a
prettyTypingRule (ElemEqRefl ctx e ty) =
  "el-eq-refl " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem e ++ " : " ++ prettyTy ty
prettyTypingRule (ElemEqSym ctx e0 e1 ty) =
  "el-eq-sym " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem e1 ++ " ≐ " ++ prettyElem e0 ++ " : " ++ prettyTy ty
prettyTypingRule (ElemEqTrans ctx e0 e1 e2 ty) =
  "el-eq-trans " ++ prettyCtx ctx ++ " ⊦ " ++ prettyElem e0 ++ " ≐ " ++ prettyElem e2 ++ " : " ++ prettyTy ty ++ " via " ++ prettyElem e1
prettyTypingRule (TelEqRefl ctx tel) =
  "tel-refl " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTel tel
prettyTypingRule (TelEqSym ctx tel0 tel1) =
  "tel-sym " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTel tel1 ++ " ≐ " ++ prettyTel tel0
prettyTypingRule (TelEqTrans ctx tel0 tel1 tel2) =
  "tel-trans " ++ prettyCtx ctx ++ " ⊦ " ++ prettyTel tel0 ++ " ≐ " ++ prettyTel tel2 ++ " via " ++ prettyTel tel1
prettyTypingRule (SpineEqRefl ctx spine tel) =
  "sp-refl " ++ prettyCtx ctx ++ " ⊦ " ++ prettySpine spine ++ " : " ++ prettyTel tel
prettyTypingRule (SpineEqSym ctx s0 s1 tel) =
  "sp-sym " ++ prettyCtx ctx ++ " ⊦ " ++ prettySpine s1 ++ " ≐ " ++ prettySpine s0 ++ " : " ++ prettyTel tel
prettyTypingRule (SpineEqTrans ctx s0 s1 s2 tel) =
  "sp-trans " ++ prettyCtx ctx ++ " ⊦ " ++ prettySpine s0 ++ " ≐ " ++ prettySpine s2 ++ " : " ++ prettyTel tel ++ " via " ++ prettySpine s1

export
prettyJudgementForm : JudgementForm -> String
prettyJudgementForm (JfCtxWf ctx)       = prettyCtxWf ctx
prettyJudgementForm (JfCtxEq p)         = prettyCtxEq p
prettyJudgementForm (JfTyWf p)          = prettyTyWf p
prettyJudgementForm (JfTyEq p)          = prettyTyEq p
prettyJudgementForm (JfSubWf p)         = prettySubWf p
prettyJudgementForm (JfSubEq p)         = prettySubEq p
prettyJudgementForm (JfSubNormWf p)     = prettySubNormWf p
prettyJudgementForm (JfSubNormEq p)     = prettySubNormEq p
prettyJudgementForm (JfElemWf p)        = prettyElemWf p
prettyJudgementForm (JfElemEq p)        = prettyElemEq p
prettyJudgementForm (JfTelWf p)         = prettyTelWf p
prettyJudgementForm (JfTelEq p)         = prettyTelEq p
prettyJudgementForm (JfSpineWf p)       = prettySpineWf p
prettyJudgementForm (JfSpineEq p)       = prettySpineEq p
