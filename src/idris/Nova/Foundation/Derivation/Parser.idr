module Nova.Foundation.Derivation.Parser

import Data.SnocList

import Me.Russoul.Text.Lexer.Token
import Me.Russoul.Text.Lexer
import Me.Russoul.Text.Parser
import Me.Russoul.Text.Parser.OverToken
import Me.Russoul.Text.Position
import Me.Russoul.Text.Range

import Nova.Foundation.Syntax
import Nova.Foundation.Parser
import Nova.Foundation.Derivation

%default covering

sp : Rule ()
sp = optSpace

-- ===== ComputeRule parser =====
-- Mirrors the Elem parser structure, using ComputeRule constructors.
-- Operators by precedence (lowest to highest):
--   α , β          (InSigmaIntro, right-assoc)
--   α → β          (InPiTy, right-assoc)
--   α ⨯ β          (InSigmaTy, right-assoc)
--   α ≡ β ∈ γ      (InEqTy)
--   α ᐅ β          (InExt, right-assoc)
--   λ α            (InPiIntro, prefix)
--   𝟘-elim α       (InZeroElim, prefix)
--   ℕ-elim α β γ   (InNatElim, prefix)
--   S α            (InNatIntro1, prefix)
--   El α           (InEl, prefix)
--   quot-elim α β  (InQuotElim, prefix)
--   α @            (InPiElim, postfix)
--   α .π₁          (InSigmaElim1, postfix)
--   α .π₂          (InSigmaElim2, postfix)
--   ↓              (Here, atom)
--   id             (ComputeRule.Id, atom)
--   (α)            (parenthesised, atom)

mutual
  export
  parseComputeRule : Rule ComputeRule
  parseComputeRule = do
    alpha <- parseComputeNoComma
    (do sp; char_ ','; sp; beta <- parseComputeRule; pure (InSigmaIntro alpha beta))
      <|> (do sp; char_ ';'; sp; beta <- parseComputeRule; pure (Composition alpha beta))
      <|> pure alpha

  parseComputeNoComma : Rule ComputeRule
  parseComputeNoComma = do
    alpha <- parseComputePrefix
    (do sp; str_ "→"; sp; beta <- parseComputeNoComma; pure (InPiTy alpha beta))
      <|> (do sp; str_ "⨯"; sp; beta <- parseComputeNoComma; pure (InSigmaTy alpha beta))
      <|> (do sp; str_ "≡"; sp
              beta  <- parseComputePrefix; sp; str_ "∈"; sp
              gamma <- parseComputePrefix
              pure (InEqTy alpha beta gamma))
      <|> (do sp; str_ "ᐅ"; sp; beta <- parseComputeNoComma; pure (InExt alpha beta))
      <|> pure alpha

  parseComputePrefix : Rule ComputeRule
  parseComputePrefix =
        (do str_ "λ";      space; a <- parseComputeAtom; pure (InPiIntro a))
    <|> (do str_ "𝟘-elim"; space; a <- parseComputeAtom; pure (InZeroElim a))
    <|> (do str_ "ℕ-elim"; space
            a <- parseComputeAtom; space
            b <- parseComputeAtom; space
            c <- parseComputeAtom
            pure (InNatElim a b c))
    <|> (do str_ "S";  space; a <- parseComputeAtom; pure (InNatIntro1 a))
    <|> (do str_ "El"; space; a <- parseComputeAtom; pure (InEl a))
    <|> (do str_ "quot-elim"; space
            a <- parseComputeAtom; space
            b <- parseComputeAtom
            pure (InQuotElim a b))
    <|> parseComputePostfix

  -- Level 3: @, projections (α @, α .π₁, α .π₂, left-assoc)
  parseComputePostfix : Rule ComputeRule
  parseComputePostfix = do
    alpha <- parseComputeAtom
    parseComputePostfixCont alpha

  parseComputePostfixCont : ComputeRule -> Rule ComputeRule
  parseComputePostfixCont alpha =
        (do sp; str_ ".π₁"; parseComputePostfixCont (InSigmaElim1 alpha))
    <|> (do sp; str_ ".π₂"; parseComputePostfixCont (InSigmaElim2 alpha))
    <|> (do sp; beta <- parseComputeAtom; parseComputePostfixCont (InPiApp alpha beta))
    <|> pure alpha

  parseComputeAtom : Rule ComputeRule
  parseComputeAtom =
        (str_ "↓"  $> Here)
    <|> (str_ "id" $> Id)
    <|> inParen parseComputeRule

-- ===== TypingRule parser =====
-- Keyword-first: each rule starts with a unique keyword.

export
parseTypingRule : Rule TypingRule
parseTypingRule =
  -- Context
  (str_ "ctx-emp" $> CtxWfEmpty) <|>
  (do str_ "ctx-ext"; space
      ctx <- parseCtx
      case ctx of
        g :< ty => pure (CtxWfExt g ty)
        [<]     => fail "ctx-ext: requires non-empty context") <|>
  (do str_ "ctx-refl"; space; ctx <- parseCtx; pure (CtxEqRefl ctx)) <|>
  (do str_ "ctx-sym"; space
      ctx1 <- parseCtx; sp; str_ "≐"; sp; ctx0 <- parseCtx
      pure (CtxEqSym ctx0 ctx1)) <|>
  (do str_ "ctx-trans"; space
      ctx0 <- parseCtx; sp; str_ "≐"; sp; ctx2 <- parseCtx
      sp; str_ "via"; sp; ctx1 <- parseCtx
      pure (CtxEqTrans ctx0 ctx1 ctx2)) <|>
  (do str_ "ctx-cmp"; space
      ctx <- parseCtx; sp; str_ "via"; sp; alpha <- parseComputeRule
      pure (CtxWfCompute ctx alpha)) <|>
  -- Substitution wf
  (do str_ "sub-term"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp; _ <- parseSub
      pure (SubWfTerminal ctx)) <|>
  (do str_ "sub-ext"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp
      sigma <- parseSub; sp; str_ "to"; sp; delta <- parseCtx
      case (sigma, delta) of
        (Ext s e, d :< ty) => pure (SubWfExt s e ctx d ty)
        _ => fail "sub-ext: expected σ, e and non-empty target context") <|>
  -- Substitution eq
  (do str_ "sub-refl"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp
      s <- parseSub; sp; char_ ':'; sp; d <- parseCtx
      pure (SubEqRefl s ctx d)) <|>
  (do str_ "sub-sym"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp
      s1 <- parseSub; sp; str_ "≐"; sp; s0 <- parseSub; sp; char_ ':'; sp; d <- parseCtx
      pure (SubEqSym s0 s1 ctx d)) <|>
  (do str_ "sub-trans"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp
      s0 <- parseSub; sp; str_ "≐"; sp; s2 <- parseSub; sp; char_ ':'; sp; d <- parseCtx
      sp; str_ "via"; sp; s1 <- parseSub
      pure (SubEqTrans s0 s1 s2 ctx d)) <|>
  -- Normal substitution wf (ext-eq before ext — longer keyword first)
  (do str_ "sub-norm-term"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp; _ <- parseSubNorm
      pure (SubNormWfTerminal ctx)) <|>
  (do str_ "sub-norm-ext-eq"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp
      full0 <- parseSubNorm; sp; str_ "≐"; sp; full1 <- parseSubNorm
      sp; char_ ':'; sp; delta <- parseCtx
      case (full0, full1, delta) of
        (es0 :< t0, es1 :< t1, d :< ty) => pure (SubNormEqExt es0 es1 t0 t1 ctx d ty)
        _ => fail "sub-norm-ext-eq: expected e˲, t = e˲', t' and non-empty target context") <|>
  (do str_ "sub-norm-ext"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp
      sigma <- parseSubNorm; sp; str_ "to"; sp; delta <- parseCtx
      case (sigma, delta) of
        (es :< e, d :< ty) => pure (SubNormWfExt es e ctx d ty)
        _ => fail "sub-norm-ext: expected e˲, e and non-empty target context") <|>
  -- Normal substitution eq
  (do str_ "sub-norm-refl"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp
      s <- parseSubNorm; sp; char_ ':'; sp; d <- parseCtx
      pure (SubNormEqRefl s ctx d)) <|>
  (do str_ "sub-norm-sym"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp
      s1 <- parseSubNorm; sp; str_ "≐"; sp; s0 <- parseSubNorm; sp; char_ ':'; sp; d <- parseCtx
      pure (SubNormEqSym s0 s1 ctx d)) <|>
  (do str_ "sub-norm-trans"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp
      s0 <- parseSubNorm; sp; str_ "≐"; sp; s2 <- parseSubNorm; sp; char_ ':'; sp; d <- parseCtx
      sp; str_ "via"; sp; s1 <- parseSubNorm
      pure (SubNormEqTrans s0 s1 s2 ctx d)) <|>
  -- Type wf
  (do str_ "ty-zero"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; ty <- parseTy
      case ty of
        Ty.ZeroTy => pure (TyWfZero ctx)
        _         => fail "ty-zero: expected 𝟘") <|>
  (do str_ "ty-one";  space; ctx <- parseCtx; sp; str_ "⊦"; sp; ty <- parseTy
      case ty of
        Ty.OneTy => pure (TyWfOne ctx)
        _        => fail "ty-one: expected 𝟙") <|>
  (do str_ "ty-nat";  space; ctx <- parseCtx; sp; str_ "⊦"; sp; ty <- parseTy
      case ty of
        Ty.NatTy => pure (TyWfNat ctx)
        _        => fail "ty-nat: expected ℕ") <|>
  (do str_ "ty-univ"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; ty <- parseTy
      case ty of
        Ty.UniverseTy => pure (TyWfUniverse ctx)
        _             => fail "ty-univ: expected 𝕌") <|>
  (do str_ "ty-pi"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; ty <- parseTy
      case ty of
        PiTy a b => pure (TyWfPi ctx a b)
        _        => fail "ty-pi: expected A → B") <|>
  (do str_ "ty-sigma"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; ty <- parseTy
      case ty of
        SigmaTy a b => pure (TyWfSigma ctx a b)
        _           => fail "ty-sigma: expected A ⨯ B") <|>
  (do str_ "ty-quotient"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; ty <- parseTy
      case ty of
        Quotient a r => pure (TyWfQuotient ctx a r)
        _            => fail "ty-quotient: expected A / R") <|>
  (do str_ "ty-wf-subst"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      sigma <- parseSub; sp; str_ "to"; sp; delta <- parseCtx; sp; str_ "⊦"; sp
      a <- parseTy
      pure (TyWfSubst ctx delta sigma a)) <|>
  (do str_ "ty-eq-form"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; ty <- parseTy
      case ty of
        Ty.EqTy l r a => pure (TyWfEq ctx l r a)
        _             => fail "ty-eq-form: expected l ≡ r ∈ A") <|>
  (do str_ "ty-el"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; ty <- parseTy
      case ty of
        El e => pure (TyWfEl ctx e)
        _    => fail "ty-el: expected El e") <|>
  (do str_ "ty-cmp"; space
      ctx <- parseCtx; sp; str_ "via"; sp; alpha <- parseComputeRule
      sp; str_ "⊦"; sp; ty <- parseTy; sp; str_ "via"; sp; beta <- parseComputeRule
      pure (TyWfCompute ctx alpha ty beta)) <|>
  -- Type eq
  (do str_ "ty-refl"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; ty <- parseTy
      pure (TyEqRefl ctx ty)) <|>
  (do str_ "ty-sym"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      ty1 <- parseTy; sp; str_ "≐"; sp; ty0 <- parseTy
      pure (TyEqSym ctx ty0 ty1)) <|>
  (do str_ "ty-trans"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      ty0 <- parseTy; sp; str_ "≐"; sp; ty2 <- parseTy; sp; str_ "via"; sp; ty1 <- parseTy
      pure (TyEqTrans ctx ty0 ty1 ty2)) <|>
  (do str_ "ty-eq-cong"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      ty0 <- parseTy; sp; str_ "≐"; sp; ty1 <- parseTy
      case (ty0, ty1) of
        (Ty.EqTy a0 b0 t0, Ty.EqTy a1 b1 t1) => pure (TyEqCongEqTy ctx a0 b0 t0 a1 b1 t1)
        _ => fail "ty-eq-cong: expected (a₀ ≡ b₀ ∈ T₀) = (a₁ ≡ b₁ ∈ T₁)") <|>
  (do str_ "ty-el-cong"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      ty0 <- parseTy; sp; str_ "≐"; sp; ty1 <- parseTy
      case (ty0, ty1) of
        (Ty.El t0, Ty.El t1) => pure (TyEqCongEl ctx t0 t1)
        _ => fail "ty-el-cong: expected El t₀ = El t₁") <|>
  (do str_ "ty-eq-subst"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      sigma0 <- parseSub; sp; str_ "≐"; sp; sigma1 <- parseSub
      sp; str_ "to"; sp; delta <- parseCtx; sp; str_ "⊦"; sp
      a0 <- parseTy; sp; str_ "≐"; sp; a1 <- parseTy
      pure (TyEqSubst ctx delta sigma0 sigma1 a0 a1)) <|>
  -- Element wf: intro / elim  (longer keywords before shorter sharing same prefix)
  (do str_ "el-var"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp; str_ "☐"; n <- subscriptNat
      pure (ElemWfVar ctx n)) <|>
  (do str_ "el-one"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; str_ "()"
      pure (ElemWfOneIntro ctx)) <|>
  (do str_ "el-zero"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; str_ "Z"
      pure (ElemWfZeroIntro ctx)) <|>
  (do str_ "el-suc"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      str_ "S"; space; e <- parseElemAtom
      pure (ElemWfSucIntro ctx e)) <|>
  (do str_ "el-pi-i"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; e <- parseElem
      case e of
        PiIntro f => do
          sp; char_ ':'; sp; ty <- parseTy
          case ty of
            PiTy a b => pure (ElemWfPiIntro ctx f a b)
            _        => fail "el-pi-i: expected A → B after :"
        _ => fail "el-pi-i: expected λ f") <|>
  (do str_ "el-pi-e"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      char_ '('; sp; f <- parseElem; sp; char_ ':'; sp; ty <- parseTy; sp; char_ ')'
      sp; e <- parseElemAtom
      case ty of
        PiTy a b => pure (ElemWfPiApp ctx f a b e)
        _        => fail "el-pi-e: expected A → B") <|>
  (do str_ "el-sigma-i"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; e <- parseElem
      case e of
        SigmaIntro u v => do
          sp; char_ ':'; sp; ty <- parseTy
          case ty of
            SigmaTy a b => pure (ElemWfSigmaIntro ctx u v a b)
            _           => fail "el-sigma-i: expected A ⨯ B after :"
        _ => fail "el-sigma-i: expected u, v") <|>
  (do str_ "el-sigma-e1"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      char_ '('; sp; e <- parseElem; sp; char_ ':'; sp; ty <- parseTy; sp; char_ ')'
      sp; str_ ".π₁"
      case ty of
        SigmaTy a b => pure (ElemWfSigmaElim1 ctx e a b)
        _           => fail "el-sigma-e1: expected A ⨯ B") <|>
  (do str_ "el-sigma-e2"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      char_ '('; sp; e <- parseElem; sp; char_ ':'; sp; ty <- parseTy; sp; char_ ')'
      sp; str_ ".π₂"
      case ty of
        SigmaTy a b => pure (ElemWfSigmaElim2 ctx e a b)
        _           => fail "el-sigma-e2: expected A ⨯ B") <|>
  (do str_ "el-zero-e"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; e <- parseElem
      case e of
        ZeroElim t => do
          sp; char_ ':'; sp; ty <- parseTy
          pure (ElemWfZeroElim ctx t ty)
        _ => fail "el-zero-e: expected 𝟘-elim e") <|>
  (do str_ "el-nat-e"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; e <- parseElem
      case e of
        NatElim z s t => do
          space; str_ "motive"; space; ty <- parseTy
          pure (ElemWfNatElim ctx z s t ty)
        _ => fail "el-nat-e: expected ℕ-elim z s t") <|>
  (do str_ "el-class"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; e <- parseElem
      case e of
        Class a => do
          sp; char_ ':'; sp; ty <- parseTy
          case ty of
            Quotient tyA r => pure (ElemWfClass ctx a tyA r)
            _              => fail "el-class: expected A / R after :"
        _ => fail "el-class: expected class a") <|>
  (do str_ "el-quot-elim"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      str_ "quot-elim"; space; f <- parseElemAtom; space
      char_ '('; sp; q <- parseElem; sp; char_ ':'; sp; ty <- parseTy; sp; char_ ')'
      space; str_ "motive"; space; motive <- parseTy
      case ty of
        Quotient tyA r => pure (ElemWfQuotElim ctx tyA r motive f q)
        _              => fail "el-quot-elim: expected quot-elim f (q : A / R) motive B") <|>
  (do str_ "el-wf-subst"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      sigma <- parseSub; sp; str_ "to"; sp; delta <- parseCtx; sp; str_ "⊦"; sp
      t <- parseElem; sp; char_ ':'; sp; a <- parseTy
      pure (ElemWfSubst ctx delta sigma t a)) <|>
  -- el-reflect before el-refl (shares "el-refl" prefix at token level)
  (do str_ "el-reflect"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; e <- parseElem
      sp; char_ ':'; sp; char_ '('; sp; ty <- parseTy; sp; char_ ')'
      sp; str_ "reflect"
      case ty of
        Ty.EqTy a0 a1 a => pure (ElemEqReflection ctx e a0 a1 a)
        _               => fail "el-reflect: expected equality type") <|>
  (do str_ "el-refl"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      str_ "Refl"; sp; char_ ':'; sp; e <- parseElemAtom; sp; str_ "∈"; sp; ty <- parseTy
      pure (ElemWfRefl ctx e ty)) <|>
  -- el-ty-coe-eq before el-ty-coe (longer keyword first)
  (do str_ "el-ty-coe-eq"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      e0 <- parseElem; sp; str_ "≐"; sp; e1 <- parseElem
      sp; char_ ':'; sp; ty0 <- parseTy; sp; str_ "↝"; sp; ty1 <- parseTy
      pure (ElemEqTyCoe ctx e0 e1 ty0 ty1)) <|>
  (do str_ "el-ty-coe"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; e <- parseElem
      sp; char_ ':'; sp; ty0 <- parseTy; sp; str_ "↝"; sp; ty1 <- parseTy
      pure (ElemWfTyCoe ctx e ty0 ty1)) <|>
  (do str_ "el-ctx-coe"; space
      ctx0 <- parseCtx; sp; str_ "≐"; sp; ctx1 <- parseCtx
      sp; str_ "⊦"; sp; e <- parseElem; sp; char_ ':'; sp; ty <- parseTy
      pure (ElemWfCtxCoe ctx0 ctx1 e ty)) <|>
  -- Element wf: universe codes
  (do str_ "el-zero-ty"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; e <- parseElem
      sp; char_ ':'; sp; str_ "𝕌"
      case e of
        Elem.ZeroTy => pure (ElemWfZeroTy ctx)
        _           => fail "el-zero-ty: expected 𝟘") <|>
  (do str_ "el-one-ty"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; e <- parseElem
      sp; char_ ':'; sp; str_ "𝕌"
      case e of
        Elem.OneTy => pure (ElemWfOneTy ctx)
        _          => fail "el-one-ty: expected 𝟙") <|>
  (do str_ "el-nat-ty"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; e <- parseElem
      sp; char_ ':'; sp; str_ "𝕌"
      case e of
        Elem.NatTy => pure (ElemWfNatTy ctx)
        _          => fail "el-nat-ty: expected ℕ") <|>
  (do str_ "el-pi-ty"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; e <- parseElem
      sp; char_ ':'; sp; str_ "𝕌"
      case e of
        Elem.PiTy a b => pure (ElemWfPiTy ctx a b)
        _             => fail "el-pi-ty: expected A → B") <|>
  (do str_ "el-sigma-ty"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; e <- parseElem
      sp; char_ ':'; sp; str_ "𝕌"
      case e of
        Elem.SigmaTy a b => pure (ElemWfSigmaTy ctx a b)
        _                => fail "el-sigma-ty: expected A ⨯ B") <|>
  (do str_ "el-eq-ty"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; e <- parseElem
      sp; char_ ':'; sp; str_ "𝕌"
      case e of
        Elem.EqTy l r a => pure (ElemWfEqTy ctx l r a)
        _               => fail "el-eq-ty: expected l ≡ r ∈ A") <|>
  (do str_ "el-cmp"; space
      ctx <- parseCtx; sp; str_ "via"; sp; alpha <- parseComputeRule
      sp; str_ "⊦"; sp; e <- parseElem; sp; str_ "via"; sp; beta <- parseComputeRule
      sp; char_ ':'; sp; ty <- parseTy; sp; str_ "via"; sp; gamma <- parseComputeRule
      pure (ElemWfCompute ctx alpha e beta ty gamma)) <|>
  -- Signature (sig-var-eq before sig-var before sig — longer keywords first)
  (do str_ "sig-var-eq"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; e <- parseElem
      case e of
        SigVar x sigma => pure (ElemEqSigVar ctx sigma x)
        _              => fail "sig-var-eq: expected x[σ]") <|>
  (do str_ "sig-var"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; e <- parseElem
      case e of
        SigVar x sigma => pure (ElemWfSigVar ctx sigma x)
        _              => fail "sig-var: expected x[σ]") <|>
  (do str_ "sig"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      x <- parseSigIdentifier; sp; str_ "≔"; sp; a <- parseElem; sp; char_ ':'; sp; ty <- parseTy
      pure (SigExt ctx x a ty)) <|>
  -- Element equality (el-ty-coe-eq already above; el-eq-trans before el-eq-ty for safety)
  (do str_ "el-eq-refl"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      e <- parseElem; sp; char_ ':'; sp; ty <- parseTy
      pure (ElemEqRefl ctx e ty)) <|>
  (do str_ "el-eq-sym"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      e1 <- parseElem; sp; str_ "≐"; sp; e0 <- parseElem; sp; char_ ':'; sp; ty <- parseTy
      pure (ElemEqSym ctx e0 e1 ty)) <|>
  (do str_ "el-eq-trans"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      e0 <- parseElem; sp; str_ "≐"; sp; e2 <- parseElem; sp; char_ ':'; sp; ty <- parseTy
      sp; str_ "via"; sp; e1 <- parseElem
      pure (ElemEqTrans ctx e0 e1 e2 ty)) <|>
  (do str_ "el-suc-cong"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      e0 <- parseElem; sp; str_ "≐"; sp; e1 <- parseElem
      case (e0, e1) of
        (NatIntro1 t0, NatIntro1 t1) => pure (ElemEqCongSuc ctx t0 t1)
        _ => fail "el-suc-cong: expected S t₀ = S t₁") <|>
  (do str_ "el-app-cong"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      char_ '('; sp; f0 <- parseElem; sp; str_ "≐"; sp; f1 <- parseElem
      sp; char_ ':'; sp; ty <- parseTy; sp; char_ ')'
      sp; a0 <- parseElemAtom; sp; str_ "≐"; sp; a1 <- parseElemAtom
      case ty of
        PiTy a b => pure (ElemEqCongPiApp ctx f0 f1 a b a0 a1)
        _        => fail "el-app-cong: expected A → B") <|>
  -- el-class-cong before el-quot-eq (both share the "el-c"/"el-q" split, no
  -- real ambiguity, kept together for readability)
  (do str_ "el-class-cong"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      e0 <- parseElem; sp; str_ "≐"; sp; e1 <- parseElem
      sp; char_ ':'; sp; ty <- parseTy
      case (e0, e1, ty) of
        (Class a0, Class a1, Quotient tyA r) => pure (ElemEqCongClass ctx tyA r a0 a1)
        _ => fail "el-class-cong: expected class a₀ = class a₁ : A / R") <|>
  (do str_ "el-quot-eq"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      e0 <- parseElem; sp; str_ "≐"; sp; e1 <- parseElem
      sp; char_ ':'; sp; ty <- parseTy
      sp; str_ "via"; sp; witness <- parseElem
      case (e0, e1, ty) of
        (Class a, Class b, Quotient tyA r) => pure (ElemEqQuotient ctx tyA r a b witness)
        _ => fail "el-quot-eq: expected class a = class b : A / R via r") <|>
  (do str_ "el-eq-subst"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      sigma0 <- parseSub; sp; str_ "≐"; sp; sigma1 <- parseSub
      sp; str_ "to"; sp; delta <- parseCtx; sp; str_ "⊦"; sp
      t0 <- parseElem; sp; str_ "≐"; sp; t1 <- parseElem; sp; char_ ':'; sp; a <- parseTy
      pure (ElemEqSubst ctx delta sigma0 sigma1 t0 t1 a)) <|>
  -- Telescope equality
  (do str_ "tel-refl"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; tel <- parseTel
      pure (TelEqRefl ctx tel)) <|>
  (do str_ "tel-sym"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      tel1 <- parseTel; sp; str_ "≐"; sp; tel0 <- parseTel
      pure (TelEqSym ctx tel0 tel1)) <|>
  (do str_ "tel-trans"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      tel0 <- parseTel; sp; str_ "≐"; sp; tel2 <- parseTel; sp; str_ "via"; sp; tel1 <- parseTel
      pure (TelEqTrans ctx tel0 tel1 tel2)) <|>
  -- Spine equality
  (do str_ "sp-refl"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      spine <- parseSpine; sp; char_ ':'; sp; tel <- parseTel
      pure (SpineEqRefl ctx spine tel)) <|>
  (do str_ "sp-sym"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      s1 <- parseSpine; sp; str_ "≐"; sp; s0 <- parseSpine; sp; char_ ':'; sp; tel <- parseTel
      pure (SpineEqSym ctx s0 s1 tel)) <|>
  (do str_ "sp-trans"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      s0 <- parseSpine; sp; str_ "≐"; sp; s2 <- parseSpine; sp; char_ ':'; sp; tel <- parseTel
      sp; str_ "via"; sp; s1 <- parseSpine
      pure (SpineEqTrans ctx s0 s1 s2 tel))

-- Parse a list of typing rules, each prefixed by "- ".
export
parseListTypingRule : Rule (List TypingRule)
parseListTypingRule = many (do sp; char_ '-'; space; parseTypingRule)

-- ===== JudgementForm parser =====
--
-- Keyword-first: each form starts with a unique keyword.
--
--   ctx-wf  Γ                   (JfCtxWf)
--   ctx-eq  Γ = Γ'              (JfCtxEq)
--   sub-wf  σ : Γ ⇒ Δ          (JfSubWf)
--   sub-eq  σ = σ' : Γ ⇒ Δ    (JfSubEq)
--   sub-norm-wf  e˲ : Γ ⇒ Δ norm       (JfSubNormWf)
--   sub-norm-eq  e˲ = e˲' : Γ ⇒ Δ norm (JfSubNormEq)
--   ty-wf   Γ ⊦ T               (JfTyWf)
--   ty-eq   Γ ⊦ T = T'          (JfTyEq)
--   el-wf   Γ ⊦ t : T           (JfElemWf)
--   el-eq   Γ ⊦ t = t' : T      (JfElemEq)
--   tel-wf  Γ ⊦ Δ               (JfTelWf)
--   tel-eq  Γ ⊦ Δ = Δ'          (JfTelEq)
--   sp-wf   Γ ⊦ ē : Δ           (JfSpineWf)
--   sp-eq   Γ ⊦ ē = ē' : Δ     (JfSpineEq)

export
parseJudgementForm : Rule JudgementForm
parseJudgementForm =
  (do str_ "ctx-wf"; space; ctx <- parseCtx
      pure (JfCtxWf ctx)) <|>
  (do str_ "ctx-eq"; space
      ctx <- parseCtx; sp; str_ "≐"; sp; ctx' <- parseCtx
      pure (JfCtxEq (ctx, ctx'))) <|>
  (do str_ "sub-wf"; space
      s <- parseSub; sp; char_ ':'; sp; g <- parseCtx; sp; str_ "⇒"; sp; d <- parseCtx
      pure (JfSubWf (s, g, d))) <|>
  (do str_ "sub-eq"; space
      s <- parseSub; sp; str_ "≐"; sp; s' <- parseSub; sp
      char_ ':'; sp; g <- parseCtx; sp; str_ "⇒"; sp; d <- parseCtx
      pure (JfSubEq (s, s', g, d))) <|>
  (do str_ "sub-norm-wf"; space
      s <- parseSubNorm; sp; char_ ':'; sp; g <- parseCtx; sp; str_ "⇒"; sp; d <- parseCtx
      sp; str_ "norm"
      pure (JfSubNormWf (s, g, d))) <|>
  (do str_ "sub-norm-eq"; space
      s <- parseSubNorm; sp; str_ "≐"; sp; s' <- parseSubNorm; sp
      char_ ':'; sp; g <- parseCtx; sp; str_ "⇒"; sp; d <- parseCtx
      sp; str_ "norm"
      pure (JfSubNormEq (s, s', g, d))) <|>
  (do str_ "ty-wf"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; ty <- parseTy
      pure (JfTyWf (ctx, ty))) <|>
  (do str_ "ty-eq"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      ty <- parseTy; sp; str_ "≐"; sp; ty' <- parseTy
      pure (JfTyEq (ctx, ty, ty'))) <|>
  (do str_ "el-wf"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      e <- parseElem; sp; char_ ':'; sp; ty <- parseTy
      pure (JfElemWf (ctx, e, ty))) <|>
  (do str_ "el-eq"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      e <- parseElem; sp; str_ "≐"; sp; e' <- parseElem; sp; char_ ':'; sp; ty <- parseTy
      pure (JfElemEq (ctx, e, e', ty))) <|>
  (do str_ "tel-wf"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; tel <- parseTel
      pure (JfTelWf (ctx, tel))) <|>
  (do str_ "tel-eq"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      tel <- parseTel; sp; str_ "≐"; sp; tel' <- parseTel
      pure (JfTelEq (ctx, tel, tel'))) <|>
  (do str_ "sp-wf"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      spine <- parseSpine; sp; char_ ':'; sp; tel <- parseTel
      pure (JfSpineWf (ctx, spine, tel))) <|>
  (do str_ "sp-eq"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      spine <- parseSpine; sp; str_ "≐"; sp; spine' <- parseSpine; sp
      char_ ':'; sp; tel <- parseTel
      pure (JfSpineEq (ctx, spine, spine', tel)))

-- Parse a list of judgement forms, each prefixed by "- ".
export
parseListJudgementForm : Rule (List JudgementForm)
parseListJudgementForm = many (do sp; char_ '-'; space; parseJudgementForm)
