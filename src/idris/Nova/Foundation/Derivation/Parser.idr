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
--   α @            (InPiElim, postfix)
--   α .π₁          (InSigmaElim1, postfix)
--   α .π₂          (InSigmaElim2, postfix)
--   α _            (InSubstElim, postfix)
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
              beta  <- parseComputePostfix; sp; str_ "∈"; sp
              gamma <- parseComputePostfix
              pure (InEqTy alpha beta gamma))
      <|> (do sp; str_ "ᐅ"; sp; beta <- parseComputeNoComma; pure (InExt alpha beta))
      <|> pure alpha

  parseComputePrefix : Rule ComputeRule
  parseComputePrefix =
        (do str_ "λ";      space; a <- parseComputeSubst; pure (InPiIntro a))
    <|> (do str_ "𝟘-elim"; space; a <- parseComputeSubst; pure (InZeroElim a))
    <|> (do str_ "ℕ-elim"; space
            a <- parseComputeSubst; space
            b <- parseComputeSubst; space
            c <- parseComputeSubst
            pure (InNatElim a b c))
    <|> (do str_ "S";  space; a <- parseComputeSubst; pure (InNatIntro1 a))
    <|> (do str_ "El"; space; a <- parseComputeSubst; pure (InEl a))
    <|> parseComputePostfix

  -- Level 4: SubstElim postfix on atoms (α[β], left-assoc)
  parseComputeSubst : Rule ComputeRule
  parseComputeSubst = do
    alpha <- parseComputeAtom
    parseComputeSubstCont alpha

  parseComputeSubstCont : ComputeRule -> Rule ComputeRule
  parseComputeSubstCont alpha =
    (do sp; char_ '['; sp; beta <- parseComputeRule; sp; char_ ']'
        parseComputeSubstCont (InSubstElim alpha beta))
    <|> pure alpha

  -- Level 3: @, projections (α @, α .π₁, α .π₂, left-assoc)
  parseComputePostfix : Rule ComputeRule
  parseComputePostfix = do
    alpha <- parseComputeSubst
    parseComputePostfixCont alpha

  parseComputePostfixCont : ComputeRule -> Rule ComputeRule
  parseComputePostfixCont alpha =
        (do sp; str_ ".π₁"; parseComputePostfixCont (InSigmaElim1 alpha))
    <|> (do sp; str_ ".π₂"; parseComputePostfixCont (InSigmaElim2 alpha))
    <|> (do sp; beta <- parseComputeSubst; parseComputePostfixCont (InPiApp alpha beta))
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
      ctx1 <- parseCtx; sp; str_ "="; sp; ctx0 <- parseCtx
      pure (CtxEqSym ctx0 ctx1)) <|>
  (do str_ "ctx-trans"; space
      ctx0 <- parseCtx; sp; str_ "="; sp; ctx2 <- parseCtx
      sp; str_ "via"; sp; ctx1 <- parseCtx
      pure (CtxEqTrans ctx0 ctx1 ctx2)) <|>
  (do str_ "ctx-cmp"; space
      ctx <- parseCtx; sp; str_ "via"; sp; alpha <- parseComputeRule
      pure (CtxWfCompute ctx alpha)) <|>
  -- Substitution wf
  (do str_ "sub-term"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp; _ <- parseSub
      pure (SubWfTerminal ctx)) <|>
  (do str_ "sub-id"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp; _ <- parseSub
      pure (SubWfId ctx)) <|>
  (do str_ "sub-wk"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp; _ <- parseSub
      case ctx of
        g :< ty => pure (SubWfWk g ty)
        [<]     => fail "sub-wk: requires non-empty context") <|>
  (do str_ "sub-ext"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp
      sigma <- parseSub; sp; str_ "to"; sp; delta <- parseCtx
      case (sigma, delta) of
        (Ext s e, d :< ty) => pure (SubWfExt s e ctx d ty)
        _ => fail "sub-ext: expected σ, e and non-empty target context") <|>
  (do str_ "sub-chn"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp
      sigma <- parseSub; sp; str_ "to"; sp; delta <- parseCtx
      sp; str_ "via"; sp; theta <- parseCtx
      case sigma of
        Chain s t => pure (SubWfChain s t ctx theta delta)
        _         => fail "sub-chn: expected σ ∘ τ") <|>
  -- Substitution eq
  (do str_ "sub-refl"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp
      s <- parseSub; sp; char_ ':'; sp; d <- parseCtx
      pure (SubEqRefl s ctx d)) <|>
  (do str_ "sub-sym"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp
      s1 <- parseSub; sp; str_ "="; sp; s0 <- parseSub; sp; char_ ':'; sp; d <- parseCtx
      pure (SubEqSym s0 s1 ctx d)) <|>
  (do str_ "sub-trans"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp
      s0 <- parseSub; sp; str_ "="; sp; s2 <- parseSub; sp; char_ ':'; sp; d <- parseCtx
      sp; str_ "via"; sp; s1 <- parseSub
      pure (SubEqTrans s0 s1 s2 ctx d)) <|>
  -- Type wf
  (do str_ "ty-zero"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; _ <- parseTy; pure (TyWfZero ctx)) <|>
  (do str_ "ty-one";  space; ctx <- parseCtx; sp; str_ "⊦"; sp; _ <- parseTy; pure (TyWfOne ctx)) <|>
  (do str_ "ty-nat";  space; ctx <- parseCtx; sp; str_ "⊦"; sp; _ <- parseTy; pure (TyWfNat ctx)) <|>
  (do str_ "ty-univ"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; _ <- parseTy; pure (TyWfUniverse ctx)) <|>
  (do str_ "ty-pi"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; ty <- parseTy
      case ty of
        PiTy a b => pure (TyWfPi ctx a b)
        _        => fail "ty-pi: expected A → B") <|>
  (do str_ "ty-sigma"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; ty <- parseTy
      case ty of
        SigmaTy a b => pure (TyWfSigma ctx a b)
        _           => fail "ty-sigma: expected A ⨯ B") <|>
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
      ty1 <- parseTy; sp; str_ "="; sp; ty0 <- parseTy
      pure (TyEqSym ctx ty0 ty1)) <|>
  (do str_ "ty-trans"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      ty0 <- parseTy; sp; str_ "="; sp; ty2 <- parseTy; sp; str_ "via"; sp; ty1 <- parseTy
      pure (TyEqTrans ctx ty0 ty1 ty2)) <|>
  -- Element wf: intro / elim  (longer keywords before shorter sharing same prefix)
  (do str_ "el-var"; space
      ctx <- parseCtx; sp; str_ "⊦"; sp; str_ "☐"
      case ctx of
        g :< ty => pure (ElemWfVar g ty)
        [<]     => fail "el-var: requires non-empty context") <|>
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
          sp; char_ ':'; sp; ty <- parseTy
          pure (ElemWfNatElim ctx z s t ty)
        _ => fail "el-nat-e: expected ℕ-elim z s t") <|>
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
  (do str_ "el-sub"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; e <- parseElem
      case e of
        SubstElim t sigma => do
          sp; char_ ':'; sp; ty <- parseTy; sp; str_ "from"; sp; delta <- parseCtx
          pure (ElemWfSubElim t ty sigma ctx delta)
        _ => fail "el-sub: expected t[σ]") <|>
  -- el-ty-coe-eq before el-ty-coe (longer keyword first)
  (do str_ "el-ty-coe-eq"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      e0 <- parseElem; sp; str_ "="; sp; e1 <- parseElem
      sp; char_ ':'; sp; ty0 <- parseTy; sp; str_ "↝"; sp; ty1 <- parseTy
      pure (ElemEqTyCoe ctx e0 e1 ty0 ty1)) <|>
  (do str_ "el-ty-coe"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; e <- parseElem
      sp; char_ ':'; sp; ty0 <- parseTy; sp; str_ "↝"; sp; ty1 <- parseTy
      pure (ElemWfTyCoe ctx e ty0 ty1)) <|>
  (do str_ "el-ctx-coe"; space
      ctx0 <- parseCtx; sp; str_ "="; sp; ctx1 <- parseCtx
      sp; str_ "⊦"; sp; e <- parseElem; sp; char_ ':'; sp; ty <- parseTy
      pure (ElemWfCtxCoe ctx0 ctx1 e ty)) <|>
  -- Element wf: universe codes
  (do str_ "el-zero-ty"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; _ <- parseElem
      sp; char_ ':'; sp; str_ "𝕌"
      pure (ElemWfZeroTy ctx)) <|>
  (do str_ "el-one-ty"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; _ <- parseElem
      sp; char_ ':'; sp; str_ "𝕌"
      pure (ElemWfOneTy ctx)) <|>
  (do str_ "el-nat-ty"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; _ <- parseElem
      sp; char_ ':'; sp; str_ "𝕌"
      pure (ElemWfNatTy ctx)) <|>
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
  (do str_ "sig-var-eq"; space
      e <- parseElem
      _ <- (do sp; str_ "="; sp; _ <- parseElem; sp; char_ ':'; sp; _ <- parseTy; pure ()) <|> pure ()
      case e of
        SigVar x => pure (ElemEqSigVar x)
        _        => fail "sig-var-eq: expected identifier") <|>
  (do str_ "sig-var"; space; e <- parseElem
      case e of
        SigVar x => pure (ElemWfSigVar x)
        _        => fail "sig-var: expected identifier") <|>
  (do str_ "sig"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      e <- parseElem; sp; str_ "≔"; sp; a <- parseElem; sp; char_ ':'; sp; ty <- parseTy
      case e of
        SigVar x => pure (SigExt ctx x a ty)
        _        => fail "sig: expected identifier on lhs of ≔") <|>
  -- Element equality (el-ty-coe-eq already above; el-eq-trans before el-eq-ty for safety)
  (do str_ "el-sub-cong"; space
      delta <- parseCtx; sp; str_ "⊦"; sp
      ea <- parseElem; sp; str_ "="; sp; eb <- parseElem
      sp; char_ ':'; sp; ty <- parseTy; sp; str_ "from"; sp; gamma <- parseCtx
      case (ea, eb) of
        (SubstElim a sigma, SubstElim b sigma') =>
          if sigma == sigma'
            then
              let ty_src = case ty of
                             Ty.SubstElim s sigma'' => if sigma == sigma'' then s else ty
                             _ => ty
              in pure (ElemEqSubstCong gamma delta sigma a b ty_src)
            else fail "el-sub-cong: both sides must have same substitution"
        _ => fail "el-sub-cong: both sides must be substitutions") <|>
  (do str_ "el-eq-refl"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      e <- parseElem; sp; char_ ':'; sp; ty <- parseTy
      pure (ElemEqRefl ctx e ty)) <|>
  (do str_ "el-eq-sym"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      e1 <- parseElem; sp; str_ "="; sp; e0 <- parseElem; sp; char_ ':'; sp; ty <- parseTy
      pure (ElemEqSym ctx e0 e1 ty)) <|>
  (do str_ "el-eq-trans"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      e0 <- parseElem; sp; str_ "="; sp; e2 <- parseElem; sp; char_ ':'; sp; ty <- parseTy
      sp; str_ "via"; sp; e1 <- parseElem
      pure (ElemEqTrans ctx e0 e1 e2 ty)) <|>
  -- Telescope equality
  (do str_ "tel-refl"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; tel <- parseTel
      pure (TelEqRefl ctx tel)) <|>
  (do str_ "tel-sym"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      tel1 <- parseTel; sp; str_ "="; sp; tel0 <- parseTel
      pure (TelEqSym ctx tel0 tel1)) <|>
  (do str_ "tel-trans"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      tel0 <- parseTel; sp; str_ "="; sp; tel2 <- parseTel; sp; str_ "via"; sp; tel1 <- parseTel
      pure (TelEqTrans ctx tel0 tel1 tel2)) <|>
  -- Spine equality
  (do str_ "sp-refl"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      spine <- parseSpine; sp; char_ ':'; sp; tel <- parseTel
      pure (SpineEqRefl ctx spine tel)) <|>
  (do str_ "sp-sym"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      s1 <- parseSpine; sp; str_ "="; sp; s0 <- parseSpine; sp; char_ ':'; sp; tel <- parseTel
      pure (SpineEqSym ctx s0 s1 tel)) <|>
  (do str_ "sp-trans"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      s0 <- parseSpine; sp; str_ "="; sp; s2 <- parseSpine; sp; char_ ':'; sp; tel <- parseTel
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
      ctx <- parseCtx; sp; str_ "="; sp; ctx' <- parseCtx
      pure (JfCtxEq (ctx, ctx'))) <|>
  (do str_ "sub-wf"; space
      s <- parseSub; sp; char_ ':'; sp; g <- parseCtx; sp; str_ "⇒"; sp; d <- parseCtx
      pure (JfSubWf (s, g, d))) <|>
  (do str_ "sub-eq"; space
      s <- parseSub; sp; str_ "="; sp; s' <- parseSub; sp
      char_ ':'; sp; g <- parseCtx; sp; str_ "⇒"; sp; d <- parseCtx
      pure (JfSubEq (s, s', g, d))) <|>
  (do str_ "ty-wf"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; ty <- parseTy
      pure (JfTyWf (ctx, ty))) <|>
  (do str_ "ty-eq"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      ty <- parseTy; sp; str_ "="; sp; ty' <- parseTy
      pure (JfTyEq (ctx, ty, ty'))) <|>
  (do str_ "el-wf"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      e <- parseElem; sp; char_ ':'; sp; ty <- parseTy
      pure (JfElemWf (ctx, e, ty))) <|>
  (do str_ "el-eq"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      e <- parseElem; sp; str_ "="; sp; e' <- parseElem; sp; char_ ':'; sp; ty <- parseTy
      pure (JfElemEq (ctx, e, e', ty))) <|>
  (do str_ "tel-wf"; space; ctx <- parseCtx; sp; str_ "⊦"; sp; tel <- parseTel
      pure (JfTelWf (ctx, tel))) <|>
  (do str_ "tel-eq"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      tel <- parseTel; sp; str_ "="; sp; tel' <- parseTel
      pure (JfTelEq (ctx, tel, tel'))) <|>
  (do str_ "sp-wf"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      spine <- parseSpine; sp; char_ ':'; sp; tel <- parseTel
      pure (JfSpineWf (ctx, spine, tel))) <|>
  (do str_ "sp-eq"; space; ctx <- parseCtx; sp; str_ "⊦"; sp
      spine <- parseSpine; sp; str_ "="; sp; spine' <- parseSpine; sp
      char_ ':'; sp; tel <- parseTel
      pure (JfSpineEq (ctx, spine, spine', tel)))

-- Parse a list of judgement forms, each prefixed by "- ".
export
parseListJudgementForm : Rule (List JudgementForm)
parseListJudgementForm = many (do sp; char_ '-'; space; parseJudgementForm)
