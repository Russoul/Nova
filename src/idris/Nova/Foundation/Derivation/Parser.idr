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
    <|> (do sp; str_ "@";   parseComputePostfixCont (InPiApp alpha Id))
    <|> pure alpha

  parseComputeAtom : Rule ComputeRule
  parseComputeAtom =
        (str_ "↓"  $> Here)
    <|> (str_ "id" $> Id)
    <|> inParen parseComputeRule

-- ===== TypingRule parser =====

-- Map a parsed Ty to the corresponding TyWf typing rule for a given context.
mkTyWfRule : Ctx -> Ty -> Rule TypingRule
mkTyWfRule ctx ZeroTy        = pure (TyWfZero ctx)
mkTyWfRule ctx OneTy         = pure (TyWfOne ctx)
mkTyWfRule ctx NatTy         = pure (TyWfNat ctx)
mkTyWfRule ctx UniverseTy    = pure (TyWfUniverse ctx)
mkTyWfRule ctx (PiTy a b)    = pure (TyWfPi ctx a b)
mkTyWfRule ctx (SigmaTy a b) = pure (TyWfSigma ctx a b)
mkTyWfRule ctx (EqTy l r ty) = pure (TyWfEq ctx l r ty)
mkTyWfRule ctx (El e)        = pure (TyWfEl ctx e)
mkTyWfRule _ _               = fail "substituted type cannot be a direct TyWf rule"

-- Parse the content after "Γ ⊦".
parseTurnstileContent : Ctx -> Rule TypingRule
parseTurnstileContent ctx =
  -- 0. SubWf: "σ sub-wf [to Δ [via Θ]]"
  (do sigma <- parseSub; sp; str_ "sub-wf"
      optTarget <- (do sp; str_ "to"; sp; d <- parseCtx; pure (Just d)) <|> pure Nothing
      optVia    <- (do sp; str_ "via"; sp; t <- parseCtx; pure (Just t)) <|> pure Nothing
      case (sigma, optTarget, optVia) of
        (Id, Nothing, _)   => pure (SubWfId ctx)
        (Terminal, _, _)   => pure (SubWfTerminal ctx)
        (Wk, Nothing, _)   =>
          case ctx of
            gamma :< ty => pure (SubWfWk gamma ty)
            [<]         => fail "SubWfWk requires non-empty context"
        (Ext sigma' e, Just (d :< ty), Nothing) => pure (SubWfExt sigma' e ctx d ty)
        (Chain sigma' tau, Just delta, Just theta) =>
          pure (SubWfChain sigma' tau ctx theta delta)
        _ => fail "unexpected SubWf form") <|>
  -- 1. Type form: parseTy followed by "=" Ty type [via Ty] or "type"
  (do ty0 <- parseTy; sp
      (do str_ "="; sp; ty1 <- parseTy; sp; str_ "type"
          -- optional "via mid"
          (do sp; str_ "via"; sp; tyMid <- parseTy
              pure (TyEqTrans ctx ty0 tyMid ty1)) <|>
          if ty0 == ty1
            then pure (TyEqRefl ctx ty0)
            else pure (TyEqSym ctx ty1 ty0)) <|>
      (str_ "type" *> mkTyWfRule ctx ty0)) <|>
  -- 2. Refl : e ∈ A  (ElemWfRefl)
  (do str_ "Refl"; sp; char_ ':'; sp
      e <- parseElemAtom; sp; str_ "∈"; sp; ty <- parseTy
      pure (ElemWfRefl ctx e ty)) <|>
  -- 3. (e : A ⨯ B) .π₁  or  .π₂  (ElemWfSigmaElim1/2)
  --    (f : A → B) e               (ElemWfPiApp)
  (do char_ '('; sp; e <- parseElem; sp; char_ ':'; sp; ty <- parseTy; sp; char_ ')'
      sp *>
      case ty of
        SigmaTy a b =>
          (str_ ".π₁" $> ElemWfSigmaElim1 ctx e a b) <|>
          (str_ ".π₂" $> ElemWfSigmaElim2 ctx e a b)
        PiTy a b =>
          (do e' <- parseElemAtom; pure (ElemWfPiApp ctx e a b e'))
        _ => fail "expected sigma or pi type in elimination annotation") <|>
  -- 4. General elem dispatch
  (do e <- parseElem
      -- "x ≔ a : A" — sig extension
      (do sp; str_ "≔"; sp; a <- parseElem; sp; char_ ':'; sp; ty <- parseTy
          case e of
            SigVar x => pure (SigExt ctx x a ty)
            _        => fail "expected identifier on lhs of ≔") <|>
      -- "e = e' : A [via mid | ↝ ty1 | from Γ]" — ElemEq rules
      (do sp; str_ "="; sp; e1 <- parseElem; sp; char_ ':'; sp; ty <- parseTy
          -- ElemEqTrans: "... via e_mid"
          (do sp; str_ "via"; sp; eMid <- parseElem
              pure (ElemEqTrans ctx e eMid e1 ty)) <|>
          -- ElemEqTyCoe: "... ↝ ty1"
          (do sp; str_ "↝"; sp; ty1 <- parseTy
              pure (ElemEqTyCoe ctx e e1 ty ty1)) <|>
          -- ElemEqSubstCong: "a(σ) = b(σ) : A from Γ" where A is the source type (σ applied automatically)
          (do sp; str_ "from"; sp; g <- parseCtx
              case (e, e1) of
                (SubstElim a sigma, SubstElim b sigma') =>
                  if sigma == sigma'
                    then
                      let ty_src = case ty of
                                     SubstElim s sigma'' => if sigma == sigma'' then s else ty
                                     _ => ty
                      in pure (ElemEqSubstCong g ctx sigma a b ty_src)
                    else fail "ElemEqSubstCong requires same substitution on both sides"
                _ => fail "ElemEqSubstCong requires both sides to be substitutions") <|>
          case e of
            SigVar x => pure (ElemEqSigVar x)
            _ =>
              if e == e1
                then pure (ElemEqRefl ctx e ty)
                else pure (ElemEqSym ctx e1 e ty)) <|>
      -- With type annotation ": ty0"
      (do sp; char_ ':'; sp; ty0 <- parseTy
          -- ElemWfTyCoe: "e : ty0 ↝ ty1"
          (do sp; str_ "↝"; sp; ty1 <- parseTy
              pure (ElemWfTyCoe ctx e ty0 ty1)) <|>
          -- ElemEqReflection: "a : (a₀ ≡ a₁ ∈ A) reflect"
          (do sp; str_ "reflect"
              case ty0 of
                Ty.EqTy a0 a1 a => pure (ElemEqReflection ctx e a0 a1 a)
                _               => fail "expected equality type for reflect") <|>
          case (e, ty0) of
            (ZeroElim t, a)               => pure (ElemWfZeroElim ctx t a)
            (NatElim z s t, a)            => pure (ElemWfNatElim ctx z s t a)
            (PiIntro f, PiTy a b)         => pure (ElemWfPiIntro ctx f a b)
            (SigmaIntro u v, SigmaTy a b) => pure (ElemWfSigmaIntro ctx u v a b)
            (PiApp f e', PiTy a b) => pure (ElemWfPiApp ctx f a b e')
            (SubstElim t sigma, a) => do
              optG <- (do sp; str_ "from"; sp; g <- parseCtx; pure (Just g)) <|> pure Nothing
              case optG of
                Just g  => pure (ElemWfSubElim t a sigma ctx g)
                Nothing =>
                  case ctx of
                    g :< _ => pure (ElemWfSubElim t a sigma ctx g)
                    [<]    => fail "ElemWfSubElim requires non-empty context or explicit 'from Γ'"
            _ => fail "unexpected element/type combination in typing rule") <|>
      -- Without type annotation
      (case e of
        CtxVar =>
          case ctx of
            gamma :< a => pure (ElemWfVar gamma a)
            [<]        => fail "CtxVar rule requires non-empty context"
        OneIntro         => pure (ElemWfOneIntro ctx)
        NatIntro0        => pure (ElemWfZeroIntro ctx)
        NatIntro1 e'     => pure (ElemWfSucIntro ctx e')
        Elem.ZeroTy      => pure (ElemWfZeroTy ctx)
        Elem.OneTy       => pure (ElemWfOneTy ctx)
        Elem.NatTy       => pure (ElemWfNatTy ctx)
        Elem.PiTy a b    => pure (ElemWfPiTy ctx a b)
        Elem.SigmaTy a b => pure (ElemWfSigmaTy ctx a b)
        Elem.EqTy l r t  => pure (ElemWfEqTy ctx l r t)
        SigVar x         => pure (ElemWfSigVar x)
        _                => fail "unexpected element form in typing rule"))

-- Parse "Γ ctx", "Γ | α ...", or "Γ ⊦ ..." after the context has been parsed.
parseAfterCtx : Ctx -> Rule TypingRule
parseAfterCtx ctx =
  -- "ctx" keyword: empty context or extended context
  (do str_ "ctx"
      case ctx of
        [<]         => pure CtxWfEmpty
        gamma :< ty => pure (CtxWfExt gamma ty)) <|>
  -- CtxEq rules: "= Γ₁ ctx [via Γmid]" or ElemWfCtxCoe: "= Γ₁ ⊦ e : A"
  (do str_ "="; sp; ctx1 <- parseCtx; sp
      -- ElemWfCtxCoe: "= ctx1 ⊦ e : A"
      (do str_ "⊦"; sp
          e <- parseElem; sp; char_ ':'; sp; ty <- parseTy
          pure (ElemWfCtxCoe ctx ctx1 e ty)) <|>
      -- CtxEq rules: "= ctx1 ctx [via ctxMid]"
      (do str_ "ctx"
          (do sp; str_ "via"; sp; ctxMid <- parseCtx
              pure (CtxEqTrans ctx ctxMid ctx1)) <|>
          if ctx == ctx1
            then pure (CtxEqRefl ctx)
            else pure (CtxEqSym ctx1 ctx))) <|>
  -- "| α" then "ctx", "⊦ A | β type", or "⊦ a | β : A | γ type"
  (do char_ '|'; sp; alpha <- parseComputeRule; sp
      (str_ "ctx" $> CtxWfCompute ctx alpha) <|>
      (do str_ "⊦"; sp
          (do ty <- parseTy; sp; char_ '|'; sp; beta <- parseComputeRule
              sp; str_ "type"
              pure (TyWfCompute ctx alpha ty beta)) <|>
          (do e <- parseElem; sp; char_ '|'; sp; beta <- parseComputeRule
              sp; char_ ':'; sp
              ty <- parseTy; sp; char_ '|'; sp; gamma <- parseComputeRule
              sp; str_ "type"
              pure (ElemWfCompute ctx alpha e beta ty gamma)))) <|>
  -- "⊦ ..." regular judgement
  (do str_ "⊦"; sp; parseTurnstileContent ctx)

export
parseTypingRule : Rule TypingRule
parseTypingRule = do
  ctx <- parseCtx
  sp
  parseAfterCtx ctx

-- Parse a list of typing rules, each prefixed by "- ".
export
parseListTypingRule : Rule (List TypingRule)
parseListTypingRule = many (do sp; char_ '-'; space; parseTypingRule)

-- ===== JudgementForm parser =====
--
-- Grammar (unambiguous by first-token or trailing keyword):
--
--   Sub = Sub : Ctx ⇒ Ctx        (SubEq)   — starts with ·/id/↑/(
--   Sub : Ctx ⇒ Ctx               (SubWf)
--   Ctx ctx                       (CtxWf)   — starts with ε
--   Ctx = Ctx ctx                 (CtxEq)
--   Ctx ⊦ Ty = Ty type            (TyEq)
--   Ctx ⊦ Ty type                 (TyWf)
--   Ctx ⊦ Elem = Elem : Ty        (ElemEq)
--   Ctx ⊦ Elem : Ty               (ElemWf)
--   Ctx ⊦ Tel = Tel tel           (TelEq)
--   Ctx ⊦ Tel tel                 (TelWf)
--   Ctx ⊦ · = · : Tel             (SpineEq, empty spines only)
--   Ctx ⊦ · : Tel                 (SpineWf, empty spine only)
--
-- Disambiguation after ⊦ is done by trying in order:
--   1. parseTy   then (= Ty type | type)
--   2. parseElem then (= Elem : Ty | : Ty)
--   3. parseTel  then (= Tel tel | tel)
--   4. · (empty spine marker)

afterTurnstile : Ctx -> Rule JudgementForm
afterTurnstile ctx =
  -- 1. Type judgements (Ty followed by "type" or "= Ty type")
  (do ty <- parseTy; sp
      (do str_ "="; sp; ty' <- parseTy; sp; str_ "type"
          pure (JfTyEq (ctx, ty, ty')))
        <|> (str_ "type" $> JfTyWf (ctx, ty))) <|>
  -- 2. Elem judgements (Elem followed by ":" or "= Elem :")
  (do e <- parseElem; sp
      (do str_ "="; sp; e' <- parseElem; sp; char_ ':'; sp; ty <- parseTy
          pure (JfElemEq (ctx, e, e', ty)))
        <|> (do char_ ':'; sp; ty <- parseTy; pure (JfElemWf (ctx, e, ty)))) <|>
  -- 3. Tel judgements (Tel starts with ε or A ◁ …, and ends with "tel")
  (do tel <- parseTel; sp
      (do str_ "="; sp; tel' <- parseTel; sp; str_ "tel"
          pure (JfTelEq (ctx, tel, tel')))
        <|> (str_ "tel" $> JfTelWf (ctx, tel))) <|>
  -- 4. Empty-spine judgements (· is unambiguously a spine marker here)
  (do str_ "·"; sp
      (do str_ "="; sp; str_ "·"; sp; char_ ':'; sp; tel <- parseTel
          pure (JfSpineEq (ctx, [], [], tel)))
        <|> (do char_ ':'; sp; tel <- parseTel
                pure (JfSpineWf (ctx, [], tel))))

export
parseJudgementForm : Rule JudgementForm
parseJudgementForm =
  -- Substitution judgements start with ·/id/↑/( which parseSub handles
  -- Context judgements start with ε which parseCtx handles
  -- Try Sub first since it starts with · (not ε), cleanly distinct
  (do s <- parseSub; sp
      (do str_ "="; sp; s' <- parseSub; sp; char_ ':'; sp
          g <- parseCtx; sp; str_ "⇒"; sp; d <- parseCtx
          pure (JfSubEq (s, s', g, d)))
        <|> (do char_ ':'; sp; g <- parseCtx; sp; str_ "⇒"; sp; d <- parseCtx
                pure (JfSubWf (s, g, d)))) <|>
  (do ctx <- parseCtx; sp
      (str_ "ctx" $> JfCtxWf ctx)
        <|> (do str_ "="; sp; ctx' <- parseCtx; sp; str_ "ctx"
                pure (JfCtxEq (ctx, ctx')))
        <|> (do str_ "⊦"; sp; afterTurnstile ctx))

-- Parse a list of judgement forms, each prefixed by "- ".
export
parseListJudgementForm : Rule (List JudgementForm)
parseListJudgementForm = many (do sp; char_ '-'; space; parseJudgementForm)
