module Nova.Foundation.Elaboration.Parser

-- Parser for the proof-term surface syntax in docs/NovaSurfaceSyntax.txt.
-- Mirrors the precedence levels documented there exactly: for each sort
-- X with levels X{0} .. X{N}, this module defines parseX0 .. parseXN,
-- tightest (highest number) binding closest to atoms. The exported
-- parseX is always the loosest level (X0, or the whole grammar when a
-- sort has no levels, e.g. Ctx).

import Me.Russoul.Text.Lexer.Token
import Me.Russoul.Text.Lexer
import Me.Russoul.Text.Parser
import Me.Russoul.Text.Parser.OverToken
import Me.Russoul.Text.Position
import Me.Russoul.Text.Range

import Nova.Foundation.Parser

import Nova.Foundation.Elaboration.Syntax

%hide Nova.Foundation.Parser.parseCtx

sp : Rule ()
sp = optSpace

-- Conservative ASCII identifier: letter or '_' followed by letters, digits, or '_'.
-- Reserved words specific to this grammar are excluded so they're never
-- accidentally swallowed as a signature identifier.
covering
parseIdentifier : Rule String
parseIdentifier = do
  c  <- terminal "identifier start" $ \tok =>
          case tok of
            Symbol ch => if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || ch == '_'
                         then Just ch
                         else Nothing
            _ => Nothing
  cs <- many (terminal "identifier char" $ \tok =>
          case tok of
            Symbol ch => if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') ||
                            (ch >= '0' && ch <= '9') || ch == '_'
                         then Just ch
                         else Nothing
            _ => Nothing)
  let name = pack (c :: cs)
  guard "Reserved keyword" (name /= "via" && name /= "to" && name /= "of" && name /= "motive")
  pure name

mutual
  -- ===== Ctx (Γ) =====
  -- Γ ::= ε | Γ ᐅ T   (snoc list, left-associative)
  export covering
  parseCtx : Rule Ctx
  parseCtx = do
    str_ "ε"
    exts <- many (do sp; str_ "ᐅ"; sp; parseTy0)
    pure (foldl Ctx.Ext Ctx.Empty exts)

  -- ===== CtxEq (Γ⁼) =====
  -- Γ⁼{3} ::= ε | refl | (Γ⁼{≥0})
  -- Γ⁼{2} ::= Γ⁼{≥2} ⁻¹                          (postfix, self-referential)
  -- Γ⁼{1} ::= Γ⁼{≥1} ᐅ T⁼{≥0}                    (left-assoc)
  -- Γ⁼{0} ::= Γ⁼{≥1} · Γ⁼{≥1} via Γ

  export covering
  parseCtxEq0 : Rule CtxEq
  parseCtxEq0 = do
    g0 <- parseCtxEq1
    (do sp; str_ "·"; sp; g1 <- parseCtxEq1; sp; str_ "via"; sp; g <- parseCtx
        pure (CtxEq.Trans g0 g1 g))
      <|> pure g0

  covering
  parseCtxEq1 : Rule CtxEq
  parseCtxEq1 = do
    g <- parseCtxEq2
    exts <- many (do sp; str_ "ᐅ"; sp; a <- parseTyEq0; pure a)
    pure (foldl CtxEq.Ext g exts)

  covering
  parseCtxEq2 : Rule CtxEq
  parseCtxEq2 = do
    g <- parseCtxEq3
    syms <- many (sp *> str_ "⁻¹")
    pure (foldl (\acc, () => CtxEq.Sym acc) g syms)

  covering
  parseCtxEq3 : Rule CtxEq
  parseCtxEq3 =
        (str_ "ε" $> CtxEq.Empty)
    <|> (str_ "refl" $> CtxEq.Refl)
    <|> inParen parseCtxEq0

  -- ===== Ty (T) =====
  -- T{4} ::= 𝟘 | 𝟙 | ℕ | 𝕌 | (T{≥0})
  -- T{3} ::= (Γ ⊦ T{≥0})[σ{≥0}]
  -- T{2} ::= El t{≥3} | coe-ctx T{≥0} via (Γ, Γ⁼{≥0})
  -- T{1} ::= T{≥2} → T{≥1} | T{≥2} ⨯ T{≥1} | T{≥2} / T{≥1}   (right-assoc)
  -- T{0} ::= t{≥2} ≡ t{≥2} ∈ T{≥1}

  export covering
  parseTy0 : Rule Ty
  parseTy0 =
        (do a <- parseElem2; sp; str_ "≡"; sp; b <- parseElem2; sp; str_ "∈"; sp
            t <- parseTy1
            pure (Ty.EqTy a b t))
    <|> parseTy1

  covering
  parseTy1 : Rule Ty
  parseTy1 = do
    a <- parseTy2
    (do sp; str_ "→"; sp; b <- parseTy1; pure (Ty.PiTy a b))
      <|> (do sp; str_ "⨯"; sp; b <- parseTy1; pure (Ty.SigmaTy a b))
      <|> (do sp; str_ "/"; sp; b <- parseTy1; pure (Ty.Quotient a b))
      <|> pure a

  covering
  parseTy2 : Rule Ty
  parseTy2 =
        (do str_ "El"; space; e <- parseElem3; pure (Ty.El e))
    <|> (do str_ "coe-ctx"; space; a <- parseTy0; space; str_ "via"; sp
            char_ '('; sp; g <- parseCtx; sp; char_ ','; sp; geq <- parseCtxEq0; sp; char_ ')'
            pure (Ty.CoeCtx a g geq))
    <|> parseTy3

  covering
  parseTy3 : Rule Ty
  parseTy3 =
        (do char_ '('; sp; g <- parseCtx; sp; str_ "⊦"; sp; a <- parseTy0; sp; char_ ')'
            sp; char_ '['; sp; s <- parseSub0; sp; char_ ']'
            pure (Ty.Subst g a s))
    <|> parseTy4

  covering
  parseTy4 : Rule Ty
  parseTy4 =
        (str_ "𝟘" $> Ty.ZeroTy)
    <|> (str_ "𝟙" $> Ty.OneTy)
    <|> (str_ "ℕ" $> Ty.NatTy)
    <|> (str_ "𝕌" $> Ty.UniverseTy)
    <|> inParen parseTy0

  -- ===== TyEq (T⁼) =====
  -- T⁼{4} ::= 𝟘 | 𝟙 | ℕ | 𝕌 | refl | (T⁼{≥0})
  -- T⁼{3} ::= T⁼{≥3} ⁻¹ | (Γ ⊦ T⁼{≥0} of T{≥0} = T{≥0})[σ{≥0}]
  -- T⁼{2} ::= El t⁼{≥3} | coe-ctx T⁼{≥0} via (Γ, Γ⁼{≥0}) | 𝟘-elim t{≥4}
  -- T⁼{1} ::= T⁼{≥2} → T⁼{≥1} | T⁼{≥2} ⨯ T⁼{≥1} | T⁼{≥2} / T⁼{≥1}   (right-assoc)
  -- T⁼{0} ::= t⁼{≥2} ≡ t⁼{≥2} ∈ T⁼{≥1} | T⁼{≥1} · T⁼{≥1} via T{≥0}

  export covering
  parseTyEq0 : Rule TyEq
  parseTyEq0 =
        (do a <- parseElemEq2; sp; str_ "≡"; sp; b <- parseElemEq2; sp; str_ "∈"; sp
            t <- parseTyEq1
            pure (TyEq.EqTy a b t))
    <|> (do a0 <- parseTyEq1
            (do sp; str_ "·"; sp; a1 <- parseTyEq1; sp; str_ "via"; sp; a <- parseTy0
                pure (TyEq.Trans a0 a1 a))
              <|> pure a0)

  covering
  parseTyEq1 : Rule TyEq
  parseTyEq1 = do
    a <- parseTyEq2
    (do sp; str_ "→"; sp; b <- parseTyEq1; pure (TyEq.PiTy a b))
      <|> (do sp; str_ "⨯"; sp; b <- parseTyEq1; pure (TyEq.SigmaTy a b))
      <|> (do sp; str_ "/"; sp; b <- parseTyEq1; pure (TyEq.Quotient a b))
      <|> pure a

  covering
  parseTyEq2 : Rule TyEq
  parseTyEq2 =
        (do str_ "𝟘-elim"; space; e <- parseElem4; pure (TyEq.ZeroElim e))
    <|> (str_ "El-𝟘" $> TyEq.ElZero)
    <|> (str_ "El-𝟙" $> TyEq.ElOne)
    <|> (str_ "El-ℕ" $> TyEq.ElNat)
    <|> (do str_ "El-→"; space; a <- parseElem4; space; b <- parseElem4; pure (TyEq.ElPi a b))
    <|> (do str_ "El-⨯"; space; a <- parseElem4; space; b <- parseElem4; pure (TyEq.ElSigma a b))
    <|> (do str_ "El-≡"; space; a0 <- parseElem4; space; a1 <- parseElem4; space; bigA <- parseElem4
            pure (TyEq.ElEq a0 a1 bigA))
    <|> (do str_ "El"; space; e <- parseElemEq3; pure (TyEq.El e))
    <|> (do str_ "coe-ctx"; space; a <- parseTyEq0; space; str_ "via"; sp
            char_ '('; sp; g <- parseCtx; sp; char_ ','; sp; geq <- parseCtxEq0; sp; char_ ')'
            pure (TyEq.CoeCtx a g geq))
    <|> parseTyEq3

  covering
  parseTyEq3 : Rule TyEq
  parseTyEq3 = do
    a <- parseTyEq3Atom
    syms <- many (sp *> str_ "⁻¹")
    pure (foldl (\acc, () => TyEq.Sym acc) a syms)

  covering
  parseTyEq3Atom : Rule TyEq
  parseTyEq3Atom =
        (do char_ '('; sp; g <- parseCtx; sp; str_ "⊦"; sp; a <- parseTyEq0
            space; str_ "of"; space; t0 <- parseTy0; sp; str_ "≐"; sp; t1 <- parseTy0; sp; char_ ')'
            sp; char_ '['; sp; s <- parseSub0; sp; char_ ']'
            pure (TyEq.Subst g a t0 t1 s))
    <|> parseTyEq4

  covering
  parseTyEq4 : Rule TyEq
  parseTyEq4 =
        (str_ "𝟘" $> TyEq.ZeroTy)
    <|> (str_ "𝟙" $> TyEq.OneTy)
    <|> (str_ "ℕ" $> TyEq.NatTy)
    <|> (str_ "𝕌" $> TyEq.UniverseTy)
    <|> (str_ "refl" $> TyEq.Refl)
    <|> inParen parseTyEq0

  -- ===== Sub (σ) =====
  -- σ{2} ::= · | id | ↑ | (σ{≥0})
  -- σ{1} ::= σ{≥2} ∘ σ{≥1} via Γ   (right-assoc)
  -- σ{0} ::= σ{≥0} , t{≥1}         (left-assoc)

  export covering
  parseSub0 : Rule Sub
  parseSub0 = do
    s <- parseSub1
    rest <- many (do sp; char_ ','; sp; e <- parseElem1; pure e)
    pure (foldl Sub.Ext s rest)

  covering
  parseSub1 : Rule Sub
  parseSub1 = do
    s <- parseSub2
    (do sp; str_ "∘"; sp; t <- parseSub1; sp; str_ "via"; sp; g <- parseCtx
        pure (Sub.Chain s t g))
      <|> pure s

  covering
  parseSub2 : Rule Sub
  parseSub2 =
        (str_ "·"  $> Sub.Terminal)
    <|> (str_ "id" $> Sub.Id)
    <|> (str_ "↑"  $> Sub.Wk)
    <|> inParen parseSub0

  -- ===== SubNorm (t˲) =====
  -- t˲{1} ::= · | coe-dom t˲{≥0} via (Γ, Γ⁼{≥0}) | coe-codom t˲{≥0} via (Γ, Γ⁼{≥0}) | (t˲{≥0})
  -- t˲{0} ::= t˲{≥1} , t{≥1} | t˲{≥1} ∘ σ{≥0} via Γ   (`,` left-assoc)

  export covering
  parseSubNorm0 : Rule SubNorm
  parseSubNorm0 = do
    s <- parseSubNorm1
    conts <- many (
          (do sp; char_ ','; sp; e <- parseElem1; pure (Left e))
      <|> (do sp; str_ "∘"; sp; t <- parseSub0; sp; str_ "via"; sp; g <- parseCtx; pure (Right (t, g))))
    pure (foldl (\acc, c => case the (Either Elem (Sub, Ctx)) c of
                              Left e      => SubNorm.Ext acc e
                              Right (t,g) => SubNorm.Chain acc t g)
                s conts)

  covering
  parseSubNorm1 : Rule SubNorm
  parseSubNorm1 =
        (str_ "·" $> SubNorm.Terminal)
    <|> (do str_ "coe-dom"; space; s <- parseSubNorm0; space; str_ "via"; sp
            char_ '('; sp; g <- parseCtx; sp; char_ ','; sp; geq <- parseCtxEq0; sp; char_ ')'
            pure (SubNorm.CoeDom s g geq))
    <|> (do str_ "coe-codom"; space; s <- parseSubNorm0; space; str_ "via"; sp
            char_ '('; sp; g <- parseCtx; sp; char_ ','; sp; geq <- parseCtxEq0; sp; char_ ')'
            pure (SubNorm.CoeCodom s g geq))
    <|> inParen parseSubNorm0

  -- ===== SubNormEq (t˲⁼) =====
  -- t˲⁼{2} ::= · | refl | coe-dom t˲⁼{≥0} via (Γ, Γ⁼{≥0}) | coe-codom t˲⁼{≥0} via (Γ, Γ⁼{≥0}) | (t˲⁼{≥0})
  -- t˲⁼{1} ::= t˲⁼{≥1} ⁻¹
  -- t˲⁼{0} ::= t˲⁼{≥1} , t⁼{≥1} | t˲⁼{≥1} ∘ σ{≥0} via Γ of t˲{≥1} = t˲{≥1} | t˲⁼{≥1} · t˲⁼{≥1} via t˲{≥0}   (`,` left-assoc)

  export covering
  parseSubNormEq0 : Rule SubNormEq
  parseSubNormEq0 = do
    s <- parseSubNormEq1
    conts <- many (
          (do sp; char_ ','; sp; e <- parseElemEq1; pure (Left e))
      <|> (do sp; str_ "∘"; sp; t <- parseSub0; sp; str_ "via"; sp; g <- parseCtx
              sp; str_ "of"; sp; e0 <- parseSubNorm1; sp; str_ "≐"; sp; e1 <- parseSubNorm1
              pure (Right (t, g, e0, e1))))
    let s' = foldl (\acc, c => case the (Either ElemEq (Sub, Ctx, SubNorm, SubNorm)) c of
                                  Left e            => SubNormEq.Ext acc e
                                  Right (t,g,e0,e1) => SubNormEq.Chain acc e0 e1 t g)
                   s conts
    (do sp; str_ "·"; sp; s1 <- parseSubNormEq1; sp; str_ "via"; sp; t <- parseSubNorm0
        pure (SubNormEq.Trans s' s1 t))
      <|> pure s'

  covering
  parseSubNormEq1 : Rule SubNormEq
  parseSubNormEq1 = do
    s <- parseSubNormEq2
    syms <- many (sp *> str_ "⁻¹")
    pure (foldl (\acc, () => SubNormEq.Sym acc) s syms)

  covering
  parseSubNormEq2 : Rule SubNormEq
  parseSubNormEq2 =
        (str_ "·" $> SubNormEq.Terminal)
    <|> (str_ "refl" $> SubNormEq.Refl)
    <|> (do str_ "coe-dom"; space; s <- parseSubNormEq0; space; str_ "via"; sp
            char_ '('; sp; g <- parseCtx; sp; char_ ','; sp; geq <- parseCtxEq0; sp; char_ ')'
            pure (SubNormEq.CoeDom s g geq))
    <|> (do str_ "coe-codom"; space; s <- parseSubNormEq0; space; str_ "via"; sp
            char_ '('; sp; g <- parseCtx; sp; char_ ','; sp; geq <- parseCtxEq0; sp; char_ ')'
            pure (SubNormEq.CoeCodom s g geq))
    <|> inParen parseSubNormEq0

  -- ===== Elem (t) =====
  -- t{5} ::= ☐ₙ | () | Z | Refl | 𝟘 | 𝟙 | ℕ | x | (t{≥0})
  -- t{4} ::= (Γ ⊦ t{≥0})[σ{≥0}]
  -- t{3} ::= (t{≥3} : T{≥2} → T{≥1}) t{≥4} | (t{≥3} : T{≥2} ⨯ T{≥1}) .π₁ | (t{≥3} : T{≥2} ⨯ T{≥1}) .π₂
  -- t{2} ::= λ t{≥3} | 𝟘-elim t{≥4} | S t{≥4} | ℕ-elim t{≥4} t{≥4} t{≥4} motive T{≥0}
  --        | class t{≥4} | quote-elim (T{≥2} / T{≥1}) t{≥4} t⁼{≥4} t{≥4} motive T{≥0}
  --        | coe-ctx t{≥0} via (Γ, Γ⁼{≥0}) | coe-ty t{≥0} via (T{≥0}, T⁼{≥0})
  -- t{1} ::= t{≥2} → t{≥1} | t{≥2} ⨯ t{≥1} | t{≥2} ≡ t{≥2} ∈ t{≥2}
  -- t{0} ::= t{≥1} , t{≥0}   (right-assoc)

  export covering
  parseElem0 : Rule Elem
  parseElem0 = do
    a <- parseElem1
    (do sp; char_ ','; sp; b <- parseElem0; pure (Elem.SigmaIntro a b))
      <|> pure a

  -- Elem without top-level comma, used inside Sub.Ext/SubNorm.Ext contexts.
  covering
  parseElem1 : Rule Elem
  parseElem1 = do
    a <- parseElem2
    (do sp; str_ "→"; sp; b <- parseElem1; pure (Elem.PiTyCode a b))
      <|> (do sp; str_ "⨯"; sp; b <- parseElem1; pure (Elem.SigmaTyCode a b))
      <|> (do sp; str_ "≡"; sp; b <- parseElem2; sp; str_ "∈"; sp; c <- parseElem2
              pure (Elem.EqTyCode a b c))
      <|> pure a

  covering
  parseElem2 : Rule Elem
  parseElem2 =
        (do str_ "λ"; space; e <- parseElem3; pure (Elem.PiIntro e))
    <|> (do str_ "𝟘-elim"; space; e <- parseElem4; pure (Elem.ZeroElim e))
    <|> (do str_ "S"; space; e <- parseElem4; pure (Elem.NatIntro1 e))
    <|> (do str_ "ℕ-elim"; space
            z <- parseElem4; space; s <- parseElem4; space; t <- parseElem4
            space; str_ "motive"; space; a <- parseTy0
            pure (Elem.NatElim z s t a))
    <|> (do str_ "class"; space; e <- parseElem4; pure (Elem.Class e))
    <|> (do str_ "quote-elim"; space
            char_ '('; sp; a <- parseTy2; sp; char_ '/'; sp; r <- parseTy1; sp; char_ ')'; space
            f <- parseElem4; space; fEq <- parseElemEq4; space; q <- parseElem4
            space; str_ "motive"; space; b <- parseTy0
            pure (Elem.QuotElim a r f fEq q b))
    <|> (do str_ "coe-ctx"; space; e <- parseElem0; space; str_ "via"; sp
            char_ '('; sp; g <- parseCtx; sp; char_ ','; sp; geq <- parseCtxEq0; sp; char_ ')'
            pure (Elem.CoeCtx e g geq))
    <|> (do str_ "coe-ty"; space; e <- parseElem0; space; str_ "via"; sp
            char_ '('; sp; a <- parseTy0; sp; char_ ','; sp; aeq <- parseTyEq0; sp; char_ ')'
            pure (Elem.CoeTy e a aeq))
    <|> parseElem3

  covering
  parseElem3 : Rule Elem
  parseElem3 =
        (do char_ '('; sp; f <- parseElem3; sp; char_ ':'; sp; a <- parseTy2
            (do sp; str_ "→"; sp; b <- parseTy1; sp; char_ ')'
                sp; e <- parseElem4
                pure (Elem.App f a b e))
              <|> (do sp; str_ "⨯"; sp; b <- parseTy1; sp; char_ ')'
                      sp; (str_ ".π₁" $> Elem.Proj1 f a b) <|> (str_ ".π₂" $> Elem.Proj2 f a b)))
    <|> parseElem4

  covering
  parseElem4 : Rule Elem
  parseElem4 =
        (do char_ '('; sp; g <- parseCtx; sp; str_ "⊦"; sp; e <- parseElem0
            sp; char_ ':'; sp; a <- parseTy0; sp; char_ ')'
            sp; char_ '['; sp; s <- parseSub0; sp; char_ ']'
            pure (Elem.Subst g a e s))
    <|> parseElem5

  covering
  parseElem5 : Rule Elem
  parseElem5 =
        (do str_ "☐"; n <- subscriptNat; pure (Elem.CtxVar n))
    <|> (do char_ '('
            sp
            unit <- optional (char_ ')')
            case unit of
              Just _  => pure Elem.OneIntro
              Nothing => do e <- parseElem0; sp; char_ ')'; pure e)
    <|> (str_ "Refl" $> Elem.Refl)
    <|> (str_ "Z"    $> Elem.NatIntro0)
    <|> (str_ "𝟘"   $> Elem.ZeroTy)
    <|> (str_ "𝟙"   $> Elem.OneTy)
    <|> (str_ "ℕ"   $> Elem.NatTy)
    <|> (do x <- parseIdentifier
            sp; char_ '['; sp; s <- parseSubNorm0; sp; char_ ']'
            pure (Elem.Var x s))

  -- ===== ElemEq (t⁼) =====
  -- t⁼{5} ::= ☐ₙ | () | Z | 𝟘 | 𝟙 | ℕ | refl | x | (t⁼{≥0})
  -- t⁼{4} ::= t⁼{≥4} ⁻¹ | x-β | (Γ ⊦ t⁼{≥0} of t{≥0} = t{≥0} : T{≥0})[σ{≥0}]
  -- t⁼{3} ::= (t⁼{≥3} : T{≥2} → T{≥1}) t⁼{≥4} | (t⁼{≥3} : T{≥2} ⨯ T{≥1}) .π₁ | (t⁼{≥3} : T{≥2} ⨯ T{≥1}) .π₂
  -- t⁼{2} ::= S t⁼{≥4} | λ t⁼{≥3} | class t⁼{≥4} | class⁼ t{≥4} | 𝟘-elim t{≥4}
  --         | ℕ-elim z⁼{≥4} s⁼{≥4} t⁼{≥4} motive T{≥0}
  --         | ℕ-elim-η z{≥4} s{≥4} f⁼{≥4} f₀⁼{≥4} f₁⁼{≥4} t{≥4} motive t{≥0} = t{≥0} : T{≥0}
  --         | quote-elim (T{≥2} / T{≥1}) f⁼{≥4} resp₀{≥4} resp₁{≥4} q⁼{≥4} motive T{≥0}
  --         | reflect t{≥4} | coe-ctx t⁼{≥0} via (Γ, Γ⁼{≥0}) | coe-ty t⁼{≥0} via (T{≥0}, T⁼{≥0})
  -- t⁼{1} ::= t⁼{≥2} → t⁼{≥1} | t⁼{≥2} ⨯ t⁼{≥1} | t⁼{≥2} ≡ t⁼{≥2} ∈ t⁼{≥2}
  -- t⁼{0} ::= t⁼{≥1} , t⁼{≥0} | t⁼{≥1} · t⁼{≥1} via t{≥0}   (`,` right-assoc)

  export covering
  parseElemEq0 : Rule ElemEq
  parseElemEq0 = do
    a <- parseElemEq1
    (do sp; char_ ','; sp; b <- parseElemEq0; pure (ElemEq.SigmaIntro a b))
      <|> (do sp; str_ "·"; sp; b <- parseElemEq1; sp; str_ "via"; sp; t <- parseElem0
              pure (ElemEq.Trans a b t))
      <|> pure a

  covering
  parseElemEq1 : Rule ElemEq
  parseElemEq1 = do
    a <- parseElemEq2
    (do sp; str_ "→"; sp; b <- parseElemEq1; pure (ElemEq.PiTyCode a b))
      <|> (do sp; str_ "⨯"; sp; b <- parseElemEq1; pure (ElemEq.SigmaTyCode a b))
      <|> (do sp; str_ "≡"; sp; b <- parseElemEq2; sp; str_ "∈"; sp; c <- parseElemEq2
              pure (ElemEq.EqTyCode a b c))
      <|> pure a

  covering
  parseElemEq2 : Rule ElemEq
  parseElemEq2 =
        (do str_ "S"; space; e <- parseElemEq4; pure (ElemEq.NatIntro1 e))
    <|> (do str_ "λ"; space; e <- parseElemEq3; pure (ElemEq.PiIntro e))
    <|> (do str_ "class⁼"; space; e <- parseElem4; pure (ElemEq.ClassEq e))
    <|> (do str_ "class"; space; e <- parseElemEq4; pure (ElemEq.Class e))
    <|> (do str_ "𝟘-elim"; space; e <- parseElem4; pure (ElemEq.ZeroElim e))
    <|> (do str_ "Π-β"; space; f <- parseElem4; space; e <- parseElem4
            space; str_ "motive"; space; a <- parseTy0
            pure (ElemEq.PiBeta f e a))
    <|> (do str_ "Π-η"; space; f <- parseElem4
            space; str_ "motive"; space; a <- parseTy0
            pure (ElemEq.PiEta f a))
    <|> (do str_ "Σ-β₁"; space; a <- parseElem4; space; b <- parseElem4
            space; str_ "motive"; space; t <- parseTy0
            pure (ElemEq.SigmaBeta1 a b t))
    <|> (do str_ "Σ-β₂"; space; a <- parseElem4; space; b <- parseElem4
            space; str_ "motive"; space; t <- parseTy0
            pure (ElemEq.SigmaBeta2 a b t))
    <|> (do str_ "Σ-η"; space; e <- parseElem4
            space; str_ "motive"; space; t <- parseTy0
            pure (ElemEq.SigmaEta e t))
    <|> (do str_ "ℕ-elim-β-Z"; space; z <- parseElem4; space; s <- parseElem4
            space; str_ "motive"; space; a <- parseTy0
            pure (ElemEq.NatElimBetaZ z s a))
    <|> (do str_ "ℕ-elim-β-S"; space; z <- parseElem4; space; s <- parseElem4; space; t <- parseElem4
            space; str_ "motive"; space; a <- parseTy0
            pure (ElemEq.NatElimBetaS z s t a))
    <|> (do str_ "ℕ-elim-η"; space
            z <- parseElem4; space; s <- parseElem4; space
            fEq <- parseElemEq4; space; f0Eq <- parseElemEq4; space; f1Eq <- parseElemEq4; space
            t <- parseElem4
            space; str_ "motive"; space; f0 <- parseElem0; sp; str_ "≐"; sp; f1 <- parseElem0
            sp; char_ ':'; sp; a <- parseTy0
            pure (ElemEq.NatElimEta z s fEq f0Eq f1Eq t f0 f1 a))
    <|> (do str_ "ℕ-elim"; space
            zEq <- parseElemEq4; space; sEq <- parseElemEq4; space; tEq <- parseElemEq4
            space; str_ "motive"; space; a <- parseTy0
            pure (ElemEq.NatElim zEq sEq tEq a))
    <|> (do str_ "quote-elim-β"; space
            char_ '('; sp; a <- parseTy2; sp; char_ '/'; sp; r <- parseTy1; sp; char_ ')'; space
            f <- parseElem4; space; fEq <- parseElemEq4; space; e <- parseElem4
            space; str_ "motive"; space; b <- parseTy0
            pure (ElemEq.QuotElimBeta a r f fEq e b))
    <|> (do str_ "quote-elim-η"; space
            char_ '('; sp; a <- parseTy2; sp; char_ '/'; sp; r <- parseTy1; sp; char_ ')'; space
            g <- parseElem4; space; f <- parseElem4; space; fEq <- parseElemEq4; space
            eEq <- parseElemEq4; space; q <- parseElem4
            space; str_ "motive"; space; b <- parseTy0
            pure (ElemEq.QuotElimEta a r g f fEq eEq q b))
    <|> (do str_ "quote-elim"; space
            char_ '('; sp; a <- parseTy2; sp; char_ '/'; sp; r <- parseTy1; sp; char_ ')'; space
            fEq <- parseElemEq4; space; resp0 <- parseElemEq4; space; resp1 <- parseElemEq4
            space; qEq <- parseElemEq4
            space; str_ "motive"; space; b <- parseTy0
            pure (ElemEq.QuotElim a r fEq resp0 resp1 qEq b))
    <|> (do str_ "reflect"; space; e <- parseElem4; pure (ElemEq.Reflect e))
    <|> (do str_ "coe-ctx"; space; e <- parseElemEq0; space; str_ "via"; sp
            char_ '('; sp; g <- parseCtx; sp; char_ ','; sp; geq <- parseCtxEq0; sp; char_ ')'
            pure (ElemEq.CoeCtx e g geq))
    <|> (do str_ "coe-ty"; space; e <- parseElemEq0; space; str_ "via"; sp
            char_ '('; sp; a <- parseTy0; sp; char_ ','; sp; aeq <- parseTyEq0; sp; char_ ')'
            pure (ElemEq.CoeTy e a aeq))
    <|> parseElemEq3

  covering
  parseElemEq3 : Rule ElemEq
  parseElemEq3 =
        (do char_ '('; sp; f <- parseElemEq3; sp; char_ ':'; sp; a <- parseTy2
            (do sp; str_ "→"; sp; b <- parseTy1; sp; char_ ')'
                sp; e <- parseElemEq4
                pure (ElemEq.App f a b e))
              <|> (do sp; str_ "⨯"; sp; b <- parseTy1; sp; char_ ')'
                      sp; (str_ ".π₁" $> ElemEq.Proj1 f a b) <|> (str_ ".π₂" $> ElemEq.Proj2 f a b)))
    <|> parseElemEq4

  covering
  parseElemEq4 : Rule ElemEq
  parseElemEq4 = do
    a <- parseElemEq4Atom
    syms <- many (sp *> str_ "⁻¹")
    pure (foldl (\acc, () => ElemEq.Sym acc) a syms)

  covering
  parseElemEq4Atom : Rule ElemEq
  parseElemEq4Atom =
        (do char_ '('; sp; g <- parseCtx; sp; str_ "⊦"; sp; e <- parseElemEq0
            space; str_ "of"; space; t0 <- parseElem0; sp; str_ "≐"; sp; t1 <- parseElem0
            sp; char_ ':'; sp; a <- parseTy0; sp; char_ ')'
            sp; char_ '['; sp; s <- parseSub0; sp; char_ ']'
            pure (ElemEq.Subst g e t0 t1 a s))
    <|> parseElemEq5

  covering
  parseElemEq5 : Rule ElemEq
  parseElemEq5 =
        (do str_ "☐"; n <- subscriptNat; pure (ElemEq.CtxVar n))
    <|> (do char_ '('
            sp
            unit <- optional (char_ ')')
            case unit of
              Just _  => pure ElemEq.OneIntro
              Nothing => do e <- parseElemEq0; sp; char_ ')'; pure e)
    <|> (str_ "Z"    $> ElemEq.NatIntro0)
    <|> (str_ "𝟘"   $> ElemEq.ZeroTy)
    <|> (str_ "𝟙"   $> ElemEq.OneTy)
    <|> (str_ "ℕ"   $> ElemEq.NatTy)
    <|> (str_ "refl" $> ElemEq.Refl)
    <|> (do x <- parseIdentifier
            (str_ "-β" $> ElemEq.Unfold x) <|> pure (ElemEq.Var x))

-- ===== SigEntry / Sig (Σ) =====
-- SigEntry ::= Γ ⊦ x ≔ t{≥0} : T{≥0}
-- Sig      ::= ε | Sig SigEntry   (concretely: one "- <entry>" per line,
--                                  matching the .rules/.target list convention)

export covering
parseSigEntry : Rule SigEntry
parseSigEntry = do
  g <- parseCtx
  sp; str_ "⊦"; sp
  x <- parseIdentifier
  sp; str_ "≔"; sp
  t <- parseElem0
  sp; char_ ':'; sp
  a <- parseTy0
  pure (MkSigEntry g x t a)

export covering
parseSig : Rule Sig
parseSig = do
  entries <- many (do sp; char_ '-'; space; e <- parseSigEntry; pure e)
  pure (foldl (:<) [<] entries)
