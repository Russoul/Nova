module Nova.Foundation.Parser

import Data.SnocList

import Me.Russoul.Text.Lexer.Token
import Me.Russoul.Text.Lexer
import Me.Russoul.Text.Parser
import Me.Russoul.Text.Parser.OverToken
import Me.Russoul.Text.Position
import Me.Russoul.Text.Range

import Nova.Foundation.Syntax

public export
Rule : Type -> Type
Rule = Grammar () Token

-- Optional whitespace between tokens
sp : Rule ()
sp = optSpace

-- Parse content surrounded by parentheses
export
inParen : Rule a -> Rule a
inParen p = do
  char_ '('
  sp
  x <- p
  sp
  char_ ')'
  pure x

-- ===== Block 1: Sub and Elem parsers (mutually recursive) =====
--
-- Sub and Elem are mutually recursive because:
--   Sub.Ext : Sub -> Elem -> Sub
--   Elem.SubstElim : Elem -> Sub -> Elem

mutual
  -- σ, e₁, e₂   (left-assoc Ext)
  -- σ ∘ τ        (right-assoc Chain)
  -- ·            (Terminal)
  -- id           (Id)
  -- ↑            (Wk)
  export covering
  parseSub : Rule Sub
  parseSub = do
    s    <- parseSubChain
    rest <- many (do sp; char_ ','; sp; e <- parseElemNoComma; pure e)
    pure (foldl Ext s rest)

  covering
  parseSubChain : Rule Sub
  parseSubChain = do
    s <- parseSubAtom
    (do sp; str_ "∘"; sp; t <- parseSubChain; pure (Chain s t))
      <|> pure s

  covering
  parseSubAtom : Rule Sub
  parseSubAtom =
        (str_ "·"  $> Terminal)
    <|> (str_ "id" $> Id)
    <|> (str_ "↑"  $> Wk)
    <|> inParen parseSub

  -- e₁ , e₂          (right-assoc SigmaIntro)
  -- e₁ → e₂          (right-assoc PiTy element)
  -- e₁ ⨯ e₂          (right-assoc SigmaTy element)
  -- e₀ ≡ e₁ ∈ e₂     (EqTy element)
  -- λ e               (PiIntro)
  -- S e               (NatIntro1)
  -- 𝟘-elim e          (ZeroElim)
  -- ℕ-elim z s t      (NatElim)
  -- e @               (PiElim)
  -- e .π₁             (SigmaElim1)
  -- e .π₂             (SigmaElim2)
  -- e(σ)              (SubstElim)
  -- ☐                 (CtxVar)
  -- ()                (OneIntro)
  -- Z                 (NatIntro0)
  -- Refl              (Refl)
  -- 𝟘 𝟙 ℕ            (universe codes ZeroTy OneTy NatTy)
  export covering
  parseElem : Rule Elem
  parseElem = do
    e <- parseElemNoComma
    (do sp; char_ ','; sp; e' <- parseElem; pure (SigmaIntro e e'))
      <|> pure e

  -- Element without top-level comma, used inside Sub.Ext and Spine
  -- to avoid ambiguity with SigmaIntro's comma.
  covering
  parseElemNoComma : Rule Elem
  parseElemNoComma = do
    e <- parseElemPrefix
    (do sp; str_ "→"; sp; e' <- parseElemNoComma; pure (Elem.PiTy e e'))
      <|> (do sp; str_ "⨯"; sp; e' <- parseElemNoComma; pure (Elem.SigmaTy e e'))
      <|> (do sp; str_ "≡"; sp
              e1 <- parseElemPrefix; sp; str_ "∈"; sp
              e2 <- parseElemPrefix
              pure (Elem.EqTy e e1 e2))
      <|> pure e

  -- Prefix operators: take an atomic argument
  covering
  parseElemPrefix : Rule Elem
  parseElemPrefix =
        (do str_ "λ";      space; e <- parseElemAtom; pure (PiIntro e))
    <|> (do str_ "𝟘-elim"; space; e <- parseElemAtom; pure (ZeroElim e))
    <|> (do str_ "ℕ-elim"; space
            z <- parseElemAtom; space
            s <- parseElemAtom; space
            t <- parseElemAtom
            pure (NatElim z s t))
    <|> (do str_ "S"; space; e <- parseElemAtom; pure (NatIntro1 e))
    <|> parseElemPostfix

  -- Level 4: SubstElim postfix on atoms (t[σ], left-assoc)
  covering
  parseElemSubst : Rule Elem
  parseElemSubst = do
    e <- parseElemAtom
    parseElemSubstCont e

  covering
  parseElemSubstCont : Elem -> Rule Elem
  parseElemSubstCont e =
    (do sp; char_ '['; sp; s <- parseSub; sp; char_ ']'
        parseElemSubstCont (Elem.SubstElim e s))
    <|> pure e

  -- Level 3: PiApp and projections (t t, t .π₁, t .π₂, left-assoc)
  -- Argument of application is at level 4 (may be a substituted term).
  covering
  parseElemPostfix : Rule Elem
  parseElemPostfix = do
    e <- parseElemSubst
    parseElemPostfixCont e

  covering
  parseElemPostfixCont : Elem -> Rule Elem
  parseElemPostfixCont e =
        (do sp; str_ ".π₁"; parseElemPostfixCont (SigmaElim1 e))
    <|> (do sp; str_ ".π₂"; parseElemPostfixCont (SigmaElim2 e))
    <|> (do sp; e' <- parseElemSubst; parseElemPostfixCont (PiApp e e'))
    <|> pure e

  -- Conservative ASCII identifier: letter or '_' followed by letters, digits, or '_'.
  -- Used for signature variable names. Keywords like Z, Refl, S are tried first
  -- in parseElemAtom so they are not consumed as identifiers.
  export covering
  parseSigIdentifier : Rule String
  parseSigIdentifier = do
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
    guard "Reserved keyword: via" (name /= "via")
    pure name

  -- Atomic elements: constants, or parenthesised expression.
  -- After '(' peek for ')' to distinguish () = OneIntro from (e).
  export covering
  parseElemAtom : Rule Elem
  parseElemAtom =
        (str_ "☐" $> CtxVar)
    <|> (do char_ '('
            sp
            unit <- optional (char_ ')')
            case unit of
              Just _  => pure OneIntro
              Nothing => do e <- parseElem; sp; char_ ')'; pure e)
    <|> (str_ "Refl" $> Refl)
    <|> (str_ "Z"    $> NatIntro0)
    <|> (str_ "𝟘"   $> Elem.ZeroTy)
    <|> (str_ "𝟙"   $> Elem.OneTy)
    <|> (str_ "ℕ"   $> Elem.NatTy)
    <|> map SigVar parseSigIdentifier

-- ===== Block 2: Ty parsers =====
--
-- Ty depends on Elem (for EqTy's Elem arguments and El's argument)
-- and on Sub (for SubstElim's substitution). Both are already defined above.
-- Within this block, parseTy ↔ parseTyAtom (via inParen) form a cycle.

mutual
  -- e₀ ≡ e₁ ∈ A      (EqTy:  two Elem args + Ty)
  -- A → B             (PiTy)
  -- A ⨯ B             (SigmaTy)
  -- El e              (El, e is an Elem atom)
  -- A(σ)              (SubstElim, postfix)
  -- 𝟘 𝟙 ℕ 𝕌          (constant types)
  export covering
  parseTy : Rule Ty
  parseTy =
        (do e0 <- parseElemPrefix; sp
            str_ "≡"; sp
            e1 <- parseElemPrefix; sp
            str_ "∈"; sp
            a  <- parseTyArrow
            pure (Ty.EqTy e0 e1 a))
    <|> parseTyArrow

  -- A → B  or  A ⨯ B  (right-associative infix)
  covering
  parseTyArrow : Rule Ty
  parseTyArrow = do
    a <- parseTyEl
    (do sp; str_ "→"; sp; b <- parseTyArrow; pure (Ty.PiTy a b))
      <|> (do sp; str_ "⨯"; sp; b <- parseTyArrow; pure (Ty.SigmaTy a b))
      <|> pure a

  -- El e  (prefix El; no postfix subst — El is at level 2, subst is level 3)
  covering
  parseTyEl : Rule Ty
  parseTyEl =
        (do str_ "El"; space; e <- parseElemAtom; pure (El e))
    <|> parseTyPostfix

  -- Apply postfix subst A(σ)(τ)... to an already-parsed type
  covering
  parseTyPostfix : Rule Ty
  parseTyPostfix = do
    a <- parseTyAtom
    parseTyPostfixCont a

  covering
  parseTyPostfixCont : Ty -> Rule Ty
  parseTyPostfixCont a =
        (do sp; char_ '['; sp; s <- parseSub; sp; char_ ']'; parseTyPostfixCont (Ty.SubstElim a s))
    <|> pure a

  -- Constant types and parenthesised type
  covering
  parseTyAtom : Rule Ty
  parseTyAtom =
        (str_ "𝟘" $> Ty.ZeroTy)
    <|> (str_ "𝟙" $> Ty.OneTy)
    <|> (str_ "ℕ" $> Ty.NatTy)
    <|> (str_ "𝕌" $> Ty.UniverseTy)
    <|> inParen parseTy

-- ===== Ctx, Tel, Spine =====

-- Γ ::= ε | Γ ᐅ A   (snoc list, left-associative)
export covering
parseCtx : Rule Ctx
parseCtx = do
  str_ "ε"
  exts <- many (do sp; str_ "ᐅ"; sp; parseTy)
  pure (foldl (:<) Lin exts)

-- Δ ::= ε | A ◁ Δ   (list, right-associative)
export covering
parseTel : Rule Tel
parseTel =
      (str_ "ε" $> [])
  <|> (do a <- parseTy
          sp; str_ "◁"; sp
          rest <- parseTel
          pure (a :: rest))

-- ē ::= · | e₁, ..., eₙ   (comma-separated, no trailing ·)
-- Elements in the spine are parsed without top-level comma to avoid
-- ambiguity with SigmaIntro; use parentheses for pairs in spines.
export covering
parseSpine : Rule Spine
parseSpine =
      (str_ "·" $> [])
  <|> (do e    <- parseElemNoComma
          rest <- many (do sp; char_ ','; sp; parseElemNoComma)
          pure (e :: rest))

-- ===== Convenience runner =====

export
runParser : Rule a -> String -> Either String a
runParser rule input =
  let (_, toks) = tokenise (unpack input) in
  case parseWith () (rule <* eof) toks of
    Left err  => Left (show err)
    Right (_, _, x, _) => Right x
