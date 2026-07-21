module Nova.Kernel.Parser

import Data.SnocList

import Me.Russoul.Text.Lexer.Token
import Me.Russoul.Text.Lexer
import Me.Russoul.Text.Parser
import Me.Russoul.Text.Parser.OverToken
import Me.Russoul.Text.Position
import Me.Russoul.Text.Range

import Nova.Kernel.Syntax

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
-- Sub and Elem are mutually recursive because Sub.Ext : Sub -> Elem -> Sub
-- embeds an Elem. (SigVar's substitution argument is a SubNorm, i.e. a plain
-- SnocList Elem — it doesn't depend on Sub at all.)

mutual
  -- σ, e₁, e₂   (left-assoc Ext)
  -- ·            (Terminal)
  --
  -- No id/↑/∘: nothing in this codebase's derivations ever needs the
  -- general Sub constructed via identity, weakening, or composition —
  -- every substitution actually used is written as an explicit, flat
  -- extension list, exactly like SubNorm's own grammar. Id/Wk/Chain still
  -- exist on the core Sub type (used internally, e.g. for quotient-type
  -- formation's `A[↑]`) — they're just not surface-syntax-constructible
  -- via a dedicated sub-id/sub-wk/sub-chn rule anymore.
  export covering
  parseSub : Rule Sub
  parseSub = do
    str_ "·"
    rest <- many (do sp; char_ ','; sp; e <- parseElemNoComma; pure e)
    pure (foldl Ext Terminal rest)

  -- e₁ , e₂          (right-assoc SigmaIntro)
  -- e₁ → e₂          (right-assoc PiTy element)
  -- e₁ ⨯ e₂          (right-assoc SigmaTy element)
  -- e₁ / e₂          (right-assoc QuotTy element)
  -- e₀ ≡ e₁ ∈ e₂     (EqTy element)
  -- λ e               (PiIntro)
  -- S e               (NatIntro1)
  -- 𝟘-elim e          (ZeroElim)
  -- ℕ-elim z s t      (NatElim)
  -- class e           (Class)
  -- quot-elim f q     (QuotElim)
  -- e @               (PiElim)
  -- e .π₁             (SigmaElim1)
  -- e .π₂             (SigmaElim2)
  -- ☐ₙ                (CtxVar)
  -- ()                (OneIntro)
  -- Z                 (NatIntro0)
  -- Refl              (Refl)
  -- 𝟘 𝟙 ℕ            (universe codes ZeroTy OneTy NatTy)
  -- x[t˲]             (SigVar)
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
      <|> (do sp; str_ "/"; sp; e' <- parseElemNoComma; pure (Elem.QuotTy e e'))
      <|> (do sp; str_ "≡"; sp
              e1 <- parseElemPrefix; sp; str_ "∈"; sp
              e2 <- parseElemPrefix
              pure (Elem.EqTy e e1 e2))
      <|> pure e

  -- Prefix operators: take an atomic argument
  covering
  parseElemPrefix : Rule Elem
  parseElemPrefix =
        (do str_ "λ";      space; e <- parseElemPostfix; pure (PiIntro e))
    <|> (do str_ "𝟘-elim"; space; e <- parseElemAtom; pure (ZeroElim e))
    <|> (do str_ "ℕ-elim"; space
            z <- parseElemAtom; space
            s <- parseElemAtom; space
            t <- parseElemAtom
            pure (NatElim z s t))
    <|> (do str_ "S"; space; e <- parseElemAtom; pure (NatIntro1 e))
    <|> (do str_ "class"; space; e <- parseElemAtom; pure (Class e))
    <|> (do str_ "quot-elim"; space
            f <- parseElemAtom; space
            q <- parseElemAtom
            pure (QuotElim f q))
    <|> parseElemPostfix

  -- Level 3: PiApp and projections (t t, t .π₁, t .π₂, left-assoc)
  -- Argument of application is an atom.
  covering
  parseElemPostfix : Rule Elem
  parseElemPostfix = do
    e <- parseElemAtom
    parseElemPostfixCont e

  covering
  parseElemPostfixCont : Elem -> Rule Elem
  parseElemPostfixCont e =
        (do sp; str_ ".π₁"; parseElemPostfixCont (SigmaElim1 e))
    <|> (do sp; str_ ".π₂"; parseElemPostfixCont (SigmaElim2 e))
    <|> (do sp; e' <- parseElemAtom; parseElemPostfixCont (PiApp e e'))
    <|> pure e

  -- t˲ ::= · | t˲ , t   (normal substitution: a plain snoc-list of elements,
  -- with no Chain/Id/Wk/Terminal — only SigVar carries one of these).
  export covering
  parseSubNorm : Rule SubNorm
  parseSubNorm = do
    str_ "·"
    rest <- many (do sp; char_ ','; sp; e <- parseElemNoComma; pure e)
    pure (foldl (:<) [<] rest)

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
    guard "Reserved keyword" (name /= "via" && name /= "to")
    pure name

  -- Atomic elements: constants, or parenthesised expression.
  -- After '(' peek for ')' to distinguish () = OneIntro from (e).
  export covering
  parseElemAtom : Rule Elem
  parseElemAtom =
        (do str_ "☐"; n <- subscriptNat; pure (CtxVar n))
    <|> (do char_ '('
            sp
            unit <- optional (char_ ')')
            case unit of
              Just _  => pure OneIntro
              Nothing => do e <- parseElem; sp; char_ ')'; pure e)
    <|> (str_ "Refl" $> Refl)
    <|> (str_ "Z"    $> NatIntro0)
    <|> (str_ "⋆"    $> Star)
    <|> (do str_ "∥"; sp; t <- parseTy; sp; str_ "∥"; pure (Squash t))
    <|> (str_ "𝟘"   $> Elem.ZeroTy)
    <|> (str_ "𝟙"   $> Elem.OneTy)
    <|> (str_ "ℕ"   $> Elem.NatTy)
    <|> (do x <- parseSigIdentifier
            sp; char_ '['; sp; es <- parseSubNorm; sp; char_ ']'
            pure (SigVar x es))

  -- ===== Ty parsers =====
  --
  -- Ty depends on Elem for EqTy's Elem arguments and El's argument;
  -- Elem depends back on Ty for ∥T∥'s squashee, so the two live in one
  -- mutual block.

  -- e₀ ≡ e₁ ∈ A      (EqTy:  two Elem args + Ty)
  -- A → B             (PiTy)
  -- A ⨯ B             (SigmaTy)
  -- A / r             (Quotient; r is an Ω-valued Elem)
  -- El e              (El, e is an Elem atom)
  -- Prf e             (Prf, e is an Elem atom)
  -- 𝟘 𝟙 ℕ 𝕌 Ω        (constant types)
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

  -- A → B  or  A ⨯ B  or  A / r  (right-associative infix)
  covering
  parseTyArrow : Rule Ty
  parseTyArrow = do
    a <- parseTyEl
    (do sp; str_ "→"; sp; b <- parseTyArrow; pure (Ty.PiTy a b))
      <|> (do sp; str_ "⨯"; sp; b <- parseTyArrow; pure (Ty.SigmaTy a b))
      <|> (do sp; str_ "/"; sp; r <- parseElemNoComma; pure (Ty.Quotient a r))
      <|> pure a

  -- El e / Prf e  (prefix, argument is an Elem atom)
  covering
  parseTyEl : Rule Ty
  parseTyEl =
        (do str_ "El"; space; e <- parseElemAtom; pure (El e))
    <|> (do str_ "Prf"; space; e <- parseElemAtom; pure (Prf e))
    <|> parseTyAtom

  -- Constant types, signature type variable, and parenthesised type
  covering
  parseTyAtom : Rule Ty
  parseTyAtom =
        (str_ "𝟘" $> Ty.ZeroTy)
    <|> (str_ "𝟙" $> Ty.OneTy)
    <|> (str_ "ℕ" $> Ty.NatTy)
    <|> (str_ "𝕌" $> Ty.UniverseTy)
    <|> (str_ "Ω" $> Ty.PropTy)
    <|> (do x <- parseSigIdentifier
            sp; char_ '['; sp; es <- parseSubNorm; sp; char_ ']'
            pure (Ty.SigVar x es))
    <|> inParen parseTy

-- ===== Convenience runner =====

export
runParser : Rule a -> String -> Either String a
runParser rule input =
  let (_, toks) = tokenise (unpack input) in
  case parseWith () (rule <* eof) toks of
    Left err  => Left (show err)
    Right (_, _, x, _) => Right x
