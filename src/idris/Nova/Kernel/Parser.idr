module Nova.Kernel.Parser

import Data.List
import Data.Maybe
import Data.SnocList
import Data.String

import Me.Russoul.Text.Lexer.Token
import Me.Russoul.Text.Lexer
import Me.Russoul.Text.Parser
import Me.Russoul.Text.Parser.OverToken
import Me.Russoul.Text.Position
import Me.Russoul.Text.Range

import Nova.Kernel.Syntax

||| Semantic classification of a token span. Accumulated in the
||| grammar's state as parsing proceeds (see `emit`), so a classifier
||| never has to re-derive what the parser already knows structurally.
||| Mirrors the docs renderer's highlighting classes
||| (tools/render-specs.py's DEFAULT_VOCAB: kw/tos/nova/meta collapse
||| to Keyword/Identifier here since surface files have no ToS/meta
||| alphabets to distinguish), for LSP semantic tokens.
public export
data TokenKind = Keyword | Identifier | Operator | Number | Comment

public export
Rule : Type -> Type
Rule = Grammar (SnocList (Range, TokenKind)) Token

||| Record a classified span in the accumulator. A no-op location-wise
||| when the wrapped grammar consumed nothing (bounds returns Nothing).
export
emit : Maybe Range -> TokenKind -> Rule ()
emit Nothing _ = pure ()
emit (Just r) k = update (:< (r, k))

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
  -- e₀ ≡ e₁ ∈ A      (EqTy element: the Ω-valued equality prop; A a TYPE)
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
    e <- parseElemSum
    (do sp; str_ "→"; sp; e' <- parseElemNoComma; pure (Elem.PiTy e e'))
      <|> (do sp; str_ "⨯"; sp; e' <- parseElemNoComma; pure (Elem.SigmaTy e e'))
      <|> (do sp; str_ "/"; sp; e' <- parseElemNoComma; pure (Elem.QuotTy e e'))
      <|> (do sp; str_ "≡"; sp
              e1 <- parseElemSum; sp; str_ "∈"; sp
              t2 <- parseTyEl
              pure (Elem.EqTy e e1 t2))
      <|> pure e

  -- e₁ ⊎ e₂ (right-assoc SumTy element) — non-dependent; binds
  -- TIGHTER than the other infix element formers (Agda's convention:
  -- a ⊎ b → c is (a ⊎ b) → c)
  covering
  parseElemSum : Rule Elem
  parseElemSum = do
    e <- parseElemPrefix
    (do sp; str_ "⊎"; sp; e' <- parseElemSum; pure (Elem.SumTy e e'))
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
    <|> (do str_ "inj₁"; space; e <- parseElemAtom; pure (Inj1 e))
    <|> (do str_ "inj₂"; space; e <- parseElemAtom; pure (Inj2 e))
    <|> (do str_ "⊎-elim"; space
            l <- parseElemAtom; space
            r <- parseElemAtom; space
            t <- parseElemAtom
            pure (SumElim l r t))
    <|> (do str_ "let"; space
            a <- parseElemAtom; space
            b <- parseElemAtom
            pure (Let a b))
    <|> (do str_ "class"; space; e <- parseElemAtom; pure (Class e))
    <|> (do str_ "ν"; space; f <- parsePolyAtom; pure (Elem.NuTy f))
    <|> (do str_ "out"; space; e <- parseElemAtom; pure (Out e))
    <|> (do str_ "corec"; space
            f <- parsePolyAtom; space
            a <- parseElemAtom; space
            g <- parseElemAtom; space
            x <- parseElemAtom
            pure (Corec f a g x))
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
  -- Used for signature variable names. Keywords like Z, S are tried first
  -- in parseElemAtom so they are not consumed as identifiers.
  export covering
  parseSigIdentifier : Rule String
  parseSigIdentifier = do
    c  <- terminal "an identifier" $ \tok =>
            case tok of
              Symbol ch => if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || ch == '_'
                           then Just ch
                           else Nothing
              _ => Nothing
    cs <- many (terminal "more of the identifier" $ \tok =>
            case tok of
              Symbol ch => if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') ||
                              (ch >= '0' && ch <= '9') || ch == '_'
                           then Just ch
                           else Nothing
              _ => Nothing)
    let name = pack (c :: cs)
    guard "an identifier ('\{name}' is a reserved keyword)" (name /= "via" && name /= "to")
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
    <|> (do str_ "Z"
            -- boundary: `Zfoo` is a signature name, not Z then foo
            next <- optional (nextIs "next" (\t => case t of
                      Symbol ch => (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') ||
                                   (ch >= '0' && ch <= '9') || ch == '_' || ch == '\''
                      _ => False))
            case next of
              Just _ => fail "a keyword (this one runs on into an identifier)"
              Nothing => pure NatIntro0)
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

  -- e₀ ≡ e₁ ∈ A      (the equality prop, standing as a type — prop-lift)
  -- A → B             (PiTy)
  -- A ⨯ B             (SigmaTy)
  -- A / r             (QuotTy; r is an Ω-valued Elem)
  -- El e              (El, e is an Elem atom)
  -- 𝟘 𝟙 ℕ 𝕌 Ω        (constant types)
  export covering
  parseTy : Rule Ty
  parseTy =
        (do e0 <- parseElemPrefix; sp
            str_ "≡"; sp
            e1 <- parseElemPrefix; sp
            str_ "∈"; sp
            a  <- parseTyArrow
            pure (Elem.EqTy e0 e1 a))
    <|> parseTyArrow

  -- A → B  or  A ⨯ B  or  A / r  (right-associative infix)
  covering
  parseTyArrow : Rule Ty
  parseTyArrow = do
    a <- parseTySum
    (do sp; str_ "→"; sp; b <- parseTyArrow; pure (PiTy a b))
      <|> (do sp; str_ "⨯"; sp; b <- parseTyArrow; pure (SigmaTy a b))
      <|> (do sp; str_ "/"; sp; r <- parseElemNoComma; pure (QuotTy a r))
      <|> pure a

  -- A ⊎ B (right-assoc, non-dependent) — tighter than → ⨯ /
  covering
  parseTySum : Rule Ty
  parseTySum = do
    a <- parseTyEl
    (do sp; str_ "⊎"; sp; b <- parseTySum; pure (SumTy a b))
      <|> pure a

  -- ν F  (El and Prf are retired — a code or a prop in type position
  -- is just the code / the prop)
  covering
  parseTyEl : Rule Ty
  parseTyEl =
        (do str_ "ν"; space; f <- parsePolyAtom; pure (NuTy f))
    <|> parseTyAtom

  -- Polynomials (one-hole codes): binders and products at the top,
  -- sums tighter, atoms innermost — the surface grammar's levels.
  covering
  parsePoly : Rule Poly
  parsePoly =
        (do f <- parsePolySum
            (do sp; str_ "⨯"; sp; g <- parsePoly; pure (PProd f g))
              <|> pure f)
    -- binding forms: a CODE left-hand side (El retired) binds a Nova
    -- variable in the body
    <|> (do a <- parseElemAtom; sp
            (do str_ "⨯"; sp; f <- parsePoly; pure (PSigma a f))
              <|> (do str_ "→"; sp; f <- parsePoly; pure (PPi a f)))

  covering
  parsePolySum : Rule Poly
  parsePolySum = do
    f <- parsePolyAtom
    (do sp; str_ "⊎"; sp; g <- parsePolySum; pure (PSum f g))
      <|> pure f

  covering
  parsePolyAtom : Rule Poly
  parsePolyAtom =
        (str_ "𝕏" $> PHole)
    <|> (do str_ "K"; space; a <- parseElemAtom; pure (PConst a))
    <|> (do char_ '('; sp; f <- parsePoly; sp; char_ ')'; pure f)

  -- Constant types, signature type variable, and parenthesised type
  covering
  parseTyAtom : Rule Ty
  parseTyAtom =
        (str_ "𝟘" $> ZeroTy)
    <|> (str_ "𝟙" $> OneTy)
    <|> (str_ "ℕ" $> NatTy)
    <|> (str_ "𝕌" $> UniverseTy)
    <|> (str_ "Ω" $> PropTy)
    <|> (do x <- parseSigIdentifier
            sp; char_ '['; sp; es <- parseSubNorm; sp; char_ ']'
            pure (SigVar x es))
    <|> inParen parseTy
    -- El retired: a code atom in type position is the type
    <|> parseElemAtom

-- ===== Parse-error rendering =====

-- `ParsingError`'s own `Show` is a debugging dump: internal jargon
-- ("PARSING ERROR", "Last commited"), the state accumulator, and
-- positions spelled inline. None of that belongs in a compiler
-- diagnostic — the LOCATION is the renderer's job
-- (`Nova.Diagnostic`), so what these produce is the location-free
-- half: what the grammar wanted, and what it found instead.

||| Humanize one accumulated expectation. The combinator library
||| spells a character terminal "Expected symbol: x" and a string one
||| "Expected string: xs" (the lexer emits one token per CHARACTER, so
||| even a keyword is matched letter by letter); everything else is a
||| hand-written label from this grammar's own `terminal`/`fail`/
||| `guard` calls and already reads as prose.
humanExpectation : String -> String
humanExpectation s =
  fromMaybe s $
        (\c => "'\{c}'") <$> dropPrefix "Expected symbol: "
    <|> (\c => "'\{c}'") <$> dropPrefix "Expected string: "
    <|> ("end of input" <$ dropPrefix "Expected end of input")
 where
  dropPrefix : String -> Maybe String
  dropPrefix p = if isPrefixOf p s then Just (substr (length p) (length s) s) else Nothing

||| "a", "a or b", "a, b or c" — the expectation listing.
oneOf : List String -> String
oneOf [] = "something else"
oneOf [x] = x
oneOf xs = case unsnoc' xs of
  Nothing => "something else"
  Just (init, last) => "\{joinBy ", " init} or \{last}"
 where
  unsnoc' : List String -> Maybe (List String, String)
  unsnoc' ys = case reverse ys of
    [] => Nothing
    (y :: rest) => Just (reverse rest, y)

||| What the parser was looking at when it gave up. Tokens are single
||| characters (see `Me.Russoul.Text.Lexer`), so this names the
||| character rather than pretending to a wider token.
found : List (Range, Token) -> String
found [] = "reached the end of the file"
found ((_, Symbol c) :: _) = "found '\{cast {to = String} c}'"
found ((_, Whitespace) :: _) = "found whitespace"
found ((_, Comment _) :: _) = "found a comment"

||| The message half of a parse failure: expectations and what was
||| found. Carries no position — `Nova.Diagnostic` places it.
export
parseErrMessage : ParsingError Token st -> String
parseErrMessage (Error expected _ _ _ leftover) =
  -- the same absorption `showExpected` applies (an expectation
  -- contained in another is redundant to print), kept here so the
  -- pieces stay a LIST all the way to the listing
  let kept = filter (\x => not (any (\y => x /= y && isInfixOf x y) expected)) expected in
  "expected \{oneOf (nub (map humanExpectation kept))}, but \{found leftover}"

||| Secondary lines for a parse failure: where the parser had
||| committed, which is the construct the failure sits inside
||| (`commit` is placed right after an item's or a definiens' opening
||| keyword — see `Nova.Elaboration.Parser`).
export
parseErrNotes : ParsingError Token st -> List String
parseErrNotes (Error _ _ Nothing _ _) = []
parseErrNotes (Error _ _ (Just p) _ _) =
  ["while parsing the construct beginning at \{show (p.line + 1)}:\{show (p.column + 1)}"]

-- ===== Convenience runner =====

export
runParser : Rule a -> String -> Either String a
runParser rule input =
  let (_, toks) = tokenise (unpack input) in
  case parseWith [<] (rule <* eof) toks of
    Left err  => Left (parseErrMessage err)
    Right (_, _, x, _) => Right x
