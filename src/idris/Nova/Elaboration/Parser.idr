module Nova.Elaboration.Parser

-- Parser for elaboration surface files (docs/NovaElaboration.txt):
-- named text ⇝ indexed surface AST (Nova.Elaboration.Surface).
--
-- Name resolution happens HERE, during parsing — an unbound identifier
-- is a parse-time error, and the elaborator never sees a name except as
-- display metadata retained in binder positions. Grammar and precedence
-- follow NovaNamedSyntax.txt with the elaboration additions: ascription
-- `(t : T)` and mandatory motive-first eliminator annotations.
--
-- Comments (`--` line, `{- -}` block) are handled by the lexer; this
-- module normalizes Comment tokens into whitespace before parsing so
-- .nova files may be freely commented.

import Data.List
import Data.Maybe
import Data.String
import Data.SnocList

import Me.Russoul.Text.Lexer.Token
import Me.Russoul.Text.Lexer
import Me.Russoul.Text.Parser
import Me.Russoul.Text.Parser.OverToken
import Me.Russoul.Text.Position
import Me.Russoul.Text.Range

import Nova.Kernel.Parser
import Nova.Elaboration.Named
import Nova.Elaboration.Surface

%default covering

sp : Rule ()
sp = optSpace

-- Every fixed-syntax literal match doubles as a semantic-token
-- classification at its exact span (mirrors tools/render-specs.py's
-- "kw" class, which likewise covers both alphabetic keywords and
-- punctuation like `: ; , [ ]`) — every str_/char_ call site below
-- was mechanically renamed to kw/kwc, so this is the one place that
-- decides the classification.
||| Is this a character that may continue an identifier? Keywords whose
||| spelling ends in one must stop at a name boundary: `ZOnly` is an
||| identifier, not the keyword `Z` followed by `Only`.
isNameTail : Char -> Bool
isNameTail ch = (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') ||
                (ch >= '0' && ch <= '9') || ch == '_' || ch == '\''

kw : String -> Rule ()
kw s = do
  (r, ()) <- bounds (str_ s)
  case last' (unpack s) of
    Just c => when (isNameTail c) $ do
      next <- optional (nextIs "next" (\tok => case tok of
                Symbol ch => isNameTail ch
                _ => False))
      case next of
        Just _ => fail "a keyword (this one runs on into an identifier)"
        Nothing => pure ()
    Nothing => pure ()
  emit r Keyword

kwc : Char -> Rule ()
kwc c = do
  (r, ()) <- bounds (char_ c)
  emit r Keyword

||| A token with an ASCII FALLBACK spelling (docs/NovaElaboration.txt,
||| "ASCII fallbacks"). Both spellings parse to the same AST; the
||| Unicode form is tried first and is the only one the distill printer
||| ever emits, so a file written in ASCII normalizes to Unicode.
|||
||| Every fallback is unusable as an operator NAME, which is what keeps
||| `def == : …` from shadowing the equality token. Most get that for
||| free — an operator name is a maximal run of Surface.opChar, so any
||| spelling carrying a non-opChar (`\\`, `:`, `|`, `.`, a letter)
||| cannot be one. The two that are pure opChar runs, `->` and `==`,
||| are reserved explicitly in parseOpName below.
kw2 : (unicode : String) -> (ascii : String) -> Rule ()
kw2 u a = kw u <|> kw a

-- NameEnv and `wildcard` are reused from the derivation named parser —
-- they are front-end-generic (a snoc-list of names, "_").

resolveVar : NameEnv -> String -> Maybe Nat
resolveVar [<] x = Nothing
resolveVar (env :< y) x =
  if x == y && x /= wildcard
    then Just Z
    else map S (resolveVar env x)

-- Same lexical conventions as parseLocalIdentifier, with the item
-- keywords reserved instead of the rule keywords.
parseName : Rule String
parseName = do
  (r, name) <- bounds parseNameRaw
  emit r Identifier
  pure name
 where
  parseNameRaw : Rule String
  parseNameRaw = do
    c  <- terminal "an identifier" $ \tok =>
            case tok of
              Symbol ch => if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || ch == '_'
                           then Just ch
                           else Nothing
              _ => Nothing
    cs <- many (terminal "more of the identifier" $ \tok =>
            case tok of
              Symbol ch => if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') ||
                              (ch >= '0' && ch <= '9') || ch == '_' || ch == '\''
                           then Just ch
                           else Nothing
              _ => Nothing)
    let name = pack (c :: cs)
    -- S/Z/Refl/class are also reserved: unlike def/type/El/import/
    -- infixl/infixr they're syntactically valid identifiers, so without
    -- this a shadowing binder would parse fine and only misbehave at a
    -- REFERENCE site — loudly for S/class (they consume a following atom,
    -- so the parse fails deep and confusingly) or silently for Z/Refl
    -- (bare tokens — a reference just parses as the literal zero/Refl,
    -- no error at all).
    -- let/in are reserved for the same reason as S/class: both are
    -- syntactically valid identifiers, and a binder named `in` would
    -- misparse every let-body boundary after it. `using` joined them
    -- with the elided ≡ (docs/NovaPerfectSurface.txt, Phase 4): an
    -- ∈-less equality's right side is an application chain, which
    -- would otherwise swallow a following using-clause
    guard "an identifier ('\{name}' is a reserved keyword)"
                             (name /= "def" && name /= "type" && name /= "El" &&
                              name /= "import" && name /= "infixl" && name /= "infixr" &&
                              name /= "S" && name /= "Z" && name /= "class" &&
                              name /= "data" && name /= "let" && name /= "in" &&
                              name /= "using" &&
    -- the ASCII spellings of 𝕌 Ω ℕ 𝟘 𝟙 and of the injections: valid
    -- identifiers, so they need the same reservation S/Z/class do, or a
    -- binder of that name would shadow the constructor or constant at
    -- every later reference. The UNICODE spellings need no entry and
    -- could take none: ₁ 𝟘 ℕ are not identifier characters, so inj₁ and
    -- the constants are unshadowable already.
                              name /= "Set" && name /= "Prop" &&
                              name /= "Nat" && name /= "Void" && name /= "Unit" &&
                              name /= "inj1" && name /= "inj2")
    pure name

||| The label of a `?x` HOLE. Identifier-shaped, but NOT an
||| identifier: a hole name resolves against nothing — not Γ, not Σ
||| — so the keyword reservations `parseName` carries (they exist to
||| stop a binder from shadowing a constant at a REFERENCE site) have
||| nothing to protect here. `?in` is a fine name for a goal.
parseHoleLabel : Rule String
parseHoleLabel = do
  c  <- terminal "a hole name" $ \tok =>
          case tok of
            Symbol ch => if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || ch == '_'
                         then Just ch
                         else Nothing
            _ => Nothing
  cs <- many (terminal "more of the hole name" $ \tok =>
          case tok of
            Symbol ch => if isNameTail ch then Just ch else Nothing
            _ => Nothing)
  pure (pack (c :: cs))

||| A decimal numeral — sugar for an S-tower over Z (a maximal digit
||| run; identifiers cannot start with a digit, so no ambiguity).
parseNumeral : Rule Nat
parseNumeral = do
  (r, ds) <- bounds (do d <- digit; ds <- many digit; pure (d :: ds))
  emit r Number
  pure (foldl (\acc, d => acc * 10 + d) 0 ds)
 where
  digit : Rule Nat
  digit = terminal "a decimal digit" $ \tok => case tok of
    Symbol ch => if ch >= '0' && ch <= '9'
                   then Just (cast (ord ch - ord '0'))
                   else Nothing
    _ => Nothing

sucTower : Nat -> SElem
sucTower Z = SZeroN
sucTower (S k) = SSuc (sucTower k)

||| A name with its span — binder positions record it so the LSP can
||| ascribe the elaborated type to the occurrence.
parseNameR : Rule SName
parseNameR = do
  (r, x) <- bounds parseName
  pure (x, r)

||| A possibly-qualified name: x or M.x or A.B.x. The dot only counts
||| when an identifier follows (so `p.π₁` backtracks to a projection).
parseDottedName : Rule String
parseDottedName = do
  n <- parseName
  rest <- many (do kwc '.'; parseName)
  pure (joinBy "." (n :: rest))

||| An operator token: a maximal run of operator-alphabet characters
||| (operators ARE names — see Nova.Elaboration.Surface).
export
parseOpName : Rule String
parseOpName = do
  (r, name) <- bounds parseOpNameRaw
  emit r Operator
  pure name
 where
  opTok : Token -> Maybe Char
  opTok (Symbol ch) = if opChar ch then Just ch else Nothing
  opTok _ = Nothing
  parseOpNameRaw : Rule String
  parseOpNameRaw = do
    c <- terminal "an operator" opTok
    cs <- many (terminal "more of the operator" opTok)
    let name = pack (c :: cs)
    -- The ASCII fallbacks for → and ≡. Every other fallback carries a
    -- non-opChar and so could never be lexed as an operator name; these
    -- two are pure opChar runs, so the exclusion is explicit — without
    -- it `def -> : …` would shadow the arrow token itself.
    guard "an operator name (-> and == spell reserved tokens)"
          (name /= "->" && name /= "==")
    pure name

||| A possibly-qualified operator (+ or M.+): the mention form's and
||| the definition header's name grammar.
parseOpRef : Rule String
parseOpRef = do
  pre <- many (do n <- parseName; kwc '.'; pure n)
  op <- parseOpName
  pure (joinBy "." (pre ++ [op]))

||| A lemma reference for a `using` clause (term-level `⋆ using` and
||| item-level `def … using`): a dotted path whose segments are
||| identifiers or bare operator tokens (no infix context here, so no
||| mention form needed) — M.x, M.+, +.eq and nat.+.eq all name
||| entries (the .eq suffix cites a defining equation).
usingName : Rule String
usingName = do
  n <- parseName <|> parseOpName
  rest <- many (do kwc '.'; parseName <|> parseOpName)
  pure (joinBy "." (n :: rest))

export
parseUsingNames : Rule (List String)
parseUsingNames =
      (do kwc '('; sp
          n <- usingName
          ns <- many (do sp; kwc ','; sp; usingName)
          sp; kwc ')'
          pure (n :: ns))
  <|> (do n <- usingName; pure [n])

||| Grow a spine step's span: from the head's start to what this step
||| consumed. Every PREFIX of an application or projection chain is a
||| node of its own — `f a` inside `f a b` — and each wants its own
||| position, so the level's single span (which covers the whole
||| chain) is not enough.
grew : (head : SElem) -> (step : Maybe Range) -> SElem -> SElem
grew hd step new =
  atPos (case (posOf hd, step) of
           (Just a, Just b) => Just (union a b)
           (a, b) => a <|> b) new

foldGroups : (String -> a -> b -> b) -> List (String, a) -> b -> b
foldGroups f [] b = b
foldGroups f ((x, t) :: rest) b = f x t (foldGroups f rest b)

||| The body of `sigma-elim (x y. t) w`, reindexed from the context it
||| was PARSED against — the site's binders Γ₀ ▷ w ▷ Γ₁ with x and y
||| pushed innermost — to the ELIMINATION context Γ₀ ▷ x ▷ y ▷ Γ₁,
||| where w (index i at the site) is gone and its two components stand
||| where it stood. Nothing when the body mentions w itself: that
||| context has no such entry, and the operator wrote the wrong name.
|||
||| Parsing reads the body BEFORE the scrutinee, so the two-slot push
||| is the only environment available at the time; this remap is what
||| pays for the surface order (docs/NovaElaboration.txt, e-sigmaelim).
sigmaElimBody : (i : Nat) -> SElem -> Maybe SElem
sigmaElimBody i b = mapVarsE remap 0 b
 where
  remap : Nat -> Nat -> Maybe Nat
  remap d k = case minus k d of
    -- the two pushed slots: y innermost, then x — they land where w
    -- stood, y at w's own index and x one further out
    Z         => Just (i + d)
    (S Z)     => Just (S i + d)
    (S (S m)) =>
      if m < i then Just (m + d)               -- inside Γ₁: unchanged
      else if m == i then Nothing              -- w itself: eliminated
      else Just (S m + d)                      -- inside Γ₀: one further out

-- ===== Types and elements (mutually recursive) =====

mutual
  -- Every level of the term and type grammar records the span of what
  -- it parsed (`atPos`/`atPosTy`), so an elaboration error can name
  -- the exact sub-expression it is about. A level that adds no node
  -- of its own hands its child straight back and the two spans
  -- coincide, so re-wrapping replaces rather than nests.

  -- T{0}: eq-type on top, then the arrow level
  export
  parseSTy : FixTable -> NameEnv -> Rule STy
  parseSTy tbl env = do
    (r, x) <- bounds (parseSTyRaw tbl env)
    pure (atPosTy r x)

  -- ONE ≡ production, shared with the element level (SEqC below): sides
  -- at t{≥1¼} so the ⊎ code reaches them, ∈-type at T{≥1} so an arrow
  -- reaches it. The two positions used to disagree on BOTH operands
  -- (type: sides t{≥1½}, ∈-type T{≥1}; element: sides t{≥1¼}, ∈-type
  -- T{≥2}), so `A ⊎ B ≡ C` parsed only as an element and
  -- `a ≡ b ∈ A → B` only as a type. Unified at the more permissive
  -- level of each pair, so no spelling that parsed before stops.
  --
  -- The BINDER form is tried FIRST, ahead of the ≡ branch. A binder
  -- group and an ASCRIPTION are the same tokens — `(x : a)` — and the ≡
  -- branch's sides can now reach the non-dependent ×, so without this
  -- ordering `∥(x : a) × br x ≡ t∥` (bracket.brSurj) parses as the
  -- equation `((x : a) × br x) ≡ t` over an ascribed, unbound `x`
  -- instead of the Σ over an equation that it says. The binder branch
  -- only commits once a → or × follows its groups, so a genuine
  -- ascription — `(x : A) ≡ y` — still falls through to the ≡ branch.
  parseSTyRaw : FixTable -> NameEnv -> Rule STy
  parseSTyRaw tbl env =
        parseSTyBinder tbl env
    <|> (do (r, (e0, e1, ma)) <- bounds (do
              e0 <- parseSElemSumC tbl env; sp
              kw2 "≡" "=="; sp
              e1 <- parseSElemSumC tbl env
              ma <- optional (do sp; kw2 "∈" "\\in"; sp; parseSTyArrow tbl env)
              pure (e0, e1, ma))
            pure (STyEq r e0 e1 ma))
    <|> parseSTyInfix tbl env

  -- T{1}: named binder forms and the sugared right-assoc infixes.
  -- Binder groups iterate: (x:T) (y:U) → B ≡ (x:T) → (y:U) → B
  -- (and likewise for ×).
  parseSTyArrow : FixTable -> NameEnv -> Rule STy
  parseSTyArrow tbl env = do
    (r, x) <- bounds (parseSTyArrowRaw tbl env)
    pure (atPosTy r x)

  parseSTyArrowRaw : FixTable -> NameEnv -> Rule STy
  parseSTyArrowRaw tbl env = parseSTyBinder tbl env <|> parseSTyInfix tbl env

  -- T{1}, binder half. The body is full T{≥0} — a trailing ≡-type needs
  -- no parens, so lemma statements read as written, and the Σ-of-record
  -- idiom keeps its last field bare.
  parseSTyBinder : FixTable -> NameEnv -> Rule STy
  parseSTyBinder tbl env =
    do (env', groups) <- parseBinderGroups tbl env
       sp
       (do kw2 "→" "->"; sp; b <- parseSTy tbl env'
           pure (foldr (\(imp, x, t), acc =>
                         if imp then STyImpPi x t acc else STyPi x t acc) b groups))
         <|> (do kw2 "×" "\\x"; sp
                 guard "!implicit binders are Π-only: {x : T} × … is not a type"
                       (all (\(imp, _, _) => not imp) groups)
                 b <- parseSTy tbl env'
                 pure (foldr (\(_, x, t), acc => STySigma x t acc) b groups))

  -- T{1}, non-binder half: the sugared right-assoc → and the quotient.
  -- Non-dependent × is NOT here — it lives at T{1¾}, below ⊎.
  parseSTyInfix : FixTable -> NameEnv -> Rule STy
  parseSTyInfix tbl env =
    do a <- parseSTySum tbl env
       (do sp; kw2 "→" "->"; sp; b <- parseSTy tbl (env :< wildcard); pure (STyPi wildcard a b))
         <|> (do sp; kw "/"; sp; (x, y, r) <- parseQuotRel tbl env; pure (STyQuot a x y r))
         <|> pure a

  -- T{1½}: ⊎ — non-dependent, right-assoc, binds TIGHTER than the T{1}
  -- binder forms (A ⊎ B → C is (A ⊎ B) → C) and LOOSER than ×:
  -- A ⊎ B × C is A ⊎ (B × C), product before sum, as at the element
  -- level where * (infixl 7) binds tighter than + (infixl 6).
  parseSTySum : FixTable -> NameEnv -> Rule STy
  parseSTySum tbl env = do
    a <- parseSTyProd tbl env
    (do sp; kw2 "⊎" "\\/"; sp; b <- parseSTySum tbl env; pure (STySum a b))
      <|> pure a

  -- T{1¾}: NON-DEPENDENT × — right-assoc, tighter than ⊎, so A × B → C
  -- is (A × B) → C (the uncurrying shape reads without parentheses).
  -- The BINDER form (x : A) × B stays up at T{1} beside →, where its
  -- body extends maximally: the two are different operators sharing a
  -- token, and `A × B` is therefore NO LONGER sugar for `(_ : A) × B`.
  parseSTyProd : FixTable -> NameEnv -> Rule STy
  parseSTyProd tbl env = do
    a <- parseSTyEl tbl env
    (do sp; kw2 "×" "\\x"; sp; b <- parseSTyProd tbl (env :< wildcard); pure (STySigma wildcard a b))
      <|> pure a

  -- one or more (x:T) / {x:T} groups, each scoping over the ones
  -- after it — braces mark IMPLICIT binders (STyImpPi,
  -- docs/NovaPerfectSurface.txt Phase 3). A group may bind SEVERAL
  -- names at one written domain — (x y : T) — none scoping over the
  -- domain: each name past the first takes the domain WEAKENED by
  -- its predecessors (Nova.Elaboration.Surface, shiftTy), so the
  -- sugar is index arithmetic, not re-parsing
  parseBinderGroups : FixTable -> NameEnv -> Rule (NameEnv, List (Bool, String, STy))
  parseBinderGroups tbl env = do
    (imp, close) <- (kwc '(' $> (False, ')')) <|> (kwc '{' $> (True, '}'))
    sp; x <- parseName
    xs <- many (do space; parseName)
    sp; kwc ':'; sp
    a <- parseSTy tbl env; sp; kwc close
    let names = x :: xs
    let env1 = env <>< names
    rest <- optional (do sp; parseBinderGroups tbl env1)
    case rest of
      Nothing => pure (env1, groupTys imp names a)
      Just (env', groups) => pure (env', groupTys imp names a ++ groups)
   where
    groupTys : Bool -> List String -> STy -> List (Bool, String, STy)
    groupTys _ [] _ = []
    groupTys imp (n :: ns) a = (imp, n, a) :: groupTys imp ns (shiftTy 0 a)

  -- (x y. r)  or bare r as sugar for (_ _. r) — r is an Ω-valued ELEMENT
  parseQuotRel : FixTable -> NameEnv -> Rule (SName, SName, SElem)
  parseQuotRel tbl env =
        (do kwc '('; sp; x <- parseNameR; space; y <- parseNameR
            sp; kwc '.'; sp; r <- parseSElemNoComma tbl (env :< fst x :< fst y); sp; kwc ')'
            pure (x, y, r))
    <|> (do r <- parseSElemPrefix tbl (env :< wildcard :< wildcard); pure ((wildcard, Nothing), (wildcard, Nothing), r))

  -- T{2}: ν / atoms and CODE APPLICATION SPINES (El is retired:
  -- a code in type position is spelled directly — `Vect n`, a bound
  -- 𝕌-variable, a computed code in parens)
  parseSTyEl : FixTable -> NameEnv -> Rule STy
  parseSTyEl tbl env = do
    (r, x) <- bounds (parseSTyElRaw tbl env)
    pure (atPosTy r x)

  parseSTyElRaw : FixTable -> NameEnv -> Rule STy
  parseSTyElRaw tbl env =
        -- a SQUASH standing as a type (prop-lift; Prf is retired
        -- WITHOUT a legacy spelling — a prop stands bare)
        (do kw2 "∥" "||"; sp; t <- parseSTy tbl env; sp; kw2 "∥" "||"; pure (STyEl (SSquash t)))
    <|> (do kw2 "ν" "\\nu"; space; f <- parseSPolyAtom tbl env; pure (STyNu f))
    <|> (do t <- parseSTyAtom tbl env
            args <- many (do space; parseSElemAtom tbl env)
            case args of
              [] => pure t
              _ => case tyHeadElem t of
                     Just h => pure (STyEl (foldl SApp h args))
                     -- FATAL: `parseSTy` already tried the equality
                     -- production, and nothing above reads an applied
                     -- type former either, so this verdict must not be
                     -- outrun by a sibling's expectation
                     Nothing => fatal "!this type former takes no arguments")
   where
    tyHeadElem : STy -> Maybe SElem
    tyHeadElem ty = case unPosTy ty of
      STySig x => Just (SSig Nothing x)
      STyEl e => Just e
      _ => Nothing

  -- Polynomials (NovaElaboration.txt, F{·} grammar): binders and
  -- products at the top, sums tighter, atoms innermost.
  parseSPoly : FixTable -> NameEnv -> Rule SPoly
  parseSPoly tbl env =
        (do kwc '('; sp; x <- parseNameR; sp; kwc ':'; sp
            a <- parseSElemNoComma tbl env; sp; kwc ')'; sp
            (do kw2 "×" "\\x"; sp; f <- parseSPoly tbl (env :< fst x); pure (SPSigma x a f))
              <|> (do kw2 "→" "->"; sp; f <- parseSPoly tbl (env :< fst x); pure (SPPi x a f)))
    <|> (do f <- parseSPolySum tbl env
            (do sp; kw2 "×" "\\x"; sp; g <- parseSPoly tbl env; pure (SPProd f g))
              <|> pure f)

  -- F{1½}: ⊎, right-assoc, tighter than × (as everywhere)
  parseSPolySum : FixTable -> NameEnv -> Rule SPoly
  parseSPolySum tbl env = do
    f <- parseSPolyAtom tbl env
    (do sp; kw2 "⊎" "\\/"; sp; g <- parseSPolySum tbl env; pure (SPSum f g))
      <|> pure f

  -- F{2}: atoms — the hole, constants, parens
  parseSPolyAtom : FixTable -> NameEnv -> Rule SPoly
  parseSPolyAtom tbl env =
        (kw2 "𝕏" "\\X" $> SPHole)
    <|> (do kw "K"; space; a <- parseSElemAtom tbl env; pure (SPConst a))
    <|> (do kwc '('; sp; f <- parseSPoly tbl env; sp; kwc ')'; pure f)

  -- T{4}: atoms
  parseSTyAtom : FixTable -> NameEnv -> Rule STy
  parseSTyAtom tbl env = do
    (r, x) <- bounds (parseSTyAtomRaw tbl env)
    pure (atPosTy r x)

  parseSTyAtomRaw : FixTable -> NameEnv -> Rule STy
  parseSTyAtomRaw tbl env =
        (kw2 "𝟘" "Void" $> STyZero)
    <|> (kw2 "𝟙" "Unit" $> STyOne)
    <|> (kw2 "ℕ" "Nat" $> STyNat)
    <|> (kw2 "𝕌" "Set" $> STyUniv)
    <|> (kw2 "Ω" "Prop" $> STyProp)
    <|> (do (r, x) <- bounds parseDottedName
            case unpack x of
              -- `_`-leading identifiers were the OLD hole spelling;
              -- holes are written `?x` now, and are ELEMENT forms
              -- (e-hole is checking-only, and a type position offers
              -- nothing to check against). Binder wildcards are a
              -- separate production and unaffected.
              ('_' :: rest) => fail "!a `_`-leading name is not a hole — spell the type out (holes are `?x`, and only in term position)"
              _ =>
                case resolveVar env x of
                  -- a BINDER name in type position is a bound CODE
                  -- (El retired: the code is the type)
                  Just i  => pure (STyEl (SVar r x i))
                  Nothing => pure (STySig x))
    <|> (do kwc '('; sp; t <- parseSTy tbl env; sp; kwc ')'; pure t)
        -- a parenthesized ELEMENT in type position is a CODE — the
        -- type grammar's spines cover only atom-headed applications,
        -- so operator applications ((a ≤ b)) and other element forms
        -- land here (El retired: the code is the type)
    <|> (do kwc '('; sp; e <- parseSElemNoComma tbl env; sp; kwc ')'; pure (STyEl e))
        -- a bare ELEMENT ATOM in type position — operator-shaped
        -- names in particular (⊥, ⊤ — Prf retired: a nullary prop
        -- stands as a type under its own name)
    <|> (do e <- parseSElemAtom tbl env; pure (STyEl e))

  -- t{0}: top-level comma = pair (right-assoc)
  export
  parseSElem : FixTable -> NameEnv -> Rule SElem
  parseSElem tbl env = do
    (r, x) <- bounds (parseSElemRaw tbl env)
    pure (atPos r x)

  parseSElemRaw : FixTable -> NameEnv -> Rule SElem
  parseSElemRaw tbl env = do
    e <- parseSElemNoComma tbl env
    (do sp; kwc ','; sp; e' <- parseSElem tbl env; pure (SPair e e'))
      <|> pure e

  -- t{1}: universe-code binder/infix forms and eq-code; binder groups
  -- iterate exactly as at the type level
  parseSElemNoComma : FixTable -> NameEnv -> Rule SElem
  parseSElemNoComma tbl env = do
    (r, x) <- bounds (parseSElemNoCommaRaw tbl env)
    pure (atPos r x)

  parseSElemNoCommaRaw : FixTable -> NameEnv -> Rule SElem
  parseSElemNoCommaRaw tbl env =
        (do (env', groups) <- parseBinderGroupsC tbl env
            sp
            (do kw2 "→" "->"; sp; b <- parseSElemNoComma tbl env'; pure (foldGroups SPiC groups b))
              <|> (do kw2 "×" "\\x"; sp; b <- parseSElemNoComma tbl env'; pure (foldGroups SSigmaC groups b)))
    <|> (do e <- parseSElemSumC tbl env
            (do sp; kw2 "→" "->"; sp; e' <- parseSElemNoComma tbl (env :< wildcard); pure (SPiC wildcard e e'))
              <|> (do sp; kw "/"; sp; (x, y, r) <- parseQuotRelC tbl env; pure (SQuotC e x y r))
              -- calc chain: ≡⟨ … ⟩ disambiguates from the equality
              -- prop by its very next character (backtracking)
              <|> (do sp; links <- parseChainLinks tbl env
                      pure (SChain e links))
              <|> (do (r, (e1, mt2)) <- bounds (do
                        sp; kw2 "≡" "=="; sp
                        e1 <- parseSElemSumC tbl env
                        mt2 <- optional (do sp; kw2 "∈" "\\in"; sp; parseSTyArrow tbl env)
                        pure (e1, mt2))
                      pure (SEqC r e e1 mt2))
              <|> pure e)

  -- links of a calc chain: ≡⟨ justification ⟩ midpoint, one or more
  -- (docs/SearchlessElaboration.md §5.2); the justification is a full
  -- element (delimited by ⟩), the midpoint sits at the equality
  -- prop's own side level
  parseChainLinks : FixTable -> NameEnv -> Rule (List (SElem, SElem))
  parseChainLinks tbl env = do
    kw2 "≡⟨" "\\<"; sp
    j <- parseSElem tbl env
    sp; kw2 "⟩" "\\>"; sp
    x <- parseSElemSumC tbl env
    rest <- optional (do sp; parseChainLinks tbl env)
    pure ((j, x) :: fromMaybe [] rest)

  -- t{1¼}: the ⊎ code — like the ⊎ type, tighter than the t{1} binder
  -- forms and looser than the × code below
  parseSElemSumC : FixTable -> NameEnv -> Rule SElem
  parseSElemSumC tbl env = do
    (r, x) <- bounds (parseSElemSumCRaw tbl env)
    pure (atPos r x)

  parseSElemSumCRaw : FixTable -> NameEnv -> Rule SElem
  parseSElemSumCRaw tbl env = do
    e <- parseSElemProdC tbl env
    (do sp; kw2 "⊎" "\\/"; sp; e' <- parseSElemSumC tbl env; pure (SSumC e e'))
      <|> pure e

  -- t{1⅜}: the NON-DEPENDENT × code — right-assoc, tighter than ⊎ and
  -- looser than the declared operators, mirroring T{1¾} at the type
  -- level. The binder form (x : a) × b stays at t{1}; see parseSTyProd
  parseSElemProdC : FixTable -> NameEnv -> Rule SElem
  parseSElemProdC tbl env = do
    (r, x) <- bounds (parseSElemProdCRaw tbl env)
    pure (atPos r x)

  parseSElemProdCRaw : FixTable -> NameEnv -> Rule SElem
  parseSElemProdCRaw tbl env = do
    e <- parseSElemOp tbl env
    (do sp; kw2 "×" "\\x"; sp; e' <- parseSElemProdC tbl (env :< wildcard); pure (SSigmaC wildcard e e'))
      <|> pure e

  -- t{1½}: declared infix operators — precedence climbing over the
  -- fixity table. An operator token is a NAME; infix use is
  -- application of it.
  parseSElemOp : FixTable -> NameEnv -> Rule SElem
  parseSElemOp tbl env = do
    (r, x) <- bounds (parseSElemOpRaw tbl env)
    pure (atPos r x)

  -- `cur` is the operator this operand chain is already committed to at
  -- the current precedence: the one last folded in here, or — when we
  -- descended through a RIGHT-associative operator, which passes its own
  -- precedence down — that parent. Two operators of EQUAL precedence and
  -- DIFFERENT associativity meeting under it have no agreed reading, and
  -- climbing would otherwise pick one silently by written order (the
  -- first operator's associativity winning): `a ≤ b ∨ c` folding left
  -- while `a ∨ b ≤ c` folds right, for the same pair of fixities.
  parseSElemOpRaw : FixTable -> NameEnv -> Rule SElem
  parseSElemOpRaw tbl env = climb 0 Nothing
   where
    mutual
      climb : Nat -> Maybe (Nat, Assoc, String) -> Rule SElem
      climb minP cur = do
        l <- parseSElemPrefix tbl env
        cont l minP cur

      cont : SElem -> Nat -> Maybe (Nat, Assoc, String) -> Rule SElem
      cont l minP cur =
            (do (span, (rng, op, assoc, p, r)) <- bounds (do
                  sp
                  (rng, op) <- bounds parseOpName
                  case lookup op tbl of
                    Nothing => fail "an operator with a fixity in scope ('\{op}' has none)"
                    Just (assoc, p) => do
                      guard "an operator binding at least this tightly" (p >= minP)
                      -- FATAL, not a branch rejection: no sibling could
                      -- legitimately parse what this branch has read —
                      -- the clash is a property of the fixity table and
                      -- the two consumed tokens, and no minP would have
                      -- accepted it. The two guards above ARE branch
                      -- rejections (the loop's normal exits) and stay
                      -- ordinary failures. NB fatal escapes optional and
                      -- many too, so a clash inside `optional (… ∈ …)`
                      -- or a chain justification aborts rather than
                      -- yielding Nothing — deliberate: there is no
                      -- reading of the clash to fall back to.
                      case cur of
                        Just (q, a, prev) =>
                          when (p == q && a /= assoc) $
                            let msg = "!'\{prev}' and '\{op}' both have precedence \{show p} but associate in opposite directions — parenthesize, or give them different precedences" in
                            -- located at the SECOND operator, so the caret
                            -- lands on it rather than on the position
                            -- parsing stopped at (the space past it, which
                            -- is all a bare `fatal` can synthesize)
                            maybe (fatal msg) (\r => fatalLoc r msg) rng
                        Nothing => pure ()
                      sp
                      r <- climb (case assoc of AssocL => S p; AssocR => p)
                                 (case assoc of AssocL => Nothing; AssocR => Just (p, assoc, op))
                      pure (rng, op, assoc, p, r))
                cont (grew l span (SApp (SApp (SSig rng op) l) r)) minP (Just (p, assoc, op)))
        <|> pure l

  -- multi-name groups as at the type level (shiftElem for the
  -- weakened copies)
  parseBinderGroupsC : FixTable -> NameEnv -> Rule (NameEnv, List (String, SElem))
  parseBinderGroupsC tbl env = do
    kwc '('; sp; x <- parseName
    xs <- many (do space; parseName)
    sp; kwc ':'; sp
    a <- parseSElem tbl env; sp; kwc ')'
    let names = x :: xs
    let env1 = env <>< names
    rest <- optional (do sp; parseBinderGroupsC tbl env1)
    case rest of
      Nothing => pure (env1, groupElems names a)
      Just (env', groups) => pure (env', groupElems names a ++ groups)
   where
    groupElems : List String -> SElem -> List (String, SElem)
    groupElems [] _ = []
    groupElems (n :: ns) a = (n, a) :: groupElems ns (shiftElem 0 a)

  parseQuotRelC : FixTable -> NameEnv -> Rule (SName, SName, SElem)
  parseQuotRelC tbl env =
        (do kwc '('; sp; x <- parseNameR; space; y <- parseNameR
            sp; kwc '.'; sp; r <- parseSElemNoComma tbl (env :< fst x :< fst y); sp; kwc ')'
            pure (x, y, r))
    <|> (do r <- parseSElemPrefix tbl (env :< wildcard :< wildcard); pure ((wildcard, Nothing), (wildcard, Nothing), r))

  -- t{2}: prefix forms, motive-first eliminators
  parseSElemPrefix : FixTable -> NameEnv -> Rule SElem
  parseSElemPrefix tbl env = do
    (r, x) <- bounds (parseSElemPrefixRaw tbl env)
    pure (atPos r x)

  parseSElemPrefixRaw : FixTable -> NameEnv -> Rule SElem
  parseSElemPrefixRaw tbl env =
        -- λ's body extends MAXIMALLY (ProvingFeedback F-1): over
        -- operators, the code formers → × ⊎ /, ≡-elements, calc
        -- chains, AND pairs — λx. ℕ × ℕ is λx. (ℕ × ℕ), and
        -- λx. a , b is λx. (a , b). A λ that is a non-final pair
        -- component must therefore be parenthesised, the
        -- Agda/Haskell convention.
        (do kw2 "λ" "\\"; sp; x <- parseNameR; sp; kwc '.'; sp
            e <- parseSElem tbl (env :< fst x)
            pure (SLam x e))
        -- let x ≔ e in b / let x : T ≔ e in b — the annotated form is
        -- sugar for an ascribed definiens (the definiens elaborates in
        -- inference mode); the body extends maximally, like λ's.
        -- The body's indices are counted against the CORE context,
        -- which has TWO entries per let (el-let: the value, then its
        -- unfolding equation) — so x is pushed under a wildcard slot
        -- and resolves to index 1, the hypothesis slot (never
        -- resolvable) holding index 0
    <|> (do kw "let"; space; x <- parseNameR; sp
            manno <- optional (do kwc ':'; sp; t <- parseSTy tbl env; sp; pure t)
            kw2 "≔" ":="; sp
            e <- parseSElem tbl env; sp
            kw "in"; sp
            b <- parseSElem tbl (env :< fst x :< wildcard)
            pure (SLet x (maybe e (SAnn e) manno) b))
    <|> (do kw2 "𝟘-elim" "Void-elim"; space; e <- parseSElemAtom tbl env; pure (SZeroElim e))
    <|> (do kw2 "ℕ-elim" "Nat-elim"; space
            -- the motive group is safely optional here: z is an ATOM,
            -- and no valid element atom has the (name. …) shape
            mmot <- optional (do
              kwc '('; sp; n <- parseNameR; sp; kwc '.'; sp
              mot <- parseSTy tbl (env :< fst n); sp; kwc ')'; sp
              pure (n, mot))
            z <- parseSElemAtom tbl env; sp
            kwc '('; sp; n2 <- parseNameR; space; ih <- parseNameR
            sp; kwc '.'; sp; s <- parseSElem tbl (env :< fst n2 :< fst ih); sp; kwc ')'; sp
            t <- parseSElemAtom tbl env
            pure (SNatElim mmot z n2 ih s t))
    <|> (do kw "S"; space; e <- parseSElemAtom tbl env; pure (SSuc e))
    <|> (do kw2 "inj₁" "inj1"; space; e <- parseSElemAtom tbl env; pure (SInj1 e))
    <|> (do kw2 "inj₂" "inj2"; space; e <- parseSElemAtom tbl env; pure (SInj2 e))
        -- ⊎-elim with an explicit motive, then the motive-less form
        -- (checking-only): a case group (x. ELEM) whose body is a
        -- bare name also parses as a motive group (z. TYPE), so the
        -- three-group spelling is tried first and the two-group
        -- spelling is the fallback
    <|> (do kw2 "⊎-elim" "\\/-elim"; space
            kwc '('; sp; z <- parseNameR; sp; kwc '.'; sp
            mot <- parseSTy tbl (env :< fst z); sp; kwc ')'; sp
            kwc '('; sp; a <- parseNameR; sp; kwc '.'; sp
            l <- parseSElem tbl (env :< fst a); sp; kwc ')'; sp
            kwc '('; sp; b <- parseNameR; sp; kwc '.'; sp
            r <- parseSElem tbl (env :< fst b); sp; kwc ')'; sp
            t <- parseSElemAtom tbl env
            pure (SSumElim (Just (z, mot)) a l b r t))
    <|> (do kw2 "⊎-elim" "\\/-elim"; space
            kwc '('; sp; a <- parseNameR; sp; kwc '.'; sp
            l <- parseSElem tbl (env :< fst a); sp; kwc ')'; sp
            kwc '('; sp; b <- parseNameR; sp; kwc '.'; sp
            r <- parseSElem tbl (env :< fst b); sp; kwc ')'; sp
            t <- parseSElemAtom tbl env
            pure (SSumElim Nothing a l b r t))
    <|> (do kw "class"; space; e <- parseSElemAtom tbl env; pure (SClass e))
    <|> (do kw2 "ν" "\\nu"; space; f <- parseSPolyAtom tbl env; pure (SNuC f))
    <|> (do kw "out"; space; e <- parseSElemAtom tbl env; pure (SOut e))
    <|> (do kw "corec"; space
            kwc '('; sp; x <- parseNameR; sp; kwc ':'; sp
            a <- parseSElemNoComma tbl env; sp; kwc '.'; sp
            f <- parseSElem tbl (env :< fst x); sp; kwc ')'; sp
            u <- parseSElemAtom tbl env
            pure (SCorec x a f u))
    <|> (do kw "coind"; space
            kwc '('; sp; x <- parseNameR; space; y <- parseNameR; sp; kwc '.'; sp
            r <- parseSElem tbl (env :< fst x :< fst y); sp; kwc ')'; sp
            pw <- parseSElemAtom tbl env; sp
            kwc '('; sp; mx <- parseNameR; space; my <- parseNameR; space; mh <- parseNameR
            sp; kwc '.'; sp
            q <- parseSElem tbl (env :< fst mx :< fst my :< fst mh); sp; kwc ')'
            pure (SCoind x y r pw mx my mh q))
        -- quot-elim likewise: with-motive first, motive-less fallback
    <|> (do kw "quot-elim"; space
            kwc '('; sp; z <- parseNameR; sp; kwc '.'; sp
            mot <- parseSTy tbl (env :< fst z); sp; kwc ')'; sp
            kwc '('; sp; a <- parseNameR; sp; kwc '.'; sp
            f <- parseSElem tbl (env :< fst a); sp; kwc ')'; sp
            q <- parseSElemAtom tbl env
            pure (SQuotElim (Just (z, mot)) a f q))
    <|> (do kw "quot-elim"; space
            kwc '('; sp; a <- parseNameR; sp; kwc '.'; sp
            f <- parseSElem tbl (env :< fst a); sp; kwc ')'; sp
            q <- parseSElemAtom tbl env
            pure (SQuotElim Nothing a f q))
        -- sigma-elim (x y. t) w — the Σ VARIABLE elimination. The
        -- body is parsed against the site's binders with x and y
        -- pushed innermost (the scrutinee is only read after it), and
        -- REINDEXED against the elimination context once w's index is
        -- known: a name resolution, so it belongs here and not in the
        -- elaborator (docs/NovaElaboration.txt, e-sigmaelim)
    <|> (do kw "sigma-elim"; space; commit
            kwc '('; sp; x <- parseNameR; space; y <- parseNameR; sp; kwc '.'; sp
            b <- parseSElem tbl (env :< fst x :< fst y); sp; kwc ')'; sp
            w <- parseSElemAtom tbl env
            case unPos w of
              SVar wrng nm i => case sigmaElimBody i b of
                Just b' => pure (SSigmaElim x y b' w)
                Nothing =>
                  let msg = "a sigma-elim body free of '\{nm}' — the variable this eliminates, so the body's context has no such entry (its components are \{fst x} and \{fst y})" in
                  maybe (fail msg) (\r => failLoc r msg) (posOf w <|> wrng)
              -- not a variable: the elaborator says so, at the
              -- scrutinee's own span. The body keeps its parse
              -- indices; nothing ever reads them
              _ => pure (SSigmaElim x y b w))
    <|> (do kw "squash-elim"; space
            e <- parseSElemAtom tbl env; sp
            kwc '('; sp; x <- parseNameR; sp; kwc '.'; sp
            body <- parseSElem tbl (env :< fst x); sp; kwc ')'
            pure (SSquashElim e x body))
    <|> (do (r, _) <- bounds (kw2 "⋆" "\\star")
            -- `using` is a CONTEXTUAL keyword: recognized only here,
            -- immediately after ⋆ (a witness genuinely named `using`
            -- is written parenthesized: ⋆ (using))
            u <- optional (do space; kw "using"; space; parseUsingNames)
            case u of
              Just ns => pure (SStarUsing r ns)
              Nothing => do
                w <- optional (do space; parseSElemAtom tbl env)
                pure (case w of
                        Nothing => SStar r
                        Just e  => SStarWit e))
    <|> parseSElemApp tbl env

  -- t{3}: application / projection chains
  parseSElemApp : FixTable -> NameEnv -> Rule SElem
  parseSElemApp tbl env = do
    (r, x) <- bounds (parseSElemAppRaw tbl env)
    pure (atPos r x)

  parseSElemAppRaw : FixTable -> NameEnv -> Rule SElem
  parseSElemAppRaw tbl env = do
    e <- parseSElemAtom tbl env
    cont e
   where
    cont : SElem -> Rule SElem
    cont e =
          (do (r, _) <- bounds (do sp; kw2 ".π₁" ".1"); cont (grew e r (SProj1 e)))
      <|> (do (r, _) <- bounds (do sp; kw2 ".π₂" ".2"); cont (grew e r (SProj2 e)))
      -- {t} — an implicit-position override argument — and {} — the
      -- NO-INSERT marker, suppressing trailing-implicit insertion
      -- (docs/NovaPerfectSurface.txt, Phases 3b/3d); NB `{-` opens a
      -- comment at the lexer, so an override starting with an
      -- operator needs a space: { -x } — the Haskell convention
      <|> (do (r, mt) <- bounds (do
                sp; kwc '{'; sp
                (do kwc '}'; pure Nothing)
                  <|> (do t <- parseSElem tbl env; sp; kwc '}'; pure (Just t)))
              case mt of
                Nothing => cont (grew e r (SNoIns e))
                Just t => cont (grew e r (SApp e (SImpArg t))))
      <|> (do (r, e') <- bounds (do sp; parseSElemAtom tbl env)
              cont (grew e r (SApp e e')))
      <|> pure e

  -- t{5}: atoms, including ascription
  parseSElemAtom : FixTable -> NameEnv -> Rule SElem
  parseSElemAtom tbl env = do
    (r, x) <- bounds (parseSElemAtomRaw tbl env)
    pure (atPos r x)

  parseSElemAtomRaw : FixTable -> NameEnv -> Rule SElem
  parseSElemAtomRaw tbl env =
        -- mention form: (+) — the operator as an ordinary reference
        (do (r, op) <- bounds (do kwc '('; sp; op <- parseOpRef; sp; kwc ')'; pure op); pure (SSig r op))
        -- a FIXITY-FREE operator token is an ordinary name atom (⊥, ⊤,
        -- prefix-applied ¬); declared-infix operators are excluded, so
        -- application juxtaposition never captures them.
        --
        -- ?x — a named HOLE (docs/NovaElaboration.txt, e-hole) — is
        -- read HERE rather than as a production of its own, because
        -- `?` is an opChar: a `?` that starts an atom is already this
        -- alternative's token, so recognizing the hole costs one
        -- string comparison on a path an operator token reached
        -- anyway. A production ahead of this one would instead probe
        -- for `?` at EVERY atom of every file — measured at +6% on
        -- the corpus's load-parse phase, which is exactly the kind of
        -- cost a hole-free file must not pay. The maximal opChar run
        -- decides: `?` before an identifier start is a hole, while
        -- `?`, `?!` and `<?>` still lex as operator names
    <|> (do (rng, res) <- bounds (the (Rule (Either String (Maybe Range, String))) $ do
              (orng, op) <- bounds parseOpName
              if op == "?"
                then do (lrng, x) <- bounds parseHoleLabel
                        emit lrng Identifier
                        pure (Left x)
                else pure (Right (orng, op)))
            case res of
              Left x => pure (SHole rng x)
              Right (orng, op) =>
                case lookup op tbl of
                  Nothing => pure (SSig orng op)
                  Just _ => fail "an atom (a declared infix operator cannot begin one)")
    <|> (do kwc '('
            sp
            unit <- optional (kwc ')')
            case unit of
              Just _  => pure SUnitI
              Nothing => do
                e <- parseSElem tbl env
                sp
                (do kwc ':'; sp; ty <- parseSTy tbl env; sp; kwc ')'
                    pure (SAnn e ty))
                  <|> (do kwc ')'; pure e))
    <|> (kw "Z"    $> SZeroN)
    <|> (sucTower <$> parseNumeral)
    <|> (do (r, _) <- bounds (kw2 "⋆" "\\star"); pure (SStar r))
    <|> (do kw2 "∥" "||"; sp; t <- parseSTy tbl env; sp; kw2 "∥" "||"; pure (SSquash t))
    <|> (kw2 "𝟘" "Void"   $> SZeroC)
    <|> (kw2 "𝟙" "Unit"   $> SOneC)
    <|> (kw2 "ℕ" "Nat"   $> SNatC)
    <|> (do (r, x) <- bounds parseDottedName
            case unpack x of
              -- a BARE `_` is a BLANK: a per-site elided argument at
              -- an explicit Π position (docs/NovaPerfectSurface.txt,
              -- Phase 4). Other `_`-leading identifiers were the OLD
              -- hole spelling; holes are written `?x` now (e-hole).
              -- Binder wildcards are a separate production and
              -- unaffected.
              ['_'] => pure (SBlank r)
              ('_' :: rest) => fail "!a `_`-leading name is not a hole — holes are written `?x`"
              _ =>
                case resolveVar env x of
                  Just i  => pure (SVar r x i)
                  -- locals shadow the signature; whether the name
                  -- exists in Σ is the elaborator's question, not the
                  -- parser's (a dotted name never resolves locally)
                  Nothing => pure (SSig r x))

-- ===== Items =====
--
-- Items are always declared in the EMPTY context: parameters are
-- ordinary Π-binders in the item's type (the iterated binder syntax
-- keeps that pleasant), and references to an item are bare names.

-- ===== QIIT signature literals (the data item) =====
--
-- Inside a literal, name resolution is three-layered: the literal's
-- own entries and inductive binders (the ToS zone) resolve FIRST, then
-- external binders (the Nova zone), then Σ. A Π domain is INDUCTIVE
-- exactly when it is `El` of a chain headed by a ToS name — anything
-- else is an external surface type. Both classifications happen here,
-- at parse time; the elaborator never sees a name.

||| An identifier resolving in the ToS environment.
tosName : NameEnv -> Rule (String, Nat)
tosName tos = do
  x <- parseName
  case resolveVar tos x of
    Just i => pure (x, i)
    Nothing => do guard "a name bound by the signature literal" False
                  pure ("", 0)

mutual
  ||| A ToS application chain: a ToS head applied to arguments, each
  ||| argument itself ToS (a name or parenthesized chain) or external
  ||| (an ordinary surface atom over the external zone).
  sqChain : FixTable -> NameEnv -> NameEnv -> Rule SQTm
  sqChain tbl tos ext = do
    (x, i) <- tosName tos
    args <- many (do sp; sqArg tbl tos ext)
    pure (foldl app (SQVar x i) args)
   where
    app : SQTm -> Either SElem SQTm -> SQTm
    app f (Left e) = SQAppE f e
    app f (Right t) = SQAppI f t

  sqArg : FixTable -> NameEnv -> NameEnv -> Rule (Either SElem SQTm)
  sqArg tbl tos ext =
        (do (x, i) <- tosName tos; pure (Right (SQVar x i)))
    <|> (do kwc '('; sp; t <- sqChain tbl tos ext; sp; kwc ')'; pure (Right t))
    <|> (Left <$> parseSElemAtom tbl ext)

  sqCode : FixTable -> NameEnv -> NameEnv -> Rule SQTm
  sqCode tbl tos ext =
        (do kwc '('; sp; t <- sqChain tbl tos ext; sp; kwc ')'; pure t)
    <|> sqChain tbl tos ext

sqDomain : FixTable -> NameEnv -> NameEnv -> Rule (Either STy SQTm)
sqDomain tbl tos ext =
      (do kw "El"; space; q <- sqCode tbl tos ext; pure (Right q))
      -- the QIIT sublanguage keeps El: `El a` at a NON-ToS name is a
      -- small EXTERNAL domain (the code as a type; canonical distill
      -- form spells it bare)
  <|> (do kw "El"; space; e <- parseSElemAtom tbl ext; pure (Left (STyEl e)))
  <|> (Left <$> parseSTy tbl ext)

||| An ANONYMOUS domain: like `sqDomain`, but the external case stops
||| below the arrow level (T{2}) — a greedy full type would swallow
||| the rest of the entry (`ℕ → El Q` must be TWO pieces, not one
||| function type). Higher-order external domains stay parenthesized,
||| which re-enters the full type grammar.
sqDomainNoArrow : FixTable -> NameEnv -> NameEnv -> Rule (Either STy SQTm)
sqDomainNoArrow tbl tos ext =
      (do kw "El"; space; q <- sqCode tbl tos ext; pure (Right q))
  <|> (do kw "El"; space; e <- parseSElemAtom tbl ext; pure (Left (STyEl e)))
  <|> (Left <$> parseSTyEl tbl ext)

sqRes : FixTable -> NameEnv -> NameEnv -> Rule SQRes
sqRes tbl tos ext =
      (do kw "U"; pure SQResU)
  <|> (do l <- sqChain tbl tos ext; sp; kw2 "≡" "=="; sp
          r <- sqChain tbl tos ext; sp; kw2 "∈" "\\in"; sp
          kw "El"; space; u <- sqCode tbl tos ext
          pure (SQResEq l r u))
  <|> (do kw "El"; space; q <- sqCode tbl tos ext; pure (SQResEl q))

sqBinders : FixTable -> NameEnv -> NameEnv -> Rule (NameEnv, NameEnv, List (String, Either STy SQTm))
sqBinders tbl tos ext = do
  kwc '('; sp; x <- parseName; sp; kwc ':'; sp
  d <- sqDomain tbl tos ext; sp; kwc ')'
  let tos' : NameEnv
      tos' = case d of
               Left _ => tos
               Right _ => tos :< x
  let ext' : NameEnv
      ext' = case d of
               Left _ => ext :< x
               Right _ => ext
  rest <- optional (do sp; sqBinders tbl tos' ext')
  case rest of
    Nothing => pure (tos', ext', [(x, d)])
    Just (tos'', ext'', bs) => pure (tos'', ext'', (x, d) :: bs)

||| An entry's telescope-and-result: named binder groups iterate as
||| before ((x : D) (y : D') → R ≡ (x : D) → (y : D') → R), and a
||| NON-DEPENDENT domain may stand bare — `cls : El a → El Q` — the
||| anonymous binder entering the right zone under the wildcard name
||| (which never resolves, so nothing can reference it).
sqTele : FixTable -> NameEnv -> NameEnv -> Rule (List (String, Either STy SQTm), SQRes)
sqTele tbl tos ext =
      (do (tos', ext', bs) <- sqBinders tbl tos ext
          sp; kw2 "→" "->"; sp
          (rest, res) <- sqTele tbl tos' ext'
          pure (bs ++ rest, res))
  <|> (do d <- sqDomainNoArrow tbl tos ext
          sp; kw2 "→" "->"; sp
          let tos' = case d of { Left _ => tos; Right _ => tos :< wildcard }
          let ext' = case d of { Left _ => ext :< wildcard; Right _ => ext }
          (rest, res) <- sqTele tbl tos' ext'
          pure ((wildcard, d) :: rest, res))
  <|> (do res <- sqRes tbl tos ext
          pure ([], res))

sqDecl : FixTable -> NameEnv -> NameEnv -> Rule SQDecl
sqDecl tbl penv entries = do
  n <- parseName; sp; kwc ':'; sp
  (bs, res) <- sqTele tbl entries penv
  pure (MkSQDecl n bs res)

parseSData : FixTable -> Rule SItem
parseSData tbl = do
  kw "data"; sp
  commit
  (penv, params) <- parseParams [<]
  kwc '('; sp
  ds <- go penv [<]
  sp; kwc ')'
  pure (SData params ds)
 where
  ||| Zero or more [x : T] PARAMETER groups — the literal's ambient
  ||| telescope, each scoping over the ones after it.
  parseParams : NameEnv -> Rule (NameEnv, List (String, STy))
  parseParams env =
        (do kwc '['; sp; x <- parseName; sp; kwc ':'; sp
            t <- parseSTy tbl env; sp; kwc ']'; sp
            (env', rest) <- parseParams (env :< x)
            pure (env', (x, t) :: rest))
    <|> pure (env, [])
  go : NameEnv -> NameEnv -> Rule (List SQDecl)
  go penv entries = do
    d <- sqDecl tbl penv entries
    rest <- optional (do sp; kwc ';'; sp; go penv (entries :< d.dqname))
    pure (d :: fromMaybe [] rest)

-- ===== Defining equations (the clausal def item) =====
--
-- Clause LHSs are pattern spellings headed by the item's own name;
-- the marker `|` is RESERVED for this role (withdrawn from the
-- operator alphabet — see Nova.Elaboration.Surface.opChar), and the
-- clause separator is ≔, as at def, so `=` stays an ordinary
-- operator token.

mutual
  ||| pat ::= x | Z | S pat | inj₁ pat | inj₂ pat | (pat) — any depth
  ||| (the FRAGMENT demands depth 1, the grammar does not); constructor
  ||| arguments sit at atom level, like application arguments.
  parsePat : Rule SPat
  parsePat =
        (do kw "S"; space; p <- parsePatAtom; pure (SPSuc p))
    <|> (do kw2 "inj₁" "inj1"; space; p <- parsePatAtom; pure (SPInj1 p))
    <|> (do kw2 "inj₂" "inj2"; space; p <- parsePatAtom; pure (SPInj2 p))
    <|> parsePatAtom

  parsePatAtom : Rule SPat
  parsePatAtom =
        (kw "Z" $> SPZero)
    <|> (patTower <$> parseNumeral)
    <|> (do kwc '('; sp; p <- parsePat; sp; kwc ')'; pure p)
    <|> (do x <- parseNameR; pure (SPVar x))
   where
    patTower : Nat -> SPat
    patTower Z = SPZero
    patTower (S k) = SPSuc (patTower k)

||| The binder telescope a clause's patterns spell: one slot per
||| variable in order of first appearance; a wildcard is always a
||| fresh slot, a repeated name reuses its slot (nonlinear LHS —
||| expressible here, rejected by the structural fragment).
patVarsOf : List SPat -> List SName
patVarsOf = foldl goP []
 where
  goP : List SName -> SPat -> List SName
  goP acc (SPVar x) =
    if fst x /= wildcard && elem (fst x) (map fst acc)
      then acc
      else acc ++ [x]
  goP acc SPZero = acc
  goP acc (SPSuc p) = goP acc p
  goP acc (SPInj1 p) = goP acc p
  goP acc (SPInj2 p) = goP acc p

||| lhs ::= n pat* | pat op pat — the head must be the item's own name
||| (parsed as an ordinary application or infix spelling and REREAD as
||| patterns; the mention form (op) works as a prefix head).
parseClauseLhs : String -> Rule (List SPat)
parseClauseLhs iname =
      (do h <- parseHead
          guard headed (h == iname)
          many (do sp; parsePatAtom))
  <|> (do p1 <- parsePat; sp
          op <- parseOpName
          guard headed (op == iname)
          sp
          p2 <- parsePat
          pure [p1, p2])
      -- Neither spelling was headed by the item's name. The guards
      -- above cannot say so: inside a choice a guard is a branch
      -- REJECTION — the engine reports whichever branch read
      -- furthest, so one branch's message is routinely outrun by its
      -- sibling's, and neither branch may speak for the other anyway
      -- (a name-headed LHS is exactly how the infix spelling starts:
      -- `| x + y ≔ …` for `def +`). So the DIAGNOSIS is its own last
      -- branch: it re-reads the same LHS with the head check dropped,
      -- which takes it at least as far as any sibling got, and fails
      -- there saying what is actually wrong.
  <|> (do h <- anyHead
          fatal "!every clause must be headed by the item's own name ('\{iname}'), not '\{h}'")
      -- no head under either spelling — `| Z ≔ …` for `| f Z ≔ …`.
      -- This branch consumes nothing, so it could never outrun a
      -- sibling on depth; FATAL is what lets it be heard. Both
      -- diagnosing branches are fatal, so the one that read a head
      -- (and can name it) ends the alternation before this one.
  <|> fatal "!every clause must be headed by the item's own name ('\{iname}')"
 where
  headed : String
  headed = "a clause headed by '\{iname}'"

  parseHead : Rule String
  parseHead =
        parseName
    <|> parseOpName
    <|> (do kwc '('; sp; op <- parseOpRef; sp; kwc ')'; pure op)

  ||| The LHS's head under either spelling, head check dropped.
  anyHead : Rule String
  anyHead =
        (do h <- parseHead; ignore (many (do sp; parsePatAtom)); pure h)
    <|> (do ignore parsePat; sp; parseOpName)

||| clause ::= | lhs ≔ t ([n])? — the RHS is parsed in the LHS's
||| binder telescope; the optional [n] names the clause's equation
||| lemma.
parseSClauseRaw : FixTable -> String -> Rule SClause
parseSClauseRaw tbl iname = do
  kwc '|'; sp
  commit
  pats <- parseClauseLhs iname
  sp; kw2 "≔" ":="; sp
  let vars = patVarsOf pats
  rhs <- parseSElem tbl ([<] <>< map fst vars)
  mn <- optional (do sp; kwc '['; sp; n <- parseName; sp; kwc ']'; pure n)
  pure (MkSClause pats vars rhs mn Nothing)

||| The clause with its own source span attached — what the item macro
||| reports its generated equation lemma at.
export
parseSClause : FixTable -> String -> Rule SClause
parseSClause tbl iname = do
  (r, c) <- bounds (parseSClauseRaw tbl iname)
  pure ({ crange := r } c)

-- COMMITS: after an item's leading keyword the parse can be nothing
-- else, so commit — a failure deep inside the item then propagates
-- with its REAL position instead of backtracking to the item
-- boundary, where the file loop would end and report a useless
-- "Expected end of input" at the next `def`. The commit inside the
-- optional ≔-body keeps `def x : T ≔ <garbage>` a hard error at the
-- garbage rather than mis-reading the item as a declaration. The
-- commit after a clause's `|` likewise keeps a malformed clause a
-- hard error while letting the clause loop end cleanly at the next
-- item.
export
parseSItem : FixTable -> Rule SItem
parseSItem tbl =
      (do kw "def"; space; commit
          (r, x) <- bounds (parseName <|> parseOpName); sp
          kwc ':'; sp
          ty <- parseSTy tbl [<]; sp
          -- item-level using (SearchlessElaboration.md §5.3): scopes
          -- EVERY discharge of the item — ⋆s, switches, WD premises —
          -- to the named lemmas plus hypotheses
          muses <- optional (do kw "using"; sp; ns <- parseUsingNames; sp; pure ns)
          metaEta <- optional (do kwc '['; sp; n <- parseName; sp; kwc ']'; sp; pure n)
          mbody <- optional (do kw2 "≔" ":="; sp; commit; parseSElem tbl [<])
          cls <- many (do sp; parseSClause tbl x)
          case (metaEta, mbody, cls) of
            (Nothing, Just body, []) => pure (SDef x ty body muses)
            -- a def without a definiens: a DECLARATION
            (Nothing, Nothing, []) =>
              case muses of
                Nothing => pure (SDeclDef r x ty)
                Just _ => fail "!a declaration discharges nothing — a using-clause is for defs with a definiens"
            (_, _, (c :: cs)) =>
              case muses of
                Nothing => pure (SClausalDef r x ty metaEta mbody (c :: cs))
                Just _ => fail "!a using-clause on a clausal def is not supported yet"
            (Just _, _, []) => fail "!a uniqueness-name override must be followed by clauses")
  <|> (do kw "type"; space; commit
          x <- parseName; sp
          kw2 "≔" ":="; sp
          ty <- parseSTy tbl [<]
          pure (STypeDef x ty))
  <|> parseSData tbl

export
parseSImport : Rule SImport
parseSImport = do
  (r, (m, opens)) <- bounds $ do
    kw "import"; space; commit
    m <- parseDottedName
    opens <- optional (do sp; kwc '('; sp
                          n <- parseName <|> parseOpName
                          rest <- many (do sp; kwc ','; sp; (parseName <|> parseOpName))
                          sp; kwc ')'
                          pure (n :: rest))
    pure (m, opens)
  pure (MkSImport m (fromMaybe [] opens) r)

||| infixl 6 +  /  infixr 3 ⊕ — fixity for an operator NAME; takes
||| effect for the rest of the file and is exported with the name.
parseFixity : Rule (String, Assoc, Nat)
parseFixity = do
  assoc <- (kw "infixl" $> AssocL) <|> (kw "infixr" $> AssocR)
  space
  commit
  (r, d) <- bounds (terminal "a precedence digit (0-9)" digitTok)
  emit r Number
  space
  op <- parseOpName
  pure (op, assoc, d)
 where
  digitTok : Token -> Maybe Nat
  digitTok (Symbol ch) =
    if ch >= '0' && ch <= '9' then Just (cast (ord ch - ord '0')) else Nothing
  digitTok _ = Nothing

||| A file: imports, then fixity declarations and items interleaved.
||| The initial table holds the fixities of OPENED imported operators;
||| declared fixities extend it as parsing proceeds and are returned
||| for export.
||| Each item is paired with its source range (the whole `def`/`type`/
||| `data` item, not sub-expression precision) — enough for LSP
||| diagnostics to anchor at the right item without threading Range
||| through STy/SElem themselves.
export
parseSFile : FixTable -> Rule (List SImport, FixTable, List (Maybe Range, SItem), List SBodyEntry)
parseSFile tbl0 = do
  sp
  imports <- many (do i <- parseSImport; sp; pure i)
  (decls, items, body) <- go tbl0
  pure (imports, decls, items, body)
 where
  go : FixTable -> Rule (FixTable, List (Maybe Range, SItem), List SBodyEntry)
  go tbl =
        (do (r, f) <- bounds parseFixity; sp
            (decls, items, body) <- go (f :: tbl)
            pure (f :: decls, items, Left (r, f) :: body))
    <|> (do (r, i) <- bounds (parseSItem tbl); sp
            (decls, items, body) <- go tbl
            pure (decls, (r, i) :: items, Right (r, i) :: body))
    <|> pure ([], [], [])

||| Pass 1 of the loader's two-stage parse: just the import header
||| (the dependencies' fixity tables are needed before the body can be
||| parsed).
export
parseSHeader : Rule (List SImport)
parseSHeader = do
  sp
  imports <- many (do i <- parseSImport; sp; pure i)
  ignore (many (terminal "any token at all" anyTok))
  pure imports
 where
  anyTok : Token -> Maybe ()
  anyTok _ = Just ()

-- ===== Runner =====

-- Comment tokens become whitespace; consecutive whitespace collapses,
-- so `optSpace`'s single-token model keeps working on commented files.
normaliseTokens : List (Range, Token) -> List (Range, Token)
normaliseTokens [] = []
normaliseTokens ((r, Comment _) :: rest) = normaliseTokens ((r, Whitespace) :: rest)
normaliseTokens ((r, Whitespace) :: (r', Comment _) :: rest) =
  normaliseTokens ((r, Whitespace) :: (r', Whitespace) :: rest)
normaliseTokens ((r, Whitespace) :: (_, Whitespace) :: rest) =
  normaliseTokens ((r, Whitespace) :: rest)
normaliseTokens (t :: rest) = t :: normaliseTokens rest

||| Alongside the parsed value, returns every classified token span
||| seen during the parse (see `Nova.Kernel.Parser.emit`) plus every
||| stripped comment's range (comments never reach the grammar as
||| tokens — `normaliseTokens` below turns them into whitespace before
||| parsing even starts, so they're tagged straight from the lexer's
||| own record of what it stripped). Order is unspecified — an LSP
||| consumer sorts by start position before encoding.
-- A single-line comment token's END position, as the lexer encodes
-- it, is the START of the FOLLOWING line (it folds in having consumed
-- the terminating newline) — correct for the lexer's own bookkeeping,
-- wrong as a semantic-token span (its length would come out as
-- `0 - startColumn`). Every comment here is single-line by construction
-- (`Me.Russoul.Text.Lexer.mkWithBounds`'s multi-line-comment case
-- ships one token per line for exactly this reason), so the span
-- these are re-clipped to — start column to the end of that physical
-- source line — is always the true comment extent.
clipCommentRange : List String -> Range -> Range
clipCommentRange lines (MkRange start _) =
  case drop (cast start.line) lines of
    (line :: _) => MkRange start (MkPosition start.line (cast (length line)))
    []          => MkRange start start

||| The span a parsing error points at — a real token range when the
||| failure is at a token, a one-column-wide range at the consumed
||| position otherwise (an LSP diagnostic needs SOME width).
parseErrRange : ParsingError Token (SnocList (Range, TokenKind)) -> Range
parseErrRange err =
  case err.range of
    Left r  => r
    Right p => MkRange p (MkPosition p.line (p.column + 1))

||| A parse failure, in the shape `Nova.Diagnostic` renders: the span
||| it points at, the location-free message, and secondary notes.
public export
record ParseFail where
  constructor MkParseFail
  pfrange : Maybe Range
  pfmsg : String
  pfnotes : List String

export
runSurfaceParser : Rule a -> String -> Either ParseFail (SnocList (Range, TokenKind), a)
runSurfaceParser rule input =
  let (commentRanges, toks) = tokenise (unpack input)
      srcLines = lines input in
  case parseWith [<] (rule <* eof) (normaliseTokens toks) of
    Left err  => Left (MkParseFail (Just (parseErrRange err)) (parseErrMessage err) (parseErrNotes err))
    Right (kinds, _, x, _) =>
      Right (kinds <>< map (\r => (clipCommentRange srcLines r, Comment)) (toList commentRanges), x)
