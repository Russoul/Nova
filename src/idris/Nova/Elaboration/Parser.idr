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
--
-- LAYOUT (docs/NovaElaboration.txt, Layout): the surface is
-- indentation-significant. Every line break is seen by exactly one of
-- the whitespace combinators below — `ws` reports it, `sp`/`space`
-- demand that the new line stand past the enclosing block column b,
-- and a spine's `argPos` decides whether the new line is one more
-- ARGUMENT (a term-initial line indented past the spine's reference
-- column r — the indent of the line its head sits on). The two
-- columns live in the grammar state (Nova.Kernel.Parser.PState):
-- `block` is set by `inBlock` for the extent of a block argument or a
-- data literal, `indent` follows the most recently crossed line break.

import Data.List
import Data.Maybe
import Data.String
import Data.SnocList
import Data.Vect

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

%hide Me.Russoul.Text.Parser.OverToken.space

-- ===== Layout primitives =====

||| The start of the next token; Nothing at the end of the input.
peekPos : Rule (Maybe Position)
peekPos = (Just <$> position) <|> pure Nothing

indentNow : Rule Int
indentNow = (.indent) <$> get

blockNow : Rule Int
blockNow = (.block) <$> get

||| Run a grammar with the block column set to `c` — the extent of a
||| block argument or of a data literal's entries. Restored after
||| (and, on failure, by backtracking: the state is functional).
inBlock : Int -> Rule a -> Rule a
inBlock c p = do
  b <- blockNow
  update { block := c }
  x <- p
  update { block := b }
  pure x

||| Consume optional whitespace, reporting a crossed LINE BREAK: Just c
||| when the next token is the first on a later line, at column c (the
||| state's indent becomes c); Nothing when it stands on the same line
||| as the previous token, or when nothing follows at all. Whitespace
||| is one fused token spanning from the previous token's end to the
||| next token's start (Me.Russoul.Text.Lexer.mergeWhitespace), so the
||| comparison of the two positions is the whole test.
ws : Rule (Maybe Int)
ws = do
  Just p0 <- peekPos
    | Nothing => pure Nothing
  Just () <- optional (ignore (is "whitespace" isSpace))
    | Nothing => pure Nothing
  Just p1 <- peekPos
    | Nothing => pure Nothing
  if p1.line > p0.line
    then do update { indent := p1.column }; pure (Just p1.column)
    else pure Nothing

||| Columns in layout messages count from 1, as the diagnostic's own
||| location does (the grammar's columns count from 0).
col : Int -> String
col c = show (c + 1)

||| The message a line that leaves its block carries — a DIAGNOSIS
||| (leading "!", Nova.Kernel.Parser.splitDiagnoses) when it becomes
||| the error: at a required position it says exactly what went wrong,
||| while at an optional position its failure is how every construct
||| ends at the next item or block line.
offside : Int -> Int -> String
offside b c = "!a line indented past column \{col b} — this one starts at column \{col c}, which ends the enclosing block"

||| Optional whitespace at a REQUIRED or CONTINUATION position: a line
||| break is fine as long as the new line stands past the enclosing
||| block column.
sp : Rule ()
sp = do
  mc <- ws
  case mc of
    Nothing => pure ()
    Just c => do
      b <- blockNow
      guard (offside b c) (c > b)

||| Mandatory whitespace, with the same line-break discipline.
space : Rule ()
space = do
  Just p0 <- peekPos
    | Nothing => fail "whitespace"
  ignore (is "whitespace" isSpace)
  Just p1 <- peekPos
    | Nothing => pure ()
  when (p1.line > p0.line) $ do
    update { indent := p1.column }
    b <- blockNow
    guard (offside b p1.column) (p1.column > b)

||| The layout CURSOR of a spine: the reference column r (the indent of
||| the head's line) and, once opened, its argument block's column.
record Lay where
  constructor MkLay
  lr : Int
  lblk : Maybe Int

||| Where a spine's next argument stands, if anywhere.
data ArgPos
  = NoArg            -- the line ended and the next line is not this spine's
  | SameLine         -- juxtaposition, as ever
  | BlockLine        -- an ARGUMENT LINE, at the cursor's block column
  | Misaligned Int   -- a line between r and the open block's column

||| Consume the whitespace before a possible next argument and classify
||| its position (docs/NovaElaboration.txt, Layout — OPTIONAL
||| POSITIONS). The cursor comes back with its block column set when a
||| block opens. `NoArg` and `Misaligned` leave the decision to the
||| caller, whose branch failing restores the whitespace.
argPos : Lay -> Rule (Lay, ArgPos)
argPos lay = do
  mc <- ws
  case mc of
    Nothing => pure (lay, SameLine)
    Just c => do
      b <- blockNow
      if c <= b then pure (lay, NoArg) else
        case lay.lblk of
          Nothing =>
            if c > lay.lr then pure ({ lblk := Just c } lay, BlockLine) else pure (lay, NoArg)
          Just c0 =>
            if c == c0 then pure (lay, BlockLine)
            else if c > c0 then pure (lay, NoArg)
            else if c > lay.lr then pure (lay, Misaligned c)
            else pure (lay, NoArg)

||| A one-character range at the next token, for a layout verdict's
||| caret.
nextRange : Rule (Maybe Range)
nextRange = do
  mp <- peekPos
  pure (map (\p => MkRange p (MkPosition p.line (p.column + 1))) mp)

misalignedMsg : Int -> Int -> String
misalignedMsg c c0 = "!an argument line at column \{col c} — this spine's arguments stand at column \{col c0}"

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

||| Match a keyword's spelling, reporting THE KEYWORD at every
||| character rather than the next character it wanted. A keyword that
||| half-matches is otherwise the loudest thing in the report: `S ` in
||| term position half-matches `Set` (the ASCII fallback for 𝕌) and
||| used to answer "expected 'e'", a letter the reader never typed and
||| cannot place. Naming the keyword says what was being attempted, so
||| the sibling expectation — an identifier, and why `S` is not one —
||| reads as the answer it is.
kwStr : String -> Rule ()
kwStr s = go (unpack s)
 where
  -- built once per keyword match, not once per character: this is the
  -- hot path (every atom tries several keywords before it settles)
  msg : String
  msg = "'\{s}'"

  go : List Char -> Rule ()
  go [] = pure ()
  go (c :: cs) = do
    _ <- terminal msg (\tok => case tok of
           Symbol ch => if ch == c then Just () else Nothing
           _ => Nothing)
    go cs

kw : String -> Rule ()
kw s = do
  (r, ()) <- bounds (kwStr s)
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

||| The DEFINIENS token `=` of a clause and of a let: exactly one `=`,
||| not the head of a longer operator run (`==` is ≡'s ASCII spelling,
||| `=>` and `<=` are operator names). Reserved as a NAME in
||| parseOpName below, so no fixity can ever make it infix.
kwEq : Rule ()
kwEq = do
  (r, ()) <- bounds (char_ '=')
  next <- optional (nextIs "next" (\tok => case tok of
            Symbol ch => opChar ch
            _ => False))
  case next of
    Just _ => fail "'=' (this one runs on into an operator)"
    Nothing => pure ()
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
    -- S/Z/Refl/class are also reserved: unlike El/import/infixl/
    -- infixr they're syntactically valid identifiers, so without
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
    -- `out` is S/class's case exactly — it consumes a following atom —
    -- with a second, quieter failure of its own: `out` is a plain
    -- identifier in TYPE position too (the type grammar reads no
    -- keyword-headed code), so an unreserved `out t` there read as an
    -- APPLICATION of a signature name and asked after an `out` nobody
    -- declared. The other keyword-headed forms need no entry: 𝟘-elim,
    -- ⊎-elim, quot-elim and squash-elim carry a `-`, and ν, ⋆, inj₁
    -- and inj₂ are not identifiers at all. corec and coind ARE
    -- identifiers and are deliberately left free: each is followed by
    -- a parenthesized binder group, so a shadowing binder misparses
    -- only where the text after it happens to look like the keyword's
    -- own syntax — and neither is a reference form a hand-written
    -- proof reaches for as a variable name
    -- (`def` and `type` were item keywords once; items are keyword-free
    -- now — docs/NovaElaboration.txt, Surface syntax — and both are
    -- ordinary identifiers)
    guard "an identifier ('\{name}' is a reserved keyword)"
                             (name /= "El" &&
                              name /= "import" && name /= "infixl" && name /= "infixr" &&
                              name /= "S" && name /= "Z" && name /= "class" &&
                              name /= "data" && name /= "let" && name /= "in" &&
                              name /= "using" && name /= "out" &&
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
    guard "an operator name (->, == and = spell reserved tokens)"
          (name /= "->" && name /= "==" && name /= "=")
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
sigmaElimBody i b = mapVarsE remap b
 where
  remap : Nat -> Maybe Nat
  -- the two pushed slots: y innermost, then x — they land where w
  -- stood, y at w's own index and x one further out
  remap Z         = Just i
  remap (S Z)     = Just (S i)
  remap (S (S m)) =
    if m < i then Just m                       -- inside Γ₁: unchanged
    else if m == i then Nothing                -- w itself: eliminated
    else Just (S m)                            -- inside Γ₀: one further out
||| foldGroups over groups carrying an IMPLICIT flag; the former is
||| chosen per group (Π implicit or explicit, × always explicit).
foldGroupsC : (Bool -> String -> a -> b -> b) -> List (Bool, String, a) -> b -> b
foldGroupsC f [] b = b
foldGroupsC f ((imp, x, t) :: rest) b = f imp x t (foldGroupsC f rest b)

||| The proof of `≡-elim p x w`, reindexed from the site's own binders
||| to the ELIMINATION context, where the variable x (index i) and the
||| equation variable w (index j, standing INSIDE it, so j < i) are
||| both gone: the entries between them come one nearer, those outside
||| x two. Nothing when the proof mentions either — that context has no
||| such entry, and the operator wrote a name the elimination removed.
|||
||| The twin of sigmaElimBody, and it exists for the same reason: the
||| grammar reads the methods before the scrutinees, so the proof is
||| parsed against the environment available at the time and shifted
||| once the two variables are known.
eqElimProof : (i, j : Nat) -> SElem -> Maybe SElem
eqElimProof i j b = mapVarsE remap b
 where
  remap : Nat -> Maybe Nat
  remap m =
    if m == j || m == i then Nothing                 -- w, x: eliminated
    else if m < j then Just m                        -- inside w: unchanged
    else if m < i then Just (minus m 1)              -- between them: w gone
    else Just (minus m 2)                            -- outside x: both gone

||| One branch of `sum-elim (a. l) (b. r) w`, reindexed from the
||| context it was PARSED against — the site's binders with the
||| branch's own name pushed innermost — to the context that branch is
||| ELABORATED in, where w (index i at the site) is gone and the
||| branch's binder stands exactly where it stood.
|||
||| The two contexts have the SAME LENGTH, so every other variable
||| keeps its index; only the pushed binder moves, from 0 to i.
||| Nothing when the branch mentions w — that context has no such
||| entry, and its components are what the branch was given instead.
sumSplitBranch : (i : Nat) -> SElem -> Maybe SElem
sumSplitBranch i b = mapVarsE remap b
 where
  remap : Nat -> Maybe Nat
  remap Z     = Just i                           -- the binder, into w's slot
  remap (S m) = if m == i then Nothing           -- w itself: eliminated
                else Just m                      -- everything else stands

||| The body of `unsquash (x. t) w`, reindexed from the context it was
||| PARSED against — the site's binders with x pushed innermost — to
||| the one it is ELABORATED in, where w is gone and x stands innermost
||| still. The two have the SAME LENGTH, one entry for the other, so
||| the entries before w keep their indices and those after it are
||| already where they belong; only w's own slot disappears.
unsquashBody : (i : Nat) -> SElem -> Maybe SElem
unsquashBody i b = mapVarsE remap b
 where
  remap : Nat -> Maybe Nat
  remap k =
    if k <= i then Just k                 -- x, then the entries after w
    else if k == S i then Nothing         -- w itself: eliminated
    else Just (minus k 1)                 -- the entries before it

-- ===== Types and elements (mutually recursive) =====

mutual
  -- Every level of the term and type grammar records the span of what
  -- it parsed (`atPos`/`atPosTy`), so an elaboration error can name
  -- the exact sub-expression it is about. A level that adds no node
  -- of its own hands its child straight back and the two spans
  -- coincide, so re-wrapping replaces rather than nests.

  -- ===== Type positions are ELEMENT positions =====
  --
  -- The T ladder is gone (docs/NovaElaboration.txt, THE TERM GRAMMAR
  -- MERGE): types are terms at 𝕍, so a type position enters the ONE
  -- term grammar at the level that reads what the T level read.
  --
  --   T{0}, T{1} → t{1}  parseSElemNoComma: binder groups, → × ⊎ /,
  --                      the equality prop, calc chains. NOT t{0}: a
  --                      type is not a pair, and a comma at the end of
  --                      a type belongs to whatever encloses it
  --   T{2}       → t{2}  parseSElemPrefix: keyword forms and spines
  --
  -- What each position GAINS is what the t ladder always had and T
  -- lacked: infix operators (so `a ≤ b` needs no parentheses as a
  -- type), λ and let, the keyword-headed forms.
  export
  parseSTy : FixTable -> NameEnv -> Rule STy
  parseSTy = parseSElemNoComma

  ||| The ∈-annotation's level, and every other former T{≥1} position.
  parseSTyArrow : FixTable -> NameEnv -> Rule STy
  parseSTyArrow = parseSElemNoComma

  ||| Former T{2} — the QIIT literal's anonymous external domain, which
  ||| must stop before the entry's own `→`.
  parseSTyEl : FixTable -> NameEnv -> Rule STy
  parseSTyEl = parseSElemPrefix

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
            (do kw2 "→" "->"; sp; b <- parseSElemNoComma tbl env'
                pure (foldGroupsC (\imp => if imp then SImpPiC else SPiC) groups b))
              -- an implicit binder is Π-only, as at the type level
              <|> (do kw2 "×" "\\x"; sp
                      guard "!implicit binders are Π-only: {x : a} × … is not a code"
                            (all (\(imp, _, _) => not imp) groups)
                      b <- parseSElemNoComma tbl env'
                      pure (foldGroupsC (\_ => SSigmaC) groups b)))
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
  -- level. The binder form (x : a) × b stays at t{1}
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
  -- Groups iterate and may be IMPLICIT — `{x : a}` — exactly as at the
  -- type level. A group and a spine's brace STEP share their opening
  -- token and are disjoint by the `:` a group must carry and an
  -- override cannot (an ascription is parenthesized); a group is read
  -- only HERE, at the head of the binder branch, never after a spine
  -- head. See docs/NovaElaboration.txt, THE TERM GRAMMAR MERGE.
  parseBinderGroupsC : FixTable -> NameEnv -> Rule (NameEnv, List (Bool, String, SElem))
  parseBinderGroupsC tbl env = do
    (imp, close) <- (kwc '(' $> (False, ')')) <|> (kwc '{' $> (True, '}'))
    sp; x <- parseName
    xs <- many (do space; parseName)
    sp; kwc ':'; sp
    a <- parseSElem tbl env; sp; kwc close
    let names = x :: xs
    let env1 = env <>< names
    rest <- optional (do sp; parseBinderGroupsC tbl env1)
    case rest of
      Nothing => pure (env1, groupElems imp names a)
      Just (env', groups) => pure (env', groupElems imp names a ++ groups)
   where
    groupElems : Bool -> List String -> SElem -> List (Bool, String, SElem)
    groupElems _ [] _ = []
    groupElems imp (n :: ns) a = (imp, n, a) :: groupElems imp ns (shiftElem 0 a)

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
        -- let x = e in b / let x : T = e in b — the annotated form is
        -- sugar for an ascribed definiens (the definiens elaborates in
        -- inference mode); the body extends maximally, like λ's.
        -- The body's indices are counted against the CORE context,
        -- which has TWO entries per let (el-let: the value, then its
        -- unfolding equation) — so x is pushed under a wildcard slot
        -- and resolves to index 1, the hypothesis slot (never
        -- resolvable) holding index 0
    <|> (do kw "let"; space; x <- parseNameR; sp
            manno <- optional (do kwc ':'; sp; t <- parseSTy tbl env; sp; pure t)
            kwEq; sp
            e <- parseSElem tbl env; sp
            kw "in"; sp
            b <- parseSElem tbl (env :< fst x :< wildcard)
            pure (SLet x (maybe e (SAnn e) manno) b))
        -- a KEYWORD-HEADED form (t{2½}) is a spine HEAD, so a
        -- projection or a further argument reaches it without
        -- parentheses: `out t .π₂` is `(out t) .π₂`. λ and let stay
        -- above the spine — their bodies extend maximally, so a
        -- trailing `.π₂` is read INSIDE the body, where it belongs.
        -- The form hands its layout cursor on, so an argument block
        -- it opened continues as the spine's
    <|> (do (lay, e) <- parseSElemKeyword tbl env
            parseSpine tbl env lay e)
    <|> parseSElemApp tbl env

  -- ===== Argument slots (docs/NovaElaboration.txt, Layout — ⟪·⟫) =====
  --
  -- A keyword form's argument is read by a SLOT reader: on the head's
  -- line an atom or a parenthesized group, exactly as before; on an
  -- ARGUMENT LINE the bare content of that group — the layout extent
  -- standing in for the closing parenthesis. Each reader threads the
  -- form's layout cursor, so the slots share one argument block and
  -- the spine continuation past the form's last slot picks it up.

  ||| A plain block argument — what an argument line of an ordinary
  ||| spine holds: a maximal term, optionally ascribed.
  blockArg : FixTable -> NameEnv -> Rule SElem
  blockArg tbl env = do
    e <- parseSElem tbl env
    (do sp; kwc ':'; sp; ty <- parseSTy tbl env; pure (SAnn e ty))
      <|> pure e

  ||| An atom-level slot (a scrutinee, ℕ-elim's z, a proof): an atom on
  ||| the line, a block argument on an argument line.
  slotAtom : FixTable -> NameEnv -> Lay -> Rule (Lay, SElem)
  slotAtom tbl env lay = do
    (lay', ap) <- argPos lay
    case ap of
      SameLine => do e <- parseSElemAtom tbl env; pure (lay', e)
      BlockLine => do
        let Just c = lay'.lblk | Nothing => fail "an argument"
        e <- inBlock c (blockArg tbl env)
        pure (lay', e)
      Misaligned c => do
        let Just c0 = lay.lblk | Nothing => fail "an argument"
        rng <- nextRange
        maybe (fatal (misalignedMsg c c0)) (\r => fatalLoc r (misalignedMsg c c0)) rng
      NoArg => fail "an argument"

  ||| A polynomial slot (ν's): an atom on the line, a full polynomial
  ||| on an argument line.
  slotPoly : FixTable -> NameEnv -> Lay -> Rule (Lay, SPoly)
  slotPoly tbl env lay = do
    (lay', ap) <- argPos lay
    case ap of
      SameLine => do f <- parseSPolyAtom tbl env; pure (lay', f)
      BlockLine => do
        let Just c = lay'.lblk | Nothing => fail "a polynomial"
        f <- inBlock c (parseSPoly tbl env)
        pure (lay', f)
      Misaligned c => do
        let Just c0 = lay.lblk | Nothing => fail "a polynomial"
        rng <- nextRange
        maybe (fatal (misalignedMsg c c0)) (\r => fatalLoc r (misalignedMsg c c0)) rng
      NoArg => fail "a polynomial"

  ||| The names of a BARE abstraction `x₁ … xₙ. t`: whitespace-separated,
  ||| the binder dot GLUED to the last name and followed by whitespace —
  ||| which is what tells `x. t` from a projection `x .π₁` or a dotted
  ||| name `M.x` (docs/NovaElaboration.txt, Layout — BLOCK ARGUMENT).
  bareNames : (n : Nat) -> Rule (List SName)
  bareNames Z = pure []
  bareNames (S Z) = do x <- parseNameR; kwc '.'; space; pure [x]
  bareNames (S k) = do x <- parseNameR; space; xs <- bareNames k; pure (x :: xs)

  ||| The names of a PARENTHESIZED abstraction, opening paren and dot
  ||| included: `(x₁ … xₙ. `.
  parenNames : (n : Nat) -> Rule (List SName)
  parenNames n = do
    kwc '('; sp
    xs <- go n
    sp; kwc '.'; sp
    pure xs
   where
    go : Nat -> Rule (List SName)
    go Z = pure []
    go (S Z) = do x <- parseNameR; pure [x]
    go (S k) = do x <- parseNameR; space; xs <- go k; pure (x :: xs)

  ||| An abstraction slot of `n` binders: `(x₁ … xₙ. body)` on the line
  ||| (the body at the slot's own level), or bare on an argument line
  ||| (the body a full t{≥0} — there is no encloser to claim a comma).
  slotAbsN : FixTable -> NameEnv -> (n : Nat) ->
             (bodyParen : NameEnv -> Rule SElem) -> Lay -> Rule (Lay, List SName, SElem)
  slotAbsN tbl env n bodyParen lay = do
    (lay', ap) <- argPos lay
    case ap of
      SameLine => do
        xs <- parenNames n
        body <- bodyParen (env <>< map fst xs)
        sp; kwc ')'
        pure (lay', xs, body)
      -- on an argument line the PARENTHESIZED group is legal too (⟪φ⟫
      -- is `(φ)` anywhere, or bare φ on an argument line), and it is
      -- tried first: a bare group can never begin with `(`
      BlockLine => do
        let Just c = lay'.lblk | Nothing => fail "a binder group"
        (xs, body) <- inBlock c (
              (do xs <- parenNames n
                  body <- bodyParen (env <>< map fst xs)
                  sp; kwc ')'
                  pure (xs, body))
          <|> (do xs <- bareNames n
                  body <- parseSElem tbl (env <>< map fst xs)
                  pure (xs, body)))
        pure (lay', xs, body)
      Misaligned c => do
        let Just c0 = lay.lblk | Nothing => fail "a binder group"
        rng <- nextRange
        maybe (fatal (misalignedMsg c c0)) (\r => fatalLoc r (misalignedMsg c c0)) rng
      NoArg => fail "a binder group"

  slotAbs1 : FixTable -> NameEnv -> (NameEnv -> Rule SElem) -> Lay -> Rule (Lay, SName, SElem)
  slotAbs1 tbl env bodyParen lay = do
    (lay', xs, body) <- slotAbsN tbl env 1 bodyParen lay
    case xs of
      [x] => pure (lay', x, body)
      _ => fail "a one-binder group"

  slotAbs2 : FixTable -> NameEnv -> (NameEnv -> Rule SElem) -> Lay -> Rule (Lay, SName, SName, SElem)
  slotAbs2 tbl env bodyParen lay = do
    (lay', xs, body) <- slotAbsN tbl env 2 bodyParen lay
    case xs of
      [x, y] => pure (lay', x, y, body)
      _ => fail "a two-binder group"

  slotAbs3 : FixTable -> NameEnv -> (NameEnv -> Rule SElem) -> Lay -> Rule (Lay, SName, SName, SName, SElem)
  slotAbs3 tbl env bodyParen lay = do
    (lay', xs, body) <- slotAbsN tbl env 3 bodyParen lay
    case xs of
      [x, y, z] => pure (lay', x, y, z, body)
      _ => fail "a three-binder group"

  ||| corec's CARRIER binder `(x : a. f)`: the carrier code, then the
  ||| coalgebra body over x.
  slotCarrier : FixTable -> NameEnv -> Lay -> Rule (Lay, SName, SElem, SElem)
  slotCarrier tbl env lay = do
    (lay', ap) <- argPos lay
    case ap of
      SameLine => do
        kwc '('; sp; x <- parseNameR; sp; kwc ':'; sp
        a <- parseSElemNoComma tbl env; sp; kwc '.'; sp
        f <- parseSElem tbl (env :< fst x); sp; kwc ')'
        pure (lay', x, a, f)
      BlockLine => do
        let Just c = lay'.lblk | Nothing => fail "a carrier binder"
        (x, a, f) <- inBlock c (
              (do kwc '('; sp; x <- parseNameR; sp; kwc ':'; sp
                  a <- parseSElemNoComma tbl env; sp; kwc '.'; sp
                  f <- parseSElem tbl (env :< fst x); sp; kwc ')'
                  pure (x, a, f))
          <|> (do x <- parseNameR; sp; kwc ':'; sp
                  a <- parseSElemNoComma tbl env; kwc '.'; space
                  f <- parseSElem tbl (env :< fst x)
                  pure (x, a, f)))
        pure (lay', x, a, f)
      Misaligned c => do
        let Just c0 = lay.lblk | Nothing => fail "a carrier binder"
        rng <- nextRange
        maybe (fatal (misalignedMsg c c0)) (\r => fatalLoc r (misalignedMsg c c0)) rng
      NoArg => fail "a carrier binder"

  ||| The motive slot of ℕ-elim: safely OPTIONAL, because z is an atom
  ||| and no atom (nor any block-argument term) has the `name. …`
  ||| shape.
  optMotive : FixTable -> NameEnv -> Lay -> Rule (Lay, Maybe (SName, STy))
  optMotive tbl env lay = do
    m <- optional (slotAbs1 tbl env (\e => parseSTy tbl e) lay)
    pure (case m of
            Just (lay', n, mot) => (lay', Just (n, mot))
            Nothing => (lay, Nothing))

  -- t{2½}: the keyword-headed forms — eliminators and the one-argument
  -- introductions. Each takes its own arguments through the slot
  -- readers, so the form ends exactly where the keyword's own syntax
  -- does and the spine continuation above may pick up from there —
  -- argument block included.
  parseSElemKeyword : FixTable -> NameEnv -> Rule (Lay, SElem)
  parseSElemKeyword tbl env = do
    (r, (lay, x)) <- bounds (parseSElemKeywordRaw tbl env)
    pure (lay, atPos r x)

  parseSElemKeywordRaw : FixTable -> NameEnv -> Rule (Lay, SElem)
  parseSElemKeywordRaw tbl env = do
    -- the reference column: the indent of the line the keyword sits on
    r0 <- indentNow
    let lay0 = MkLay r0 Nothing
    forms lay0
   where
    tyBody : NameEnv -> Rule SElem
    tyBody e = parseSTy tbl e

    elBody : NameEnv -> Rule SElem
    elBody e = parseSElem tbl e

    forms : Lay -> Rule (Lay, SElem)
    forms lay0 =
          (do kw2 "𝟘-elim" "Void-elim"; (l1, e) <- slotAtom tbl env lay0; pure (l1, SZeroElim e))
      <|> (do kw2 "ℕ-elim" "Nat-elim"
              (l1, mmot) <- optMotive tbl env lay0
              (l2, z) <- slotAtom tbl env l1
              (l3, n2, ih, s) <- slotAbs2 tbl env elBody l2
              (l4, t) <- slotAtom tbl env l3
              pure (l4, SNatElim mmot z n2 ih s t))
      <|> (do kw "S"; (l1, e) <- slotAtom tbl env lay0; pure (l1, SSuc e))
      <|> (do kw2 "inj₁" "inj1"; (l1, e) <- slotAtom tbl env lay0; pure (l1, SInj1 e))
      <|> (do kw2 "inj₂" "inj2"; (l1, e) <- slotAtom tbl env lay0; pure (l1, SInj2 e))
          -- ⊎-elim with an explicit motive, then the motive-less form
          -- (checking-only): a case group (x. ELEM) whose body is a
          -- bare name also parses as a motive group (z. TYPE), so the
          -- three-group spelling is tried first and the two-group
          -- spelling is the fallback
      <|> (do kw2 "⊎-elim" "\\/-elim"
              (l1, z, mot) <- slotAbs1 tbl env tyBody lay0
              (l2, a, l) <- slotAbs1 tbl env elBody l1
              (l3, b, r) <- slotAbs1 tbl env elBody l2
              (l4, t) <- slotAtom tbl env l3
              pure (l4, SSumElim (Just (z, mot)) a l b r t))
      <|> (do kw2 "⊎-elim" "\\/-elim"
              (l1, a, l) <- slotAbs1 tbl env elBody lay0
              (l2, b, r) <- slotAbs1 tbl env elBody l1
              (l3, t) <- slotAtom tbl env l2
              pure (l3, SSumElim Nothing a l b r t))
      <|> (do kw "class"; (l1, e) <- slotAtom tbl env lay0; pure (l1, SClass e))
      <|> (do kw2 "ν" "\\nu"; (l1, f) <- slotPoly tbl env lay0; pure (l1, SNuC f))
      <|> (do kw "out"; (l1, e) <- slotAtom tbl env lay0; pure (l1, SOut e))
      <|> (do kw "corec"
              (l1, x, a, f) <- slotCarrier tbl env lay0
              (l2, u) <- slotAtom tbl env l1
              pure (l2, SCorec x a f u))
      <|> (do kw "coind"
              (l1, x, y, r) <- slotAbs2 tbl env elBody lay0
              (l2, pw) <- slotAtom tbl env l1
              (l3, mx, my, mh, q) <- slotAbs3 tbl env elBody l2
              pure (l3, SCoind x y r pw mx my mh q))
          -- quot-elim likewise: with-motive first, motive-less fallback
      <|> (do kw "quot-elim"
              (l1, z, mot) <- slotAbs1 tbl env tyBody lay0
              (l2, a, f) <- slotAbs1 tbl env elBody l1
              (l3, q) <- slotAtom tbl env l2
              pure (l3, SQuotElim (Just (z, mot)) a f q))
      <|> (do kw "quot-elim"
              (l1, a, f) <- slotAbs1 tbl env elBody lay0
              (l2, q) <- slotAtom tbl env l1
              pure (l2, SQuotElim Nothing a f q))
          -- ≡-elim p x w — the EQUALITY variable elimination. Methods
          -- first, scrutinees last, as everywhere in the family; the
          -- proof sits at atom level, like ℕ-elim's binder-less z. The
          -- reindexing is sigma-elim's, doubled
          -- (docs/NovaElaboration.txt, e-eqelim)
      <|> (do kw2 "≡-elim" "eq-elim"; commit
              (l1, p) <- slotAtom tbl env lay0
              (l2, x) <- slotAtom tbl env l1
              (l3, w) <- slotAtom tbl env l2
              case (unPos x, unPos w) of
                (SVar _ xn i, SVar wr wn j) =>
                  -- j >= i is the elaborator's error to report (at the
                  -- equation's own span), and the remap would be
                  -- meaningless: leave the proof as parsed
                  if j >= i then pure (l3, SEqElim p x w)
                  else case eqElimProof i j p of
                    Just p' => pure (l3, SEqElim p' x w)
                    Nothing =>
                      let msg = "a ≡-elim proof free of '\{xn}' and '\{wn}' — the variables this eliminates, so the proof's context has no such entry" in
                      maybe (fail msg) (\r => failLoc r msg) (posOf x <|> posOf w <|> wr)
                -- not both variables: the elaborator says so, at their
                -- own spans. The proof keeps its parse indices; nothing
                -- ever reads them
                _ => pure (l3, SEqElim p x w))
          -- unsquash (x. t) w — the ∥∥ VARIABLE elimination. Method
          -- first, scrutinee last, as everywhere in the family; the body
          -- is reindexed against its own context once w is read
          -- (docs/NovaElaboration.txt, e-unsquash)
      <|> (do kw "unsquash"; commit
              (l1, x, b) <- slotAbs1 tbl env elBody lay0
              (l2, w) <- slotAtom tbl env l1
              case unPos w of
                SVar wrng nm i => case unsquashBody i b of
                  Just b' => pure (l2, SUnsquash x b' w)
                  Nothing =>
                    let msg = "an unsquash body free of '\{nm}' — the variable this eliminates, so the body's context has no such entry (it has the witness \{fst x} instead)" in
                    maybe (fail msg) (\r => failLoc r msg) (posOf w <|> wrng)
                _ => pure (l2, SUnsquash x b w))
          -- sum-elim (a. l) (b. r) w — the ⊎ VARIABLE elimination.
          -- Methods first, scrutinee last, as everywhere in the family;
          -- each branch is reindexed against ITS OWN elimination
          -- context once w is read (docs/NovaElaboration.txt, e-sumsplit)
      <|> (do kw "sum-elim"; commit
              (l1, a, l) <- slotAbs1 tbl env elBody lay0
              (l2, b, r) <- slotAbs1 tbl env elBody l1
              (l3, w) <- slotAtom tbl env l2
              case unPos w of
                SVar wrng nm i =>
                  case (sumSplitBranch i l, sumSplitBranch i r) of
                    (Just l', Just r') => pure (l3, SSumSplit a l' b r' w)
                    _ =>
                      let msg = "a sum-elim branch free of '\{nm}' — the variable this eliminates, so a branch's context has no such entry (it has \{fst a} or \{fst b} there instead)" in
                      maybe (fail msg) (\rr => failLoc rr msg) (posOf w <|> wrng)
                -- not a variable: the elaborator says so, at its own
                -- span. The branches keep their parse indices; nothing
                -- ever reads them
                _ => pure (l3, SSumSplit a l b r w))
          -- sigma-elim (x y. t) w — the Σ VARIABLE elimination. The
          -- body is parsed against the site's binders with x and y
          -- pushed innermost (the scrutinee is only read after it), and
          -- REINDEXED against the elimination context once w's index is
          -- known: a name resolution, so it belongs here and not in the
          -- elaborator (docs/NovaElaboration.txt, e-sigmaelim)
      <|> (do kw "sigma-elim"; commit
              (l1, x, y, b) <- slotAbs2 tbl env elBody lay0
              (l2, w) <- slotAtom tbl env l1
              case unPos w of
                SVar wrng nm i => case sigmaElimBody i b of
                  Just b' => pure (l2, SSigmaElim x y b' w)
                  Nothing =>
                    let msg = "a sigma-elim body free of '\{nm}' — the variable this eliminates, so the body's context has no such entry (its components are \{fst x} and \{fst y})" in
                    maybe (fail msg) (\r => failLoc r msg) (posOf w <|> wrng)
                -- not a variable: the elaborator says so, at the
                -- scrutinee's own span. The body keeps its parse
                -- indices; nothing ever reads them
                _ => pure (l2, SSigmaElim x y b w))
      <|> (do kw "squash-elim"
              (l1, e) <- slotAtom tbl env lay0
              (l2, x, body) <- slotAbs1 tbl env elBody l1
              pure (l2, SSquashElim e x body))
      <|> (do (r, _) <- bounds (kw2 "⋆" "\\star")
              -- `using` is a CONTEXTUAL keyword: recognized only here,
              -- immediately after ⋆ (a witness genuinely named `using`
              -- is written parenthesized: ⋆ (using))
              u <- optional (do space; kw "using"; space; parseUsingNames)
              case u of
                Just ns => pure (lay0, SStarUsing r ns)
                Nothing => do
                  w <- optional (slotAtom tbl env lay0)
                  pure (case w of
                          Nothing => (lay0, SStar r)
                          Just (l1, e) => (l1, SStarWit e)))

  -- t{3}: application / projection chains
  parseSElemApp : FixTable -> NameEnv -> Rule SElem
  parseSElemApp tbl env = do
    (r, x) <- bounds (parseSElemAppRaw tbl env)
    pure (atPos r x)

  parseSElemAppRaw : FixTable -> NameEnv -> Rule SElem
  parseSElemAppRaw tbl env = do
    -- the reference column: the indent of the line the head sits on
    r0 <- indentNow
    e <- parseSElemAtom tbl env
    parseSpine tbl env (MkLay r0 Nothing) e

  ||| The postfix continuation of a spine, over an already-parsed head:
  ||| arguments, implicit overrides and projections, left-associative.
  ||| Shared by the two kinds of head — an ATOM (t{5}, the ordinary
  ||| case) and a KEYWORD-HEADED form (t{2½}: `out t`, `S n`, an
  ||| eliminator), so `out t .π₂` needs no parentheses.
  |||
  ||| LAYOUT: the next argument may also stand on an ARGUMENT LINE —
  ||| a term-initial line indented past the spine's reference column,
  ||| or at the column of the block already open (docs/
  ||| NovaElaboration.txt, Layout — rule 2). There it is a whole
  ||| block argument; a line the argument reading rejects (an
  ||| operator, an arrow, a chain link, `using`, …) closes the spine
  ||| and is handed to the enclosing construct by backtracking.
  parseSpine : FixTable -> NameEnv -> Lay -> SElem -> Rule SElem
  parseSpine tbl env lay e =
        (do (lay', ap) <- argPos lay
            case ap of
              NoArg => fail "an argument"
              SameLine => step lay' False
              BlockLine => step lay' True
              -- a term-initial line between r and the block's column
              -- is a VERDICT, not a rejection — but only once it has
              -- READ as an argument; a continuation token (→, ≡⟨, an
              -- operator) between the two columns is the enclosing
              -- construct's, as anywhere
              Misaligned c => do
                let Just c0 = lay.lblk | Nothing => fail "an argument"
                rng <- nextRange
                _ <- inBlock c (blockArg tbl env)
                maybe (fatal (misalignedMsg c c0)) (\r => fatalLoc r (misalignedMsg c c0)) rng)
    <|> pure e
   where
    ||| One spine step, on the head's line or on an argument line (the
    ||| projection and override steps read the same either way; a
    ||| plain argument is an atom on the line, a block argument on an
    ||| argument line).
    step : Lay -> (onLine : Bool) -> Rule SElem
    step lay' onLine =
          (do (r, _) <- bounds (kw2 ".π₁" ".1"); parseSpine tbl env lay' (grew e r (SProj1 e)))
      <|> (do (r, _) <- bounds (kw2 ".π₂" ".2"); parseSpine tbl env lay' (grew e r (SProj2 e)))
      -- {t} — an implicit-position override argument — and {} — the
      -- NO-INSERT marker, suppressing trailing-implicit insertion
      -- (docs/NovaPerfectSurface.txt, Phases 3b/3d); NB `{-` opens a
      -- comment at the lexer, so an override starting with an
      -- operator needs a space: { -x } — the Haskell convention
      <|> (do (r, mt) <- bounds (do
                kwc '{'; sp
                (do kwc '}'; pure Nothing)
                  <|> (do t <- parseSElem tbl env; sp; kwc '}'; pure (Just t)))
              case mt of
                Nothing => parseSpine tbl env lay' (grew e r (SNoIns e))
                Just t => parseSpine tbl env lay' (grew e r (SApp e (SImpArg t))))
      <|> (if onLine
             then do
               let Just c = lay'.lblk | Nothing => fail "an argument"
               (r, e') <- bounds (inBlock c (blockArg tbl env))
               parseSpine tbl env lay' (grew e r (SApp e e'))
             else do
               (r, e') <- bounds (parseSElemAtom tbl env)
               parseSpine tbl env lay' (grew e r (SApp e e')))

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
        -- 𝕌 and Ω are TERMS (typed at 𝕍). They read here so that a
        -- type position can be an ordinary element position — see
        -- docs/NovaElaboration.txt, THE TERM GRAMMAR MERGE
    <|> (kw2 "𝕌" "Set"    $> SUnivC)
    <|> (kw2 "Ω" "Prop"   $> SPropC)
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

||| `El` where the literal's own sorts do not reach — the RETIRED
||| Nova-level El (`El ℕ`), which the ToS's El only looks like. It had
||| no bare counterpart to fall back on: the printer spells an external
||| domain as the code it is (Distill.renderQDomain), so a literal
||| written this way elaborated and then failed its own round trip,
||| `El ℕ` re-parsing as the bare type it was printed as.
|||
||| A DIAGNOSIS, last and FATAL, for the reason the clause-head one is:
||| a branch rejection here is outrun by whichever sibling read
||| furthest, and the caret lands on the entry's `;` with nothing said
||| about the `El` that caused it. `El` is a reserved word, so no
||| sibling could have read it anyway.
externalEl : Rule a
externalEl = do
  -- located at the `El` itself: a bare `fatal` can only synthesize the
  -- position parsing stopped at, which is the domain past it
  (r, _) <- bounds (kw "El")
  let msg = "!El marks a domain in this literal's own sorts — an external domain IS its code: spell it bare"
  space
  maybe (fatal msg) (\r' => fatalLoc r' msg) r

sqDomain : FixTable -> NameEnv -> NameEnv -> Rule (Either STy SQTm)
sqDomain tbl tos ext =
      (do kw "El"; space; q <- sqCode tbl tos ext; pure (Right q))
  <|> (Left <$> parseSTy tbl ext)
  <|> externalEl

||| An ANONYMOUS domain: like `sqDomain`, but the external case stops
||| below the arrow level (T{2}) — a greedy full type would swallow
||| the rest of the entry (`ℕ → El Q` must be TWO pieces, not one
||| function type). Higher-order external domains stay parenthesized,
||| which re-enters the full type grammar.
sqDomainNoArrow : FixTable -> NameEnv -> NameEnv -> Rule (Either STy SQTm)
sqDomainNoArrow tbl tos ext =
      (do kw "El"; space; q <- sqCode tbl tos ext; pure (Right q))
  <|> (Left <$> parseSTyEl tbl ext)
  <|> externalEl

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
  (nr, n) <- bounds parseName; sp; kwc ':'; sp
  (bs, res) <- sqTele tbl entries penv
  pure (MkSQDecl n nr bs res)

||| data [x : T]* ⏎ entry+ — the entries form a LAYOUT BLOCK on the
||| lines after the header, one per line at one column, an entry's own
||| continuation lines deeper still (docs/NovaElaboration.txt, Layout).
parseSData : FixTable -> Rule SItem
parseSData tbl = do
  kw "data"
  commit
  (penv, params) <- parseParams [<]
  b <- blockNow
  mc <- ws
  let Just c = mc
    | Nothing => fatal "!a data literal's entries begin on the line after its header, indented"
  fatalGuard (offside b c) (c > b)
  ds <- inBlock c (do
    d <- sqDecl tbl penv [<]
    rest <- go c penv ([<] :< d.dqname)
    pure (d :: rest))
  pure (SData params ds)
 where
  ||| Zero or more [x : T] PARAMETER groups — the literal's ambient
  ||| telescope, each scoping over the ones after it. The whitespace
  ||| BEFORE a group belongs to the group's branch, so the line break
  ||| before the first entry is left for the block to read.
  parseParams : NameEnv -> Rule (NameEnv, List (String, STy))
  parseParams env =
        (do sp; kwc '['; sp; x <- parseName; sp; kwc ':'; sp
            t <- parseSTy tbl env; sp; kwc ']'
            (env', rest) <- parseParams (env :< x)
            pure (env', (x, t) :: rest))
    <|> pure (env, [])
  ||| The entries after the first: each on a line of its own at the
  ||| block's column. A line left of it ends the literal (and the
  ||| item); a line right of it is a stray continuation the entry
  ||| before did not read, which the file loop reports.
  go : Int -> NameEnv -> NameEnv -> Rule (List SQDecl)
  go c penv entries =
        (do mc <- ws
            guard "an entry at column \{col c}" (mc == Just c)
            d <- sqDecl tbl penv entries
            rest <- go c penv (entries :< d.dqname)
            pure (d :: rest))
    <|> pure []

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

||| A column-0 line that begins an ITEM rather than a clause: a
||| signature (`n :`) or a keyword item. Read to be REJECTED: the clause
||| run ends there, and backtracking hands the line to the file loop.
itemStart : Rule ()
itemStart =
      (do ignore (parseName <|> parseOpName); sp; kwc ':')
  <|> kw "data" <|> kw "import" <|> kw "infixl" <|> kw "infixr"

||| clause ::= lhs = t ([n])? — a COLUMN-0 line directly under its
||| signature (docs/NovaElaboration.txt, Layout); nothing marks it but
||| its column and its not being an item. The RHS is parsed in the
||| LHS's binder telescope; the optional [n] names the clause's
||| equation lemma.
parseSClauseRaw : FixTable -> String -> Rule SClause
parseSClauseRaw tbl iname = do
  isItem <- (do itemStart; pure True) <|> pure False
  guard "a clause (this line begins an item)" (not isItem)
  commit
  pats <- parseClauseLhs iname
  sp; kwEq; sp
  let vars = patVarsOf pats
  rhs <- parseSElem tbl ([<] <>< map fst vars)
  mn <- optional (do sp; kwc '['; sp; (nr, n) <- bounds parseName; sp; kwc ']'; pure (n, nr))
  pure (MkSClause pats vars rhs (map fst mn) (mn >>= snd) Nothing)

||| The clause with its own source span attached — what the item macro
||| reports its generated equation lemma at.
export
parseSClause : FixTable -> String -> Rule SClause
parseSClause tbl iname = do
  -- the line break to column 0 is read BEFORE the span is taken, so
  -- the clause's range starts at its own first token
  mc <- ws
  guard "a clause at column 1" (mc == Just 0)
  (r, c) <- bounds (parseSClauseRaw tbl iname)
  pure ({ crange := r } c)

-- COMMITS: once a column-0 line has read as `n :` the item can be
-- nothing but a signature, so commit — a failure deep inside then
-- propagates with its REAL position instead of backtracking to the
-- item boundary, where the file loop would end and report a useless
-- "Expected end of input" at the next line. The commit inside a
-- clause (after the line has been told from an item) likewise keeps
-- a malformed clause — the definiens included — a hard error while
-- letting the clause run end cleanly at the next item.
--
-- The whitespace BEFORE each optional piece sits inside the piece's
-- branch: a line break to the next item (column 0, ≤ the file block)
-- fails `sp`, and the branch's failure restores the whitespace for
-- the file loop to read.
export
parseSItem : FixTable -> Rule SItem
parseSItem tbl =
      parseSData tbl
  <|> (do (r, x) <- bounds (parseName <|> parseOpName); sp
          kwc ':'; commit; sp
          ty <- parseSTy tbl [<]
          -- item-level using (SearchlessElaboration.md §5.3): scopes
          -- EVERY discharge of the item — ⋆s, switches, WD premises —
          -- to the named lemmas plus hypotheses
          muses <- optional (do sp; kw "using"; sp; parseUsingNames)
          metaEta <- optional (do sp; kwc '['; sp; (nr, n) <- bounds parseName; sp; kwc ']'; pure (n, nr))
          cls <- many (parseSClause tbl x)
          -- A signature's definiens is a CLAUSE (docs/NovaElaboration.txt,
          -- Surface syntax): `x = t` is the clause with ZERO patterns.
          -- Alone, it is a plain definition; beside pattern clauses it is
          -- the WITNESS of the clausal item (existence supplied by hand);
          -- no clause at all is a declaration.
          let (wits, eqs) = partition (\c => null c.cpats) cls
          case (wits, eqs) of
            ([], []) =>
              case (metaEta, muses) of
                (Just _, _) => fail "!a uniqueness-name override must be followed by clauses"
                (Nothing, Just _) => fail "!a declaration discharges nothing — a using-clause is for definitions with a definiens"
                (Nothing, Nothing) => pure (SDeclDef r x ty)
            ([c], []) =>
              case (metaEta, c.cname) of
                (Just _, _) => fail "!a uniqueness-name override must be followed by clauses"
                (_, Just _) => fail "!a definition's clause names no lemma — the [name] override belongs to a pattern clause"
                (Nothing, Nothing) => pure (SDef r x ty c.crhs muses)
            (_ :: _ :: _, _) => fail "!at most one clause of an item may spell no pattern — that clause is its definiens (or, beside pattern clauses, its witness)"
            (mw, (e :: es)) =>
              case muses of
                Just _ => fail "!a using-clause on a clausal definition is not supported yet"
                Nothing =>
                  case mw of
                    [w] => case w.cname of
                      Just _ => fail "!the witness clause names no lemma — the [name] override belongs to a pattern clause"
                      Nothing => pure (SClausalDef r x ty (map fst metaEta) (metaEta >>= snd) (Just w.crhs) (e :: es))
                    _ => pure (SClausalDef r x ty (map fst metaEta) (metaEta >>= snd) Nothing (e :: es)))

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

||| The whitespace between two items of the file block: a line break to
||| column 0, or nothing at all (the end of the input, or garbage on
||| the same line — which the next item's parse then reports). An
||| indented line here is an error: nothing above it could read it as
||| a continuation, and nothing below it can. A plain failure, not a
||| verdict, so that a DEEPER failure — the construct inside the item
||| that refused the line for its own reason — wins the report when
||| there is one.
itemSep : Rule ()
itemSep = do
  mc <- ws
  case mc of
    Nothing => pure ()
    Just 0 => pure ()
    Just c => fail "!column \{col c} does not continue the item above — indent it past the term it belongs to, or start an item at column 1"

||| The file's first token must open an item, at column 0.
atColumn0 : Rule ()
atColumn0 = do
  mp <- peekPos
  case mp of
    Nothing => pure ()
    Just p => do
      rng <- nextRange
      let msg = "!a file's first item starts at column 1 — this line starts at column \{col p.column}"
      when (p.column /= 0) (maybe (fatal msg) (\r => fatalLoc r msg) rng)

||| A file: imports, then fixity declarations and items interleaved,
||| one per column-0 line (the file is the block at column 0 —
||| docs/NovaElaboration.txt, Layout).
||| The initial table holds the fixities of OPENED imported operators;
||| declared fixities extend it as parsing proceeds and are returned
||| for export.
||| Each item is paired with its source range (the whole item, not
||| sub-expression precision) — enough for LSP diagnostics to anchor
||| at the right item without threading Range through STy/SElem
||| themselves.
export
parseSFile : FixTable -> Rule (List SImport, FixTable, List (Maybe Range, SItem), List SBodyEntry)
parseSFile tbl0 = do
  atColumn0
  imports <- many (do i <- parseSImport; itemSep; pure i)
  (decls, items, body) <- go tbl0
  pure (imports, decls, items, body)
 where
  go : FixTable -> Rule (FixTable, List (Maybe Range, SItem), List SBodyEntry)
  go tbl =
        (do (r, f) <- bounds parseFixity; itemSep
            (decls, items, body) <- go (f :: tbl)
            pure (f :: decls, items, Left (r, f) :: body))
    <|> (do (r, i) <- bounds (parseSItem tbl); itemSep
            (decls, items, body) <- go tbl
            pure (decls, (r, i) :: items, Right (r, i) :: body))
    <|> pure ([], [], [])

||| Pass 1 of the loader's two-stage parse: just the import header
||| (the dependencies' fixity tables are needed before the body can be
||| parsed). Layout-blind on purpose: a layout fault in the body is
||| pass 2's to report.
export
parseSHeader : Rule (List SImport)
parseSHeader = do
  optSpace
  imports <- many (do i <- parseSImport; optSpace; pure i)
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
parseErrRange : ParsingError Token st -> Range
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

||| A TAB in a line's indentation: a lexical error under layout (a tab
||| has no agreed width — docs/NovaElaboration.txt, Layout). Reported
||| at the tab.
tabInIndent : List String -> Maybe Range
tabInIndent ls = go 0 ls
 where
  go : Int -> List String -> Maybe Range
  go _ [] = Nothing
  go i (l :: rest) =
    let lead = takeWhile (\c => c == ' ' || c == '\t') (unpack l) in
    case findIndex (== '\t') lead of
      Just k => Just (MkRange (MkPosition i (cast (finToNat k))) (MkPosition i (cast (finToNat k) + 1)))
      Nothing => go (i + 1) rest

export
runSurfaceParser : Rule a -> String -> Either ParseFail (SnocList (Range, TokenKind), a)
runSurfaceParser rule input =
  let (commentRanges, toks) = tokenise (unpack input)
      srcLines = lines input in
  case tabInIndent srcLines of
    Just r => Left (MkParseFail (Just r) "a tab in indentation — layout counts columns, and a tab has no agreed width; indent with spaces" [])
    Nothing =>
      case parseWith initPState (rule <* eof) (normaliseTokens toks) of
        Left err  => Left (MkParseFail (Just (parseErrRange err)) (parseErrMessage err) (parseErrNotes err))
        Right (st, _, x, _) =>
          Right (st.kinds <>< map (\r => (clipCommentRange srcLines r, Comment)) (toList commentRanges), x)
