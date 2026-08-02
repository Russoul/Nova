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
        Just _ => fail "keyword is a prefix of an identifier"
        Nothing => pure ()
    Nothing => pure ()
  emit r Keyword

kwc : Char -> Rule ()
kwc c = do
  (r, ()) <- bounds (char_ c)
  emit r Keyword

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
    c  <- terminal "identifier start" $ \tok =>
            case tok of
              Symbol ch => if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || ch == '_'
                           then Just ch
                           else Nothing
              _ => Nothing
    cs <- many (terminal "identifier char" $ \tok =>
            case tok of
              Symbol ch => if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') ||
                              (ch >= '0' && ch <= '9') || ch == '_' || ch == '\''
                           then Just ch
                           else Nothing
              _ => Nothing)
    let name = pack (c :: cs)
    -- S/Z/Refl/class are also reserved: unlike def/type/El/Prf/import/
    -- infixl/infixr they're syntactically valid identifiers, so without
    -- this a shadowing binder would parse fine and only misbehave at a
    -- REFERENCE site — loudly for S/class (they consume a following atom,
    -- so the parse fails deep and confusingly) or silently for Z/Refl
    -- (bare tokens — a reference just parses as the literal zero/Refl,
    -- no error at all).
    guard "Reserved keyword" (name /= "def" && name /= "type" && name /= "El" && name /= "Prf" &&
                              name /= "import" && name /= "infixl" && name /= "infixr" &&
                              name /= "S" && name /= "Z" && name /= "class" &&
                              name /= "data")
    pure name

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
    c <- terminal "operator char" opTok
    cs <- many (terminal "operator char" opTok)
    pure (pack (c :: cs))

||| A possibly-qualified operator (+ or M.+): the mention form's and
||| the definition header's name grammar.
parseOpRef : Rule String
parseOpRef = do
  pre <- many (do n <- parseName; kwc '.'; pure n)
  op <- parseOpName
  pure (joinBy "." (pre ++ [op]))

foldGroups : (String -> a -> b -> b) -> List (String, a) -> b -> b
foldGroups f [] b = b
foldGroups f ((x, t) :: rest) b = f x t (foldGroups f rest b)

-- ===== Types and elements (mutually recursive) =====

mutual
  -- T{0}: eq-type on top, then the arrow level
  export
  parseSTy : FixTable -> NameEnv -> Rule STy
  parseSTy tbl env =
        (do e0 <- parseSElemOp tbl env; sp
            kw "≡"; sp
            e1 <- parseSElemOp tbl env; sp
            kw "∈"; sp
            a  <- parseSTyArrow tbl env
            pure (STyEq e0 e1 a))
    <|> parseSTyArrow tbl env

  -- T{1}: named binder forms and the sugared right-assoc infixes.
  -- Binder groups iterate: (x:T) (y:U) → B ≡ (x:T) → (y:U) → B
  -- (and likewise for ⨯).
  parseSTyArrow : FixTable -> NameEnv -> Rule STy
  parseSTyArrow tbl env =
        -- the codomain is full T{≥0}: a trailing ≡-type needs no parens,
        -- so lemma statements read as written
        (do (env', groups) <- parseBinderGroups tbl env
            sp
            (do kw "→"; sp; b <- parseSTy tbl env'; pure (foldGroups STyPi groups b))
              <|> (do kw "⨯"; sp; b <- parseSTy tbl env'; pure (foldGroups STySigma groups b)))
    <|> (do a <- parseSTyEl tbl env
            (do sp; kw "→"; sp; b <- parseSTy tbl (env :< wildcard); pure (STyPi wildcard a b))
              <|> (do sp; kw "⨯"; sp; b <- parseSTy tbl (env :< wildcard); pure (STySigma wildcard a b))
              <|> (do sp; kw "/"; sp; (x, y, r) <- parseQuotRel tbl env; pure (STyQuot a x y r))
              <|> pure a)

  -- one or more (x:T) groups, each scoping over the ones after it
  parseBinderGroups : FixTable -> NameEnv -> Rule (NameEnv, List (String, STy))
  parseBinderGroups tbl env = do
    kwc '('; sp; x <- parseName; sp; kwc ':'; sp
    a <- parseSTy tbl env; sp; kwc ')'
    rest <- optional (do sp; parseBinderGroups tbl (env :< x))
    case rest of
      Nothing => pure (env :< x, [(x, a)])
      Just (env', groups) => pure (env', (x, a) :: groups)

  -- (x y. r)  or bare r as sugar for (_ _. r) — r is an Ω-valued ELEMENT
  parseQuotRel : FixTable -> NameEnv -> Rule (SName, SName, SElem)
  parseQuotRel tbl env =
        (do kwc '('; sp; x <- parseNameR; space; y <- parseNameR
            sp; kwc '.'; sp; r <- parseSElemNoComma tbl (env :< fst x :< fst y); sp; kwc ')'
            pure (x, y, r))
    <|> (do r <- parseSElemPrefix tbl (env :< wildcard :< wildcard); pure ((wildcard, Nothing), (wildcard, Nothing), r))

  -- T{2}: El / Prf
  parseSTyEl : FixTable -> NameEnv -> Rule STy
  parseSTyEl tbl env =
        (do kw "El"; space; e <- parseSElemAtom tbl env; pure (STyEl e))
    <|> (do kw "Prf"; space; e <- parseSElemAtom tbl env; pure (STyPrf e))
    <|> parseSTyAtom tbl env

  -- T{4}: atoms
  parseSTyAtom : FixTable -> NameEnv -> Rule STy
  parseSTyAtom tbl env =
        (do (r, x) <- bounds (do kwc '?'; parseName); pure (STyHole r False x))
    <|> (kw "𝟘" $> STyZero)
    <|> (kw "𝟙" $> STyOne)
    <|> (kw "ℕ" $> STyNat)
    <|> (kw "𝕌" $> STyUniv)
    <|> (kw "Ω" $> STyProp)
    <|> (do (r, x) <- bounds parseDottedName
            case unpack x of
              ('_' :: rest) => pure (STyHole r True (pack rest))
              _ => pure (STySig x))
    <|> (do kwc '('; sp; t <- parseSTy tbl env; sp; kwc ')'; pure t)

  -- t{0}: top-level comma = pair (right-assoc)
  export
  parseSElem : FixTable -> NameEnv -> Rule SElem
  parseSElem tbl env = do
    e <- parseSElemNoComma tbl env
    (do sp; kwc ','; sp; e' <- parseSElem tbl env; pure (SPair e e'))
      <|> pure e

  -- t{1}: universe-code binder/infix forms and eq-code; binder groups
  -- iterate exactly as at the type level
  parseSElemNoComma : FixTable -> NameEnv -> Rule SElem
  parseSElemNoComma tbl env =
        (do (env', groups) <- parseBinderGroupsC tbl env
            sp
            (do kw "→"; sp; b <- parseSElemNoComma tbl env'; pure (foldGroups SPiC groups b))
              <|> (do kw "⨯"; sp; b <- parseSElemNoComma tbl env'; pure (foldGroups SSigmaC groups b)))
    <|> (do e <- parseSElemOp tbl env
            (do sp; kw "→"; sp; e' <- parseSElemNoComma tbl (env :< wildcard); pure (SPiC wildcard e e'))
              <|> (do sp; kw "⨯"; sp; e' <- parseSElemNoComma tbl (env :< wildcard); pure (SSigmaC wildcard e e'))
              <|> (do sp; kw "/"; sp; (x, y, r) <- parseQuotRelC tbl env; pure (SQuotC e x y r))
              <|> (do sp; kw "≡"; sp
                      e1 <- parseSElemOp tbl env; sp; kw "∈"; sp
                      t2 <- parseSTyEl tbl env
                      pure (SEqC e e1 t2))
              <|> pure e)

  -- t{1½}: declared infix operators — precedence climbing over the
  -- fixity table. An operator token is a NAME; infix use is
  -- application of it.
  parseSElemOp : FixTable -> NameEnv -> Rule SElem
  parseSElemOp tbl env = climb 0
   where
    mutual
      climb : Nat -> Rule SElem
      climb minP = do
        l <- parseSElemPrefix tbl env
        cont l minP

      cont : SElem -> Nat -> Rule SElem
      cont l minP =
            (do sp
                (rng, op) <- bounds parseOpName
                case lookup op tbl of
                  Nothing => fail "operator '\{op}' has no fixity in scope"
                  Just (assoc, p) => do
                    guard "operator precedence" (p >= minP)
                    sp
                    r <- climb (case assoc of AssocL => S p; AssocR => p)
                    cont (SApp (SApp (SSig rng op) l) r) minP)
        <|> pure l

  parseBinderGroupsC : FixTable -> NameEnv -> Rule (NameEnv, List (String, SElem))
  parseBinderGroupsC tbl env = do
    kwc '('; sp; x <- parseName; sp; kwc ':'; sp
    a <- parseSElem tbl env; sp; kwc ')'
    rest <- optional (do sp; parseBinderGroupsC tbl (env :< x))
    case rest of
      Nothing => pure (env :< x, [(x, a)])
      Just (env', groups) => pure (env', (x, a) :: groups)

  parseQuotRelC : FixTable -> NameEnv -> Rule (SName, SName, SElem)
  parseQuotRelC tbl env =
        (do kwc '('; sp; x <- parseNameR; space; y <- parseNameR
            sp; kwc '.'; sp; r <- parseSElemNoComma tbl (env :< fst x :< fst y); sp; kwc ')'
            pure (x, y, r))
    <|> (do r <- parseSElemPrefix tbl (env :< wildcard :< wildcard); pure ((wildcard, Nothing), (wildcard, Nothing), r))

  -- t{2}: prefix forms, motive-first eliminators
  parseSElemPrefix : FixTable -> NameEnv -> Rule SElem
  parseSElemPrefix tbl env =
        -- λ's body extends over operators: λx. x + y ≡ λx. (x + y)
        (do kw "λ"; sp; x <- parseNameR; sp; kwc '.'; sp
            e <- parseSElemOp tbl (env :< fst x); pure (SLam x e))
    <|> (do kw "𝟘-elim"; space; e <- parseSElemAtom tbl env; pure (SZeroElim e))
    <|> (do kw "ℕ-elim"; space
            kwc '('; sp; n <- parseNameR; sp; kwc '.'; sp
            mot <- parseSTy tbl (env :< fst n); sp; kwc ')'; sp
            z <- parseSElemAtom tbl env; sp
            kwc '('; sp; n2 <- parseNameR; space; ih <- parseNameR
            sp; kwc '.'; sp; s <- parseSElem tbl (env :< fst n2 :< fst ih); sp; kwc ')'; sp
            t <- parseSElemAtom tbl env
            pure (SNatElim n mot z n2 ih s t))
    <|> (do kw "S"; space; e <- parseSElemAtom tbl env; pure (SSuc e))
    <|> (do kw "class"; space; e <- parseSElemAtom tbl env; pure (SClass e))
    <|> (do kw "quot-elim"; space
            kwc '('; sp; z <- parseNameR; sp; kwc '.'; sp
            mot <- parseSTy tbl (env :< fst z); sp; kwc ')'; sp
            kwc '('; sp; a <- parseNameR; sp; kwc '.'; sp
            f <- parseSElem tbl (env :< fst a); sp; kwc ')'; sp
            q <- parseSElemAtom tbl env
            pure (SQuotElim z mot a f q))
    <|> (do kw "squash-elim"; space
            e <- parseSElemAtom tbl env; sp
            kwc '('; sp; x <- parseNameR; sp; kwc '.'; sp
            body <- parseSElem tbl (env :< fst x); sp; kwc ')'
            pure (SSquashElim e x body))
    <|> (do kw "⋆"
            w <- optional (do space; parseSElemAtom tbl env)
            pure (case w of
                    Nothing => SStar
                    Just e  => SStarWit e))
    <|> parseSElemApp tbl env

  -- t{3}: application / projection chains
  parseSElemApp : FixTable -> NameEnv -> Rule SElem
  parseSElemApp tbl env = do
    e <- parseSElemAtom tbl env
    cont e
   where
    cont : SElem -> Rule SElem
    cont e =
          (do sp; kw ".π₁"; cont (SProj1 e))
      <|> (do sp; kw ".π₂"; cont (SProj2 e))
      <|> (do sp; e' <- parseSElemAtom tbl env; cont (SApp e e'))
      <|> pure e

  -- t{5}: atoms, including ascription
  parseSElemAtom : FixTable -> NameEnv -> Rule SElem
  parseSElemAtom tbl env =
        -- a rigid hole: `?` immediately followed by a name (the
        -- char-level token stream enforces adjacency — a space fails
        -- the name parser). Tried before the operator atom, so a bare
        -- `?` operator token stays available
        (do (r, x) <- bounds (do kwc '?'; parseName); pure (SHole r False x))
        -- mention form: (+) — the operator as an ordinary reference
    <|> (do (r, op) <- bounds (do kwc '('; sp; op <- parseOpRef; sp; kwc ')'; pure op); pure (SSig r op))
        -- a FIXITY-FREE operator token is an ordinary name atom (⊥, ⊤,
        -- prefix-applied ¬); declared-infix operators are excluded, so
        -- application juxtaposition never captures them
    <|> (do (rng, op) <- bounds parseOpName
            case lookup op tbl of
              Nothing => pure (SSig rng op)
              Just _ => fail "infix operator in atom position")
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
    <|> (kw "⋆"    $> SStar)
    <|> (do kw "∥"; sp; t <- parseSTy tbl env; sp; kw "∥"; pure (SSquash t))
    <|> (kw "𝟘"   $> SZeroC)
    <|> (kw "𝟙"   $> SOneC)
    <|> (kw "ℕ"   $> SNatC)
    <|> (do (r, x) <- bounds parseDottedName
            case unpack x of
              -- a `_`-leading identifier (or bare `_`) is a SOLVABLE
              -- hole — the elaborator may instantiate it; `_`-leading
              -- names are reserved for this (binder wildcards are a
              -- separate production and unaffected)
              ('_' :: rest) => pure (SHole r True (pack rest))
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
    Nothing => do guard "a ToS-scope name" False
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
  <|> (Left <$> parseSTy tbl ext)

||| An ANONYMOUS domain: like `sqDomain`, but the external case stops
||| below the arrow level (T{2}) — a greedy full type would swallow
||| the rest of the entry (`ℕ → El Q` must be TWO pieces, not one
||| function type). Higher-order external domains stay parenthesized,
||| which re-enters the full type grammar.
sqDomainNoArrow : FixTable -> NameEnv -> NameEnv -> Rule (Either STy SQTm)
sqDomainNoArrow tbl tos ext =
      (do kw "El"; space; q <- sqCode tbl tos ext; pure (Right q))
  <|> (Left <$> parseSTyEl tbl ext)

sqRes : FixTable -> NameEnv -> NameEnv -> Rule SQRes
sqRes tbl tos ext =
      (do kw "U"; pure SQResU)
  <|> (do l <- sqChain tbl tos ext; sp; kw "≡"; sp
          r <- sqChain tbl tos ext; sp; kw "∈"; sp
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
          sp; kw "→"; sp
          (rest, res) <- sqTele tbl tos' ext'
          pure (bs ++ rest, res))
  <|> (do d <- sqDomainNoArrow tbl tos ext
          sp; kw "→"; sp
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

-- COMMITS: after an item's leading keyword the parse can be nothing
-- else, so commit — a failure deep inside the item then propagates
-- with its REAL position instead of backtracking to the item
-- boundary, where the file loop would end and report a useless
-- "Expected end of input" at the next `def`. The commit inside the
-- optional ≔-body keeps `def x : T ≔ <garbage>` a hard error at the
-- garbage rather than mis-reading the item as a declaration.
export
parseSItem : FixTable -> Rule SItem
parseSItem tbl =
      (do kw "def"; space; commit
          (r, x) <- bounds (parseName <|> parseOpName); sp
          kwc ':'; sp
          ty <- parseSTy tbl [<]; sp
          mbody <- optional (do kw "≔"; sp; commit; parseSElem tbl [<])
          pure (case mbody of
                  Just body => SDef x ty body
                  -- a def without a definiens: a DECLARATION
                  Nothing => SDeclDef r x ty))
  <|> (do kw "type"; space; commit
          x <- parseName; sp
          kw "≔"; sp
          ty <- parseSTy tbl [<]
          pure (STypeDef x ty))
  <|> parseSData tbl

export
parseSImport : Rule SImport
parseSImport = do
  kw "import"; space; commit
  m <- parseDottedName
  opens <- optional (do sp; kwc '('; sp
                        n <- parseName <|> parseOpName
                        rest <- many (do sp; kwc ','; sp; (parseName <|> parseOpName))
                        sp; kwc ')'
                        pure (n :: rest))
  pure (MkSImport m (fromMaybe [] opens))

||| infixl 6 +  /  infixr 3 ⊕ — fixity for an operator NAME; takes
||| effect for the rest of the file and is exported with the name.
parseFixity : Rule (String, Assoc, Nat)
parseFixity = do
  assoc <- (kw "infixl" $> AssocL) <|> (kw "infixr" $> AssocR)
  space
  commit
  (r, d) <- bounds (terminal "precedence digit (0-9)" digitTok)
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
parseSFile : FixTable -> Rule (List SImport, FixTable, List (Maybe Range, SItem))
parseSFile tbl0 = do
  sp
  imports <- many (do i <- parseSImport; sp; pure i)
  (decls, items) <- go tbl0
  pure (imports, decls, items)
 where
  go : FixTable -> Rule (FixTable, List (Maybe Range, SItem))
  go tbl =
        (do f <- parseFixity; sp
            (decls, items) <- go (f :: tbl)
            pure (f :: decls, items))
    <|> (do (r, i) <- bounds (parseSItem tbl); sp
            (decls, items) <- go tbl
            pure (decls, (r, i) :: items))
    <|> pure ([], [])

||| Pass 1 of the loader's two-stage parse: just the import header
||| (the dependencies' fixity tables are needed before the body can be
||| parsed).
export
parseSHeader : Rule (List SImport)
parseSHeader = do
  sp
  imports <- many (do i <- parseSImport; sp; pure i)
  ignore (many (terminal "any token" anyTok))
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

export
runSurfaceParser : Rule a -> String -> Either (Maybe Range, String) (SnocList (Range, TokenKind), a)
runSurfaceParser rule input =
  let (commentRanges, toks) = tokenise (unpack input)
      srcLines = lines input in
  case parseWith [<] (rule <* eof) (normaliseTokens toks) of
    Left err  => Left (Just (parseErrRange err), showParseErr err)
    Right (kinds, _, x, _) =>
      Right (kinds <>< map (\r => (clipCommentRange srcLines r, Comment)) (toList commentRanges), x)
