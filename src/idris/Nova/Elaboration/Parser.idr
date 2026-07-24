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
                            name /= "S" && name /= "Z" && name /= "Refl" && name /= "class" &&
                            name /= "data")
  pure name

||| A possibly-qualified name: x or M.x or A.B.x. The dot only counts
||| when an identifier follows (so `p.π₁` backtracks to a projection).
parseDottedName : Rule String
parseDottedName = do
  n <- parseName
  rest <- many (do char_ '.'; parseName)
  pure (joinBy "." (n :: rest))

||| An operator token: a maximal run of operator-alphabet characters
||| (operators ARE names — see Nova.Elaboration.Surface).
export
parseOpName : Rule String
parseOpName = do
  c <- terminal "operator char" opTok
  cs <- many (terminal "operator char" opTok)
  pure (pack (c :: cs))
 where
  opTok : Token -> Maybe Char
  opTok (Symbol ch) = if opChar ch then Just ch else Nothing
  opTok _ = Nothing

||| A possibly-qualified operator (+ or M.+): the mention form's and
||| the definition header's name grammar.
parseOpRef : Rule String
parseOpRef = do
  pre <- many (do n <- parseName; char_ '.'; pure n)
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
            str_ "≡"; sp
            e1 <- parseSElemOp tbl env; sp
            str_ "∈"; sp
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
            (do str_ "→"; sp; b <- parseSTy tbl env'; pure (foldGroups STyPi groups b))
              <|> (do str_ "⨯"; sp; b <- parseSTy tbl env'; pure (foldGroups STySigma groups b)))
    <|> (do a <- parseSTyEl tbl env
            (do sp; str_ "→"; sp; b <- parseSTy tbl (env :< wildcard); pure (STyPi wildcard a b))
              <|> (do sp; str_ "⨯"; sp; b <- parseSTy tbl (env :< wildcard); pure (STySigma wildcard a b))
              <|> (do sp; str_ "/"; sp; (x, y, r) <- parseQuotRel tbl env; pure (STyQuot a x y r))
              <|> pure a)

  -- one or more (x:T) groups, each scoping over the ones after it
  parseBinderGroups : FixTable -> NameEnv -> Rule (NameEnv, List (String, STy))
  parseBinderGroups tbl env = do
    char_ '('; sp; x <- parseName; sp; char_ ':'; sp
    a <- parseSTy tbl env; sp; char_ ')'
    rest <- optional (do sp; parseBinderGroups tbl (env :< x))
    case rest of
      Nothing => pure (env :< x, [(x, a)])
      Just (env', groups) => pure (env', (x, a) :: groups)

  -- (x y. r)  or bare r as sugar for (_ _. r) — r is an Ω-valued ELEMENT
  parseQuotRel : FixTable -> NameEnv -> Rule (String, String, SElem)
  parseQuotRel tbl env =
        (do char_ '('; sp; x <- parseName; space; y <- parseName
            sp; char_ '.'; sp; r <- parseSElemNoComma tbl (env :< x :< y); sp; char_ ')'
            pure (x, y, r))
    <|> (do r <- parseSElemPrefix tbl (env :< wildcard :< wildcard); pure (wildcard, wildcard, r))

  -- T{2}: El / Prf
  parseSTyEl : FixTable -> NameEnv -> Rule STy
  parseSTyEl tbl env =
        (do str_ "El"; space; e <- parseSElemAtom tbl env; pure (STyEl e))
    <|> (do str_ "Prf"; space; e <- parseSElemAtom tbl env; pure (STyPrf e))
    <|> parseSTyAtom tbl env

  -- T{4}: atoms
  parseSTyAtom : FixTable -> NameEnv -> Rule STy
  parseSTyAtom tbl env =
        (str_ "𝟘" $> STyZero)
    <|> (str_ "𝟙" $> STyOne)
    <|> (str_ "ℕ" $> STyNat)
    <|> (str_ "𝕌" $> STyUniv)
    <|> (str_ "Ω" $> STyProp)
    <|> (do x <- parseDottedName; pure (STySig x))
    <|> (do char_ '('; sp; t <- parseSTy tbl env; sp; char_ ')'; pure t)

  -- t{0}: top-level comma = pair (right-assoc)
  export
  parseSElem : FixTable -> NameEnv -> Rule SElem
  parseSElem tbl env = do
    e <- parseSElemNoComma tbl env
    (do sp; char_ ','; sp; e' <- parseSElem tbl env; pure (SPair e e'))
      <|> pure e

  -- t{1}: universe-code binder/infix forms and eq-code; binder groups
  -- iterate exactly as at the type level
  parseSElemNoComma : FixTable -> NameEnv -> Rule SElem
  parseSElemNoComma tbl env =
        (do (env', groups) <- parseBinderGroupsC tbl env
            sp
            (do str_ "→"; sp; b <- parseSElemNoComma tbl env'; pure (foldGroups SPiC groups b))
              <|> (do str_ "⨯"; sp; b <- parseSElemNoComma tbl env'; pure (foldGroups SSigmaC groups b)))
    <|> (do e <- parseSElemOp tbl env
            (do sp; str_ "→"; sp; e' <- parseSElemNoComma tbl (env :< wildcard); pure (SPiC wildcard e e'))
              <|> (do sp; str_ "⨯"; sp; e' <- parseSElemNoComma tbl (env :< wildcard); pure (SSigmaC wildcard e e'))
              <|> (do sp; str_ "/"; sp; (x, y, r) <- parseQuotRelC tbl env; pure (SQuotC e x y r))
              <|> (do sp; str_ "≡"; sp
                      e1 <- parseSElemOp tbl env; sp; str_ "∈"; sp
                      e2 <- parseSElemOp tbl env
                      pure (SEqC e e1 e2))
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
                op <- parseOpName
                case lookup op tbl of
                  Nothing => fail "operator '\{op}' has no fixity in scope"
                  Just (assoc, p) => do
                    guard "operator precedence" (p >= minP)
                    sp
                    r <- climb (case assoc of AssocL => S p; AssocR => p)
                    cont (SApp (SApp (SSig op) l) r) minP)
        <|> pure l

  parseBinderGroupsC : FixTable -> NameEnv -> Rule (NameEnv, List (String, SElem))
  parseBinderGroupsC tbl env = do
    char_ '('; sp; x <- parseName; sp; char_ ':'; sp
    a <- parseSElem tbl env; sp; char_ ')'
    rest <- optional (do sp; parseBinderGroupsC tbl (env :< x))
    case rest of
      Nothing => pure (env :< x, [(x, a)])
      Just (env', groups) => pure (env', (x, a) :: groups)

  parseQuotRelC : FixTable -> NameEnv -> Rule (String, String, SElem)
  parseQuotRelC tbl env =
        (do char_ '('; sp; x <- parseName; space; y <- parseName
            sp; char_ '.'; sp; r <- parseSElemNoComma tbl (env :< x :< y); sp; char_ ')'
            pure (x, y, r))
    <|> (do r <- parseSElemPrefix tbl (env :< wildcard :< wildcard); pure (wildcard, wildcard, r))

  -- t{2}: prefix forms, motive-first eliminators
  parseSElemPrefix : FixTable -> NameEnv -> Rule SElem
  parseSElemPrefix tbl env =
        -- λ's body extends over operators: λx. x + y ≡ λx. (x + y)
        (do str_ "λ"; sp; x <- parseName; sp; char_ '.'; sp
            e <- parseSElemOp tbl (env :< x); pure (SLam x e))
    <|> (do str_ "𝟘-elim"; space; e <- parseSElemAtom tbl env; pure (SZeroElim e))
    <|> (do str_ "ℕ-elim"; space
            char_ '('; sp; n <- parseName; sp; char_ '.'; sp
            mot <- parseSTy tbl (env :< n); sp; char_ ')'; sp
            z <- parseSElemAtom tbl env; sp
            char_ '('; sp; n2 <- parseName; space; ih <- parseName
            sp; char_ '.'; sp; s <- parseSElem tbl (env :< n2 :< ih); sp; char_ ')'; sp
            t <- parseSElemAtom tbl env
            pure (SNatElim n mot z n2 ih s t))
    <|> (do str_ "S"; space; e <- parseSElemAtom tbl env; pure (SSuc e))
    <|> (do str_ "class"; space; e <- parseSElemAtom tbl env; pure (SClass e))
    <|> (do str_ "quot-elim"; space
            char_ '('; sp; z <- parseName; sp; char_ '.'; sp
            mot <- parseSTy tbl (env :< z); sp; char_ ')'; sp
            char_ '('; sp; a <- parseName; sp; char_ '.'; sp
            f <- parseSElem tbl (env :< a); sp; char_ ')'; sp
            q <- parseSElemAtom tbl env
            pure (SQuotElim z mot a f q))
    <|> (do str_ "squash-elim"; space
            e <- parseSElemAtom tbl env; sp
            char_ '('; sp; x <- parseName; sp; char_ '.'; sp
            body <- parseSElem tbl (env :< x); sp; char_ ')'
            pure (SSquashElim e x body))
    <|> (do str_ "⋆"
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
          (do sp; str_ ".π₁"; cont (SProj1 e))
      <|> (do sp; str_ ".π₂"; cont (SProj2 e))
      <|> (do sp; e' <- parseSElemAtom tbl env; cont (SApp e e'))
      <|> pure e

  -- t{5}: atoms, including ascription
  parseSElemAtom : FixTable -> NameEnv -> Rule SElem
  parseSElemAtom tbl env =
        -- mention form: (+) — the operator as an ordinary reference
        (do char_ '('; sp; op <- parseOpRef; sp; char_ ')'; pure (SSig op))
    <|> (do char_ '('
            sp
            unit <- optional (char_ ')')
            case unit of
              Just _  => pure SUnitI
              Nothing => do
                e <- parseSElem tbl env
                sp
                (do char_ ':'; sp; ty <- parseSTy tbl env; sp; char_ ')'
                    pure (SAnn e ty))
                  <|> (do char_ ')'; pure e))
    <|> (str_ "Refl" $> SRefl)
    <|> (str_ "Z"    $> SZeroN)
    <|> (str_ "⋆"    $> SStar)
    <|> (do str_ "∥"; sp; t <- parseSTy tbl env; sp; str_ "∥"; pure (SSquash t))
    <|> (str_ "𝟘"   $> SZeroC)
    <|> (str_ "𝟙"   $> SOneC)
    <|> (str_ "ℕ"   $> SNatC)
    <|> (do x <- parseDottedName
            case resolveVar env x of
              Just i  => pure (SVar x i)
              -- locals shadow the signature; whether the name exists
              -- in Σ is the elaborator's question, not the parser's
              -- (a dotted name never resolves locally)
              Nothing => pure (SSig x))

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
    <|> (do char_ '('; sp; t <- sqChain tbl tos ext; sp; char_ ')'; pure (Right t))
    <|> (Left <$> parseSElemAtom tbl ext)

  sqCode : FixTable -> NameEnv -> NameEnv -> Rule SQTm
  sqCode tbl tos ext =
        (do char_ '('; sp; t <- sqChain tbl tos ext; sp; char_ ')'; pure t)
    <|> sqChain tbl tos ext

sqDomain : FixTable -> NameEnv -> NameEnv -> Rule (Either STy SQTm)
sqDomain tbl tos ext =
      (do str_ "El"; space; q <- sqCode tbl tos ext; pure (Right q))
  <|> (Left <$> parseSTy tbl ext)

sqRes : FixTable -> NameEnv -> NameEnv -> Rule SQRes
sqRes tbl tos ext =
      (do str_ "U"; pure SQResU)
  <|> (do l <- sqChain tbl tos ext; sp; str_ "≡"; sp
          r <- sqChain tbl tos ext; sp; str_ "∈"; sp
          str_ "El"; space; u <- sqCode tbl tos ext
          pure (SQResEq l r u))
  <|> (do str_ "El"; space; q <- sqCode tbl tos ext; pure (SQResEl q))

sqBinders : FixTable -> NameEnv -> NameEnv -> Rule (NameEnv, NameEnv, List (String, Either STy SQTm))
sqBinders tbl tos ext = do
  char_ '('; sp; x <- parseName; sp; char_ ':'; sp
  d <- sqDomain tbl tos ext; sp; char_ ')'
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

sqDecl : FixTable -> NameEnv -> NameEnv -> Rule SQDecl
sqDecl tbl penv entries = do
  n <- parseName; sp; char_ ':'; sp
  withBinders n <|> bare n
 where
  withBinders : String -> Rule SQDecl
  withBinders n = do
    (tos, ext, bs) <- sqBinders tbl entries penv
    sp; str_ "→"; sp
    res <- sqRes tbl tos ext
    pure (MkSQDecl n bs res)
  bare : String -> Rule SQDecl
  bare n = do
    res <- sqRes tbl entries penv
    pure (MkSQDecl n [] res)

parseSData : FixTable -> Rule SItem
parseSData tbl = do
  str_ "data"; sp
  (penv, params) <- parseParams [<]
  char_ '('; sp
  ds <- go penv [<]
  sp; char_ ')'
  pure (SData params ds)
 where
  ||| Zero or more [x : T] PARAMETER groups — the literal's ambient
  ||| telescope, each scoping over the ones after it.
  parseParams : NameEnv -> Rule (NameEnv, List (String, STy))
  parseParams env =
        (do char_ '['; sp; x <- parseName; sp; char_ ':'; sp
            t <- parseSTy tbl env; sp; char_ ']'; sp
            (env', rest) <- parseParams (env :< x)
            pure (env', (x, t) :: rest))
    <|> pure (env, [])
  go : NameEnv -> NameEnv -> Rule (List SQDecl)
  go penv entries = do
    d <- sqDecl tbl penv entries
    rest <- optional (do sp; char_ ';'; sp; go penv (entries :< d.dqname))
    pure (d :: fromMaybe [] rest)

export
parseSItem : FixTable -> Rule SItem
parseSItem tbl =
      (do str_ "def"; space
          x <- parseName <|> parseOpName; sp
          char_ ':'; sp
          ty <- parseSTy tbl [<]; sp
          str_ "≔"; sp
          body <- parseSElem tbl [<]
          pure (SDef x ty body))
  <|> (do str_ "type"; space
          x <- parseName; sp
          str_ "≔"; sp
          ty <- parseSTy tbl [<]
          pure (STypeDef x ty))
  <|> parseSData tbl

export
parseSImport : Rule SImport
parseSImport = do
  str_ "import"; space
  m <- parseDottedName
  opens <- optional (do sp; char_ '('; sp
                        n <- parseName <|> parseOpName
                        rest <- many (do sp; char_ ','; sp; (parseName <|> parseOpName))
                        sp; char_ ')'
                        pure (n :: rest))
  pure (MkSImport m (fromMaybe [] opens))

||| infixl 6 +  /  infixr 3 ⊕ — fixity for an operator NAME; takes
||| effect for the rest of the file and is exported with the name.
parseFixity : Rule (String, Assoc, Nat)
parseFixity = do
  assoc <- (str_ "infixl" $> AssocL) <|> (str_ "infixr" $> AssocR)
  space
  d <- terminal "precedence digit (0-9)" digitTok
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
export
parseSFile : FixTable -> Rule (List SImport, FixTable, List SItem)
parseSFile tbl0 = do
  sp
  imports <- many (do i <- parseSImport; sp; pure i)
  (decls, items) <- go tbl0
  pure (imports, decls, items)
 where
  go : FixTable -> Rule (FixTable, List SItem)
  go tbl =
        (do f <- parseFixity; sp
            (decls, items) <- go (f :: tbl)
            pure (f :: decls, items))
    <|> (do i <- parseSItem tbl; sp
            (decls, items) <- go tbl
            pure (decls, i :: items))
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

export
runSurfaceParser : Rule a -> String -> Either String a
runSurfaceParser rule input =
  let (_, toks) = tokenise (unpack input) in
  case parseWith () (rule <* eof) (normaliseTokens toks) of
    Left err  => Left (show err)
    Right (_, _, x, _) => Right x
