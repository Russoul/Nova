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
  guard "Reserved keyword" (name /= "def" && name /= "type" && name /= "El")
  pure name

-- ===== Types and elements (mutually recursive) =====

mutual
  -- T{0}: eq-type on top, then the arrow level
  export
  parseSTy : NameEnv -> Rule STy
  parseSTy env =
        (do e0 <- parseSElemPrefix env; sp
            str_ "≡"; sp
            e1 <- parseSElemPrefix env; sp
            str_ "∈"; sp
            a  <- parseSTyArrow env
            pure (STyEq e0 e1 a))
    <|> parseSTyArrow env

  -- T{1}: named binder forms and the sugared right-assoc infixes
  parseSTyArrow : NameEnv -> Rule STy
  parseSTyArrow env =
        (do char_ '('; sp; x <- parseName; sp; char_ ':'; sp
            a <- parseSTy env; sp; char_ ')'; sp
            (do str_ "→"; sp; b <- parseSTyArrow (env :< x); pure (STyPi x a b))
              <|> (do str_ "⨯"; sp; b <- parseSTyArrow (env :< x); pure (STySigma x a b)))
    <|> (do a <- parseSTyEl env
            (do sp; str_ "→"; sp; b <- parseSTyArrow (env :< wildcard); pure (STyPi wildcard a b))
              <|> (do sp; str_ "⨯"; sp; b <- parseSTyArrow (env :< wildcard); pure (STySigma wildcard a b))
              <|> (do sp; str_ "/"; sp; (x, y, r) <- parseQuotRel env; pure (STyQuot a x y r))
              <|> pure a)

  -- (x y. R)  or bare R as sugar for (_ _. R)
  parseQuotRel : NameEnv -> Rule (String, String, STy)
  parseQuotRel env =
        (do char_ '('; sp; x <- parseName; space; y <- parseName
            sp; char_ '.'; sp; r <- parseSTy (env :< x :< y); sp; char_ ')'
            pure (x, y, r))
    <|> (do r <- parseSTyEl (env :< wildcard :< wildcard); pure (wildcard, wildcard, r))

  -- T{2}: El
  parseSTyEl : NameEnv -> Rule STy
  parseSTyEl env =
        (do str_ "El"; space; e <- parseSElemAtom env; pure (STyEl e))
    <|> parseSTyAtom env

  -- T{4}: atoms
  parseSTyAtom : NameEnv -> Rule STy
  parseSTyAtom env =
        (str_ "𝟘" $> STyZero)
    <|> (str_ "𝟙" $> STyOne)
    <|> (str_ "ℕ" $> STyNat)
    <|> (str_ "𝕌" $> STyUniv)
    <|> (do x <- parseSigIdentifier
            sp; char_ '['; sp; es <- parseSSubst env; sp; char_ ']'
            pure (STySig x es))
    <|> (do char_ '('; sp; t <- parseSTy env; sp; char_ ')'; pure t)

  -- t˲: empty, or a bare comma-separated list
  parseSSubst : NameEnv -> Rule (List SElem)
  parseSSubst env = do
    first <- optional (parseSElemNoComma env)
    case first of
      Nothing => pure []
      Just e  => do
        rest <- many (do sp; char_ ','; sp; parseSElemNoComma env)
        pure (e :: rest)

  -- t{0}: top-level comma = pair (right-assoc)
  export
  parseSElem : NameEnv -> Rule SElem
  parseSElem env = do
    e <- parseSElemNoComma env
    (do sp; char_ ','; sp; e' <- parseSElem env; pure (SPair e e'))
      <|> pure e

  -- t{1}: universe-code binder/infix forms and eq-code
  parseSElemNoComma : NameEnv -> Rule SElem
  parseSElemNoComma env =
        (do char_ '('; sp; x <- parseName; sp; char_ ':'; sp
            a <- parseSElem env; sp; char_ ')'; sp
            (do str_ "→"; sp; b <- parseSElemNoComma (env :< x); pure (SPiC x a b))
              <|> (do str_ "⨯"; sp; b <- parseSElemNoComma (env :< x); pure (SSigmaC x a b)))
    <|> (do e <- parseSElemPrefix env
            (do sp; str_ "→"; sp; e' <- parseSElemNoComma (env :< wildcard); pure (SPiC wildcard e e'))
              <|> (do sp; str_ "⨯"; sp; e' <- parseSElemNoComma (env :< wildcard); pure (SSigmaC wildcard e e'))
              <|> (do sp; str_ "/"; sp; (x, y, r) <- parseQuotRelC env; pure (SQuotC e x y r))
              <|> (do sp; str_ "≡"; sp
                      e1 <- parseSElemPrefix env; sp; str_ "∈"; sp
                      e2 <- parseSElemPrefix env
                      pure (SEqC e e1 e2))
              <|> pure e)

  parseQuotRelC : NameEnv -> Rule (String, String, SElem)
  parseQuotRelC env =
        (do char_ '('; sp; x <- parseName; space; y <- parseName
            sp; char_ '.'; sp; r <- parseSElemNoComma (env :< x :< y); sp; char_ ')'
            pure (x, y, r))
    <|> (do r <- parseSElemPrefix (env :< wildcard :< wildcard); pure (wildcard, wildcard, r))

  -- t{2}: prefix forms, motive-first eliminators
  parseSElemPrefix : NameEnv -> Rule SElem
  parseSElemPrefix env =
        (do str_ "λ"; sp; x <- parseName; sp; char_ '.'; sp
            e <- parseSElemPrefix (env :< x); pure (SLam x e))
    <|> (do str_ "𝟘-elim"; space; e <- parseSElemAtom env; pure (SZeroElim e))
    <|> (do str_ "ℕ-elim"; space
            char_ '('; sp; n <- parseName; sp; char_ '.'; sp
            mot <- parseSTy (env :< n); sp; char_ ')'; sp
            z <- parseSElemAtom env; sp
            char_ '('; sp; n2 <- parseName; space; ih <- parseName
            sp; char_ '.'; sp; s <- parseSElem (env :< n2 :< ih); sp; char_ ')'; sp
            t <- parseSElemAtom env
            pure (SNatElim n mot z n2 ih s t))
    <|> (do str_ "S"; space; e <- parseSElemAtom env; pure (SSuc e))
    <|> (do str_ "class"; space; e <- parseSElemAtom env; pure (SClass e))
    <|> (do str_ "quot-elim"; space
            char_ '('; sp; z <- parseName; sp; char_ '.'; sp
            mot <- parseSTy (env :< z); sp; char_ ')'; sp
            char_ '('; sp; a <- parseName; sp; char_ '.'; sp
            f <- parseSElem (env :< a); sp; char_ ')'; sp
            q <- parseSElemAtom env
            pure (SQuotElim z mot a f q))
    <|> parseSElemApp env

  -- t{3}: application / projection chains
  parseSElemApp : NameEnv -> Rule SElem
  parseSElemApp env = do
    e <- parseSElemAtom env
    cont e
   where
    cont : SElem -> Rule SElem
    cont e =
          (do sp; str_ ".π₁"; cont (SProj1 e))
      <|> (do sp; str_ ".π₂"; cont (SProj2 e))
      <|> (do sp; e' <- parseSElemAtom env; cont (SApp e e'))
      <|> pure e

  -- t{5}: atoms, including ascription
  parseSElemAtom : NameEnv -> Rule SElem
  parseSElemAtom env =
        (do char_ '('
            sp
            unit <- optional (char_ ')')
            case unit of
              Just _  => pure SUnitI
              Nothing => do
                e <- parseSElem env
                sp
                (do char_ ':'; sp; ty <- parseSTy env; sp; char_ ')'
                    pure (SAnn e ty))
                  <|> (do char_ ')'; pure e))
    <|> (str_ "Refl" $> SRefl)
    <|> (str_ "Z"    $> SZeroN)
    <|> (str_ "𝟘"   $> SZeroC)
    <|> (str_ "𝟙"   $> SOneC)
    <|> (str_ "ℕ"   $> SNatC)
    <|> (do x <- parseSigIdentifier
            sp; char_ '['; sp; es <- parseSSubst env; sp; char_ ']'
            pure (SSig x es))
    <|> (do x <- parseName
            case resolveVar env x of
              Just i  => pure (SVar x i)
              Nothing => fail "unbound variable '\{x}'")

-- ===== Items =====

parseTelescope : NameEnv -> Rule (NameEnv, List (String, STy))
parseTelescope env = go env []
 where
  go : NameEnv -> List (String, STy) -> Rule (NameEnv, List (String, STy))
  go env acc =
        (do char_ '('; sp; x <- parseName; sp; char_ ':'; sp
            ty <- parseSTy env; sp; char_ ')'; sp
            go (env :< x) (acc ++ [(x, ty)]))
    <|> pure (env, acc)

export
parseSItem : Rule SItem
parseSItem =
      (do str_ "def"; space
          x <- parseName; sp
          (env, tel) <- parseTelescope [<]
          char_ ':'; sp
          ty <- parseSTy env; sp
          str_ "≔"; sp
          body <- parseSElem env
          pure (SDef x tel ty body))
  <|> (do str_ "type"; space
          x <- parseName; sp
          (env, tel) <- parseTelescope [<]
          str_ "≔"; sp
          ty <- parseSTy env
          pure (STypeDef x tel ty))

export
parseSFile : Rule (List SItem)
parseSFile = do
  sp
  items <- many (do i <- parseSItem; sp; pure i)
  pure items

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
