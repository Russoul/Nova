module ETT.Surface.Parser

import Data.Fin
import Data.Maybe

import public Text.Parser.Fork

import Text.Lexer

import Text.Parser.CharUtil

import Data.Util

import Data.Location

import ETT.Core.Name

import ETT.Surface.SemanticToken
import ETT.Surface.Language
import ETT.Surface.ParserUtil

import Data.List.Elem

public export
Level : Type
Level = Fin 5

public export
zeroHead : Rule Head
zeroHead = do
  r <- spName "Z"
  pure (NatVal0 r)

public export
oneHead : Rule Head
oneHead = do
  r <- spName "S"
  pure (NatVal1 r)

public export
natElimHead : Rule Head
natElimHead = do
  r <- spName "ℕ-elim"
  pure (NatElim r)

public export
natTyHead : Rule Head
natTyHead = do
  r <- spName "ℕ"
  pure (NatTy r)

public export
jHead : Rule Head
jHead = do
  r <- spName "J"
  pure (EqElim r)

public export
universeTyHead : Rule Head
universeTyHead = do
  r <- spName "𝕌"
  pure (UniverseTy r)

public export
eqValHead : Rule Head
eqValHead = do
  r <- spName "Refl"
  pure (EqVal r)

public export
varHead : Rule Head
varHead = do
  x <- located varName
  pure (Var (fst x) (snd x))

public export
holeHead : Rule Head
holeHead = do
  l <- delim "?"
  x <- located varName
  pure (Hole (l + fst x) (snd x) Nothing)

public export
holeVarsHead : Rule Head
holeVarsHead = do
  l0 <- delim "?"
  x <- varName
  l1 <- delim "("
  ls <- sepBy (optSpaceDelim *> delim "," <* optSpaceDelim) varName
  l1 <- delim ")"
  pure (Hole (l0 + l1) x (Just ls))

public export
unnamedHoleVarsHead : Rule Head
unnamedHoleVarsHead = do
  l0 <- delim "?("
  ls <- sepBy (optSpaceDelim *> delim "," <* optSpaceDelim) varName
  l1 <- delim ")"
  pure (UnnamedHole (l0 + l1) (Just ls))

public export
unnamedHoleHead : Rule Head
unnamedHoleHead = do
  l <- delim "?"
  pure (UnnamedHole l Nothing)

public export
unfoldHead : Rule Head
unfoldHead = do
  l <- delim "!"
  x <- located varName
  pure (Unfold (l + fst x) (snd x))

public export
piBetaHead : Rule Head
piBetaHead = do
  r <- spName "Π-β"
  pure (PiBeta r)

public export
piEtaHead : Rule Head
piEtaHead = do
  r <- spName "Π-η"
  pure (PiEta r)

public export
natBetaZHead : Rule Head
natBetaZHead = do
  r <- spName "ℕ-β-Z"
  pure (NatBetaZ r)

public export
natBetaSHead : Rule Head
natBetaSHead = do
  r <- spName "ℕ-β-S"
  pure (NatBetaS r)

public export
piEqHead : Rule Head
piEqHead = do
  r <- spName "Π⁼"
  pure (PiEq r)

mutual
  public export
  head : Rule Head
  head = zeroHead
     <|> oneHead
     <|> natElimHead
     <|> natTyHead
     <|> universeTyHead
     <|> eqValHead
     <|> varHead
     <|> holeVarsHead
     <|> holeHead
     <|> unnamedHoleVarsHead
     <|> unnamedHoleHead
     <|> unfoldHead
     <|> piBetaHead
     <|> piEtaHead
     <|> piEqHead
     <|> natBetaZHead
     <|> natBetaSHead
     <|> jHead

  public export
  head2 : Rule Head
  head2 = head <|> (inParentheses (located $ term 0) <&> uncurry Tm)

  public export
  section : Rule (Range, VarName, Term)
  section = do
    l <- delim "("
    optSpaceDelim
    x <- located varName
    spaceDelim
    delim_ ":"
    mustWork $ do
      spaceDelim
      ty <- term 0
      optSpaceDelim
      r <- delim ")"
      pure (l + r, snd x, ty)

  public export
  continuePi : (Range, Range, VarName, Term) -> Rule Term
  continuePi (l, lx, x, a) = do
    spaceDelim
    delim_ "→"
    commit
    spaceDelim
    b <- located (term 0)
    pure (PiTy (l + fst b) x a (snd b))

  public export
  continueSigma : (Range, Range, VarName, Term) -> Rule Term
  continueSigma (l, lx, x, a) = do
    spaceDelim
    delim_ "⨯"
    commit
    spaceDelim
    b <- located (term 0)
    pure (SigmaTy (l + fst b) x a (snd b))

  public export
  piVal : Rule Term
  piVal = do
    x <- located varName
    spaceDelim
    delim_ "↦"
    commit
    spaceDelim
    f <- located (term 0)
    pure (PiVal (fst x + fst f) (snd x) (snd f))

  public export
  continueAnnPiVal : (Range, Range, VarName, Term) -> Rule Term
  continueAnnPiVal (r, r0, x, ty) = do
    spaceDelim
    delim_ "↦"
    commit
    spaceDelim
    f <- located (term 0)
    pure (AnnotatedPiVal (r + fst f) x ty (snd f))

  public export
  sectionBinder : Rule Term
  sectionBinder = do
    s <- located section
    continuePi s <|> continueSigma s <|> continueAnnPiVal s

  public export
  app : Rule Term
  app = do
    (p0, h) <- located head2
    (p1, es) <- located elim
    guard "elimination spine must be non-empty" (length es > 0)
    pure (App (p0 + p1) h es)

  ||| Parse a Term exactly at level 3
  public export
  term3 : Rule Term
  term3 = app

  pair : Rule Term
  pair = do
    l0 <- delim "("
    a <- term 0
    optSpaceDelim
    delim_ ","
    optSpaceDelim
    b <- term 0
    l1 <- delim ")"
    pure (SigmaVal (l0 + l1) a b)

  ||| Parse a Term exactly at level 3
  public export
  term4 : Rule Term
  term4 = (located head <&> (\(p, x) => App p x []))
      <|> inParentheses (term 0)
      <|> pair

  public export
  continueEq : (Range, Term) -> Rule Term
  continueEq a = do
    spaceDelim
    delim_ "≡"
    commit
    spaceDelim
    b <- term 3
    spaceDelim
    delim_ "∈"
    spaceDelim
    ty <- located (term 0)
    pure (EqTy (fst a + fst ty) (snd a) b (snd ty))

  public export
  continueExp : (Range, Term) -> Rule Term
  continueExp (l, a) = do
    spaceDelim
    delim_ "→"
    commit
    spaceDelim
    b <- located (term 2)
    pure (FunTy (l + fst b) a (snd b))

  public export
  continueProd : (Range, Term) -> Rule Term
  continueProd (l, a) = do
    spaceDelim
    delim_ "⨯"
    commit
    spaceDelim
    b <- located (term 3)
    pure (ProdTy (l + fst b) a (snd b))

  ||| Continue an e{≥3}
  public export
  continue : (Range, Term) -> Bool -> Rule Term
  continue lhs True = continueEq lhs <|> continueProd lhs <|> continueExp lhs
  continue lhs False = continueExp lhs

  public export
  op : Bool -> Rule Term
  op both = do
    a <- located (term3 <|> term4)
    t <- optional (continue a both)
    pure (fromMaybe (snd a) t)

  ||| Parse a TypE at level ≥ n
  public export
  term : Level -> Rule Term
  term 0 =           sectionBinder <|> piVal <|> op True
  term 1 =                                       op True
  term 2 =                                       op False
  term 3 =                                       term3 <|> term4
  term 4 =                                       term4


  public export
  termArg0 : Rule (List VarName, Term)
  termArg0 = do
    xs <- many (varName <* delim "." <* optSpaceDelim)
    e <- term 0
    pure (xs, e)

  public export
  termArg1 : Rule (List VarName, Term)
  termArg1 = (term 4 <&> ([], )) <|> inParentheses termArg0

  public export
  elim : Rule Elim
  elim = many $ do
    spaceDelim
    (Arg <$> termArg1) <|> (Pi1 <$ delim_ ".π₁") <|> (Pi2 <$ delim_ ".π₂")

  public export
  typingSignature : Rule TopLevel
  typingSignature = do
    l <- delim "assume"
    spaceDelim
    x <- varName
    spaceDelim
    delim_ ":"
    spaceDelim
    ty <- located (term 0)
    pure (TypingSignature (l + fst ty) x (snd ty))

  public export
  letSignature : Rule TopLevel
  letSignature = do
    l <- delim "let"
    spaceDelim
    x <- varName
    spaceDelim
    delim_ ":"
    spaceDelim
    ty <- term 0
    spaceDelim
    delim_ "≔"
    spaceDelim
    rhs <- located (term 0)
    pure (LetSignature (l + fst rhs) x ty (snd rhs))

  public export
  topLevel : Rule TopLevel
  topLevel = typingSignature <|> letSignature

  public export
  surfaceFile : Rule (List1 TopLevel)
  surfaceFile = do
    sepBy1 spaceDelimDef topLevel
