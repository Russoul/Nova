module ETT.Surface.Parser

import Data.Fin

import public Text.Parser.Fork

import Text.Lexer

import Text.Parser.CharUtil

import Data.Util

import Data.Location

import ETT.Core.VarName

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
elHead : Rule Head
elHead = do
  r <- spName "El"
  pure (El r)

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
  pure (Hole (l + fst x) (snd x))

public export
head : Rule Head
head = zeroHead <|> oneHead <|> natElimHead <|> natTyHead <|> universeTyHead <|> eqValHead <|> elHead <|> varHead <|> holeHead

mutual
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
  piTy : Rule Term
  piTy = do
    (l, x, a) <- section
    spaceDelim
    delim_ "→"
    commit
    spaceDelim
    b <- located (term 0)
    pure (PiTy (l + fst b) x a (snd b))

  public export
  funTy : Rule Term
  funTy = do
    (l, a) <- located (term 3)
    spaceDelim
    delim_ "→"
    commit
    spaceDelim
    b <- located (term 2)
    pure (FunTy (l + fst b) a (snd b))

  public export
  piVal : Rule Term
  piVal = do
    x <- located varName
    spaceDelim
    delim_ "↦"
    spaceDelim
    f <- located (term 0)
    pure (PiVal (fst x + fst f) (snd x) (snd f))

  ||| Parse a Term exactly at level 0
  public export
  term0 : Rule Term
  term0 = piTy <|> piVal

  public export
  eqTy : Rule Term
  eqTy = do
    a <- located (term 3)
    spaceDelim
    delim_ "≡"
    spaceDelim
    b <- term 3
    spaceDelim
    delim_ "∈"
    spaceDelim
    ty <- located (term 0)
    pure (EqTy (fst a + fst ty) (snd a) b (snd ty))

  ||| Parse a Term exactly at level 1
  public export
  term1 : Rule Term
  term1 = eqTy

  public export
  app : Rule Term
  app = do
    (p0, h) <- located head
    (p1, es) <- located elim
    guard "elimination spine must be non-empty" (length es > 0)
    pure (App (p0 + p1) h es)

  ||| Parse a Term exactly at level 2
  public export
  term2 : Rule Term
  term2 = funTy

  ||| Parse a Term exactly at level 3
  public export
  term3 : Rule Term
  term3 = app

  ||| Parse a Term exactly at level 3
  public export
  term4 : Rule Term
  term4 = (located head <&> (\(p, x) => App p x [])) <|> inParentheses (term 0)

  ||| Parse a TypE at level ≥ n
  public export
  term : Level -> Rule Term
  term 0 = term0 <|> term1 <|> term2 <|> term3 <|> term4
  term 1 =           term1 <|> term2 <|> term3 <|> term4
  term 2 =                     term2 <|> term3 <|> term4
  term 3 =                               term3 <|> term4
  term 4 =                                         term4


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
    termArg1

  public export
  typingSignature : Rule TopLevel
  typingSignature = do
    x <- located varName
    spaceDelim
    delim_ ":"
    spaceDelim
    ty <- located (term 0)
    pure (TypingSignature (fst x + fst ty) (snd x) (snd ty))

  public export
  letSignature : Rule TopLevel
  letSignature = do
    x <- located varName
    spaceDelim
    delim_ "≔"
    spaceDelim
    rhs <- term 0
    spaceDelim
    delim_ ":"
    spaceDelim
    ty <- located (term 0)
    pure (LetSignature (fst x + fst ty) (snd x) rhs (snd ty))

  public export
  topLevel : Rule TopLevel
  topLevel = typingSignature <|> letSignature

  public export
  surfaceFile : Rule (List1 TopLevel)
  surfaceFile = do
    sepBy1 spaceDelimDef topLevel
