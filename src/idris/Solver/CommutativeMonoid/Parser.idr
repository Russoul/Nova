module Solver.CommutativeMonoid.Parser

import Data.Fin
import Data.List
import Data.SnocList

import Text.Lexing.Token
import Text.Parsing.Fork
import Text.Parsing.TokenUtil

import Solver.CommutativeMonoid.Language


public export
Rule : Type -> Type
Rule a = Grammar () Token a

public export
var : Rule String
var = (pack . forget . map toChar <$> some (is "char" (isSymbol isAlpha)))

public export
parseContext : Rule (SnocList String)
parseContext = do
  result <- (cast . forget <$> sepBy1 space var) <|> (str_ "ε" $> [<])
  guard "Variables must be pairwise unique" (length (nub (cast {to = List String} result)) == length result)
  pure result

mutual
  public export
  parseVarTerm : (vars : SnocList String) -> Rule (Term (Fin (length vars)))
  parseVarTerm [<] = fail "Trying to parse a variable term in empty context"
  parseVarTerm (xs :< x) =
    (str_ x $> Var FZ) <|> (parseVarTerm xs <&> map FS)

  public export
  parsePlusTermArg : (vars : SnocList String) -> Rule (Term (Fin (length vars)))
  parsePlusTermArg vars =
    parseVarTerm vars <|> parseZeroTerm vars <|> inParens (parseTerm vars)

  public export
  parsePlusTerm : (vars : SnocList String) -> Rule (Term (Fin (length vars)))
  parsePlusTerm vars = do
    sepBy1 (optSpace *> str_ "+" <* optSpace) (parsePlusTermArg vars) <&> sum

  public export
  parseZeroTerm : (vars : SnocList String) -> Rule (Term (Fin (length vars)))
  parseZeroTerm vars = do
    str_ "0" $> Zero

  public export
  parseTerm : (vars : SnocList String) -> Rule (Term (Fin (length vars)))
  parseTerm vars =
    parsePlusTerm vars
      <|>
    inParens (parseTerm vars)

||| x̄ ⊦ t
public export
parseContextualTerm : Rule (vars : SnocList String ** Term (Fin (length vars)))
parseContextualTerm = do
  ctx <- parseContext
  optSpace
  str_ "⊦"
  optSpace
  tm <- parseTerm ctx
  pure (ctx ** tm)
