module Text.Parsing.TokenUtil


import Data.Fin
import Data.SnocList
import Data.Location

import Text.Lexing.Token
import Text.Lexing.Tokeniser
import public Text.Parsing.Fork

public export
char : Char -> Grammar st Token Token
char x = is ("Expected symbol: " ++ cast x) (isSymbol (== x))

public export
char_ : Char -> Grammar st Token ()
char_ = ignore . char

namespace List1
  public export
  str : List1 Char -> Grammar st Token (List1 Token)
  str (x ::: []) = map singleton (char x)
  str (x ::: a :: as) = map cons (char x) <*> str (a ::: as)

namespace String
  public export
  str : String -> Grammar st Token (List1 Token)
  str s =
    case unpack s of --FIX: RETHINK THIS
      [] => fail "[Internal error] Attempt to parse an empty string"
      (x :: xs) => List1.str (x ::: xs) <|> fail "Expected string: \{s}"

public export
str_ : String -> Grammar st Token ()
str_ = ignore . str

public export
digit : Grammar st Token (Fin 10)
digit = 0 <$ char_ '0'
    <|> 1 <$ char_ '1'
    <|> 2 <$ char_ '2'
    <|> 3 <$ char_ '3'
    <|> 4 <$ char_ '4'
    <|> 5 <$ char_ '5'
    <|> 6 <$ char_ '6'
    <|> 7 <$ char_ '7'
    <|> 8 <$ char_ '8'
    <|> 9 <$ char_ '9'

public export
digits : Grammar st Token (List1 (Fin 10))
digits = some digit

public export
nat : Grammar st Token Nat
nat = do
  n <- digits
  pure (convert ([<] <>< (forget n)) 1)
 where
  -- decimal = {1, 10, 100, ...}
  convert : SnocList (Fin 10) -> (decimal : Nat) -> Nat
  convert [<] _ = 0
  convert (left :< x) decimal = convert left (decimal * 10) + finToNat x * decimal

public export
space : Grammar st Token ()
space = ignore $ is "whitespace" isSpace

public export
optSpace : Grammar st Token ()
optSpace = optional space $> ()

public export
inParens : Grammar st Token a -> Grammar st Token a
inParens p = do
  str_ "("
  optSpace
  x <- p
  optSpace
  str_ ")"
  pure x
