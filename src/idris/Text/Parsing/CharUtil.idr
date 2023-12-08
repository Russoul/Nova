module Text.Parsing.CharUtil

import Data.List
import Data.List1
import Data.Maybe
import Data.Either
import Data.String
import Data.Fin

import Text.Parsing.Fork

------------- Utilities for grammars over Char ----------------

public export
Digit : Type
Digit = Fin 10

||| Define parsers as consuming grammars over characters.
public export
Parser : (s : Type) -> (ty : Type) -> Type
Parser s ty = Grammar s Char ty

export
toString : Foldable t
        => Parser s (t Char)
        -> Parser s String
toString p = map (foldr (\char, str => cast char ++ str) "") p

export
lower : Parser s Char
lower = terminal "lower" (\x => toMaybe (isLower x) x)

export
upper : Parser s Char
upper = terminal "upper" (\x => toMaybe (isUpper x) x)

export
alpha : Parser s Char
alpha = terminal "alpha" (\x => toMaybe (isAlpha x) x)

public export
mbDigit : Char -> Maybe Digit
mbDigit '0' = Just 0
mbDigit '1' = Just 1
mbDigit '2' = Just 2
mbDigit '3' = Just 3
mbDigit '4' = Just 4
mbDigit '5' = Just 5
mbDigit '6' = Just 6
mbDigit '7' = Just 7
mbDigit '8' = Just 8
mbDigit '9' = Just 9
mbDigit _   = Nothing

public export
mbSubscriptDigit : Char -> Maybe Digit
mbSubscriptDigit '₀' = Just 0
mbSubscriptDigit '₁' = Just 1
mbSubscriptDigit '₂' = Just 2
mbSubscriptDigit '₃' = Just 3
mbSubscriptDigit '₄' = Just 4
mbSubscriptDigit '₅' = Just 5
mbSubscriptDigit '₆' = Just 6
mbSubscriptDigit '₇' = Just 7
mbSubscriptDigit '₈' = Just 8
mbSubscriptDigit '₉' = Just 9
mbSubscriptDigit _   = Nothing

export
digit : Parser s Digit
digit = terminal "digit" mbDigit

export
subscriptDigit : Parser s Digit
subscriptDigit = terminal "subscript digit" mbSubscriptDigit

export
digits : Parser s (List1 Digit)
digits = some digit

littleEndianBase10ToNat : List Digit -> Nat
littleEndianBase10ToNat [] = 0
littleEndianBase10ToNat (x :: xs) = finToNat x + 10 * littleEndianBase10ToNat xs

||| Big-endian string of base10 digits to Nat
public export
[BigEndianBase10] Cast (List1 Digit) Nat where
  cast = littleEndianBase10ToNat . forget . reverse

public export
nat : Parser s Nat
nat = map (cast @{BigEndianBase10}) digits

export
alphaNum : Parser s Char
alphaNum = terminal "alphanumeric" (\x => toMaybe (isAlphaNum x) x)

export
space : Parser s Char
space = terminal "space" (\x => toMaybe (x == ' ') x)

export
spaceLike : Parser s Char
spaceLike = space

||| Parse an exact char. Case-sensetive.
export
char : Char -> Parser s Char
char c = terminal (cast c) (\x => toMaybe (x == c) x)

||| Parse an exact char. Case-sensetive. Ignore the result.
export
char_ : Char -> Parser s ()
char_ = ignore . char

||| Parse anything but the given char.
export
notChar : Char -> Parser s Char
notChar c = terminal "notChar" (\x => toMaybe (x /= c) x)

||| Parse one char from the list.
||| Prefer ones closer to the head of the list.
||| Fail if the list is empty or none of the chars matches.
export
oneOf : String -> Parser s Char
oneOf str =
  case fastUnpack str of
    [] => fail "oneOf \"\""
    x :: rest => char x <|> go rest
 where
  go : List Char -> Parser s Char
  go [] = fail "oneOf: no match"
  go (x :: xs) = char x <|> go xs

||| Parser an exact char. Case-insensetive.
export
charLike : Char -> Parser s Char
charLike c =
  char (toLower c) <|> char (toUpper c)

||| Non-empty string. Case-sensitive.
export
str : String -> Parser s String
str c =
  case fastUnpack c of
    [] => fail "str \"\""
    x :: xs => toString $
      seqList1 (map char (x ::: xs))

||| Non-empty string. Case-sensitive. Ignore the result.
export
str_ : String -> Parser s ()
str_ = ignore . str

export
newline : Parser s ()
newline =  str_ "\r\n" <|> str_ "\n"

||| Non-empty string. Case-insensitive.
export
strLike : String -> Parser s String
strLike c =
  case fastUnpack c of
    [] => fail "strLike \"\""
    x :: xs => toString $
      seqList1 (map charLike (x ::: xs))

||| Run the parser on the list of tokens,
||| expecting full consumption of the input.
export
parseFull : (act : Grammar () tok ty)
         -> (xs : List tok)
         -> Either (List1 (ParsingError tok ())) ty
parseFull act xs = do
  (x, []) <- parse act (map irrelevantBounds xs)
    | (x, toks@(_ :: _)) => Left (singleton $ Error "Some input left unconsumed" () Nothing)
  Right x

export
parseFull' : (act : Grammar () Char ty)
          -> (xs : String)
          --        vvvvvv Error Msg
          -> Either String ty
parseFull' act xs =
  mapFst (\(Error str () tok ::: _) => str) $
    parseFull act (fastUnpack xs)

export
mbParseAll : (act : Grammar () Char ty)
          -> (xs : String)
          -> Maybe ty
mbParseAll act xs = eitherToMaybe $
  mapFst (\(Error str () tok ::: _) => str) $
    parseFull act (fastUnpack xs)
