module Nova.Surface.ParserGeneral

import Data.Fin
import Data.SnocList
import Data.Location

import Text.Lexing.Token
import Text.Lexing.Tokeniser
import public Text.Parsing.Fork

import Nova.Surface.SemanticToken


public export
record ParsingSt where
  constructor MkParsingSt
  semToks : SnocList SemanticToken

public export
initialParsingSt : ParsingSt
initialParsingSt = MkParsingSt [<]

||| Grammar specialised for Nova:
||| token is Token
||| state is semantic tokens
public export
Rule : (ty : Type) -> Type
Rule = Grammar ParsingSt Token

public export
appendSemanticToken : SemanticToken -> Rule ()
appendSemanticToken tok = do
  update {semToks $= (:< tok)}

||| Run the parser on the list of tokens,
||| expecting partial consumption of the input.
export
parsePartial : (initial : ParsingSt)
            -> (act : Grammar ParsingSt Token ty)
            -> (xs : List (WithBounds Token))
            -> Either
                  (List1 (ParsingError Token ParsingSt))
                  (ParsingSt, List (WithBounds Token), ty)
parsePartial st act xs = do
  (toks, x, rest) <- parseWith st act xs
  Right (toks, rest, x)

||| Run the parser on the list of tokens,
||| expecting full consumption of the input.
||| Trims leading & trailing whitespace.
export
parseFull : (initial : ParsingSt)
         -> (act : Grammar ParsingSt Token ty)
         -> (xs : List Char)
         -> Either (List1 (ParsingError Token ParsingSt)) (ParsingSt, ty)
parseFull st act xs = do
  let (toks0, tok) = tokenise xs
  let st = {semToks $= (++ (toks0 <&> (, CommentAnn)))} st
  (st, x, []) <- parseWith st act tok
    | (_, x, toks@(tok :: _)) =>
        Left (singleton $ Error "Some input left unconsumed" st (Just tok.bounds))
  Right (st, x)

export
parseFull' : (initial : ParsingSt)
          -> (act : Grammar ParsingSt Token ty)
          -> (xs : String)
          -> Either (ParsingError Token ParsingSt) (ParsingSt, ty)
parseFull' st act xs =
  mapFst head (parseFull st act (fastUnpack xs))

public export
char : Char -> Rule Token
char x = is ("Expected symbol: " ++ cast x) (isSymbol (== x))

public export
char_ : Char -> Rule ()
char_ = ignore . char

namespace List1
  public export
  str : List1 Char -> Rule (List1 Token)
  str (x ::: []) = map singleton (char x)
  str (x ::: a :: as) = map cons (char x) <*> str (a ::: as)

namespace String
  public export
  str : String -> Rule (List1 Token)
  str s =
    case unpack s of --FIX: RETHINK THIS
      [] => fail "[Internal error] Attempt to parse an empty string"
      (x :: xs) => List1.str (x ::: xs) <|> fail "Expected string: \{s}"

public export
str_ : String -> Rule ()
str_ = ignore . str

public export
digit : Rule (Fin 10)
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
digits : Rule (List1 (Fin 10))
digits = some digit

public export
nat : Rule Nat
nat = do
  n <- digits
  pure (convert ([<] <>< (forget n)) 1)
 where
  -- decimal = {1, 10, 100, ...}
  convert : SnocList (Fin 10) -> (decimal : Nat) -> Nat
  convert [<] _ = 0
  convert (left :< x) decimal = convert left (decimal * 10) + finToNat x * decimal

public export
located : Rule a -> Rule (Range, a)
located x = do
  t <- bounds x
  pure (cast t.bounds, t.val)

public export
located_ : Rule a -> Rule Range
located_ x = do
  t <- bounds x
  pure (cast t.bounds)

public export
exact : String -> Rule Range
exact x = do
  r <- located (str_ x)
  pure (fst r)

public export
exactAnn : TermAnn -> String -> Rule Range
exactAnn ann x = do
  r <- exact x
  appendSemanticToken (r, ann)
  pure r

public export
exactAnn_ : TermAnn -> String -> Rule ()
exactAnn_ ann = ignore . exactAnn ann

public export
delim : String -> Rule Range
delim = exactAnn KeywordAnn

public export
delim_ : String -> Rule ()
delim_ = exactAnn_ KeywordAnn

public export
space : Rule ()
space = ignore $ is "whitespace" isSpace

public export
spaceDelim : Rule ()
spaceDelim = do
  ignore space
  c <- column
  guard "Wrong indentation" (c > 0)

public export
optSpaceDelim : Rule ()
optSpaceDelim = do
  r <- optional space
  case r of
    Just _ => do
      c <- column
      guard "Wrong indentation" (c > 0)
    Nothing => pure ()

public export
spaceDelimDef : Rule ()
spaceDelimDef = do
  ignore space
  c <- column
  guard "Wrong indentation" (c == 0)

public export
inParentheses : Rule a -> Rule a
inParentheses p = do
  delim_ "("
  optSpaceDelim
  t <- p
  optSpaceDelim
  delim_ ")"
  pure t

public export
inBars : Rule a -> Rule a
inBars p = do
  delim_ "|"
  optSpaceDelim
  t <- p
  optSpaceDelim
  delim_ "|"
  pure t

public export
inBraces : Rule a -> Rule a
inBraces p = do
  delim_ "{"
  optSpaceDelim
  t <- p
  optSpaceDelim
  delim_ "}"
  pure t

public export
inBrackets : Rule a -> Rule a
inBrackets p = do
  delim_ "["
  optSpaceDelim
  t <- p
  optSpaceDelim
  delim_ "]"
  pure t

public export
dotDelim : Rule ()
dotDelim = do
  optSpaceDelim
  delim_ "."
  optSpaceDelim

public export
commaDelim : Rule ()
commaDelim = do
  optSpaceDelim
  delim_ ","
  optSpaceDelim

public export
(<++>) : Rule String -> Lazy (Rule String) -> Rule String
f <++> g = do
  x <- f
  y <- g
  pure (x ++ y)

public export
withAnn : TermAnn -> Rule a -> Rule a
withAnn ann t = do
  (l, x) <- located t
  appendSemanticToken (l, ann)
  pure x

-- TODO: Is there such a function in stdlib?
-- TODO: Move!
public export
concatSepBy : String -> List1 String -> String
concatSepBy sep (x ::: xs) = foldl (\acc, s => acc ++ sep ++ s) x xs
