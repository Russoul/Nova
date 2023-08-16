module ETT.Surface.ParserUtil

import Data.List.Elem
import Data.Fin
import Data.List
import Data.Vect
import Data.List1
import Data.Maybe
import Data.SnocList
import Data.String
import Data.String.Extra
import public Text.Parser.Fork
import Text.Lexer

import Text.Parser.CharUtil

import Data.Util

import Data.Location

import ETT.Core.Name
import ETT.Surface.SemanticToken

-----------------------------------------------------------
-------------- Utililies for HOTT parser ------------------
-----------------------------------------------------------

accountFor : Char -> (Bool, Int -> Int, Int -> Int)
accountFor x = (isNL x || isSpace x, ifThenElse (isNL x) ((+ 1), const 0) (id, (+ 1)))

mkBounds : (Int, Int) -> (Int, Int) -> Bounds
mkBounds (startL, startC) (endL, endC) = MkBounds startL startC endL endC

apply2 : (a -> b, a' -> b') -> (a, a') -> (b, b')
apply2 (f, g) (x, y) = (f x, g y)

compose2 : (b -> c, b' -> c') -> (a -> b, a' -> b') -> (a -> c, a' -> c')
compose2 (g, g') (f, f') = (g . f, g' . f')

public export
data Token : Type where
 ||| Doesn't contain whitespace.
 ||| TODO Replace Char with a type that guarantees that assumption.
 Symbol : Char -> Token
 ||| Fusion of consecutive whitespace symbols, including newline (' ', '\n', etc.).
 Whitespace : Token
 ||| Fusion of symbols that are part of a comment.
 Comment : SnocList Char -> Token

public export
Show Token where
  show (Symbol c) = "'\{show c}'"
  show Whitespace = "␣"
  show (Comment com) = "/*\{fastPack (cast com)}*/"

public export
isSymbol : (Char -> Bool) -> Token -> Bool
isSymbol f (Symbol x) = f x
isSymbol f _ = False

public export
isSpace : Token -> Bool
isSpace Whitespace = True
isSpace _ = False

public export
isComment : Token -> Bool
isComment (Comment _) = True
isComment _ = False

public export
isToken : Token -> Bool -> Token -> Maybe Token

public export
toChar : Token -> Char
toChar (Symbol c) = c
toChar Whitespace = ' '
toChar (Comment _) = '/'

public export
data State = InSinglelineComment | InMultilineComment | AccWhitespace | Normal

||| Recusion principle for State.
state : a -> a -> a -> a -> State -> a
state inSinglelineComment inMultilineComment accWhitespace normal InSinglelineComment = inSinglelineComment
state inSinglelineComment inMultilineComment accWhitespace normal InMultilineComment = inMultilineComment
state inSinglelineComment inMultilineComment accWhitespace normal AccWhitespace = accWhitespace
state inSinglelineComment inMultilineComment accWhitespace normal Normal = normal

||| Populates bounds information.
||| Combines consecutive whitespace symbols into one token.
||| Combines single-line comments into one token.
export
mkWithBounds : (accW : State)
            -> state ((Int, Int), (Int -> Int, Int -> Int), SnocList Char)
                     ((Int, Int), (Int -> Int, Int -> Int), SnocList Char)
                     ((Int, Int), (Int -> Int, Int -> Int))
                     (Int, Int)
                     accW
            -> List Char
            -> List (WithBounds Token)
mkWithBounds InSinglelineComment (p, delta, comment) [] =
  let p' = delta `apply2` p in
  [MkBounded (Comment comment) False (mkBounds p p')]
mkWithBounds InMultilineComment (p, delta, comment) [] =
  let p' = delta `apply2` p in
  [MkBounded (Comment comment) False (mkBounds p p')]
-- Remove the trailing whitespace
mkWithBounds AccWhitespace (p, delta) [] = []
mkWithBounds Normal _ [] = []
mkWithBounds Normal p ('-' :: '-' :: xs) =
  mkWithBounds InSinglelineComment (p, (id, (+ 2)), [<]) xs
mkWithBounds Normal p ('{' :: '-' :: xs) =
  mkWithBounds InMultilineComment (p, (id, (+ 2)), [<]) xs
mkWithBounds AccWhitespace (p, delta) ('-' :: '-' :: xs) =
  let p' = delta `apply2` p in
  let w = MkBounded Whitespace False (mkBounds p p') in
  w :: mkWithBounds InSinglelineComment (p', (id, (+ 2)), [<]) xs
mkWithBounds AccWhitespace (p, delta) ('{' :: '-' :: xs) =
  let p' = delta `apply2` p in
  let w = MkBounded Whitespace False (mkBounds p p') in
  w :: mkWithBounds InMultilineComment (p', (id, (+ 2)), [<]) xs
mkWithBounds Normal p (x :: xs) =
  let (isW, delta) = accountFor x in
  case isW of
    False =>
      let p' = delta `apply2` p in
      MkBounded (Symbol x) False (mkBounds p p') :: mkWithBounds Normal p' xs
    True => mkWithBounds AccWhitespace (p, delta) xs
mkWithBounds AccWhitespace (p, delta) (x :: xs) =
  let (isW, delta') = accountFor x in
  case isW of
    False =>
      let p' = delta `apply2` p in
      let p'' = (delta' `compose2` delta) `apply2` p in
      MkBounded Whitespace False (mkBounds p p') :: MkBounded (Symbol x) False (mkBounds p' p'') :: mkWithBounds Normal p'' xs
    True => mkWithBounds AccWhitespace (p, delta' `compose2` delta) xs
    -- This will fail on windows                  vvvv
mkWithBounds InSinglelineComment (p, delta, str) ('\n' :: xs) =
  let p' = delta `apply2` p in
  let comment = MkBounded (Comment str) False (mkBounds p p') in
  let p'' = ((+ 1), const 0) `apply2` p' in
  comment :: mkWithBounds Normal p'' xs
    -- BUG:
    -- This will fail on windows (and not only?) vvvv
mkWithBounds InMultilineComment (p, delta, str) ('\n' :: xs) =
  -- As soon as we hit a new line,
  -- we ship a comment token and continue
  -- we do this to keep us to single-line semantic tokens only.
  let p' = delta `apply2` p in
  let comment = MkBounded (Comment str) False (mkBounds p p') in
  let p'' = ((+ 1), const 0) `apply2` p' in
  comment :: mkWithBounds InMultilineComment (p'', (id, id), str) xs
mkWithBounds InMultilineComment (p, delta, str) ('-' :: '}' :: xs) =
  let p' = ((id, (+ 2)) `compose2` delta) `apply2` p in
  let comment = MkBounded (Comment str) False (mkBounds p p') in
  comment :: mkWithBounds Normal p' xs
mkWithBounds InSinglelineComment (p, delta, str) (x :: xs) =
  mkWithBounds InSinglelineComment (p, (id, (+ 1)) `compose2` delta, str :< x) xs
mkWithBounds InMultilineComment (p, delta, str) (x :: xs) =
  mkWithBounds InMultilineComment (p, (id, (+ 1)) `compose2` delta, str :< x) xs

export
filterOutComments : List (WithBounds Token) -> (SnocList SemanticToken, List (WithBounds Token))
filterOutComments [] = ([<], [])
filterOutComments (MkBounded (Comment _) _ range :: xs) =
  mapFst (:< (cast range, CommentAnn)) (filterOutComments xs)
filterOutComments (x :: xs) =
  mapSnd (x ::) (filterOutComments xs)

min2 : (Int, Int) -> (Int, Int) -> (Int, Int)
min2 (l, c) (l', c') =
  ifThenElse (l < l') (l, c) $
    ifThenElse (l == l') (ifThenElse (c < c') (l, c) (l', c')) $
      (l', c')

max2 : (Int, Int) -> (Int, Int) -> (Int, Int)
max2 (l, c) (l', c') =
  ifThenElse (l < l') (l', c') $
    ifThenElse (l == l') (ifThenElse (c < c') (l', c') (l, c)) $
      (l, c)

||| (s, e) ∪ (s', e') =
||| (min (s, s'), max (e, e'))
export
union : Bounds -> Bounds -> Bounds
union (MkBounds sl sc el ec) (MkBounds sl' sc' el' ec') =
  let (minl, minc) = min2 (sl, sc) (sl', sc') in
  let (maxl, maxc) = max2 (el, ec) (el', ec') in
  MkBounds minl minc maxl maxc

export
mergeWhitespace : List (WithBounds Token) -> List (WithBounds Token)
mergeWhitespace [] = []
mergeWhitespace (MkBounded Whitespace r p :: MkBounded Whitespace r' p' :: xs) =
  mergeWhitespace (MkBounded Whitespace (r || r') (union p p') :: xs)
mergeWhitespace (x :: xs) = x :: mergeWhitespace xs

export
removeLeadingWhitespace : List (WithBounds Token) -> List (WithBounds Token)
removeLeadingWhitespace [] = []
removeLeadingWhitespace (MkBounded Whitespace {} :: xs) =
  removeLeadingWhitespace xs
removeLeadingWhitespace (x :: xs) = x :: xs

export
removeTrailingWhitespace : List (WithBounds Token) -> List (WithBounds Token)
removeTrailingWhitespace [] = []
removeTrailingWhitespace [MkBounded Whitespace {}] = []
removeTrailingWhitespace (x :: xs) = x :: removeTrailingWhitespace xs

namespace Show.Token
  public export
  [BriefInst] Show Token where
    show (Symbol x) = cast x
    show Whitespace = " "
    show (Comment str) = "/"

  public export
  [WithBoundsBriefInst] Show (WithBounds Token) where
    show (MkBounded tok isIrr (MkBounds l c l' c')) =
      show @{BriefInst} tok ++ "(\{show l}:\{show c}-\{show l'}:\{show c'})"

  public export
  [WithBoundsBriefListInst] Show (List (WithBounds Token)) where
    show xs = show @{NLSepList @{WithBoundsBriefInst}} xs

export
tokenise : List Char -> (SnocList SemanticToken, List (WithBounds Token))
tokenise = mapSnd removeLeadingWhitespace
         . mapSnd removeTrailingWhitespace
         . mapSnd mergeWhitespace
         . filterOutComments --vvvvvv We count starting at 0 for both axes,
         . mkWithBounds Normal (0, 0) -- solely because LSP expects this format.

public export
record ParsingSt where
  constructor MkParsingSt
  semToks : SnocList SemanticToken

public export
initialParsingSt : ParsingSt
initialParsingSt = MkParsingSt [<]

||| Grammar specialised for ETT:
||| token is Token
||| state is context info & semantic info
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
  let st = {semToks $= (++ toks0)} st
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


namespace Rule
  public export
  char : Char -> Rule Token
  char x = is ("Expected symbol: " ++ cast x) (isSymbol (== x))

  public export
  char_ : Char -> Rule ()
  char_ = ignore . char

  public export
  str' : List1 Char -> Rule (List1 Token)
  str' (x ::: []) = map singleton (char x)
  str' (x ::: a :: as) = map cons (char x) <*> str' (a ::: as)

  public export
  str : String -> Rule (List1 Token)
  str s =
    case unpack s of --FIX: RETHINK THIS
      [] => fail "[Internal error] Attempt to parse an empty string"
      (x :: xs) => str' (x ::: xs) <|> fail "Expected string: \{s}"

  public export
  str_ : String -> Rule ()
  str_ = ignore . str

  public export
  num : Rule (Fin 10)
  num = 0 <$ char_ '0'
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
nums : Rule (List1 (Fin 10))
nums = some num

public export
nat : Rule Nat
nat = do
  n <- nums
  pure (convert ([<] <>< (forget n)) 1)
 where
  -- decimal = {1, 10, 100, ...}
  convert : SnocList (Fin 10) -> (decimal : Nat) -> Nat
  convert [<] _ = 0
  convert (left :< x) decimal = convert left (decimal * 10) + finToNat x * decimal

public export
doubleStruck0 : Char
doubleStruck0 = '𝟘'

public export
doubleStruck9 : Char
doubleStruck9 = '𝟡'

public export
smallGreekAlpha : Char
smallGreekAlpha = 'α'

public export
smallGreekOmega : Char
smallGreekOmega = 'ω'

public export
capitalGreekAlpha : Char
capitalGreekAlpha = 'Α'

public export
capitalGreekOmega : Char
capitalGreekOmega = 'Ω'

public export
isSubscriptDigit : Char -> Bool
isSubscriptDigit x =
     x == '₀'
  || x == '₁'
  || x == '₂'
  || x == '₃'
  || x == '₄'
  || x == '₅'
  || x == '₆'
  || x == '₇'
  || x == '₈'
  || x == '₉'

public export
isSuperscriptDigit : Char -> Bool
isSuperscriptDigit x =
     x == '⁰'
  || x == '¹'
  || x == '²'
  || x == '³'
  || x == '⁴'
  || x == '⁵'
  || x == '⁶'
  || x == '⁷'
  || x == '⁸'
  || x == '₉'

public export
isSmallGreekLetter : Char -> Bool
isSmallGreekLetter x = ord x >= ord smallGreekAlpha && ord x <= ord smallGreekOmega

public export
isCapitalGreekLetter : Char -> Bool
isCapitalGreekLetter x = ord x >= ord capitalGreekAlpha && ord x <= ord capitalGreekOmega

public export
isDoubleStruckDigit : Char -> Bool
isDoubleStruckDigit x = ord x >= ord doubleStruck0 && ord x <= ord doubleStruck9

||| a-z|A-Z|α-ω|Α-Ω|ℕ|ℤ|𝕀|𝕊|𝕋|𝕌|ℙ|𝔽|𝟘-𝟡|⊥|⊤|∃
public export
varFirstSym : Rule Token
varFirstSym = is "first symbol of a variable" $ isSymbol $ \x =>
    isLower x
 || isUpper x
 || isSmallGreekLetter x
 || isCapitalGreekLetter x
 || x == 'ℕ'
 || x == 'ℤ'
 || x == '𝕀'
 || x == '𝕊'
 || x == '𝕋'
 || x == '𝕌'
 || x == 'ℙ'
 || x == '𝔽'
 || isDoubleStruckDigit x
 || x == '⊥'
 || x == '⊤'
 || x == '∃'
 || x == '⁼'
 || x == '-'

||| a-Z|A-Z|0-9|_|₀-₉|α-ω|Α-Ω|'|ℕ|ℤ|𝕀|𝕊|𝕋|𝕌|ℙ|𝔽|𝟘-𝟡|⊥|⊤|∃|ᵢ
public export
varNextSym : Rule Token
varNextSym = is "symbol of a variable" $ isSymbol $ \x =>
    isLower x
 || isUpper x
 || isDigit x
 || x == '\''
 || isSubscriptDigit x
 || isSuperscriptDigit x
 || isSmallGreekLetter x
 || isCapitalGreekLetter x
 || x == 'ℕ'
 || x == 'ℤ'
 || x == '𝕀'
 || x == '𝕊'
 || x == '𝕋'
 || x == '𝕌'
 || x == 'ℙ'
 || x == '𝔽'
 || isDoubleStruckDigit x
 || x == '⊥'
 || x == '⊤'
 || x == '∃'
 || x == 'ᵢ'
 || x == '⁼'
 || x == '-'

||| !@#$%^&*=+-,.:⋍≡∘⨯ᐅ><⇒⤇∨∧
public export
isOperatorSym : Char -> Bool
isOperatorSym x = elem x $
  the (List _) [ '@'
               , '#'
               , '$'
               , '%'
               , '^'
               , '&'
               , '*'
               , '='
               , '+'
               , ','
               , '.'
               , '⋍'
               , '≅'
               , '≡'
               , '∘'
               , '⨯'
               , 'ᐅ'
               , '>'
               , '<'
               , '⇒'
               , '⤇'
               , '∨'
               , '∧'
               , '→'
               , '≡'
               , '∈']

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
keyword : TermAnn -> String -> Rule Range
keyword ann x = do
  r <- located (str_ x)
  appendSemanticToken (fst r, ann)
  pure (fst r)

public export
keyword_ : TermAnn -> String -> Rule ()
keyword_ ann = ignore . keyword ann

public export
delim : String -> Rule Range
delim = keyword KeywordAnn

public export
delim_ : String -> Rule ()
delim_ = keyword_ KeywordAnn

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
inBrackets' : Rule a -> Rule a
inBrackets' p = do
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
opIdent : Rule String
opIdent = do
  op <- some (is "operator" $ isSymbol isOperatorSym)
  pure $ pack (map toChar (forget op))

nonOpIdent : Rule String
nonOpIdent = map (<+) (map toChar varFirstSym) <*> map (pack . map toChar) (many varNextSym)

concatSepBy : String -> List1 String -> String
concatSepBy sep (x ::: xs) = foldl (\acc, s => acc ++ sep ++ s) x xs

(<++>) : Rule String -> Lazy (Rule String) -> Rule String
f <++> g = do
  x <- f
  y <- g
  pure (x ++ y)

opAppIdent : Rule String
opAppIdent = ((delim_ "_" $> "_") <++> continue1') <|> (opIdent <++> continue2')
 where
  mutual
    continue1 : Rule String
    continue1 = (opIdent <++> continue2) <|> pure ""

    continue2 : Rule String
    continue2 = ((delim_ "_" $> "_") <++> continue1) <|> pure ""

    continue1' : Rule String
    continue1' = opIdent <++> continue2

    continue2' : Rule String
    continue2' = (delim_ "_" $> "_") <++> continue1

public export
prevarIdent : Rule String
prevarIdent =
  nonOpIdent <|> opAppIdent

thatManyConsumption : Nat -> Bool -> Bool
thatManyConsumption Z     = const False
thatManyConsumption (S k) = id

-- TODO:
----- MOVE THIS -----
OrRightNeutral : (a : Bool) -> a || False = a
OrRightNeutral False = Refl
OrRightNeutral True = Refl

OrIdempotent : (a : Bool) -> a = a || a
OrIdempotent False = Refl
OrIdempotent True = Refl
----- --------- -----

0
Lemma0 : (k : Nat)
      -> c || Delay (thatManyConsumption k c || Delay False) = c
Lemma0 Z = replace {p = \p => c || Delay p = c} lemma (OrRightNeutral ?)
 where
  lemma : thatManyConsumption 0 c || Delay False = False
  lemma = Refl
Lemma0 (S k) = trans (cong (c ||) (OrRightNeutral ?)) (sym $ OrIdempotent c)

public export
keywords : List String
keywords = [ "Z"
           , "S"
           , "ℕ"
           , "𝕌"
           , "ℕ-elim"
           , "Refl"
           , "J"
           , "El"
           , "."
           , "→"
           , "Π-β"
           , "Π-η"
           , "Π⁼"
           , "ℕ-β-Z"
           , "ℕ-β-S"
           ]

public export
varName : Rule VarName
varName = do
  x <- prevarIdent
  guard "ident" (not $ elem x keywords)
  pure x

public export
spName : (s : String) -> {auto _ : Elem s ParserUtil.keywords} -> Rule Range
spName expected = do
  (r, x) <- located prevarIdent
  guard "Expected special name: \{expected}" (x == expected)
  pure r

