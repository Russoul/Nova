module Nova.Surface.ParserCategorical

import Me.Russoul.Text.Range
import Me.Russoul.Text.Lexer.Token

import Data.List.Elem
import Data.String.Extra


import Nova.Surface.SemanticToken
import Nova.Surface.ParserGeneral

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

||| a-Z|A-Z|0-9|₀-₉|α-ω|Α-Ω|'|ℕ|ℤ|𝕀|𝕊|𝕋|𝕌|ℙ|𝔽|𝟘-𝟡|⊥|⊤|∃|ᵢ|-
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
 || x == 'ₘ' -- FIX: I am currently using this for "machine" names. This is a hack as no one is stopping the user from entering 'ₘ' as well!
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

||| !@#$%^&*=+,.:⋍≡∘⨯ᐅ><⇒⤇∨∧
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
               , '∈'
               , ':' ]

namespace Special
  ||| name and op can't be a special symbol
  public export
  special : List String
  special = [ "Z"
            , "S"
            , "ℕ"
            , "𝟘"
            , "𝟙"
            , "𝕌"
            , "ℕ-elim"
            , "𝟘-elim"
            , "Refl"
            , "J"
            , "El"
            , "."
            , "↦"
            , "Π-β"
            , "Π-η"
            , "Π⁼"
            , "Σ-β₁"
            , "Σ-β₂"
            , "Σ-η"
            , "Σ⁼"
            , "𝟙⁼"
            , "ℕ-β-Z"
            , "ℕ-β-S"
            , "tac"
            , "tt"
            , ":"
            , "{"
            , "}"
            , "("
            , ")"
            , "_"
            , "☐"
            , "?"
            , "!"
            , "type"
            , "$"
            ]

public export
preop : Rule String
preop = do
  op <- some (is "operator" $ isSymbol isOperatorSym)
  let op = pack (map toChar (forget op))
  guard "not a keyword" (not $ elem op special)
  pure op

public export
op : Rule String
op = preop <|> (exactAnn_ KeywordAnn "type" $> "type")

name : Rule String
name = do
  x <- map (<+) (map toChar varFirstSym) <*> map (pack . map toChar) (many varNextSym)
  guard "not a keyword" (not $ elem x special)
  pure x

opApp : Rule String
opApp = ((str_ "_" $> "_") <++> continue1') <|> (op <++> continue2')
 where
  mutual
    continue1 : Rule String
    continue1 = (op <++> continue2) <|> pure ""

    continue2 : Rule String
    continue2 = ((str_ "_" $> "_") <++> continue1) <|> pure ""

    continue1' : Rule String
    continue1' = op <++> continue2

    continue2' : Rule String
    continue2' = (str_ "_" $> "_") <++> continue1

public export
var : Rule String
var =
  name <|> opApp

public export
special : (s : String) -> {auto _ : Elem s ParserCategorical.Special.special} -> Rule Range
special s = exact s

public export
specialAnn : TermAnn -> (s : String) -> {auto _ : Elem s ParserCategorical.Special.special} -> Rule Range
specialAnn ann s = exactAnn ann s

public export
specialAnn_ : TermAnn -> (s : String) -> {auto _ : Elem s ParserCategorical.Special.special} -> Rule ()
specialAnn_ ann s = ignore (specialAnn ann s)
