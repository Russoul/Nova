module Text.Lexing.Token

import Data.SnocList

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

