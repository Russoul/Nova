module ETT.Surface.SemanticToken

import Data.AVL
import Data.Maybe
import Data.SnocList
import Data.Util

import Data.Location

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

-- TODO: revisit
public export
data TermAnn =
               -- Type Value
               TypAnn
               -- Keywords
             | KeywordAnn
               -- Let-Kan-Variable
             | LetVarAnn
               -- Bound-Kan-Variable
             | BoundVarAnn
               -- Unsolved Meta
             | UnsolvedMetaAnn
               -- Solved Meta
             | SolvedMetaAnn
               -- Comment
             | CommentAnn
               -- Eliminator
             | ElimAnn
               -- Element Value
             | ElemAnn

public export
toAnsiStyle : TermAnn -> AnsiStyle
toAnsiStyle TypAnn = color BrightBlue
toAnsiStyle KeywordAnn = color Yellow
toAnsiStyle LetVarAnn = color BrightRed
toAnsiStyle BoundVarAnn = color BrightBlack
toAnsiStyle SolvedMetaAnn = color Green
toAnsiStyle UnsolvedMetaAnn = color Magenta
toAnsiStyle CommentAnn = color Cyan
toAnsiStyle ElimAnn = color BrightRed
toAnsiStyle ElemAnn = color BrightGreen

public export
SemanticToken : Type
SemanticToken = (Range, TermAnn)

public export
SemanticTokens : Type
SemanticTokens = OrdTree (FileName, String, SnocList SemanticToken) ByFst

public export
sortSemanticTokens : SnocList SemanticToken -> SnocList SemanticToken
sortSemanticTokens = quicksort @{Ord.ByFst @{Range.Inst}}
