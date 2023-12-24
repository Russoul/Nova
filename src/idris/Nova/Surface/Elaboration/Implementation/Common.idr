module Nova.Surface.Elaboration.Implementation.Common

import Data.AVL
import Data.List
import Data.List1
import Data.SnocList
import Data.Fin
import Data.Location
import Data.String

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import Nova.Core.Context
import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Name
import Nova.Core.Pretty
import Nova.Core.Unification

import Nova.Surface.Language
import Nova.Surface.Shunting
import Nova.Surface.Operator
import Nova.Surface.SemanticToken


namespace Typ
  public export
  instantiateByElaboration : Omega -> OmegaName -> Typ -> Omega
  instantiateByElaboration omega idx rhs =
    case (lookup idx omega) of
      Just (MetaType ctx SolveByElaboration) => insert (idx, LetType ctx rhs) omega
      _ => assert_total $ idris_crash "instantiateByElaboration"

namespace Elem
  public export
  instantiateByElaboration : Omega -> OmegaName -> Elem -> Omega
  instantiateByElaboration omega idx rhs =
    case (lookup idx omega) of
      Just (MetaElem ctx ty SolveByElaboration) => insert (idx, LetElem ctx rhs ty) omega
      _ => assert_total $ idris_crash "instantiateByElaboration"

public export
pickPrefix : List (VarName, Typ) -> List VarName -> Maybe (List (VarName, Typ))
pickPrefix ctx [] = Just []
pickPrefix [] (x :: xs) = Nothing
pickPrefix ((x', ty) :: ctx) (x :: xs) =
  case (x' == x) of
    True => pickPrefix ctx xs <&> ((x, ty) ::)
    False => Nothing
