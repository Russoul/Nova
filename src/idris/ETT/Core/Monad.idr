module ETT.Core.Monad

import public Control.Monad.JustAMonad

import Data.List
import Data.SnocList

import ETT.Core.Language

public export
M : Type -> Type
M = JustAMonad.M String ()
