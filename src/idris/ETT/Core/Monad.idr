module ETT.Core.Monad

import public Control.Monad.JustAMonad

import Data.List
import Data.SnocList

import ETT.Core.Language

public export
M : Type -> Type
M = JustAMonad.M String ()

public export
Mb : Type -> Type
Mb = M String () . Maybe

namespace Mb
  %inline
  public export
  (>>=) : Mb a -> (a -> Mb b) -> Mb b
  m >>= f = M.do
    Just x <- m
      | Nothing => return Nothing
    f x

  %inline
  public export
  (>>) : Mb () -> Mb b -> Mb b
  (>>) m f = Mb.(>>=) m (const f)

  %inline
  public export
  return : a -> Mb a
  return x = M.return (Just x)

  %inline
  public export
  nothing : Mb a
  nothing = M.return Nothing

  public export
  liftM : M a -> Mb a
  liftM f = M.do
    x <- f
    return (Just x)
