module Nova.Core.Monad

import public Control.Monad.JustAMonad

import Data.List
import Data.SnocList

import Nova.Core.Language

public export
M : Type -> Type
--               vvvvvv for critical errors only
M = JustAMonad.M String ()

public export
Mb : Type -> Type
Mb = M String () . Maybe

public export
MEither : Type -> Type -> Type
MEither err a = M String () (Either err a)

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

namespace MEither
  %inline
  public export
  (>>=) : MEither e a -> (a -> MEither e b) -> MEither e b
  m >>= f = M.do
    Right x <- m
      | Left err => return (Left err)
    f x

  %inline
  public export
  (>>) : MEither e () -> MEither e b -> MEither e b
  (>>) m f = MEither.(>>=) m (const f)

  %inline
  public export
  return : a -> MEither e a
  return x = M.return (Right x)

  %inline
  public export
  error : e -> MEither e a
  error x = M.return (Left x)

  public export
  liftM : M a -> MEither e a
  liftM f = M.do
    x <- f
    return (Right x)
