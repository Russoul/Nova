module Nova.Core.Monad

import public Control.Monad.JustAMonad

import Data.List
import Data.List1
import Data.SnocList

import Nova.Core.Language

public export
M : Type -> Type
--               vvvvvv for critical errors only
M = JustAMonad.M String ()

namespace M
  %inline
  public export
  pure : a -> M a
  pure x = return x

namespace MMaybe
  %inline
  public export
  (>>=) : M e s (Maybe a) -> (a -> M e s (Maybe b)) -> M e s (Maybe b)
  m >>= f = M.do
    Just x <- m
      | Nothing => return Nothing
    f x

  %inline
  public export
  (>>) : M e s (Maybe ()) -> M e s (Maybe b) -> M e s (Maybe b)
  (>>) m f = MMaybe.(>>=) m (const f)

  %inline
  public export
  return : a -> M e s (Maybe a)
  return x = M.return (Just x)

  %inline
  public export
  nothing : M e s (Maybe a)
  nothing = M.return Nothing

  public export
  fromMaybe : Maybe a -> M e s (Maybe a)
  fromMaybe x = M.do
    return x

  public export
  liftM : M e s a -> M e s (Maybe a)
  liftM f = M.do
    x <- f
    return (Just x)

  public export
  guard : Bool -> M e s (Maybe ())
  guard False = M.do return Nothing
  guard True = M.do return (Just ())

  public export
  mapResult : (a -> b) -> M e s (Maybe a) -> M e s (Maybe b)
  mapResult f t = M.mapResult (map f) t

  public export
  (<$>) : (a -> b) -> M e s (Maybe a) -> M e s (Maybe b)
  (<$>) = MMaybe.mapResult

  public export
  (<&>) : M e s (Maybe a) -> (a -> b) -> M e s (Maybe b)
  (<&>) = flip MMaybe.mapResult

namespace MEither
  %inline
  public export
  (>>=) : M e s (Either e' a) -> (a -> M e s (Either e' b)) -> M e s (Either e' b)
  m >>= f = M.do
    Right x <- m
      | Left err => return (Left err)
    f x

  %inline
  public export
  (>>) : M e s (Either e' ()) -> M e s (Either e' b) -> M e s (Either e' b)
  (>>) m f = MEither.(>>=) m (const f)

  %inline
  public export
  return : a -> M e s (Either e' a)
  return x = M.return (Right x)

  %inline
  public export
  error : e' -> M e s (Either e' a)
  error x = M.return (Left x)

  public export
  liftM : M e s a -> M e s (Either e' a)
  liftM f = M.do
    x <- f
    return (Right x)

  public export
  forList : List a -> (a -> M e s (Either e' b)) -> M e s (Either e' (List b))
  forList [] f = return []
  forList (x :: xs) f = MEither.do
    y <- f x
    ys <- forList xs f
    return (y :: ys)

  public export
  forSnocList : SnocList a -> (a -> M e s (Either e' b)) -> M e s (Either e' (SnocList b))
  forSnocList [<] f = return [<]
  forSnocList (xs :< x) f = MEither.do
    ys <- forSnocList xs f
    y <- f x
    return (ys :< y)

  public export
  forList1 : List1 a -> (a -> M e s (Either e' b)) -> M e s (Either e' (List1 b))
  forList1 (head ::: tail) f = MEither.do
    head' <- f head
    tail' <- forList tail f
    return (head' ::: tail')
