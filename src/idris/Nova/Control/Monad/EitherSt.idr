module Nova.Control.Monad.EitherSt

import Data.Vect

import Nova.Control.Monad.Id
import Nova.Control.Monad.St

EitherSt e s a = s -> Either e (s, a)

public export
pure : a -> EitherSt e s a
pure x i = Right (i, x)

public export
throw : e -> EitherSt e s a
throw err _ = Left err

public export
(>>=) : EitherSt e s a -> (a -> EitherSt e s b) -> EitherSt e s b
(f >>= g) i =
  case f i of
    Left err => Left err
    Right (i, r) => g r i

public export
(>>) : EitherSt e s () -> Lazy (EitherSt e s b) -> EitherSt e s b
f >> g = with [EitherSt.(>>=)] f >>= (const g)

public export
join : EitherSt e s (EitherSt e s a) -> EitherSt e s a
join m = m >>= id

public export
(<$>) : (a -> b) -> EitherSt e s a -> EitherSt e s b
(f <$> t) i = case t i of
  Left err => Left err
  Right (i, x) => Right (i, f x)

%inline
public export
(<$) : b -> EitherSt e s a -> EitherSt e s b
x <$ f = const x <$> f

%inline
public export
(<&>) : EitherSt e s a -> (a -> b) -> EitherSt e s b
(<&>) = flip (<$>)

public export
(<*>) : EitherSt e s (a -> b) -> EitherSt e s a -> EitherSt e s b
a <*> b = EitherSt.do
  f <- a
  x <- b
  pure (f x)

public export
get : EitherSt e s s
get i = Right (i, i)

public export
put : s -> EitherSt e s ()
put i _ = Right (i, ())

public export
update : (s -> s) -> EitherSt e s ()
update f i = Right (f i, ())

public export
withSt : EitherSt e s a -> EitherSt e s (s, a)
withSt f = EitherSt.do
  x <- f
  st <- get
  pure (st, x)

public export
mapSt : EitherSt e s' a -> (s -> s') -> (s' -> s) -> EitherSt e s a
mapSt m f g i =
  case m (f i) of
    Right (i', x) => Right (g i', x)
    Left err => Left err

public export
unit : EitherSt s e ()
unit = EitherSt.pure ()

public export
when : Bool -> EitherSt s e () -> EitherSt s e ()
when True f = f
when False _ = EitherSt.unit

public export
unless : Bool -> EitherSt s e () -> EitherSt s e ()
unless cond f = when (not cond) f

%inline
public export
ignore : EitherSt e s a -> EitherSt e s ()
ignore f = with EitherSt.(<$>) const () <$> f

%inline
public export
mapError : (e -> e') -> EitherSt e s a -> EitherSt e' s a
mapError f m i =
  bimap f id $ m i

namespace Maybe
  public export
  traverse : (a -> EitherSt e s b) -> Maybe a -> EitherSt e s (Maybe b)
  traverse f Nothing = EitherSt.pure Nothing
  traverse f (Just v) = EitherSt.[| Just (f v) |]

  public export
  for : Maybe a -> (a -> EitherSt e s b) -> EitherSt e s (Maybe b)
  for = flip traverse

  public export
  for_ : Maybe a -> (a -> EitherSt e s b) -> EitherSt e s ()
  for_ = ignore .: for

  public export
  foldM : (r -> a -> EitherSt e s r) -> r -> Maybe a -> EitherSt e s r
  foldM f acc Nothing = EitherSt.pure acc
  foldM f acc (Just x) = EitherSt.do
    f acc x

namespace List
  public export
  traverse : (a -> EitherSt e s b) -> List a -> EitherSt e s (List b)
  traverse f [] = EitherSt.pure []
  traverse f (v :: vs) = EitherSt.[| f v :: traverse f vs |]

  public export
  traverse_ : (a -> EitherSt e s b) -> List a -> EitherSt e s ()
  traverse_ = ignore .: traverse

  public export
  for : List a -> (a -> EitherSt e s b) -> EitherSt e s (List b)
  for = flip traverse

  public export
  for_ : List a -> (a -> EitherSt e s b) -> EitherSt e s ()
  for_ = ignore .: for

  public export
  foldM : (r -> a -> EitherSt e s r) -> r -> List a -> EitherSt e s r
  foldM f acc [] = EitherSt.pure acc
  foldM f acc (x :: xs) = EitherSt.do
    foldM f !(f acc x) xs

namespace Vect
  public export
  sequence : Vect n (EitherSt e s a) -> EitherSt e s (Vect n a)
  sequence [] = EitherSt.pure []
  sequence (f :: fs) = EitherSt.[| f :: sequence fs |]

  public export
  traverse : (a -> EitherSt e s b) -> Vect n a -> EitherSt e s (Vect n b)
  traverse f [] = EitherSt.pure []
  traverse f (x :: xs) = EitherSt.[| f x :: traverse f xs |]

namespace SnocList
  public export
  traverse : (a -> EitherSt e s b) -> SnocList a -> EitherSt e s (SnocList b)
  traverse f [<] = EitherSt.pure [<]
  traverse f (vs :< v) = EitherSt.[| traverse f vs :< f v |]

public export
run : EitherSt e s a -> s -> Either e (s, a)
run f x = f x

public export
eval : EitherSt e s a -> s -> Either e a
eval = (map snd) .: run

public export
liftId : Id a -> EitherSt e s a
liftId = pure

public export
liftSt : St s a -> EitherSt e s a
liftSt f i =
  let (i, x) = f i in
  Right (i, x)

public export
fromEither : Either e a -> EitherSt e s a
fromEither (Left err) s = Left err
fromEither (Right ok) s = Right (s, ok)

public export
(<|>) : EitherSt e s a -> Lazy (EitherSt e s a) -> EitherSt e s a
(f <|> g) i =
  case f i of
    Left _ => g i
    Right ok => Right ok

export
infixl 2 <||>

public export
(<||>) : EitherSt e s a -> EitherSt e s b -> EitherSt e s (Either a b)
f <||> g = Left <$> f <|> Right <$> g
