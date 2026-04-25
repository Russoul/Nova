module Nova.Control.Monad.StEither

import Data.Vect

import Nova.Control.Monad.Id
import Nova.Control.Monad.St

StEither e s a = s -> (s, Either e a)

public export
pure : a -> StEither e s a
pure x i = (i, Right x)

public export
throw : e -> StEither e s a
throw err i = (i, Left err)

public export
(>>=) : StEither e s a -> (a -> StEither e s b) -> StEither e s b
(f >>= g) i =
  case f i of
    (i, Left err) => (i, Left err)
    (i, Right r) => g r i

public export
(>>) : StEither e s () -> Lazy (StEither e s b) -> StEither e s b
f >> g = with [StEither.(>>=)] f >>= (const g)

public export
join : StEither e s (StEither e s a) -> StEither e s a
join m = m >>= id

public export
(<$>) : (a -> b) -> StEither e s a -> StEither e s b
(f <$> t) i = case t i of
  (i, Left err) => (i, Left err)
  (i, Right x) => (i, Right (f x))

%inline
public export
(<$) : b -> StEither e s a -> StEither e s b
x <$ f = const x <$> f

%inline
public export
(<&>) : StEither e s a -> (a -> b) -> StEither e s b
(<&>) = flip (<$>)

public export
(<*>) : StEither e s (a -> b) -> StEither e s a -> StEither e s b
a <*> b = StEither.do
  f <- a
  x <- b
  pure (f x)

public export
get : StEither e s s
get i = (i, Right i)

public export
put : s -> StEither e s ()
put i _ = (i, Right ())

public export
update : (s -> s) -> StEither e s ()
update f i = (f i, Right ())

public export
withSt : StEither e s a -> StEither e s (s, a)
withSt f = StEither.do
  x <- f
  st <- get
  pure (st, x)

public export
mapSt : StEither e s' a -> (s -> s') -> (s' -> s) -> StEither e s a
mapSt m f g i = mapFst g $ m (f i)

public export
unit : StEither s e ()
unit = StEither.pure ()

public export
when : Bool -> StEither s e () -> StEither s e ()
when True f = f
when False _ = StEither.unit

public export
unless : Bool -> StEither s e () -> StEither s e ()
unless cond f = when (not cond) f

%inline
public export
ignore : StEither e s a -> StEither e s ()
ignore f = with StEither.(<$>) const () <$> f

%inline
public export
mapError : (e -> e') -> StEither e s a -> StEither e' s a
mapError f m i =
  mapSnd (mapFst f) (m i)

namespace Maybe
  public export
  traverse : (a -> StEither e s b) -> Maybe a -> StEither e s (Maybe b)
  traverse f Nothing = StEither.pure Nothing
  traverse f (Just v) = StEither.[| Just (f v) |]

  public export
  for : Maybe a -> (a -> StEither e s b) -> StEither e s (Maybe b)
  for = flip traverse

  public export
  for_ : Maybe a -> (a -> StEither e s b) -> StEither e s ()
  for_ = ignore .: for

  public export
  foldM : (r -> a -> StEither e s r) -> r -> Maybe a -> StEither e s r
  foldM f acc Nothing = StEither.pure acc
  foldM f acc (Just x) = StEither.do
    f acc x

namespace List
  public export
  traverse : (a -> StEither e s b) -> List a -> StEither e s (List b)
  traverse f [] = StEither.pure []
  traverse f (v :: vs) = StEither.[| f v :: traverse f vs |]

  public export
  traverse_ : (a -> StEither e s b) -> List a -> StEither e s ()
  traverse_ = ignore .: traverse

  public export
  for : List a -> (a -> StEither e s b) -> StEither e s (List b)
  for = flip traverse

  public export
  for_ : List a -> (a -> StEither e s b) -> StEither e s ()
  for_ = ignore .: for

  public export
  foldM : (r -> a -> StEither e s r) -> r -> List a -> StEither e s r
  foldM f acc [] = StEither.pure acc
  foldM f acc (x :: xs) = StEither.do
    foldM f !(f acc x) xs

namespace Vect
  public export
  sequence : Vect n (StEither e s a) -> StEither e s (Vect n a)
  sequence [] = StEither.pure []
  sequence (f :: fs) = StEither.[| f :: sequence fs |]

  public export
  traverse : (a -> StEither e s b) -> Vect n a -> StEither e s (Vect n b)
  traverse f [] = StEither.pure []
  traverse f (x :: xs) = StEither.[| f x :: traverse f xs |]

namespace SnocList
  public export
  traverse : (a -> StEither e s b) -> SnocList a -> StEither e s (SnocList b)
  traverse f [<] = StEither.pure [<]
  traverse f (vs :< v) = StEither.[| traverse f vs :< f v |]

%inline
public export
run : StEither e s a -> s -> (s, Either e a)
run f x = f x

public export
eval : StEither e s a -> s -> Either e a
eval = snd .: StEither.run

public export
liftId : Id a -> StEither e s a
liftId = pure

public export
liftSt : St s a -> StEither e s a
liftSt f i =
  let (i, x) = f i in
  (i, Right x)

public export
fromEither : Either e a -> StEither e s a
fromEither x s = (s, x)
