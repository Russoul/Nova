module Nova.Control.Monad.St

import Nova.Control.Monad.Id
import Data.List1
import Data.Vect

St s a = s -> (s, a)

public export
(>>=) : St s a -> (a -> St s b) -> St s b
(f >>= g) i =
  let (i, x) = f i in g x i

public export
(=<<) : (a -> St s b) -> St s a -> St s b
(=<<) = flip (>>=)

public export
(>>) : St s () -> St s a -> St s a
f >> g = with [St.(>>=)]
 f >>= const g

public export
(<$>) : (a -> b) -> St s a -> St s b
(f <$> t) i = let (i, x) = t i in (i, f x)

%inline
public export
(<$) : b -> St s a -> St s b
(v <$ t) = const v <$> t

public export
(<&>) : St s a -> (a -> b) -> St s b
(<&>) = flip St.(<$>)

public export
(<=<) : (b -> St s c) -> (a -> St s b) -> a -> St s c
(f <=< g) x = g x >>= f

public export
pure : a -> St s a
pure x i = (i, x)

public export
unit : St s ()
unit i = (i, ())

%inline
void : St s a -> St s ()
void = with [St.(<$)] (() <$)

%inline
ignore : St s a -> St s ()
ignore = with [St.(<$)] (() <$)

public export
(<*>) : St s (a -> b) -> St s a -> St s b
(f <*> x) i =
  let (i, func) = f i in
  let (i, val) = x i in
  (i, func val)

public export
get : St s s
get i = (i, i)

public export
put : s -> St s ()
put i _ = (i, ())

public export
update : (s -> s) -> St s ()
update f i = (f i, ())

public export
when : Bool -> St s () -> St s ()
when False _ = St.pure ()
when True x = x

public export
mapState : (s -> s') -> (s' -> s) -> St s a -> St s' a
mapState f g st i =
  let (i, x) = st (g i) in
  (f i, x)

public export
liftId : Id a -> St s a
liftId = pure

namespace Maybe
  public export
  traverse : (a -> St e b) -> Maybe a -> St e (Maybe b)
  traverse f Nothing = St.[| Nothing |]
  traverse f (Just x) = St.[| Just (f x) |]

  %inline
  public export
  for : Maybe a -> (a -> St e b) -> St e (Maybe b)
  for = flip traverse

  %inline
  public export
  for_ : Maybe a -> (a -> St e b) -> St e ()
  for_ = ignore .: for

namespace List
  public export
  sequence : List (St e a) -> St e (List a)
  sequence [] = St.pure []
  sequence (f :: fs) = St.[| f :: sequence fs |]

  public export
  traverse : (a -> St e b) -> List a -> St e (List b)
  traverse f [] = St.pure []
  traverse f (x :: xs) = St.[| f x :: traverse f xs |]

  %inline
  public export
  for : List a -> (a -> St e b) -> St e (List b)
  for = flip traverse

  %inline
  public export
  for_ : List a -> (a -> St e b) -> St e ()
  for_ = St.ignore .: List.for

namespace Vect
  public export
  sequence : Vect n (St e a) -> St e (Vect n a)
  sequence [] = St.pure []
  sequence (f :: fs) = St.[| f :: sequence fs |]

  public export
  traverse : (a -> St e b) -> Vect n a -> St e (Vect n b)
  traverse f [] = St.pure []
  traverse f (x :: xs) = St.[| f x :: traverse f xs |]

  public export
  traverse_ : (a -> St e ()) -> List a -> St e ()
  traverse_ f xs = void $ List.traverse f xs

namespace SnocList
  public export
  sequence : SnocList (St e a) -> St e (SnocList a)
  sequence [<] = St.pure [<]
  sequence (fs :< f) = St.[| sequence fs :< f |]

  public export
  traverse : (a -> St e b) -> SnocList a -> St e (SnocList b)
  traverse f [<] = St.pure [<]
  traverse f (xs :< x) = St.[| traverse f xs :< f x |]

  public export
  traverse_ : (a -> St e ()) -> SnocList a -> St e ()
  traverse_ f xs = void $ SnocList.traverse f xs

namespace List1
  public export
  traverse : (a -> St e b) -> List1 a -> St e (List1 b)
  traverse f (x ::: xs) = St.[| f x ::: traverse f xs |]

public export
eval : St s a -> s -> a
eval f = snd . f

public export
run : St s a -> s -> (s, a)
run = id
