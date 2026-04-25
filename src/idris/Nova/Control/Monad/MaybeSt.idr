module Nova.Control.Monad.MaybeSt

import Nova.Control.Monad.Id
import Nova.Control.Monad.St
import Data.List1
import Data.Vect

MaybeSt s a = s -> Maybe (s, a)

public export
(>>=) : MaybeSt s a -> (a -> MaybeSt s b) -> MaybeSt s b
(f >>= g) i =
  case f i of
    Just (i, x) => g x i
    Nothing => Nothing

public export
(=<<) : (a -> MaybeSt s b) -> MaybeSt s a -> MaybeSt s b
(=<<) = flip (>>=)

public export
(>>) : MaybeSt s () -> MaybeSt s a -> MaybeSt s a
f >> g = with [MaybeSt.(>>=)]
 f >>= const g

public export
(<$>) : (a -> b) -> MaybeSt s a -> MaybeSt s b
(f <$> t) i =
  case t i of
    Just (i, x) => Just (i, f x)
    Nothing => Nothing

%inline
public export
(<$) : b -> MaybeSt s a -> MaybeSt s b
(v <$ t) = with [MaybeSt.(<$>)] const v <$> t

public export
(<&>) : MaybeSt s a -> (a -> b) -> MaybeSt s b
(<&>) = flip MaybeSt.(<$>)

public export
(<=<) : (b -> MaybeSt s c) -> (a -> MaybeSt s b) -> a -> MaybeSt s c
(f <=< g) x = g x >>= f

public export
pure : a -> MaybeSt s a
pure x i = Just (i, x)

public export
unit : MaybeSt s ()
unit i = Just (i, ())

%inline
void : MaybeSt s a -> MaybeSt s ()
void = with [MaybeSt.(<$)] (() <$)

%inline
ignore : MaybeSt s a -> MaybeSt s ()
ignore = with [MaybeSt.(<$)] (() <$)

public export
(<*>) : MaybeSt s (a -> b) -> MaybeSt s a -> MaybeSt s b
(f <*> x) i =
  let Just (i, func) = f i
       | Nothing => Nothing
  in
  let Just (i, val) = x i
       | Nothing => Nothing
  in
  Just (i, func val)

public export
get : MaybeSt s s
get i = Just (i, i)

public export
put : s -> MaybeSt s ()
put i _ = Just (i, ())

public export
update : (s -> s) -> MaybeSt s ()
update f i = Just (f i, ())

public export
when : Bool -> MaybeSt s () -> MaybeSt s ()
when False _ = MaybeSt.pure ()
when True x = x

public export
liftSt : St s a -> MaybeSt s a
liftSt e i = Just (e i)

public export
liftId : Id a -> MaybeSt s a
liftId = MaybeSt.pure

namespace Maybe
  public export
  traverse : (a -> MaybeSt e b) -> Maybe a -> MaybeSt e (Maybe b)
  traverse f Nothing = MaybeSt.[| Nothing |]
  traverse f (Just x) = MaybeSt.[| Just (f x) |]

namespace List
  public export
  sequence : List (MaybeSt e a) -> MaybeSt e (List a)
  sequence [] = MaybeSt.pure []
  sequence (f :: fs) = MaybeSt.[| f :: sequence fs |]

  public export
  traverse : (a -> MaybeSt e b) -> List a -> MaybeSt e (List b)
  traverse f [] = MaybeSt.pure []
  traverse f (x :: xs) = MaybeSt.[| f x :: traverse f xs |]

  %inline
  public export
  for : List a -> (a -> MaybeSt e b) -> MaybeSt e (List b)
  for = flip traverse

  %inline
  public export
  for_ : List a -> (a -> MaybeSt e b) -> MaybeSt e ()
  for_ = MaybeSt.ignore .: List.for

namespace Vect
  public export
  sequence : Vect n (MaybeSt e a) -> MaybeSt e (Vect n a)
  sequence [] = MaybeSt.pure []
  sequence (f :: fs) = MaybeSt.[| f :: sequence fs |]

  public export
  traverse : (a -> MaybeSt e b) -> Vect n a -> MaybeSt e (Vect n b)
  traverse f [] = MaybeSt.pure []
  traverse f (x :: xs) = MaybeSt.[| f x :: traverse f xs |]

  public export
  traverse_ : (a -> MaybeSt e ()) -> List a -> MaybeSt e ()
  traverse_ f xs = void $ List.traverse f xs

namespace SnocList
  public export
  sequence : SnocList (MaybeSt e a) -> MaybeSt e (SnocList a)
  sequence [<] = MaybeSt.pure [<]
  sequence (fs :< f) = MaybeSt.[| sequence fs :< f |]

  public export
  traverse : (a -> MaybeSt e b) -> SnocList a -> MaybeSt e (SnocList b)
  traverse f [<] = MaybeSt.pure [<]
  traverse f (xs :< x) = MaybeSt.[| traverse f xs :< f x |]

  public export
  traverse_ : (a -> MaybeSt e ()) -> SnocList a -> MaybeSt e ()
  traverse_ f xs = void $ SnocList.traverse f xs

namespace List1
  public export
  traverse : (a -> MaybeSt e b) -> List1 a -> MaybeSt e (List1 b)
  traverse f (x ::: xs) = MaybeSt.[| f x ::: traverse f xs |]

public export
eval : MaybeSt s a -> s -> Maybe a
eval f = map snd . f

public export
run : MaybeSt s a -> s -> Maybe (s, a)
run = id
