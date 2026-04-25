module Nova.Control.Monad.Id

import Data.List1

Id a = a

%inline
export
(>>=) : Id a -> (a -> Id b) -> Id b
x >>= f = f x

%inline
export
(>>) : Id () -> Id b -> Id b
x >> y = x >>= const y

%inline
export
(<$>) : (a -> b) -> Id a -> Id b
f <$> x = f x

%inline
export
(<$) : b -> Id a -> Id b
x <$ a = const x <$> a

%inline
export
(<*>) : Id (a -> b) -> Id a -> Id b
f <*> x = f x

%inline
export
(<*) : Id b -> Id a -> Id b
b <* a = const <$> b <*> a

%inline export
pure : a -> Id a
pure = id

%inline export
and : Id Bool -> Lazy (Id Bool) -> Id Bool
and True y = y
and False _ = False

infixl 0 `and`

namespace List
  %inline
  export
  traverse : (a -> Id b) -> List a -> Id (List b)
  traverse = Prelude.map

  %inline
  export
  for : List a -> (a -> Id b) -> Id (List b)
  for = flip Prelude.map

namespace List1
  %inline
  export
  traverse : (a -> Id b) -> List1 a -> Id (List1 b)
  traverse = Prelude.map

  %inline
  export
  for : List1 a -> (a -> Id b) -> Id (List1 b)
  for = flip Prelude.map
