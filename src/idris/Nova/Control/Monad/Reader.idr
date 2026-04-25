module Nova.Control.Monad.Reader

Reader r a = r -> a

export
(>>=) : Reader r a -> (a -> Reader r b) -> Reader r b
(f >>= alpha) x = alpha (f x) x

%inline
export
(>>) : Reader r () -> Reader r b -> Reader r b
x >> y = x >>= const y

export
(<$>) : (a -> b) -> Reader r a -> Reader r b
f <$> x = f . x

%inline
export
(<$) : b -> Reader r a -> Reader r b
x <$ a = const x <$> a

export
(<*>) : Reader r (a -> b) -> Reader r a -> Reader r b
(f <*> x) i = f i (x i)

%inline
export
(<*) : Reader r b -> Reader r a -> Reader r b
b <* a = const <$> b <*> a

%inline export
pure : a -> Reader r a
pure x = const x

%inline export
read : Reader r r
read = id

namespace List
  export
  traverse : (a -> Reader r b) -> List a -> Reader r (List b)
  traverse f [] = Reader.[| [] |]
  traverse f (x :: xs) = Reader.[| f x :: traverse f xs |]

  %inline
  export
  for : List a -> (a -> Reader r b) -> Reader r (List b)
  for = flip traverse
