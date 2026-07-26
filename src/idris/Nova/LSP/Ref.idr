module Nova.LSP.Ref

import Data.IORef

||| Label-indexed mutable reference — the server's global state is one
||| of these, threaded implicitly via an `auto` implicit rather than
||| passed explicitly through every handler.
public export
data Ref : (l : label) -> Type -> Type where
     [search l]
     MkRef : IORef a -> Ref x a

export
newRef : (x : label) -> t -> IO (Ref x t)
newRef x val = do
  ref <- newIORef val
  pure (MkRef ref)

export %inline
get : (x : label) -> {auto ref : Ref x a} -> IO a
get x {ref = MkRef io} = readIORef io

export %inline
put : (x : label) -> {auto ref : Ref x a} -> a -> IO ()
put x {ref = MkRef io} val = writeIORef io val

export %inline
update : (x : label) -> {auto ref : Ref x a} -> (a -> a) -> IO ()
update x f = do
  v <- get x
  put x (f v)

export %inline
gets : (l : label) -> Ref l a => (a -> b) -> IO b
gets l f = f <$> get l
