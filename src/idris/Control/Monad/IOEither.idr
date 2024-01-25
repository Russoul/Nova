module Control.Monad.IOEither

public export
(>>=) : IO (Either e a) -> (a -> IO (Either e b)) -> IO (Either e b)
(f >>= g) = Prelude.do
  case !f of
    Left e => io_pure (Left e)
    Right x => g x

public export
pure : a -> IO (Either e a)
pure x = io_pure (Right x)
