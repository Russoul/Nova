module Nova.Profile

-- MEASUREMENT SCAFFOLDING (research-performance branch).
--
-- The elaborator is pure (ElabM is a state monad over Either), so there
-- is no IO to hang timers on. This module provides the minimum: a
-- monotonic clock read behind unsafePerformIO, and a global nanosecond
-- accumulator per label, dumped at the end of a run.
--
-- Not part of the trusted path: nothing here is consulted by the
-- kernel, and `bump` is identity on its value argument.

import Data.IORef
import Data.List
import System.Clock
import System

%default covering

||| Monotonic nanoseconds. The () argument defeats CAF sharing — a
||| nullary top-level would be evaluated once and reused.
export
nowNs : () -> Integer
nowNs () = unsafePerformIO $ do
  t <- clockTime Monotonic
  pure (seconds t * 1000000000 + nanoseconds t)

export
slots : IORef (List (String, (Integer, Integer)))
slots = unsafePerformIO (newIORef [])

add : String -> Integer -> List (String, (Integer, Integer)) -> List (String, (Integer, Integer))
add k d [] = [(k, (1, d))]
add k d ((k', (n, t)) :: rest) =
  if k == k' then (k', (n + 1, t + d)) :: rest else (k', (n, t)) :: add k d rest

||| Record `d` nanoseconds against `label`, returning `x` unchanged.
export
bump : String -> Integer -> (x : a) -> a
bump label d x = unsafePerformIO $ do
  modifyIORef slots (add label d)
  pure x

||| Printed only under NOVA_PROFILE=1, so ordinary runs are unchanged.
export
dumpProfile : IO ()
dumpProfile = do
  Just _ <- getEnv "NOVA_PROFILE"
    | Nothing => pure ()
  xs <- readIORef slots
  let tot = sum (map (\(_, (_, t)) => t) xs)
  putStrLn "--- profile (ns) ---"
  traverse_ (\(k, (n, t)) =>
      putStrLn "\{k}: calls=\{show n} ms=\{show (t `div` 1000000)} raw=\{show t}")
    (sortBy (\(_, (_, a)), (_, (_, b)) => compare b a) xs)
  putStrLn "total accounted ms=\{show (tot `div` 1000000)}"
