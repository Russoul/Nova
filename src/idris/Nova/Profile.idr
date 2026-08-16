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
import Data.Maybe
import System.Clock
import System
import System.File

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

||| THE SEARCHLESS DEFAULT (SearchlessElaboration.md §5.3, now the
||| semantics of docs/NovaElaboration.txt): an item without a `using`
||| clause elaborates with an EMPTY Σ-scope — its discharges see
||| hypotheses and computation only, and store use must be named.
||| NOVA_GLOBAL_STORE=1 restores the historical prior-free search over
||| the whole store, as a migration escape hatch. Read once per
||| process; a mode, not a trusted-path concern (scoping only ever
||| removes candidates, and every discharge is kernel-replayed either
||| way).
export
scopedMode : Bool
scopedMode = unsafePerformIO (map isNothing (getEnv "NOVA_GLOBAL_STORE"))

||| STRICT-CONVERSION SURVEY MODE (NOVA_STRICT_CONV=1): the engine
||| discharges only modulo α + the computational rules (+ named
||| whole-equation matching, Prf-irrelevance, and structural
||| congruence finals) — no δ on equation sides, no η, no hops, no
||| positional rewriting. Head exposure of TYPES keeps δ, logged per
||| module (`unf <module>|<name>` labels) as the future per-item
||| `using`-unfold whitelist survey. Everything that falls outside the
||| subset surfaces as an obligation — the migration fallout map. A
||| mode below the trust boundary: the kernel path is unchanged.
export
strictConv : Bool
strictConv = unsafePerformIO (map isJust (getEnv "NOVA_STRICT_CONV"))

||| Print an audit line to stderr under NOVA_AUDIT=1, returning `x`
||| unchanged — the scope-migration survey hook (which discharge sites
||| consume which Σ-lemmas), same non-trusted-path discipline as bump.
export
audit : String -> (x : a) -> a
audit line x = unsafePerformIO $ do
  Just _ <- getEnv "NOVA_AUDIT"
    | Nothing => pure x
  _ <- fPutStrLn stderr line
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
