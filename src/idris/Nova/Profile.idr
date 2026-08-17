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

||| NOVA_SURVEY=1: migration-survey mode. Elaboration (a) does not
||| enforce the type-exposure whitelist — it only LOGS what each
||| item's whitelist would need (`unf <module>:<item>|<name>` labels) —
||| and (b) continues past obligation-laden or failing modules so one
||| run maps a whole corpus. Without it, the whitelist is enforced and
||| a failing module hard-gates the run.
export
surveyMode : Bool
surveyMode = unsafePerformIO (map isJust (getEnv "NOVA_SURVEY"))

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

||| Blocked-exposure names at the CURRENT site, so error hints can
||| name the missing `.unfold` citations. Same below-trust discipline
||| as `slots`; drained by the hint reader.
export
blockedExposures : IORef (List String)
blockedExposures = unsafePerformIO $ do
  -- distinct do-block ON PURPOSE: the Chez backend deduplicates
  -- syntactically identical nullary CAFs (see the nfCaches incident),
  -- and a bare `newIORef []` here would SHARE `slots`' ref
  r <- newIORef (the (List String) [])
  writeIORef r (the (List String) [])
  pure r

||| Record a blocked exposure, returning `x` unchanged.
export
noteBlocked : String -> (x : a) -> a
noteBlocked n x = unsafePerformIO $ do
  ns <- readIORef blockedExposures
  when (not (elem n ns)) (writeIORef blockedExposures (n :: ns))
  pure x

||| Drain the blocked-exposure names (call at an error site).
export
drainBlocked : () -> List String
drainBlocked () = unsafePerformIO $ do
  ns <- readIORef blockedExposures
  writeIORef blockedExposures (the (List String) [])
  pure (reverse ns)

||| Read the blocked-exposure set without clearing (obligation hints —
||| several obligations in one item share the notes).
export
peekBlocked : () -> List String
peekBlocked () = unsafePerformIO (map reverse (readIORef blockedExposures))

||| Clear the blocked-exposure set, returning `x` unchanged — called
||| at item start so one item's notes never annotate another's error.
export
clearBlocked : (x : a) -> a
clearBlocked x = unsafePerformIO $ do
  writeIORef blockedExposures (the (List String) [])
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
