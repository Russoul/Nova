module Nova.Kernel.NfCache

-- Normal forms of signature DEFINITIONS, memoised by name.
--
-- Both normalisers — Nova.Kernel.Beta's betaElem and Nova.Kernel's
-- kElem — unfold a definition by δ and then re-normalise its whole
-- body. At a top-level item the declaration context is empty, so the
-- spine is empty and the substitution is the identity: the call
-- recomputes nf(body) from scratch, every time the name is mentioned.
--
-- A definition's body mentions only earlier entries and names are
-- module-qualified, so nf(body) is stable — for as long as Σ is only
-- EXTENDED. It is not: the elaborator flips a SigDecl (stuck hole) to a
-- SigDef when a hole is solved, and constraint deletion rebuilds Σ, at
-- which point a cached form may mention a name whose meaning changed.
-- `resetNfCaches` is called at exactly those sites.
--
-- The two normalisers keep separate tables: they agree on results but
-- are different algorithms (kElem is fuel-bounded inside KM), and
-- nothing here should make one depend on the other.
--
-- This is measurement-driven scaffolding on the research branch, and it
-- puts unsafePerformIO on the trusted path. The principled version
-- stores the normal form ON the Σ entry, where it is immutable by
-- construction and needs no invalidation; see docs/PerfNotes.md.

import Data.IORef
import Data.SortedMap

import Nova.Kernel.Syntax

%default covering

export
betaElemNf : IORef (SortedMap String Elem)
betaElemNf = unsafePerformIO (newIORef empty)

export
betaTyNf : IORef (SortedMap String Ty)
betaTyNf = unsafePerformIO (newIORef empty)

export
kElemNf : IORef (SortedMap String Elem)
kElemNf = unsafePerformIO (newIORef empty)

export
kTyNf : IORef (SortedMap String Ty)
kTyNf = unsafePerformIO (newIORef empty)

||| Look a name up; Nothing if it has not been normalised yet.
export
nfLookup : IORef (SortedMap String a) -> String -> Maybe a
nfLookup ref x = unsafePerformIO $ do
  m <- readIORef ref
  pure (lookup x m)

||| Record a normal form, returning the value handed in.
export
nfInsert : IORef (SortedMap String a) -> String -> (v : a) -> a
nfInsert ref x v = unsafePerformIO $ do
  modifyIORef ref (insert x v)
  pure v

||| Memoise a lazily-supplied normal form under `x`.
export
nfMemo : IORef (SortedMap String a) -> String -> (Lazy a) -> a
nfMemo ref x v =
  case nfLookup ref x of
    Just w => w
    Nothing => nfInsert ref x (force v)

||| Drop every table, returning the value handed in. Called wherever Σ
||| changes non-monotonically.
export
resetNfCaches : (x : a) -> a
resetNfCaches x = unsafePerformIO $ do
  writeIORef betaElemNf empty
  writeIORef betaTyNf empty
  writeIORef kElemNf empty
  writeIORef kTyNf empty
  pure x
