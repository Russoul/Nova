module Solver.CommutativeMonoid.Language

import Data.Fin
import Data.List1

public export
data Term : Type -> Type where
  Var : x -> Term x
  Zero : Term x
  Plus : Term x -> Term x -> Term x
  -- 0 + x = x
  -- x + 0 = x
  -- x + (y + z) = (x + y) + z
  -- x + y = y + x

public export
Functor Term where
  map f (Var x) = Var (f x)
  map f Zero = Zero
  map f (Plus x y) = Plus (map f x) (map f y)


-- n     * t
-- 0     * t = Z
-- (S k) * t = t + k * t
public export
mult : Nat -> Term (Fin n) -> Term (Fin n)
mult Z t = Zero
mult (S n) t = Plus t (mult n t)

namespace Fin
  public export
  sum : {n : _} -> (Fin n -> Term (Fin n)) -> Term (Fin n)
  sum = go n
   where
    go : (k : Nat) -> (Fin k -> Term (Fin n)) -> Term (Fin n)
    go 0 f = Zero
    go (S k) f = Plus (f FZ) (go k (f . FS))

namespace List1
  public export
  sum : List1 (Term (Fin n)) -> Term (Fin n)
  sum (t ::: []) = t
  sum (t ::: (q :: qs)) = sum (Plus t q ::: qs)

