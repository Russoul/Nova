module Solver.CommutativeMonoid.Evaluation

import Data.Fin

import Solver.CommutativeMonoid.Language
import Solver.CommutativeMonoid.Value

kronecker : Fin n -> Fin n -> Nat
kronecker i j with (i == j)
 kronecker i j | True = 1
 kronecker i j | False = 0

public export
evalAlg : Term (Fin n) -> Nu n
evalAlg (Var k) = kronecker k
evalAlg Zero = zero
evalAlg (Plus x y) = evalAlg x .+. evalAlg y

public export
evalExt : a -> (a -> a -> a) -> Term (Either a (Fin n)) -> (a, Nu n)
evalExt z p (Var (Left x)) = (x, zero)
evalExt z p (Var (Right k)) = (z, kronecker k)
evalExt z p Zero = (z, zero)
evalExt z p (Plus x y) =
  let (a0, b0) = evalExt z p x
      (a1, b1) = evalExt z p y
  in
      (p a0 a1, b0 .+. b1)
