module Solver.CommutativeMonoid.Value

import Data.Fin

public export
Nu : Nat -> Type
Nu n = Fin n -> Nat

infixl 5 .+.

public export
zero : Nu n
zero = const 0

public export
(.+.) : Nu n -> Nu n -> Nu n
(f .+. g) k = f k + g k

