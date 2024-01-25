module Solver.CommutativeMonoid.Quotation

import Data.Fin

import Solver.CommutativeMonoid.Language
import Solver.CommutativeMonoid.Value

public export
quoteAlg : {n : _} -> Nu n -> Term (Fin n)
quoteAlg f = sum (\i => mult (f i) (Var i))

public export
quoteExt : {n : _} -> a -> (a -> a -> a) -> (a, Nu n) -> Term (Either a (Fin n))
quoteExt z p (a, b) = Plus (Var (Left a)) (map Right (quoteAlg b))
