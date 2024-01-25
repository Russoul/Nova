module Solver.CommutativeMonoid.Normalisation

import Data.Fin

import Solver.CommutativeMonoid.Evaluation
import Solver.CommutativeMonoid.Language
import Solver.CommutativeMonoid.Quotation
import Solver.CommutativeMonoid.Value

public export
normaliseAlg : {n : _} -> Term (Fin n) -> Term (Fin n)
normaliseAlg = quoteAlg . evalAlg

public export
normaliseExt : {n : _} -> a -> (a -> a -> a) -> Term (Either a (Fin n)) -> Term (Either a (Fin n))
normaliseExt z p = quoteExt z p . evalExt z p
