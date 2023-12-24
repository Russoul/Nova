module Nova.Surface.Operator

import Data.AlternatingList
import Data.AlternatingList1

import Nova.Core.Name

public export
record Operator where
  constructor MkOperator
  index : Bool
  seq : AlternatingList1 index String Nat
  lvl : Nat

public export
toName : Operator -> VarName
toName (MkOperator k seq lvl) = H (forget seq)
 where
  H : forall k. AlternatingList k String Nat -> VarName
  H (ConsA x rest) = x ++ H rest
  H (ConsB x rest) = "_" ++ H rest
  H [] = ""
