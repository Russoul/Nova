module Data.AlternatingList1

import Data.AlternatingList

public export
data AlternatingList1 : Bool -> Type -> Type -> Type where
  ConsA : a -> AlternatingList False a b -> AlternatingList1 True a b
  ConsB : b -> AlternatingList True a b -> AlternatingList1 False a b

public export
Bifunctor (AlternatingList1 k) where
  bimap f g (ConsA x xs) = ConsA (f x) (bimap f g xs)
  bimap f g (ConsB x xs) = ConsB (g x) (bimap f g xs)

public export
Show a => Show b => Show (AlternatingList1 k a b) where
  show (ConsA x xs) = "ConsA(\{show x}, \{show xs})"
  show (ConsB x xs) = "ConsB(\{show x}, \{show xs})"

public export
forget : AlternatingList1 k a b -> AlternatingList k a b
forget (ConsA x xs) = ConsA x xs
forget (ConsB x xs) = ConsB x xs

public export
consA : a -> AlternatingList1 False a b -> AlternatingList1 True a b
consA x xs = ConsA x (forget xs)

public export
consB : b -> AlternatingList1 True a b -> AlternatingList1 False a b
consB x xs = ConsB x (forget xs)

public export
cons : {k : _} -> (case k of False => a; True => b) -> AlternatingList1 k a b -> AlternatingList1 (not k) a b
cons {k = False} x list = consA x list
cons {k = True} x list = consB x list
