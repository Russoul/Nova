module Data.AlternatingList

public export
data AlternatingList : Bool -> Type -> Type -> Type where
  ConsA : a -> AlternatingList False a b -> AlternatingList True a b
  ConsB : b -> AlternatingList True a b -> AlternatingList False a b
  Nil : AlternatingList k a b

public export
Bifunctor (AlternatingList k) where
  bimap f g (ConsA x xs) = ConsA (f x) (bimap f g xs)
  bimap f g (ConsB x xs) = ConsB (g x) (bimap f g xs)
  bimap f g [] = []

public export
Show a => Show b => Show (AlternatingList k a b) where
  show (ConsA x xs) = "ConsA(\{show x}, \{show xs})"
  show (ConsB x xs) = "ConsB(\{show x}, \{show xs})"
  show [] = "[]"
