module Data.AlternatingSnocList1

import Data.AlternatingSnocList
import Data.AlternatingList
import Data.AlternatingList1

public export
data AlternatingSnocList1 : Bool -> Type -> Type -> Type where
  SnocA : AlternatingSnocList False a b -> a -> AlternatingSnocList1 True a b
  SnocB : AlternatingSnocList True a b -> b -> AlternatingSnocList1 False a b

public export
Bifunctor (AlternatingSnocList1 k) where
  bimap f g (SnocA xs x) = SnocA (bimap f g xs) (f x)
  bimap f g (SnocB xs x) = SnocB (bimap f g xs) (g x)

public export
Show a => Show b => Show (AlternatingSnocList1 k a b) where
  show (SnocA xs x) = "SnocA(\{show xs}, \{show x})"
  show (SnocB xs x) = "SnocB(\{show xs}, \{show x})"

public export
forget : AlternatingSnocList1 k a b -> AlternatingSnocList k a b
forget (SnocA xs x) = SnocA xs x
forget (SnocB xs x) = SnocB xs x

public export
(<>>) : {k : _} -> AlternatingSnocList k a b -> AlternatingList1 (not k) a b -> (k ** AlternatingList1 k a b)
[<] <>> list = (_ ** list)
SnocA xs x <>> list = xs <>> cons x list
SnocB xs x <>> list = xs <>> cons x list

public export
toList1 : AlternatingSnocList1 k a b -> (k ** AlternatingList1 k a b)
toList1 (SnocA xs x) = xs <>> ConsA x []
toList1 (SnocB xs x) = xs <>> ConsB x []
