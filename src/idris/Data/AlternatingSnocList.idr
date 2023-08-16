module Data.AlternatingSnocList

import Data.AlternatingList

public export
data AlternatingSnocList : Bool -> Type -> Type -> Type where
  SnocA : AlternatingSnocList False a b -> a -> AlternatingSnocList True a b
  SnocB : AlternatingSnocList True a b -> b -> AlternatingSnocList False a b
  Lin : AlternatingSnocList k a b

public export
Bifunctor (AlternatingSnocList k) where
  bimap f g (SnocA xs x) = SnocA (bimap f g xs) (f x)
  bimap f g (SnocB xs x) = SnocB (bimap f g xs) (g x)
  bimap f g [<] = [<]

public export
Show a => Show b => Show (AlternatingSnocList k a b) where
  show (SnocA xs x) = "SnocA(\{show xs}, \{show x})"
  show (SnocB xs x) = "SnocB(\{show xs}, \{show x})"
  show [<] = "[<]"

public export
(<>>) : {k : _} -> AlternatingSnocList k a b -> AlternatingList (not k) a b -> (k ** AlternatingList k a b)
[<] <>> list = (_ ** list)
SnocA xs x <>> list = xs <>> ConsA x list
SnocB xs x <>> list = xs <>> ConsB x list

public export
toList : AlternatingSnocList k a b -> (k ** AlternatingList k a b)
toList (SnocA xs x) = xs <>> ConsA x []
toList (SnocB xs x) = xs <>> ConsB x []
toList [<] = (True ** [])
