module Data.Util

import Data.Nat
import Data.Fin
import Data.Fin.Extra
import Data.List
import Data.Vect
import Data.SnocList
import Data.String
import Data.Maybe

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

||| Used to avoid unification by coercing (by induction on an equality proof)
||| a value of type `a` to a value of type `b`, the latter is
||| normally expected to be inferred by the type checker.
public export
ford : (0 _ : a = b) -> a -> b
ford Refl x = x

infixr 5 :+:
||| Infix version of `Either`.
public export
(:+:) : Type -> Type -> Type
a :+: b = Either a b

infixl 5 .+.
||| (f .+. g)(i) = f(i), if 0 ≤ i < a
||| (f .+. g)(i) = g(i), if a ≤ i < a + b
public export
(.+.) : {a, b : _}
     -> (sub : Fin a -> c)
     -> (notSub : Fin b -> c)
     -> (Fin (a + b) -> c)
(f .+. g) = either f g . splitSum

-- A few named interface implementations:

namespace Eq
  public export
  [ByFst]
  Eq k => Eq (k, v) where
    (k, v) == (k', v') = k == k'

namespace Ord
  public export
  [ByFst]
  Ord k => Ord (k, v) using Eq.ByFst where
    compare (k, v) (k', v') = compare k k'

namespace Eq
  public export
  [BySnd]
  Eq v => Eq (k, v) where
    (k, v) == (k', v') = v == v'

namespace Ord
  public export
  [BySnd]
  Ord v => Ord (k, v) using Eq.BySnd where
    compare (k, v) (k', v') = compare v v'

namespace Eq
  public export
  [BySndOutOfThree]
  Eq k => Eq (a, k, b) where
    (_, k, _) == (_, k', _) = k == k'

namespace Functor
  public export
  [List] Functor List where
    map f [] = []
    map f (x :: xs) = f x :: map f xs

namespace Ord
  public export
  [BySndOutOfThree]
  Ord k => Ord (a, k, b) using Eq.BySndOutOfThree where
    compare (_, k, _) (_, k', _) = compare k k'

namespace Show
  public export
  [Either] Show a => Show b => Show (Either a b) where
    show (Left x) = "Left " ++ "(" ++ show x ++ ")"
    show (Right x) = "Right " ++ "(" ++ show x ++ ")"

  namespace Str
    public export
    [Id]
    Show String where
      show x = x

  export
  [Pair]
  (Show a, Show b) => Show (a, b) where
    show (x, y) = "(" ++ show x ++ ", " ++ show y ++ ")"

  public export
  [CommaSepList]
  (inner : Show a) => Show (List a) where
    show []        = "[]"
    show (x :: xs) = "[" ++ show x ++ show' xs ++ "]"
     where
      show' : List a -> String
      show' []        = ""
      show' (x :: xs) = show' xs ++ ", " ++ show x

  public export
  [NLSepList]
  (inner : Show a) => Show (List a) where
    show []        = ""
    show (x :: xs) = show x ++ show' xs
     where
      show' : List a -> String
      show' []        = ""
      show' (x :: xs) = "\n" ++ show x ++ show' xs

  public export
  [NLSepSnocList]
  (inner : Show a) => Show (SnocList a) where
    show [<]        = ""
    show (xs :< x) = show' xs ++ show x
     where
      show' : SnocList a -> String
      show' [<]        = ""
      show' (xs :< x) = show' xs ++ show x ++ "\n"

||| Split an input into word-sized `Doc`.
export
words : String -> List (Doc ann)
words s = map pretty $ map pack (helper (unpack s))
  where
    helper : List Char -> List (List Char)
    helper s =
      case dropWhile isSpace s of
           [] => []
           s' => let (w, s'') = break isSpace s' in
                     w :: helper (assert_smaller s s'')

||| Insert soft line-breaks between words, so that text is broken down into multiple
||| lines when it exceeds the available width.
export
reflow : String -> Doc ann
reflow = fillSep . words

namespace SnocList
-- TODO PR to Idris2
-- TODO: Ordering doesn't make sense: we should order elements right-to-left in a SnocList.
-- NOTE: Or does it? I think Ohad has actually set up the Prelude's SnocList operations to
-- NOTE: act left-to-right ??
public export
quicksortBy : (a -> a -> Bool) -> SnocList a -> SnocList a
quicksortBy o [<] = [<]
quicksortBy o (xs :< x) =
 let smaller  = filter (not . o x) xs
     bigger   = filter       (o x) xs
     left     = quicksortBy o smaller
     right    = quicksortBy o bigger in
     left :< x ++ right

public export
quicksort : Ord a => SnocList a -> SnocList a
quicksort xs = quicksortBy (<) xs

namespace List
  public export
  foldlM : Monad m => List a -> acc -> (acc -> a -> m acc) -> m acc
  foldlM [] acc f = pure acc
  foldlM (x :: xs) acc f = foldlM xs !(f acc x) f

  public export
  foldlM_ : Monad m => List a -> acc -> (acc -> a -> m acc) -> m ()
  foldlM_ xs acc f = ignore $ foldlM xs acc f

  public export
  foldrM : Monad m => List a -> acc -> (a -> acc -> m acc) -> m acc
  foldrM [] acc f = pure acc
  foldrM (x :: xs) acc f = f x !(foldrM xs acc f)

  public export
  foldrM_ : Monad m => List a -> acc -> (a -> acc -> m acc) -> m ()
  foldrM_ xs acc f = ignore $ foldrM xs acc f

namespace SnocList
  public export
  zip : SnocList a -> SnocList b -> SnocList (a, b)
  zip [<] ys = [<]
  zip xs [<] = [<]
  zip (xs :< x) (ys :< y) = zip xs ys :< (x, y)

  public export
  lookupBy : (a -> a -> Bool) -> a -> SnocList (a, b) -> Maybe b
  lookupBy eq x [<] = Nothing
  lookupBy eq x (ls :< (l, v)) = case eq x l of
    True => Just v
    False => lookupBy eq x ls

  public export
  lookup : Ord a => a -> SnocList (a, b) -> Maybe b
  lookup x [<] = Nothing
  lookup x (ls :< (l, v)) = case x == l of
    True => Just v
    False => lookup x ls

  public export
  mbIndex : Nat -> (xs : SnocList a) -> Maybe (SnocList a, a, Fin (length xs))
  mbIndex _ [<] = Nothing
  mbIndex Z (xs :< x) = Just (xs, x, FZ)
  mbIndex (S k) (xs :< x) = map (mapSnd (mapSnd FS)) (mbIndex k xs)

namespace List
  public export
  zipEven : List a -> List b -> Maybe (List (a, b))
  zipEven [] [] = Just []
  zipEven (x :: xs) (y :: ys) = do
    rest <- zipEven xs ys
    Just ((x, y) :: rest)
  zipEven {} = Nothing

public export
toSnocListH : Vect n a -> SnocList a -> SnocList a
toSnocListH [] ys = ys
toSnocListH (x :: xs) ys = toSnocListH xs (ys :< x)

public export
toSnocList : Vect n a -> SnocList a
toSnocList xs = toSnocListH xs [<]

||| A ⊆ B : Set, where lists A, B are viewed modulo ordering and repetition.
public export
impliesAsSets : Eq a => List a -> List a -> Bool
impliesAsSets [] ys = True
impliesAsSets (x :: xs) ys = elem x ys && impliesAsSets xs ys

||| A = B : Set, where lists A, B are viewed modulo ordering and repetition.
public export
equalAsSets : Eq a => List a -> List a -> Bool
equalAsSets xs ys = impliesAsSets xs ys && impliesAsSets ys xs

public export
mbSubscript0to9 : Int -> Maybe String
mbSubscript0to9 0 = Just "₀"
mbSubscript0to9 1 = Just "₁"
mbSubscript0to9 2 = Just "₂"
mbSubscript0to9 3 = Just "₃"
mbSubscript0to9 4 = Just "₄"
mbSubscript0to9 5 = Just "₅"
mbSubscript0to9 6 = Just "₆"
mbSubscript0to9 7 = Just "₇"
mbSubscript0to9 8 = Just "₈"
mbSubscript0to9 9 = Just "₉"
mbSubscript0to9 _ = Nothing

public export
mbSuperscript0to9 : Int -> Maybe String
mbSuperscript0to9 0 = Just "⁰"
mbSuperscript0to9 1 = Just "¹"
mbSuperscript0to9 2 = Just "²"
mbSuperscript0to9 3 = Just "³"
mbSuperscript0to9 4 = Just "⁴"
mbSuperscript0to9 5 = Just "⁵"
mbSuperscript0to9 6 = Just "⁶"
mbSuperscript0to9 7 = Just "⁷"
mbSuperscript0to9 8 = Just "⁸"
mbSuperscript0to9 9 = Just "⁹"
mbSuperscript0to9 _ = Nothing

intToSubscriptH : Int -> String
intToSubscriptH x = fromMaybe "" (mbSubscript0to9 x)

intToSuperscriptH : Int -> String
intToSuperscriptH x = fromMaybe "" (mbSuperscript0to9 x)

||| Assume that the Int is non-negative.
public export
intToSubscript : Int -> String
intToSubscript x =
  let d = x `div` 10 in
  let m = x `mod` 10 in
  let x = intToSubscriptH m in
  ifThenElse (d == 0) x $
    let xs = intToSubscript d in
    xs ++ x

||| Assume that the Int is non-negative.
public export
intToSuperscript : Int -> String
intToSuperscript x =
  let d = x `div` 10 in
  let m = x `mod` 10 in
  let x = intToSuperscriptH m in
  ifThenElse (d == 0) x $
    let xs = intToSuperscript d in
    xs ++ x

public export
natToSubscript : Nat -> String
natToSubscript x = intToSubscript (cast x)

public export
natToSuperscript : Nat -> String
natToSuperscript x = intToSuperscript (cast x)

public export
natSubscript : Nat -> Doc ann
natSubscript x = pretty (natToSubscript x)

public export
natSuperscript : Nat -> Doc ann
natSuperscript x = pretty (natToSuperscript x)

||| (k + n - 1) ... (k + 2) (k + 1) k
public export
countUp : (n : Nat) -> (k : Nat) -> SnocList Nat
countUp Z _ = [<]
countUp (S k) acc = countUp k (S acc) :< acc

||| inverse of (:<)
public export
unsnoc : SnocList a -> (SnocList a, Maybe a)
unsnoc [<] = ([<], Nothing)
unsnoc (xs :< x) = (xs, Just x)

public export
zipWithConst : a -> List b -> List (a, b)
zipWithConst x [] = []
zipWithConst x (y :: ys) = (x, y) :: zipWithConst x ys

infixl 10 |>
infixl 10 >>>

public export
(|>) : a -> (a -> b) -> b
x |> f = f x

public export
(>>>) : (a -> b) -> (b -> c) -> (a -> c)
f >>> g = g . f

public export
pulloutMaybe : (Maybe a, Maybe b) -> Maybe (a, b)
pulloutMaybe (Just x, Just y) = Just (x, y)
pulloutMaybe _ = Nothing

||| Zips two lists together, records the leftovers.
public export
level : List a -> List b -> (List (a, b), Maybe (Either (List1 a) (List1 b)))
level [] [] = ([], Nothing)
level [] (y :: ys) = ([], Just (Right (y ::: ys)))
level (x :: xs) [] = ([], Just (Left (x ::: xs)))
level (x :: xs) (y :: ys) =
  mapFst ((x, y) ::) (level xs ys)

infixl 5 |.|

public export
(|.|) : (a -> Bool) -> (a -> Bool) -> (a -> Bool)
(f |.| g) x = f x || g x

||| A̅ → B
public export
NAryFun : List Type -> Type -> Type
NAryFun [] b = b
NAryFun (a :: as) last = a -> NAryFun as last

public export
replicate : Nat -> a -> SnocList a
replicate Z _ = [<]
replicate (S k) x = replicate k x :< x

public export
splitAt' : Nat -> List a -> Maybe (List a, List a)
splitAt' Z rest = Just ([], rest)
splitAt' (S k) [] = Nothing
splitAt' (S k) (x :: xs) = map (mapFst (x ::)) (splitAt' k xs)

-- Seriously?
public export
Semigroup Nat where
  x <+> y = x + y

public export
Monoid Nat where
  neutral = 0

public export
dedupBy : (a -> a -> Bool) -> List1 a -> List1 a
dedupBy f (a ::: (b :: cs)) = if f a b then dedupBy f (b ::: cs) else a `cons` dedupBy f (b ::: cs)
dedupBy f (a ::: [])         = a ::: []

||| Remove duplicate elements from a list using a custom comparison. The general
||| case of `nub`.
||| O(n^2).
|||
||| @ p  a custom comparison for detecting duplicate elements
||| @ xs the list to remove the duplicates from
public export
nubBy : (p : a -> a -> Bool) -> (xs : List1 a) -> List1 a
nubBy p (x ::: list) = insertFresh x (nubBy p list)
 where
  insertFresh : a -> List a -> List1 a
  insertFresh x [] = singleton x
  insertFresh x (y :: zs) =
    case p x y of
      True => insertFresh x zs
      False => y `cons` insertFresh x zs

zipWithIndexH : List a -> Nat -> List (a, Nat)
zipWithIndexH [] _ = []
zipWithIndexH (x :: xs) i = (x, i) :: zipWithIndexH xs (S i)

public export
zipWithIndex : List a -> List (a, Nat)
zipWithIndex xs = zipWithIndexH xs 0

public export
splitAt : SnocList a -> Nat -> Maybe (SnocList a, a, SnocList a)
splitAt [<] _ = Nothing
splitAt (xs :< x) 0 = Just (xs, x, [<])
splitAt (xs :< x) (S n) = do
  (left, center, right) <- splitAt xs n
  pure (left, center, right :< x)

public export
toSnocList1Acc : SnocList a -> List1 a -> (SnocList a, a)
toSnocList1Acc rest (x ::: []) = (rest, x)
toSnocList1Acc rest (x ::: y :: zs) = toSnocList1Acc (rest :< x) (y ::: zs)

public export
toSnocList1 : List1 a -> (SnocList a, a)
toSnocList1 list = toSnocList1Acc [<] list
