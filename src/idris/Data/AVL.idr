module Data.AVL

import Data.Nat
import Data.Maybe
import Data.SnocList
import Data.List.Lazy

import public Data.Util

-- Original source is a haskell implementation:
-- https://gist.github.com/timjb/8292342

%hide Prelude.ord

data Balance = MinusOne | Zero | PlusOne

infixl 5 `unite`

public export
Eq Balance where
  MinusOne == MinusOne = True
  Zero == Zero = True
  PlusOne == PlusOne = True
  _ == _ = False

data AVLTree k = Empty | Node k Balance (AVLTree k) (AVLTree k)

Foldable AVLTree where
  foldl f init Empty = init
  foldl f init (Node x b l r) = foldl f (f (foldl f init l) x) r

  foldr f init Empty = init
  foldr f init (Node x b l r) = foldr f (f x (foldr f init r)) l

Functor AVLTree where
  map f Empty = Empty
  map f (Node x b l r) = Node (f x) b (map f l) (map f r)

empty : AVLTree k
empty = Empty

singleton : k -> AVLTree k
singleton v = Node v Zero Empty Empty

-- Call to fix an inbalance of -2, returns True if height of root stayed
-- the same
rotateRight : AVLTree k -> (AVLTree k, Bool)
rotateRight (Node u MinusOne (Node v MinusOne ta tb) tc)
  = (Node v Zero ta (Node u Zero tb tc), False)
rotateRight (Node u MinusOne (Node v Zero ta tb) tc)
  = (Node v PlusOne ta (Node u MinusOne tb tc), True)
rotateRight (Node u MinusOne (Node v PlusOne ta (Node w bw tb tc)) td)
  = let b1 = if bw == PlusOne  then MinusOne else Zero
        b2 = if bw == MinusOne then PlusOne  else Zero
    in (Node w Zero (Node v b1 ta tb) (Node u b2 tc td), False)
rotateRight _ = assert_total $ idris_crash "unexpected call of rotateRight"

-- Call to fix an inbalance f 2, returns True if height of root stayed
-- the same
rotateLeft : AVLTree k -> (AVLTree k, Bool)
rotateLeft (Node u PlusOne tc (Node v PlusOne tb ta))
  = (Node v Zero (Node u Zero tc tb) ta, False)
rotateLeft (Node u PlusOne tc (Node v Zero tb ta))
  = (Node v MinusOne (Node u PlusOne tc tb) ta, True)
rotateLeft (Node u PlusOne td (Node v MinusOne (Node w bw tc tb) ta))
  = let b1 = if bw == PlusOne  then MinusOne else Zero
        b2 = if bw == MinusOne then PlusOne  else Zero
    in (Node w Zero (Node u b1 td tc) (Node v b2 tb ta), False)
rotateLeft _ = assert_total $ idris_crash "unexpected call of rotateLeft"

-- returns True if the height increased
insert' : Ord k => k -> AVLTree k -> (AVLTree k, Bool)
insert' v Empty = (Node v Zero Empty Empty, True)
insert' v (Node w b tl tr) = case compare v w of
  EQ => (Node v b tl tr, False)
  LT => let (tl', isHigher) = insert' v tl in case (isHigher, b) of
    (False, _)       => (Node w b tl' tr, False)
    (True, PlusOne)  => (Node w Zero tl' tr, False)
    (True, Zero)     => (Node w MinusOne tl' tr, True)
    (True, MinusOne) => rotateRight (Node w MinusOne tl' tr)
  GT => let (tr', isHigher) = insert' v tr in case (isHigher, b) of
    (False, _)       => (Node w b tl tr', False)
    (True, MinusOne) => (Node w Zero tl tr', False)
    (True, Zero)     => (Node w PlusOne tl tr', True)
    (True, PlusOne)  => rotateLeft (Node w PlusOne tl tr')

||| O(log n)
insert : Ord k => k -> AVLTree k -> AVLTree k
insert v t = fst (insert' v t)

-- returns the maximum element and true if the height decreased
deleteMaximum : Ord k => AVLTree k -> (AVLTree k, Bool, k)
deleteMaximum Empty = assert_total $ idris_crash "unexpected call of deleteMaximum"
deleteMaximum (Node v _ tl Empty) = (tl, True, v)
deleteMaximum (Node w b tl tr) =
  let (tr', isSmaller, v) = deleteMaximum tr in case (isSmaller, b) of
    (False, _)       => (Node w b tl tr', False, v)
    (True, PlusOne)  => (Node w Zero tl tr', True, v)
    (True, Zero)     => (Node w MinusOne tl tr', False, v)
    (True, MinusOne) => let (x, y) = rotateRight (Node w MinusOne tl tr')
                        in  (x, not y, v)


-- returns True if the height decreased
delete' : Ord k => k -> AVLTree k -> (AVLTree k, Bool)
delete' v Empty = (Empty, False)
delete' v (Node w b tl tr) = case compare v w of
  EQ => case tl of
    Empty => (tr, True)
    _     => let (tl', isSmaller, u) = deleteMaximum tl in case (isSmaller, b) of
      (False, _)       => (Node u b tl' tr, False)
      (True, MinusOne) => (Node u Zero tl' tr, True)
      (True, Zero)     => (Node u PlusOne tl' tr, False)
      (True, PlusOne)  => mapSnd not $ rotateLeft (Node u PlusOne tl' tr)
  LT => let (tl', isSmaller) = delete' v tl in case (isSmaller, b) of
    (False, _)       => (Node w b tl' tr, False)
    (True, MinusOne) => (Node w Zero tl' tr, True)
    (True, Zero)     => (Node w PlusOne tl' tr, False)
    (True, PlusOne)  => mapSnd not $ rotateLeft (Node w PlusOne tl' tr)
  GT => let (tr', isSmaller) = delete' v tr in case (isSmaller, b) of
    (False, _)       => (Node w b tl tr', False)
    (True, PlusOne)  => (Node w Zero tl tr', True)
    (True, Zero)     => (Node w MinusOne tl tr', False)
    (True, MinusOne) => mapSnd not $ rotateRight (Node w MinusOne tl tr')

||| O(log n)
delete : Ord k => k -> AVLTree k -> AVLTree k
delete v t = fst (delete' v t)

||| Length of the deepest path in the tree.
||| O(n)
depth : AVLTree k -> Nat
depth Empty = 0
depth (Node _ _ tl tr) = S (max (depth tl) (depth tr))

||| Number of elements in the tree.
lengthH : AVLTree a -> Nat -> Nat
lengthH Empty x = x
lengthH (Node m b left right) x = lengthH left (lengthH right (S x))

||| Total number of elements in the tree.
||| O(n)
length : AVLTree a -> Nat
length t = lengthH t Z

||| O(log n)
projLookup : Ord a' => a' -> (a -> a') -> AVLTree a -> Maybe a
projLookup key f Empty = Nothing
projLookup key f (Node x b left right)
 = case compare key (f x) of
     LT => projLookup key f left
     EQ => Just x
     GT => projLookup key f right

||| O(log n)
lookup : Ord k => k -> AVLTree (k, v) -> Maybe v
lookup key tree = snd <$> projLookup key fst tree

||| Find the first element, if any,
||| for which the predicate holds, traversing
||| the tree in post order.
||| O(n)
findFstPostOrder : (a -> Bool) -> AVLTree a -> Maybe a
findFstPostOrder p Empty = Nothing
findFstPostOrder p (Node m b left right) =
     findFstPostOrder p right
 <|> toMaybe (p m) m
 <|> findFstPostOrder p left

||| Find all elements,
||| for which the predicate holds, traversing
||| the tree in post order.
||| O(n)
findAllPostOrderH : (a -> Bool) -> AVLTree a -> List a -> List a
findAllPostOrderH p Empty acc = acc
findAllPostOrderH p (Node m b left right) acc =
     let acc = findAllPostOrderH p right acc in
     let acc = case p m of
           True => m :: acc
           False => acc in
     findAllPostOrderH p left acc

findAllPostOrder : (a -> Bool) -> AVLTree a -> List a
findAllPostOrder f tree = findAllPostOrderH f tree []

namespace SnocList
  public export
  inorder : AVLTree a -> SnocList a
  inorder Empty = [<]
  inorder (Node x b l r) = (inorder l :< x) ++ inorder r

namespace List
  public export
  inorder : AVLTree a -> List a
  inorder Empty = []
  inorder (Node x b l r) = inorder l ++ (x :: inorder r)

  public export
  preorder : AVLTree a -> List a
  preorder Empty = []
  preorder (Node x b l r) = x :: (preorder l ++ preorder r)

namespace LazyList
  public export
  inorder : AVLTree a -> LazyList a
  inorder Empty = []
  inorder (Node x b l r) = inorder l ++ (x :: inorder r)

  public export
  preorder : AVLTree a -> LazyList a
  preorder Empty = []
  preorder (Node x b l r) = x :: (preorder l ++ preorder r)

||| Ordered balanced binary tree.
public export
data OrdTree : (a : Type) -> Ord a -> Type where
  MkOrdTree : AVLTree a -> OrdTree a ord

public export
Set : (a : Type) -> Ord a => Type
Set a = OrdTree a %search

||| The action is functorial only if the order of the elements is preserved.
public export
unsafeMap : (a -> b) -> OrdTree a ord -> OrdTree b ord'
unsafeMap f (MkOrdTree t) = MkOrdTree (map f t)

||| Non-dependent eliminator.
public export
foldl : (c -> a -> c) -> c -> OrdTree a ord -> c
foldl f acc (MkOrdTree tree) = foldl f acc tree

namespace OrdTree
  public export
  empty : {ord : _} -> OrdTree a ord
  empty = MkOrdTree Empty

  public export
  singleton : a -> OrdTree a ord
  singleton x = MkOrdTree $ singleton x

  ||| O(log n)
  public export
  insert : {ord : _} -> a -> OrdTree a ord -> OrdTree a ord
  insert x (MkOrdTree t) = MkOrdTree (insert @{ord} x t)

  ||| O(log n)
  public export
  remove : {ord : _} -> a -> OrdTree a ord -> OrdTree a ord
  remove x (MkOrdTree tree) = MkOrdTree (delete x tree)

  ||| Remove every element of the second tree from the first one.
  ||| O(m * log n)
  public export
  subtract : {ord : _} -> (m : OrdTree a ord) -> (n : OrdTree a ord) -> OrdTree a ord
  subtract a b = foldl (\acc, x => remove x acc) a b

  ||| Compute union of two trees.
  ||| Elements of the left tree override equal elements of the right tree.
  ||| O(m * log (n + m))
  public export
  unite : {ord : _} -> (m : OrdTree a ord) -> (n : OrdTree a ord) -> OrdTree a ord
  unite left right =
    foldl (\tree, x => insert x tree) right left

  public export
  unite3 : {ord : _} -> (m : OrdTree a ord) -> (n : OrdTree a ord) -> (o : OrdTree a ord) -> OrdTree a ord
  unite3 m n o = unite (unite m n) o

  public export
  unite4 : {ord : _} -> OrdTree a ord -> OrdTree a ord -> OrdTree a ord -> OrdTree a ord -> OrdTree a ord
  unite4 m n o p = unite (unite (unite m n) o) p

  ||| O(log n)
  public export
  lookup : {ord : _} -> k -> OrdTree (k, v) (ByFst @{ord}) -> Maybe v
  lookup k (MkOrdTree t) = lookup k t

  ||| O(log n)
  public export
  projLookup : (ord' : Ord a') => a' -> (a -> a') -> OrdTree a ord -> Maybe a
  projLookup k f (MkOrdTree t) = projLookup k f t

  ||| O(n)
  public export
  findFstPostOrder : (a -> Bool) -> OrdTree a ord -> Maybe a
  findFstPostOrder p (MkOrdTree t) = findFstPostOrder p t

  ||| O(n)
  public export
  findAllPostOrder : (a -> Bool) -> OrdTree a ord -> List a
  findAllPostOrder p (MkOrdTree t) = findAllPostOrder p t

  ||| O(log n)
  public export
  isElem : {ord : _} -> a -> OrdTree a ord -> Bool
  isElem x tree = isJust $ projLookup {ord' = ord} x id tree

  ||| O(log n)
  public export
  extend : {ord : _} -> a -> OrdTree a ord -> Maybe (OrdTree a ord)
  extend v t =
    case isElem v t of
      False => Just (insert v t)
      True => Nothing

  ||| O(n * log n)
  public export
  mapMaybe : {ord, ord' : _} -> (a -> Maybe b) -> OrdTree a ord -> OrdTree b ord'
  mapMaybe f tree = foldl (\acc, x =>
     case f x of
       Nothing => acc
       Just t => insert t acc
    ) empty tree

  ||| O(m * log n)
  public export
  isSubset : {ord : _} -> (m : OrdTree a ord) -> (n : OrdTree a ord) -> Bool
  isSubset smaller bigger  =
    foldl (\allInBigger, x => allInBigger && isElem x bigger) True smaller

  ||| Compute intersection of two trees.
  ||| The resulting tree contains elements of the left tree.
  ||| O(m * log (n * m))
  public export
  intersect : {ord : _} -> (m : OrdTree a ord) -> (n : OrdTree a ord) -> OrdTree a ord
  intersect left right =
    foldl
      (\tree, inLeft =>
         case isElem inLeft right of
           True => insert inLeft tree
           False => tree
      )
      empty left

  ||| O(n * log n)
  public export
  fromList : {ord : _} -> (xs : List a) -> OrdTree a ord
  fromList []        = empty
  fromList (x :: xs) = insert x (fromList xs)

  ||| O(n * log n)
  public export
  fromSnocList : {ord : _} -> (xs : SnocList a) -> OrdTree a ord
  fromSnocList [<]        = empty
  fromSnocList (xs :< x)  = insert x (fromSnocList xs)

  ||| O (log n)
  public export
  append : Monoid v
        => Ord k
        => k
        -> v
        -> OrdTree (k, v) ByFst
        -> OrdTree (k, v) ByFst
  append k val t =
    case lookup k t of
      Just old => insert (k, old <+> val) t
      Nothing => insert (k, val) t

  ||| O(n)
  public export
  length : OrdTree a ord -> Nat
  length (MkOrdTree t) = length t

  -- TODO: Is it an evoking name?
  ||| O(1)
  public export
  isLeaf : OrdTree a ord -> Bool
  isLeaf (MkOrdTree Empty) = True
  isLeaf _ = False

  ||| O(1)
  public export
  isEmpty : OrdTree a ord -> Bool
  isEmpty = isLeaf

  ||| O(n)
  public export
  depth : OrdTree a ord -> Nat
  depth (MkOrdTree t) = depth t

  public export
  MaybeOrd : Ord a -> Ord (Maybe a)
  MaybeOrd _ = %search

  public export
  catMaybes : (o : Ord a) => OrdTree (Maybe a) (MaybeOrd o) -> OrdTree a o
  catMaybes tree = foldl H empty tree
   where
    H : OrdTree a o -> Maybe a -> OrdTree a o
    H tree Nothing = tree
    H tree (Just x) = insert x tree

  public export
  mapOrdTree : {o, o' : _} -> (a -> b) -> OrdTree a o -> OrdTree b o'
  mapOrdTree f tree = foldl H empty tree
   where
    H : OrdTree b o' -> a -> OrdTree b o'
    H tree x = insert (f x) tree

namespace OrdTree.LazyList
  public export
  preorder : OrdTree a ord -> LazyList a
  preorder (MkOrdTree t) = preorder t

  public export
  inorder : OrdTree a ord -> List a
  inorder (MkOrdTree t) = preorder t

namespace OrdTree.List
  public export
  preorder : OrdTree a ord -> List a
  preorder (MkOrdTree t) = preorder t

  public export
  inorder : OrdTree a ord -> List a
  inorder (MkOrdTree t) = inorder t

  public export
  reorder : {ord, ord' : _} -> OrdTree a ord -> OrdTree a ord'
  reorder tree = fromList (List.inorder tree)

namespace OrdTree.SnocList
  public export
  inorder : OrdTree a ord -> SnocList a
  inorder (MkOrdTree t) = inorder t
