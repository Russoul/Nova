module Solver.CommutativeMonoid.Language

import Data.Fin
import Data.List1
import Data.Util

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

public export
data Term : Type -> Type where
  Var : x -> Term x
  Zero : Term x
  Plus : Term x -> Term x -> Term x
  -- 0 + x = x
  -- x + 0 = x
  -- x + (y + z) = (x + y) + z
  -- x + y = y + x

public export
Show a => Show (Term a) where
  show (Var x) = "Var \{show x}"
  show Zero = "0"
  show (Plus x y) = "(\{show x}) + (\{show y})"

public export
prettyTerm : (ctx : SnocList String) -> Term (Fin (length ctx)) -> Doc ann
prettyTerm ctx (Var x) = pretty (index ctx x)
prettyTerm ctx Zero = pretty "0"
prettyTerm ctx (Plus x y) = parens (prettyTerm ctx x) <++> "+" <++> parens (prettyTerm ctx y)

public export
Functor Term where
  map f (Var x) = Var (f x)
  map f Zero = Zero
  map f (Plus x y) = Plus (map f x) (map f y)


-- n     * t
-- 0     * t = Z
-- (S k) * t = t + k * t
public export
mult : Nat -> Term (Fin n) -> Term (Fin n)
mult Z t = Zero
mult 1 t = t
mult (S n) t = Plus t (mult n t)

namespace Fin
  public export
  sum : {n : _} -> (Fin n -> Term (Fin n)) -> Term (Fin n)
  sum = go n
   where
    go : (k : Nat) -> (Fin k -> Term (Fin n)) -> Term (Fin n)
    go 0 f = Zero
    go 1 f = f 0
    go (S k) f = Plus (go k (f . FS)) (f FZ)

namespace List1
  public export
  sum : List1 (Term (Fin n)) -> Term (Fin n)
  sum (t ::: []) = t
  sum (t ::: (q :: qs)) = sum (Plus t q ::: qs)

