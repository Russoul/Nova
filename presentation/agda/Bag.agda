-- Part 4 counterpart: multisets. Plain Agda has no quotients; the two
-- usual routes are setoids (below) or --cubical HITs (at the end).
module Bag where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-comm)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality

-- ===== route 1: a setoid. A bag IS a list; "equality" is a
-- separately defined relation, and NOTHING is automatic. =====
data _≈_ {A : Set} : List A → List A → Set where
  ≈-refl  : ∀ {xs} → xs ≈ xs
  ≈-sym   : ∀ {xs ys} → xs ≈ ys → ys ≈ xs
  ≈-trans : ∀ {xs ys zs} → xs ≈ ys → ys ≈ zs → xs ≈ zs
  ≈-cons  : ∀ {x xs ys} → xs ≈ ys → (x ∷ xs) ≈ (x ∷ ys)
  ≈-swap  : ∀ {x y xs} → (x ∷ y ∷ xs) ≈ (y ∷ x ∷ xs)

sum : List ℕ → ℕ
sum []       = zero
sum (x ∷ xs) = x + sum xs

-- every function out of a bag needs its OWN respect lemma, by
-- induction over the relation — six constructors, six cases, and
-- the interesting one is the exchange law
sum-resp : ∀ {xs ys} → xs ≈ ys → sum xs ≡ sum ys
sum-resp ≈-refl            = refl
sum-resp (≈-sym p)         = sym (sum-resp p)
sum-resp (≈-trans p q)     = trans (sum-resp p) (sum-resp q)
sum-resp (≈-cons {x} p)    = cong (x +_) (sum-resp p)
sum-resp (≈-swap {x} {y} {xs}) =
  begin
    x + (y + sum xs)   ≡⟨ sym (+-assoc x y _) ⟩
    (x + y) + sum xs   ≡⟨ cong (_+ sum xs) (+-comm x y) ⟩
    (y + x) + sum xs   ≡⟨ +-assoc y x _ ⟩
    y + (x + sum xs)
  ∎
  where open ≡-Reasoning

-- and nothing stops you from writing the function that does NOT
-- respect the relation: "first" type checks fine; the mistake is
-- only caught if someone remembers to try to prove first-resp
first : List ℕ → ℕ
first []      = zero
first (x ∷ _) = x

-- ===== route 2 (--cubical): a higher inductive type =====
-- {-# OPTIONS --cubical #-}
-- data Bag (A : Type) : Type where
--   nil  : Bag A
--   ins  : A → Bag A → Bag A
--   swp  : ∀ x y m → ins x (ins y m) ≡ ins y (ins x m)
--   trunc : isSet (Bag A)
--
-- sum : Bag ℕ → ℕ
-- sum nil = 0
-- sum (ins x m) = x + sum m
-- sum (swp x y m i) = exchange x y (sum m) i        -- a PATH, applied to i
-- sum (trunc m n p q i j) = isSetℕ _ _ (cong sum p) (cong sum q) i j
--
-- Closer to Nova — the swap case IS the exchange law — but: the
-- clause is a path (a function of an interval variable), equality
-- proofs are not unique (hence the trunc constructor and its clause,
-- for every function), and transports along paths do not compute
-- away in general. Nova's BagElim asks for the same exchange law as
-- a plain equation, and ⋆ or plusSwap x y ih is the whole answer.
