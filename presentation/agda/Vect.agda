-- Part 2 counterpart: length-indexed vectors, and where intensional
-- equality starts to hurt.
module Vect where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Relation.Binary.PropositionalEquality

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

head : ∀ {A n} → Vec A (suc n) → A
head (x ∷ _) = x

_++_ : ∀ {A n m} → Vec A n → Vec A m → Vec A (n + m)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- reverse with an accumulator. The cons case DOES NOT TYPE CHECK as
-- written: rev-acc xs (x ∷ acc) : Vec A (n + suc m), the signature
-- wants Vec A (suc n + m) = Vec A (suc (n + m)), and n + suc m is not
-- definitionally suc (n + m). So a coercion goes into the PROGRAM:
rev-acc : ∀ {A n m} → Vec A n → Vec A m → Vec A (n + m)
rev-acc {A} {zero}  {m} []       acc = acc
rev-acc {A} {suc n} {m} (x ∷ xs) acc =
  subst (Vec A) (+-suc n m) (rev-acc xs (x ∷ acc))

-- and again at the top: n + 0 is not n
reverse : ∀ {A n} → Vec A n → Vec A n
reverse {A} {n} xs = subst (Vec A) (+-identityʳ n) (rev-acc xs [])

-- Consequences the audience has felt:
--   * every proof about reverse must first push through the substs
--     (subst-lemmas, "green slime" — Vec A (n + 0) never reduces);
--   * head (reverse v) does not compute past the subst unless the
--     equality proof reduces to refl, which +-identityʳ n does not
--     for a variable n.
-- Nova: the three obligations (0 + m = m, n + suc m = suc (n + m),
-- n + 0 = n) are discharged at the definition, and the program is
-- the Haskell one.

-- THE statement that cannot be written: xs ++ [] : Vec A (n + 0) but
-- xs : Vec A n, and _≡_ needs both sides at ONE type. Options:
--   (a) heterogeneous equality  xs ++ [] ≅ xs  (Relation.Binary.HeterogeneousEquality)
--   (b) an explicit cast        subst (Vec A) (+-identityʳ n) (xs ++ []) ≡ xs
-- Both are then proved by induction plus subst/≅ bookkeeping lemmas.
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)

++-[] : ∀ {A n} (xs : Vec A n) → xs ++ [] ≅ xs
++-[] []       = H.refl
++-[] {A} {suc n} (x ∷ xs) = H.icong (Vec A) (x ∷_) (+-identityʳ n) (++-[] xs)
-- (icong: a congruence whose INDEX moves along a separate equality —
-- the kind of combinator one goes looking for. In Nova the whole
-- thing is: state it, get one obligation, cite plusZr.)
