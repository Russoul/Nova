-- Part 3 counterpart: the J-toolkit, and the two things J cannot give.
module Equality where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality

-- each of these is a pattern match on refl — J in disguise
sym' : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
sym' refl = refl

trans' : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans' refl refl = refl

cong' : ∀ {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
cong' f refl = refl

-- transport is a real function: it produces a NEW value of a
-- different type, which then has to be reasoned about (subst-lemmas)
subst' : ∀ {A : Set} (P : A → Set) {a b : A} → a ≡ b → P a → P b
subst' P refl p = p

-- uniqueness of identity proofs: provable for ℕ (decidable equality,
-- Hedberg), NOT in general — and inconsistent with cubical/HoTT.
-- With --without-K it is not even provable for ℕ by matching.
uip-ℕ : ∀ {a b : ℕ} (p q : a ≡ b) → p ≡ q
uip-ℕ refl refl = refl      -- accepted only WITH K

-- function extensionality: not provable. Either postulate it …
postulate
  funext : ∀ {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
-- … which blocks computation wherever it is used, or switch to
-- --cubical, where it holds but ≡ is a path type with its own rules.

double1 double2 : ℕ → ℕ
double1 n = n + n
double2 n = 2 * n

-- pointwise agreement is provable; equality AS FUNCTIONS needs the postulate
doublesAgree : double1 ≡ double2
doublesAgree = funext λ n → {! 2 * n = n + (n + 0) — needs +-identityʳ !}

-- a vector whose length we have learned is 3: a cast, not a value
open import Data.Vec using (Vec)
learnedLength : ∀ {n} → Vec ℕ n → n ≡ 3 → Vec ℕ 3
learnedLength v h = subst (Vec ℕ) h v
