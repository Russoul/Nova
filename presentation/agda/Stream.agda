-- Part 5 counterpart: streams. The problem is not writing them; it is
-- that ≡ between two streams is USELESS, so a second equality is
-- built by hand and then never becomes the first one.
{-# OPTIONS --guardedness #-}
module Stream where

open import Data.Nat using (ℕ; zero; suc; _*_)
open import Relation.Binary.PropositionalEquality

record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A
open Stream

iterate : ∀ {A} → (A → A) → A → Stream A
hd (iterate f x) = x
tl (iterate f x) = iterate f (f x)

map : ∀ {A B} → (A → B) → Stream A → Stream B
hd (map f s) = f (hd s)
tl (map f s) = map f (tl s)

-- observations compute, as in Nova
evens : Stream ℕ
evens = map (2 *_) (iterate suc zero)

evens2 : hd (tl (tl evens)) ≡ 4
evens2 = refl

-- map id s ≡ s is NOT provable: the two sides are different
-- corecursive definitions and ≡ only sees syntax. So one defines
-- bisimilarity …
record _≈_ {A : Set} (s t : Stream A) : Set where
  coinductive
  field
    hd-≈ : hd s ≡ hd t
    tl-≈ : tl s ≈ tl t
open _≈_

map-id : ∀ {A} (s : Stream A) → map (λ x → x) s ≈ s
hd-≈ (map-id s) = refl
tl-≈ (map-id s) = map-id (tl s)

-- … and now pays for it forever: ≈ is not ≡. It does not rewrite,
-- it does not substitute into types, and every function must be
-- shown to respect it, one lemma each:
map-cong : ∀ {A B} (f : A → B) {s t : Stream A} → s ≈ t → map f s ≈ map f t
hd-≈ (map-cong f p) = cong f (hd-≈ p)
tl-≈ (map-cong f p) = map-cong f (tl-≈ p)

-- Nova: coind proves map id s ≡ s itself. Being an equality, it
-- rewrites under map, under evens, under anything — no map-cong.
