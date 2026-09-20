-- Part 1 counterpart: the primer looks the same in both worlds — the
-- difference starts at the STEP case of commutativity.
module Arith where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality

plus : ℕ → ℕ → ℕ
plus zero    m = m
plus (suc n) m = suc (plus n m)

-- closed computation: refl
twoPlusThree : plus 2 3 ≡ 5
twoPlusThree = refl

plusZr : ∀ n → plus n zero ≡ n
plusZr zero    = refl
plusZr (suc n) = cong suc (plusZr n)          -- Nova: ⋆

plusSr : ∀ n m → plus n (suc m) ≡ suc (plus n m)
plusSr zero    m = refl
plusSr (suc n) m = cong suc (plusSr n m)      -- Nova: ⋆

-- The step case. In Agda the induction hypothesis is a VALUE of type
-- plus k m ≡ plus m k; to use it you must transport it through the
-- context — cong suc, or rewrite, or a trans chain of congs. In Nova
-- ih is in scope, so plus k m and plus m k are the SAME term: the
-- chain link ≡⟨ ih ⟩ needs no cong, and the .rw version is two ⋆s.
plusComm : ∀ n m → plus n m ≡ plus m n
plusComm zero    m = sym (plusZr m)
plusComm (suc k) m =
  begin
    plus (suc k) m      ≡⟨⟩
    suc (plus k m)      ≡⟨ cong suc (plusComm k m) ⟩
    suc (plus m k)      ≡⟨ sym (plusSr m k) ⟩
    plus m (suc k)
  ∎
  where open ≡-Reasoning
