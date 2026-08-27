# Calc chains
%stub

Multi-step equational reasoning that reads like a blackboard proof.

## Syntax

- `a ≡⟨ p ⟩ b ≡⟨ q ⟩ c` — midpoints stated once, each link justified by
  an inferable proof of *some* equation.
- Checking-only, at `l ≡ r ∈ A`; it erases to `⋆`.
- A chain continues a λ body under the λ.

## What a link may be

- Any lemma application, an induction hypothesis, a hypothesis.

## When a chain is the wrong tool

- A chain runs with an **empty** Σ-scope, so a link needing a conversion
  licensed by the item's `using` clause fails — with a confusing
  symptom: an obligation that *is* the link you supplied. The same proof
  written as one `trans` goes through.
- A link that would rewrite inside a `quot-elim` scrutinee fails at
  replay; again, `trans` is the fix.

## Style

- Chain when the midpoints are the explanation; use `trans` when the
  problem is scope.
