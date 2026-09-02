# Proof recipes
%stub

The playbook, in the order you should try things.

## Restate the obligation as a lemma

- Binders become Π-arguments, the equation becomes the type; place the
  lemma **above** the failing item.

## Try `⋆` first

- β plus the stored lemmas close more than you expect.

## Induct with an equality motive

```nova
def zeroPlusId : (n : ℕ) → Z + n ≡ n using (+.eq, nat.plusZeroId) ≔ λn. ℕ-elim ⋆ (k ih. ⋆) n
```

- In the step case `ih` is in scope **and** in the store.

## Over a QIIT, use `ElimP`

- Prop-valued motives, no coherence arguments.

## Reach for the right shape

- Permutative facts never auto-rewrite: state the exact instance you
  need (`a + (b + c) ≡ b + (a + c)`).
- State shape-generic lemmas type-generically, so every instance
  follows.

## Retype with `transport`

- It is the identity function, so it inserts nothing, but its signature
  does the retyping — the way around a conversion the kernel will not
  replay.

## Prove the twin equation first

- For IH-bearing coherences, prove the standalone lemma and pass `⋆`.
