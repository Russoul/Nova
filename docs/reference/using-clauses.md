# `using`: licences and scope
%stub

The `using` clause is how you steer the engine — and the most common
source of confusion.

## Discharge scope

- An item's `using` clause names the lemmas its checking may see; an
  item without one sees hypotheses only.
- `⋆ using (…)` overrides the item's scope at one site.

## The kinds of licence

- A bare lemma name — the equation enters the site's candidate set.
- `f.eq` — permission to unfold `f`'s defining equation. **Definitions
  are opaque by default**, so this is what makes a proof "by
  computation" go through at all.
- `f.unfold` — the weaker form: head exposure only, subsumed by `f.eq`.
- `f.rw` / `hyp.rw` — permission to use a candidate as a rewrite rule.
- `pi.eta` / `sigma.eta` — the builtin η licences.
- Qualified spellings (`nat.plusComm`) and when they are needed.
- A name that resolves to nothing, or to a Σ entry that is not an
  equation lemma of the visible store, is a **structural error** — it
  could only scope the site to nothing.

## Licences are not monotone

- Citing more `.eq` can **undo** a proof: the `.eq` unfolds the goal into
  eliminator vocabulary while the store holds lemmas in the other
  vocabulary, so links stop matching.
- Symptom: a chain step reports an obligation that is literally the
  statement of the link you supplied. Suspect the `using` clause, not
  the link.
- Add hints **one at a time**, and revert any that does not strictly
  reduce the obligation count.

## Prefer the spelling that needs no licence

- Two spellings of the same term can differ in cost.
