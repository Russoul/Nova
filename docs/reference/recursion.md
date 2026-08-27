# Recursion and eliminators
%stub

How to take a value apart, and why Nova will not let you write a
recursive function the way you are used to.

## There is no general recursion

- A function that loops would be a proof of anything, so the language
  does not admit one. This is the first rule that will surprise you.
- No termination checker either: instead of accepting recursion and
  then policing it, Nova only offers shapes that terminate by
  construction.

## The eliminator

- Every type comes with one: `ℕ-elim`, `⊎-elim`, and one per sort for
  your own types.
- Reading `ℕ-elim z (n ih. s) t` — the zero case, the step case with
  its **induction hypothesis**, and the value being taken apart.
- `ih` is the recursive call, already made for you. That is the whole
  trick.

## Worked examples

- Addition, multiplication, length, map.

## The motive

- What the eliminator's result type may depend on, and why the
  dependent case needs it written down
  ([Checking and inference](#bidirectional)).

## When this is uncomfortable

- Recursion that is not structural, and what to do instead.
- [Pattern-matching definitions](#clausal-defs) give back the familiar
  spelling for the cases that fit.
