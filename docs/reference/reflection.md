# Reflection: proving by computation and by hypothesis
%stub

The rule that makes Nova's proofs short, stated for someone meeting it
for the first time.

## Two ways an equation can be obvious

- **By computation**: both sides run to the same thing. `2 + 2` and `4`
  are the same number, and the checker can see it.
- **By hypothesis**: you are given `h : a ≡ b`, and from there on the
  two are interchangeable — not "rewritable", *interchangeable*.

## `⋆`, and what writing it means

- `⋆` is the proof of every proposition. Writing it is a **request**:
  "checker, please see that these are equal."
- If it can, you are done. If it cannot, you get an obligation
  ([Reading the report](#report-and-holes)) — not an error.

## Why this is unusual

- In most proof assistants a hypothesis must be *used* explicitly, with
  `rewrite` or a transport. Here it applies itself.
- The consequences: `sym`, `trans`, `cong`, `transport` and function
  extensionality are one-liners, most of them literally `⋆`.

## The price

- The checker cannot always decide equality, so it reports what it
  could not derive instead of guessing or looping.
- This is the trade the language makes, and knowing it explains
  everything the checker asks of you later.

## Definitions are opaque

- Computation stops at a definition unless the item licenses unfolding.
  Why `⋆` sometimes needs a `using` clause to see something obvious.
