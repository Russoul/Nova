# `let`
%stub

Local definitions that stay transparent.

## Syntax

- `let x ≔ e in b`, and the annotated form `let x : T ≔ e in b`, sugar
  for `let x ≔ (e : T) in b`.
- The body extends maximally, like a λ body.

## Transparency

- The body is typed under `x` **and** its unfolding equation, so facts
  stated at the abbreviation discharge against facts about its
  unfolding, with no manual unfolding and no transport.

## From the outside

- A `let` **is** its unfolding, so lemmas about a definition that uses
  one compute as if the `let` were never there.

## When to reach for it

- Sharing a subterm that the goal mentions repeatedly; naming a step in
  a long definition.
