# Your first file
%stub

A complete, accepted file, line by line.

## The file

A worked walkthrough of a small module: a fixity, an operator
definition, and one proved lemma — every line explained.

## Anatomy of an item

- `def name : Type ≔ term` — the only shape you ever need.
- The type is the specification; the definiens is the program or proof.
- Items live in the **empty context**: parameters are Π-binders in the
  item's own type, and a reference to an item is a bare name.

## Running it

What acceptance looks like, and what the first failure looks like.

## Adding a proof

Turning an equation into a `def`, and watching it become available to
everything below it.
