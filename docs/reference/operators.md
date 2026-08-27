# Operators and fixity
%stub

Operators are ordinary names with a parsing rule attached.

## Operators are names

- `def ∘ : … ≔ …` defines the name `∘`; `f ∘ g` is application of it.
- No notation-to-name mapping, so no resugaring gap: the obligation
  printer prints the name, and the name is the operator.

## Fixity declarations

- `infixl d op` / `infixr d op`, `d` a digit 0–9.
- Effective for the rest of the file, and exported with the name.

## Fixity-free operators

- An operator token with no fixity in scope is an ordinary name atom —
  that is how nullary and prefix operator names work (`⊥`, `¬ p`).
- An operator **with** a fixity is infix-only outside the mention form,
  so application juxtaposition never captures it.

## The mention form

- `(+)` is the operator as an ordinary reference, usable wherever an
  atom is.

## Conventions in the corpus

- The precedence levels the library settles on ([Precedence and associativity](#precedence)).
