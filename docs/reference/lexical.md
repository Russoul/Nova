# Lexical structure
%stub

Identifiers, operator tokens, reserved syntax, comments, literals.

## Identifiers

- Alphanumeric: a leading letter or `_`, then letters, digits, `_`, `'`.
- A **leading `_` is reserved**. [Implicit arguments and blanks](#implicits) covers its two legal
  uses:
  the wildcard binder `_`, and a blank argument.
- Greek letters are **not** identifier characters — `(φ : T)` is a parse
  error, reported at the following binder. Write `phi`.

## Operator tokens

- Maximal runs of the operator alphabet
  `+ - * < > = & ! ? % ^ ~ @ # ⊕ ⊗ ⊙ ⊞ ⊟ ∙ ∘ · ≤ ≥ ∸ ⧺ ⊥ ⊤ ∧ ∨ ⊃ ¬ ↔`.
- Reserved theory tokens `→ ⨯ ≡ ∈ ≔ / . , :` are excluded, as is `|`
  (the clause marker), and `--` opens a comment, so no operator contains
  it.

## Reserved words and symbols

The complete fixed vocabulary, with a pointer to the chapter that
explains each.

## Numerals

- `0`, `1`, `2` … are sugar for `Z`/`S` towers.

## Comments

- `--` to end of line. There is no block comment.

## Unicode

- Why the notation is Unicode, and how to type it ([Notation and how to type it](#notation)).
