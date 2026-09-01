# Precedence and associativity
%stub

One table for parsing questions.

## Grammar levels

| level | forms | notes |
| --- | --- | --- |
| tightest | atoms, `(t)`, `(t : T)` | |
| | application, `.π₁`, `.π₂` | left-associative |
| | `×` (non-dependent) | right-associative, tighter than `⊎` |
| | `⊎` | right-associative |
| | `→`, `(x : A) × B`, `/` | right-associative, bodies maximal |
| | `≡ … ∈ …` | sides and `∈`-type at the levels above |
| loosest | `,` | right-associative |

- `×` is **two operators sharing a token**: the non-dependent form
  binds tightly, the binder form sits beside `→` and takes its body
  maximally. `A × B` is therefore not shorthand for `(_ : A) × B`.
- Two operators of equal precedence and opposite associativity are a
  parse error ([Operators and fixity](#operators)).

## Declared operators

- Where `infixl`/`infixr` levels 0–9 sit relative to the fixed syntax.

## Maximal bodies

- `λ`, `let` and calc chains extend as far right as they can.

## The library's conventions

- The levels `nat`, `prop` and the order modules settle on.
