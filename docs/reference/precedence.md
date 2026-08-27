# Precedence and associativity
%stub

One table for parsing questions.

## Grammar levels

| level | forms | notes |
| --- | --- | --- |
| tightest | atoms, `(t)`, `(t : T)` | |
| | application, `.π₁`, `.π₂` | left-associative |
| | `⊎` | right-associative, tighter than `→ ⨯ /` |
| | `→` `⨯` `/` | right-associative |
| loosest | `,` | right-associative |

## Declared operators

- Where `infixl`/`infixr` levels 0–9 sit relative to the fixed syntax.

## Maximal bodies

- `λ`, `let` and calc chains extend as far right as they can.

## The library's conventions

- The levels `nat`, `prop` and the order modules settle on.
