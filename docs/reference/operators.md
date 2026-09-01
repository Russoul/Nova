# Operators and fixity

Nova has no notation system, no mixfix declarations and no operator
overloading resolved by precedence tricks. It has something simpler:
**an operator is a name**. `+` is the name of a definition, `a + b` is
that definition applied to two arguments, and a fixity declaration is
the one extra thing you write so the parser knows how to read it
infix.

## Operators are names

```nova
infixl 6 +
def + : ℕ → ℕ → ℕ ≔ λx. λy. ℕ-elim x (n ih. S ih) y
```

`def + : …` defines the name `+`, exactly as `def plus : …` defines
the name `plus`. There is no mapping from notation to a function, and
so there is nothing that can get out of step: when the checker reports
a goal about your operator, it prints the operator.

An operator token is any run of characters from the operator alphabet:

```text
+ - * < > = & ! ? % ^ ~ @ # ⊕ ⊗ ⊙ ⊞ ⊟ ∙ ∘ · ≤ ≥ ∸ ⧺ ⊥ ⊤ ∧ ∨ ⊃ ¬ ↔
```

Runs are maximal, so `<=` is one token and not two. The reserved
theory symbols `→ × ≡ ∈ ≔ / . , :` are not in the alphabet, `|` is
the clause marker, and `--` opens a comment, so no operator can
contain it. Ordinary alphanumeric names are never operators, and
local binders are never operator-shaped.

## Fixity declarations

```nova-sketch
infixl 6 +      -- left-associative, precedence 6
infixr 5 ∧      -- right-associative, precedence 5
```

The precedence is a single digit, `0` to `9`, with higher binding
tighter. A declaration takes effect for the rest of the file, and it
is **exported with the name**: opening an operator from another module
brings its fixity along, so you never declare the same fixity twice.

The library's choices, for calibration:

| Level | Operators | |
| --- | --- | --- |
| 8 | `^` | exponentiation |
| 7 | `*` | multiplication |
| 6 | `+` `-` `∸` `⊞` | addition and its relatives |
| 5 | `∧` | conjunction |
| 4 | `∨` `<` `≤` | disjunction, the order relations |
| 3 | `⊃` | implication |
| 2 | `↔` | equivalence |
| 1 | `∘` | composition |

## Mixing associativities

Two operators at the same precedence that associate in opposite
directions have no agreed reading, so Nova refuses rather than picking
one:

```text
error: '<#' and '>#' both have precedence 4 but associate in opposite
directions — parenthesize, or give them different precedences
```

This is worth knowing because the library contains such a pair —
`∨` is `infixr 4` and `≤` is `infixl 4` — which simply never meet in
one expression. If yours do, parenthesise.

## Without a fixity

An operator token with no fixity in scope is not infix — it is an
ordinary name atom, and that is how nullary and prefix operator names
work. `⊥` and `⊤` are names of propositions, and `¬ p` is `¬` applied
to `p`, all three from `prop.nova`, none of them needing a fixity.

The trap is that using such an operator infix does not fail with
anything helpful. `Z ⊕ Z`, where `⊕` has no fixity, parses fine — as
three things juxtaposed, `Z` applied to `⊕` applied to `Z` — and you
get:

```text
Error: def a: cannot apply a term of non-Π type
```

If an infix expression produces a type error that makes no sense,
check that the operator has a fixity.

The reverse case is cleaner: once an operator *has* a fixity, it is
infix-only, and `⊕ Z Z` is a parse error.

## The mention form

Parenthesising an operator gives you the name as an ordinary atom,
usable wherever a name can go:

```nova-sketch
(⊕) Z Z
```

This works whether or not a fixity is in scope. It is also the form
used in an import list — `import nat (+)` — and in a `using` clause.

## Overloading

Two modules may define the same operator at different types, and uses
are resolved by type:

```nova-sketch
import modA (⊕)      -- ⊕ : ℕ → ℕ → ℕ
import modB (⊕)      -- ⊕ : 𝟙 → 𝟙 → 𝟙

def n : ℕ ≔ Z ⊕ Z
def u : 𝟙 ≔ () ⊕ ()
```

Both definitions are in scope at once and each use picks the one that
fits. There is one constraint, and the checker states it plainly:

```text
Error: conflicting fixities for '⊕' among the opened imports —
overloads must agree on associativity and precedence
```

The parse happens before anything is known about types, so all
overloads of a name must share one fixity. Only the elaborator, which
runs later and does know the types, tells them apart.

## Choosing operators

Two pieces of advice from the corpus. First, an operator is worth it
when the notation is already standard in the mathematics you are
writing — `≤`, `∧`, `∘` — and not otherwise; a well-named function is
easier to read than an invented symbol. Second, the glyph has to be in
the operator alphabet, which is a smaller set than "any symbol you can
type" ([Reading and typing Nova](#notation)).
