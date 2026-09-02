# Reading and typing Nova

Nova's syntax is Unicode, and this chapter comes before you write
anything because two practical problems block a newcomer otherwise:
you cannot say a glyph you have no name for, and typing a *look-alike*
character produces a parse error that does not tell you what went
wrong.

The good news is that the fixed vocabulary is small. Across the entire
corpus — thousands of lines, sixty-odd files — Nova code uses exactly
**32 non-ASCII characters**, and only twenty of them are the language
itself. Here they all are.

## The fixed syntax

These are reserved: the parser knows them, and you cannot redefine
them.

| Glyph | Say | Marks | Code point |
| --- | --- | --- | --- |
| `≔` | "is defined as" | the body of a definition | U+2254 |
| `→` | "to", or "arrow" | function type | U+2192 |
| `×` | "cross" | pair type | U+00D7 |
| `⊎` | "or", or "uplus" | disjoint union | U+228E |
| `ℕ` | "nat" | the natural numbers | U+2115 |
| `𝟘` | "empty" | the empty type | U+1D7D8 |
| `𝟙` | "unit" | the one-element type | U+1D7D9 |
| `𝕌` | "U" | the universe of types | U+1D54C |
| `Ω` | "omega" | the universe of propositions | U+03A9 |
| `∥ ∥` | "squash" | a type made into a proposition | U+2225 |
| `λ` | "lambda" | function abstraction | U+03BB |
| `⋆` | "star" | the canonical proof | U+22C6 |
| `≡` | "equals" | an equation, as a statement | U+2261 |
| `∈` | "in" | which type an equation is about | U+2208 |
| `⟨ ⟩` | "angle brackets" | around a step's justification | U+27E8/9 |
| `π` | "pi" | in the projections `.π₁` and `.π₂` | U+03C0 |
| `₁ ₂` | "one", "two" | subscripts, as in `inj₁` | U+2081/2 |
| `ν` | "nu" | a coinductive type | U+03BD |
| `𝕏` | "X" | the hole in a polynomial | U+1D54F |

The last two belong to [Coinductive types](#coinduction) and can wait.
Everything else you will meet within a few chapters.

## Operators are not syntax

The other twelve glyphs in the corpus are not part of the language at
all. They are *names*, defined in ordinary files, and they only look
special:

| Glyph | Name of | Defined in |
| --- | --- | --- |
| `≤` `∸` | at most, truncated subtraction | `natOrder`, `natMore` |
| `∘` | function composition | `prelude` |
| `⊤` `⊥` `¬` `∧` `∨` `⊃` `↔` | the logical connectives | `prop` |
| `⊞` | an example operator | `definingEq` |

You can define your own from the operator alphabet — any run of
`+ - * < > = & ! ? % ^ ~ @ # ⊕ ⊗ ⊙ ⊞ ⊟ ∙ ∘ · ≤ ≥ ∸ ⧺ ⊥ ⊤ ∧ ∨ ⊃ ¬ ↔`
is a legal name ([Operators and fixity](#operators)). Nothing above is
privileged; `∧` is a definition in `prop.nova` exactly as `plus` was a
definition in yours.

## Entering them

Most editors offer an **Agda-style input mode**: type a backslash and
a short name, and the glyph replaces it. If you have one, these cover
almost everything above.

| Sequence | Glyph | | Sequence | Glyph |
| --- | --- | --- | --- | --- |
| `\:=` | `≔` | | `\bN` | `ℕ` |
| `\to` | `→` | | `\bU` | `𝕌` |
| `\uplus` | `⊎` | | `\b0` `\b1` | `𝟘` `𝟙` |
| `\lambda` | `λ` | | `\Omega` | `Ω` |
| `\star` | `⋆` | | `\nu` | `ν` |
| `\==` | `≡` | | `\bX` | `𝕏` |
| `\in` | `∈` | | `\pi` | `π` |
| `\||` | `∥` | | `\_1` `\_2` | `₁` `₂` |
| `\<` `\>` | `⟨` `⟩` | | `\le` `\neg` | `≤` `¬` |

Without an input mode, three fallbacks work fine: copy the glyphs out
of the tables above, define editor snippets for the dozen you actually
use, or enter them by code point with your system's hex input. The
language server does not insert glyphs for you — it deliberately
provides no completion.

## Or write ASCII

Every non-ASCII token has an ASCII spelling. Both parse to the same
thing, you may mix them freely in one file, and the printer always
emits the Unicode form — so an ASCII-written file *normalises* to
Unicode when it is distilled.

| | | | | | |
| --- | --- | --- | --- | --- | --- |
| `->` `→` | `\` `λ` | `\x` `×` | `:=` `≔` | `==` `≡` | `\in` `∈` |
| `\|\|` `∥` | `\/` `⊎` | `\star` `⋆` | `\nu` `ν` | `\X` `𝕏` | `.1` `.2` |
| `Set` `𝕌` | `Prop` `Ω` | `Nat` `ℕ` | `Void` `𝟘` | `Unit` `𝟙` | `inj1` `inj2` |

So this file is accepted, and distils to the Unicode you have been
reading:

```nova-sketch
def idNat : Nat -> Nat := \x. x
```

Two wrinkles. The seven fallbacks that are valid identifiers — `Set`,
`Prop`, `Nat`, `Void`, `Unit`, `inj1`, `inj2` — become reserved words,
so you cannot use them as names of your own (a name merely *beginning*
with one, like `Setoid`, is fine). And `λ` is tried before `\x`, so
`\x. e` is a lambda binding `x` while `A \x B` is the product.

## Look-alikes that will not parse

This is where an hour goes missing. Each of these pairs looks
identical at normal font sizes, and only the left one is Nova.

| Nova wants | Not | Which is |
| --- | --- | --- |
| `×` U+00D7 | `⨯` U+2A2F | vector-or-cross-product — unrecognised here |
| `⋆` U+22C6 | `∗` U+2217, `★` U+2605, `*` | asterisk operator, black star, ASCII |
| `∥` U+2225 | `‖` U+2016, `\|\|` | double vertical line, two ASCII bars |
| `⟨ ⟩` U+27E8/9 | `<` `>`, `⟪ ⟫` | ASCII angles, doubled angles |
| `≡` U+2261 | `=` | ASCII equals |
| `≔` U+2254 | `:=` | colon then equals |
| `ℕ` U+2115 | `N` | the ASCII letter |
| `λ` U+03BB | `\` | backslash |

The symptom is always the same and always unhelpful at first sight: a
parse error listing every symbol the parser could have accepted. Read
past it to the **last line**, which names the offending character by
its code point in decimal:

```text
Next token: Symbol '\215' @ L1:11-L1:12
```

215 is `×`. That line is the fastest way to identify a look-alike:
look the number up, and compare it with the table above.

## Identifiers

- A name starts with a letter or `_` and continues with letters,
  digits, `_` and `'` — so `x'`, `plus2` and `is_even` are all fine.
- A **leading `_` is reserved**. On its own, `_` is either a wildcard
  binder (`λ_. Z`) or a blank argument
  ([Implicit arguments and blanks](#implicits)); a name that merely
  starts with one is rejected.
- **Greek letters are not identifier characters.** `(φ : ℕ)` does not
  bind `φ`; it is a parse error, and the checker will tell you
  `Next token: Symbol '\966'`. Write `phi`. This bites people who are
  transcribing mathematics, where Greek variable names are the norm.

## Comments and numerals

- `--` starts a comment that runs to the end of the line. There is no
  block comment form.
- `0`, `1`, `2` and so on are ordinary decimal literals for natural
  numbers, and stand for `Z`, `S Z`, `S (S Z)` … Numbers are just
  numbers; the tower is what they abbreviate.

## Why Unicode at all

Because the statements are meant to be read. A Nova theorem is a type,
and a type you can read aloud in the vocabulary of the mathematics it
is about is worth a modest one-off cost in typing. If the glyphs are
still an obstacle after this chapter, the practical answer is to
configure the input mode once and then forget about it.
