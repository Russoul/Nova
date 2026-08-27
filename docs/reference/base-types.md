# The built-in types
%stub

Four types come with the language: the empty type, the unit type, the
natural numbers, and — because types are values here — the universes
that classify the rest.

## `ℕ`

- `Z`, `S t`, and decimal numerals as sugar.

## `ℕ-elim`

- `ℕ-elim (n. T) z (n ih. s) t` — motive, zero case, step case (value
  and induction hypothesis), scrutinee. This spelling **infers**.
- The motive group may be dropped, giving the checking-only
  `ℕ-elim z (n ih. s) t`; the motive then comes from the expected type.
- Motive-first is a convention shared with `⊎-elim` and `quot-elim`.

## Equality motives

- Parenthesise them; `(k. Z + k ≡ k)` is the shape you will write most.

## Which argument to recurse on

- `+` recurses on its **second** argument, so `n + Z ≡ n` is
  definitional while `Z + n ≡ n` is a lemma. Choosing the reducing order
  when you get to choose.

## `𝟘` and `𝟙`

- `𝟘-elim` and `()`, and the role `𝟘` plays in refutations.
