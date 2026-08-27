# Equality: reflection instead of J
%stub

The single deepest difference, taken slowly.

## Agda's equality

- An inductive family with one constructor. `refl` is data, `J` (or
  pattern matching) is how you use it, and a proof of `a ≡ b` is a
  *thing* that must be transported along.

## Nova's equality

- A proposition at `Ω`. Proof-irrelevant, so all proofs are `⋆`; and
  reflected, so a proof makes the sides judgementally equal
  ([Reflection](#reflection)).
- There is no constructor and nothing to match on.

## What follows immediately

| Agda | Nova |
| --- | --- |
| `sym`, `trans`, `cong` by pattern matching | `⋆` |
| `subst` moves a value along a proof | `transport` is the identity |
| UIP needs `--with-K` or an axiom | a theorem, one line |
| funext is an axiom | a theorem, one line |
| `≡` is `Set`-valued, storable in a record | `Ω`-valued, with `Id` for the storable version |

## What you give up

- **Decidable type checking.** With reflection the checker cannot
  always decide, so it assumes and reports.
- **Canonicity arguments** you may be used to, and the intuition that
  a closed term of `ℕ` always evaluates.
- Pattern matching on proofs, and everything built from it.

## What it is like in practice

- Proof scripts get shorter; the work moves into stating the right
  lemmas and naming them.
- Where an Agda proof fights `subst`, a Nova proof fights the `using`
  clause.
