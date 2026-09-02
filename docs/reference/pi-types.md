# Π-types
%stub

Function types whose result mentions the argument, and the sugar that
keeps a statement readable.

## Π-types

- `(x : A) → B` and the name-dropping form `A → B`.
- Binder groups **iterate**: `(x : A) (y : B) → C` is
  `(x : A) → (y : B) → C`, and a group may bind several names at one
  domain — `(x y : ℕ)`.
- The codomain is a full type, so a lemma statement needs no
  parentheses: `(n m : ℕ) → plus n m ≡ plus m n`.

## λ

- `λx. t`, one binder at a time; the body extends **maximally** — over
  operators, over the code formers, over pairs, over calc chains.
- Consequence: a λ that is a non-final pair component must be
  parenthesised.

## Application

- Juxtaposition, left-associative.
- Implicit arguments are inserted at spines ([Implicit arguments and blanks](#implicits)).

## η

- Function η is judgemental, which is why `funext` is a theorem and not
  an axiom.

## Wildcards

- `_` in binder position, never resolvable.
