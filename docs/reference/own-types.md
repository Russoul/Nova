# Defining your own types

Nova has one way to introduce a type, and it is the `data` item. This
chapter covers the fragment that matches a `data` declaration in a
language you already know: a type, its constructors, and — because
that is what a type *is* here — the induction principle that comes
with them. The full form has more in it, and waits until
[Quotient inductive-inductive types](#qiits).

## The simplest declaration

```nova-sketch
data ( Bool : U ; true : El Bool ; false : El Bool )
```

Three things to read. `Bool : U` names the type being declared — `U`
marks it as a *sort*, the thing this declaration brings into
existence. Then each constructor is named with its type, separated by
`;`, and `El Bool` is how you say "a value of the sort being
declared".

That `El` is a marker, not a function: it flags the positions that are
*recursive*, so the checker can tell which arguments it must supply
induction hypotheses for. Anything without it is an ordinary type
from outside the declaration.

## Recursion

Constructors may take values of the type being defined:

```nova
data ( N : U
     ; z : El N
     ; s : El N → El N )
```

That is the natural numbers, declared rather than built in. `z` takes
nothing; `s` takes an `N` and gives an `N`. The layout — one entry per
line, `;` leading — is the corpus's, and the whole thing is a single
item however many lines it spans.

## Parameters

A prefix in square brackets abstracts the whole declaration over
something:

```nova
data [a : 𝕌] ( List : U
     ; nil : El List
     ; cons : a → El List → El List )
```

`a` is a parameter, so this is one declaration, not one per element
type. Note the difference between the two arguments of `cons`: `a` is
an ordinary type from outside, and `El List` is a recursive position.

Everything the declaration generates is abstracted over the parameters
too, so the type is `List ℕ` and the constructors take the parameter
first:

```nova
def twoZeros : List ℕ using (List.unfold) ≔ cons ℕ Z (cons ℕ Z (nil ℕ))
```

The `List.unfold` licence is the same opacity you have met throughout:
`List ℕ` is a name, and building a value at it means letting the
checker see what the name stands for.

## What you get back

A `data` item is a macro. It expands into ordinary definitions, and
the checker names them as it goes:

```report
defined data (List, nil, cons)
```

That line lists the sort and the constructors. It does not list the
two definitions you will use most:

- **`ListElim`** — the eliminator, which is how you take a `List`
  apart and the subject of [the next chapter](#recursion);
- **`ListElimP`** — the same thing for proving, whose motive is a
  proposition rather than a type.

The naming rule is the sort's name with `Elim` or `ElimP` appended.
[Generated names](#generated-names) has the full table, including the
equations that let the checker compute with your constructors.

## Structural, not generative

Two textually identical `data` items define the **same** type, not two
lookalikes. There is no notion of a type's identity beyond its
signature, so declaring `List` twice in two modules gives you one
`List` — which is occasionally surprising, and is why the corpus does
not do it.

## What is deferred

The full `data` item does three more things this chapter has not shown:

- **Indices** — a sort can be a *family*, `V : ℕ → U`, with
  constructors that fix their index. That is
  [Indexed families](#indexed-families).
- **Sorts indexed by other sorts** of the same declaration —
  induction-induction.
- **Equation constructors** — entries whose type is an equation rather
  than a value, which impose a quotient.

The last two, with the full grammar, are
[Quotient inductive-inductive types](#qiits). None of them changes
what this chapter said; they widen what an entry may be.
