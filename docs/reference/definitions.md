# Definitions

A Nova file is a list of definitions, and there is nothing else in it.
No statements, no imperative steps, no top-level expressions — just
names, their types, and what they stand for. This chapter is the shape
of a definition and the two ways to write the thing on the right.

## `def`

```nova-sketch
def name : type ≔ body
```

Three parts: the name you are introducing, the type it will have, and
the definition itself. The type is not optional. Nova never infers the
type of a top-level definition, and that is deliberate — the type is
the part a human reads, so you write it down.

```nova
def plusByHand : ℕ → ℕ → ℕ ≔ λm. λn. ℕ-elim n (k ih. S ih) m
```

You have already seen the other form, where the body is given by
clauses instead:

```nova
def double : ℕ → ℕ
  | double n ≔ plus n n
```

Both define exactly the same kind of thing. The clause form is a
convenience that expands into an ordinary definition
([Defining equations](#clausal-defs)); nothing downstream can tell
which you used.

## Functions

`λ` introduces a function and binds **one** argument:

```nova-sketch
λx. body
```

Multi-argument functions are nested λs, and application is
juxtaposition, left-associative — so `f x y` means `(f x) y`, and a
two-argument function is a function returning a function. This is
ordinary currying and behaves as you expect. Composition, from the
prelude, shows both at once:

```nova
def ∘ : {A B C : 𝕌} (g : B → C) (f : A → B) → A → C ≔ λA. λB. λC. λg. λf. λx. g (f x)
```

(The braces mark arguments the checker supplies for itself —
[Implicit arguments](#implicits). Ignore them for now and read the
body: five λs, then `g` applied to `f` applied to `x`.)

One rule about λ has no counterpart in most languages and will bite
you once: **the body of a λ extends as far right as it possibly can.**
It swallows operators, arrows, commas and everything else, so

```nova-sketch
λx. a , b
```

is `λx. (a , b)` and not the pair `(λx. a) , b`. A λ that is a
non-final component of a pair has to be parenthesised. The same
maximal-body rule applies to [`let`](#let).

## Everything is top-level

There is no `where`, no local function definition, and no nesting of
definitions. A helper is a definition of its own, sitting above the
thing that uses it. The only way to name something locally is
[`let`](#let), and that is an expression, not an item.

Nor is there a parameter list on a definition. If you want a
definition that works for every type, or every `n`, the quantifier
goes in the *type* and the argument is bound by a λ in the body — as
`∘` does above. Every definition in Nova is closed: it mentions
nothing but its own arguments and the names above it.

## Order matters

A definition sees the definitions above it, and nothing else:

```nova-sketch
def a : ℕ ≔ h 2      -- if h is defined below, this is an error
```

```text
Error: def a: unknown name 'h'
```

There is no forward reference and no mutual recursion between
definitions. Files read top to bottom, once. This is a stronger
constraint than most languages impose, and it is load-bearing: it is
what lets the checker treat everything above a definition as settled
when it gets there.

Within a definition, a binder shadows anything of the same name from
above — `λtwo. two` refers to the argument, whatever `two` meant in
the file.

## `type`

A definition whose body is a type can be written with `type` instead
of `def`, which saves you writing out its type:

```nova
type PiCode ≔ (𝟘 → 𝟙)
```

`type X ≔ T` and `def X : 𝕌 ≔ T` do the same job. The `type` form
exists because writing the classifier of a type is noise when the
right-hand side already says everything.

A type abbreviation is **opaque**, exactly like any other definition.
This surprises people, so it is worth seeing the failure:

```text
Error: def origin: pair checked against a non-⨯ type
  note: head exposure blocked for Pair — cite Pair.unfold
```

`Pair` was defined as `ℕ ⨯ ℕ`, and a pair was offered for it, but the
checker will not look inside a name unless the item lets it. Note the
second line: the error names the remedy, and adding
`using (Pair.unfold)` to that definition fixes it. This is the same
opacity you met with `plus` in [Your first file](#first-file), and
[`using`: licences and scope](#using-clauses) is where it is treated
properly.

## Definitions without bodies

A `def` may state a type and stop:

```nova
def plusZr : (n : ℕ) → plus n Z ≡ n
```

That declares the name without defining it. Everything below may use
it, and the file is not accepted until you supply the body — the
top-down workflow from [Your first file](#first-file), and the way to
program against an interface before you have an implementation.

## The `using` clause

Between the type and the `≔` an item may name the facts its checking
is allowed to use:

```nova
def plusZl : (n : ℕ) → plus Z n ≡ n using (plusZ) ≔ λn. ⋆
```

It is not an import and not a hint; it is this item's licence list.
[`using`: licences and scope](#using-clauses) covers it in full, and
until then, adding what the checker's `hint:` line names will get you
through.

## Two definitions that are really many

Two item forms expand into several definitions rather than one:

- a `def` **with clauses**, which also generates one equation per
  clause ([Defining equations](#clausal-defs));
- a `data` item, which generates a type, its constructors and its
  eliminators ([Defining your own types](#own-types)).

Both are macros. Everything they introduce arrives in the file as an
ordinary definition with an ordinary name, which is why the checker
announces them one by one:

```report
defined plus by clauses (plus, plusZ, plusS, plusEta)
```

## Comments

`--` starts a comment that runs to the end of the line. There is no
block comment form, and no documentation-comment convention: the
corpus puts an ordinary comment above an item and treats it as prose
for a human.
