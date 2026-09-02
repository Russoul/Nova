# Modules and imports

A file is a module, its name is its path, and `import` is the only way
one file sees another. There is no project file, no build manifest and
no search path to configure.

## Where a module lives

A module name resolves to a path **relative to the directory of the
file being checked**, with dots becoming directory separators. So from
`src/nova/nat.nova`:

- `import equality` loads `src/nova/equality.nova`;
- `import Data.Nat` would load `src/nova/Data/Nat.nova`.

Put your files in one directory and they can see each other. Check a
file from anywhere; what matters is where the file is, not where you
are.

## Qualified by default

`import M` makes `M`'s definitions available **qualified**:

```nova-sketch
import lib

def a : ℕ ≔ lib.two      -- fine
def b : ℕ ≔ two          -- Error: unknown name 'two'
```

To use a name unqualified, say so by listing it:

```nova
import equality (sym, cong, trans)
```

This is the corpus's normal style, and it is worth the small ceremony:
a reader of `nat.nova` can see at the top exactly which three
outside names appear bare in the file. Operators are listed in their
mention form — `import nat (+)` — and opening an operator brings its
fixity with it ([Operators and fixity](#operators)).

Qualified names also work where a licence is expected, which is why
`using` clauses in the corpus are full of them:

```nova
def plusZeroId : (n : ℕ) → n + Z ≡ n using (nat.+.eq) ≔ λn. ⋆
```

## What an import brings

Importing a module gives you its definitions and, for the names you
open, their fixities. It does **not** give you the modules *it*
imported. If `mid` opens `zero` from `base`, a file that opens `one`
from `mid` still cannot see `zero`:

```text
Error: def three: unknown name 'zero'
```

Transitivity applies to the *loading* of files, not to the visibility
of names — so what a file can say bare is exactly what its own import
list allows, and you never have to read a module's imports to know
what its names mean.

What does travel through the import graph is the **lemma store**: the
equations available to your `using` clauses are those of your import
closure. A module therefore checks identically on its own and as part
of a larger run, which is what makes the next section safe.

## Checking a whole development

Loading deduplicates by module name, so a module that is imported five
times is elaborated once. That makes it practical to have a single
module whose only job is to import everything:

```nova
import definingEq
import monoid
import group
```

That is the head of `src/nova/all.nova`, which imports every module in
the corpus. Checking it checks the whole development in one run:

```bash
nova elab src/nova/all.nova
```

## Names, and where they go

Name resolution happens **before** elaboration, in a pass of its own.
Every use of a name is resolved to the binder or the definition it
refers to, and after that the elaborator works with positions rather
than names; the checker's internals never consult one again.

Names reappear in exactly one place: the report. What you read in an
obligation — `(n : ℕ) (k : ℕ) (ih : plus k Z ≡ k ∈ ℕ) ⊢ …` — is
reconstructed from the names you wrote, purely so that the message is
legible. This is why the report always speaks in your vocabulary even
though nothing inside the checker does.

Within a file, the rules are the ones you would guess: a local binder
shadows an outer name, and a definition shadows an imported one.

## Conventions in the corpus

- **One topic per file**, named for it: `nat`, `equality`, `stream`,
  `ratArch`. Around sixty files, most under two hundred lines.
- **Open what you use bare, qualify the rest.** The import list at the
  top of a corpus file is short and is meant to be read.
- **Dependencies flow one way.** There is no cycle in the corpus and
  no way to write one — the loader refuses before anything is checked:

```text
Error: import cycle through module 'cyc2'
```
