# Installing and running Nova

Nova is a checker you run over a file, not a REPL you sit inside. This
chapter gets you a working binary and shows you the loop you will
spend the rest of the book in.

## Prerequisites

Nova is written in [Idris 2](https://github.com/idris-lang/Idris2) and
built with [pack](https://github.com/stefan-hoeck/idris2-pack), which
manages the Idris compiler and every dependency for you. You need:

- **Chez Scheme** — Idris 2's backend.
- **GMP** — the arbitrary-precision arithmetic library (`libgmp-dev`
  on Debian-family systems).
- **pack** — install it once by following its README; it bootstraps
  Idris 2 itself.
- **git**, to clone this repository.

Everything else is pinned in `pack.toml`: the exact Idris commit, the
package collection, and the two custom dependencies
([Just-a-Parser](https://github.com/Russoul/Just-a-Parser) for the
parser and `lsp-lib` for the editor server). You do not fetch those by
hand; pack reads the pins and does it.

## Building

From the repository root:

```bash
pack build nova.ipkg
```

That produces `build/exec/nova`. It takes a while the first time,
because pack is building the compiler as well; afterwards it is
incremental.

If you would rather have `nova` on your `PATH` than type the path:

```bash
pack install-app nova.ipkg
```

Throughout this book commands are written as `build/exec/nova …`, the
form that works straight after a build.

## Checking a file

There is one command you will use constantly:

```bash
build/exec/nova elab src/nova/nat.nova
```

`elab` reads the file, checks every item in order, and prints what it
found. There are exactly three things it can tell you.

**It is accepted.** The run names each item as it goes and finishes
with one word:

```report
Accepted.
```

That word is the whole guarantee: every definition in the file
typechecks, every theorem in it has been proved, and the kernel has
re-verified the lot. The process also exits with status `0`, so `elab`
drops straight into a script or a CI job.

While it works, each item produces a line. A plain definition just
gets its name; a definition written with clauses reports the extra
names it generated along the way:

```report
defined plus by clauses (plus, plusZ, plusS, plusEta)
```

Those extra names are the equations your clauses stand for — you will
meet them in [Defining equations](#clausal-defs) and can ignore them
until then.

**Something is malformed.** A name that does not exist, a syntax
error, a type that cannot be made sense of at all:

```nova
def bad : ℕ ≔ y
```

```report
Error: def bad: unknown name 'y'
```

Errors stop the run. They are what you would expect from any compiler,
and they mean what they say.

**It is well-formed but unproved.** This is the case with no analogue
in an ordinary compiler: the file makes sense, but the checker could
not derive some equation it needed, so it lists what it had to assume.
Chapter 1 showed one. These are **obligations**, they are a normal
part of writing a file, and [Reading the report](#report-and-holes) is
devoted to them. A file with obligations is not accepted, and the exit
status is non-zero.

## Where imports come from

A module name resolves to a path relative to **the directory of the
file you are checking**, with dots becoming directory separators. So
inside `src/nova/nat.nova`, `import equality` loads
`src/nova/equality.nova`, and `import Data.Nat` would load
`src/nova/Data/Nat.nova`. There is no search path and no project file
to configure; put your files in one directory and they can see each
other.

The corpus takes advantage of this: `src/nova/all.nova` imports every
module, so one run checks everything.

```bash
build/exec/nova elab src/nova/all.nova
```

## The loop

In practice you will:

1. Write or edit a definition.
2. Run `elab` on the file.
3. Read the report — an error to fix, or an obligation to prove.
4. Add what it asked for, above the item that needed it.
5. Run again.

That fourth step is the one that will be unfamiliar, and it is the
subject of [Part VI](#report-and-holes). What is worth noticing now is
that nothing here is interactive: the file is the whole state, and
running the checker is the only feedback mechanism. There is no
session to lose and no ordering of commands to remember.

## Two more commands

`nova` has a handful of other modes; two are worth knowing early.

```bash
build/exec/nova run <file> <name>
```

`run` requires the file to be accepted, then evaluates one top-level
definition and prints its normal form. Be warned that it prints in the
kernel's own notation rather than surface syntax — the number four
comes out as `NatIntro1 (NatIntro1 (NatIntro1 (NatIntro1
(NatIntro0))))`. It is a way to confirm that something computes, not a
pretty-printer.

```bash
build/exec/nova distill <file> <out-dir>
```

`distill` prints the file's modules back out as surface text and
verifies the round trip. You will not need it to write Nova; it exists
because the printer and the elaborator are held to being exact
inverses ([Tooling](#tooling)).

Running `nova` with no arguments lists every mode with a paragraph
each.

## Editor support

An LSP server is built separately:

```bash
pack build nova-lsp.ipkg
```

Point your editor's generic LSP client at `build/exec/nova-lsp` for
`.nova` files. There is no packaged extension for any editor yet, so
this is the manual route. What the server currently provides:

- **Diagnostics** — errors and obligations, in place, as you save.
- **Hover** — the type at a binder or an implicit; what a blank was
  solved to and why; and, on a `⋆`, the goal it is standing in for.
  That last one is Nova's equivalent of asking an editor "what goes
  here?".
- **Go to definition**, including across an import.
- **Document symbols** and **semantic tokens** — the same
  classification that colours the
  [rendered sources](nova/index.html), so your editor and this book
  agree on what is a keyword.

Completion, formatting and rename are deliberately not provided.

## Checking your work against the repository

Two scripts run everything:

```bash
./test.sh
```

runs the golden test suite and re-checks the whole corpus, and

```bash
./check-distill.sh
```

verifies that `src/nova` is in canonical printed form. If you
contribute a corpus file, both must pass.

## If it will not build

- **pack cannot resolve the collection.** `pack.toml` pins a package
  collection and a compiler commit; a transient failure is usually a
  third-party host being unreachable, and retrying is the fix.
- **A stale build directory.** `rm -rf build` and build again.
- **The glyphs come out as boxes.** That is a font problem, not a
  build problem — see [Reading and typing Nova](#notation).
