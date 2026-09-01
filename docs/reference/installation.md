# Installing and running Nova

Nova is a checker you run over a file, not a REPL you sit inside. This
chapter gets you a working binary and shows you the loop you will
spend the rest of the book in.

## Two ways to get a binary

Nova is written in [Idris 2](https://github.com/idris-lang/Idris2),
and there are two supported ways to build it. Both work; pick by which
tool you already have.

### With Nix

If you have [Nix](https://nixos.org) with flakes enabled, there is
nothing to install and nothing to configure:

```bash
nix run . -- elab src/nova/nat.nova
```

That builds the checker if it is not built already and runs it. Every
dependency — the compiler, the parser library, the language-server
library — is pinned in `flake.lock`, and the expensive parts come
prebuilt from the public binary cache, so a cold start builds only
Nova itself and its two small dependencies.

For a binary you can invoke repeatedly:

```bash
nix build          # ./result/bin/nova
```

This is the shorter road for a newcomer, because it cannot fail
halfway through bootstrapping a compiler.

### With pack

[pack](https://github.com/stefan-hoeck/idris2-pack) is the Idris
package manager, and the route to use if you are already developing
in Idris. You need:

- **Chez Scheme** — Idris 2's backend.
- **GMP** — the arbitrary-precision arithmetic library (`libgmp-dev`
  on Debian-family systems).
- **pack** itself, which bootstraps the compiler.

Then:

```bash
pack build nova.ipkg
```

That produces `build/exec/nova`. The first build takes a while,
because pack is building the compiler too; afterwards it is
incremental. `pack install-app nova.ipkg` puts `nova` on your `PATH`.

The two routes pin the same dependency versions — `flake.nix` mirrors
`pack.toml` — but not the same compiler: pack follows the pinned
Idris nightly, Nix follows the release in nixpkgs. Both are tested in
CI.

> **How commands are written in this book.** From here on you will see
> `nova elab file.nova`. Read that as whichever you set up:
> `nix run . -- elab file.nova`, `./result/bin/nova elab file.nova`,
> `build/exec/nova elab file.nova`, or plain `nova` if it is on your
> `PATH`.

## Checking a file

There is one command you will use constantly:

```bash
nova elab src/nova/nat.nova
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
input.nova:1:15: error: def bad: unknown name 'y'
1 | def bad : ℕ ≔ y
  |               ^
```

Errors stop the run. They are what you would expect from any compiler,
and they mean what they say.

**It is well-formed but unproved.** This is the case with no analogue
in an ordinary compiler: the file makes sense, but the checker could
not derive some equation it needed, so it lists what it had to assume.
Chapter 1 showed one. These are **obligations**, they are a normal
part of writing a file, and [Reading the report](#report) is
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
nova elab src/nova/all.nova
```

## The loop

In practice you will:

1. Write or edit a definition.
2. Run `elab` on the file.
3. Read the report — an error to fix, or an obligation to prove.
4. Add what it asked for, above the item that needed it.
5. Run again.

That fourth step is the one that will be unfamiliar, and it is the
subject of [Part VI](#report). What is worth noticing now is
that nothing here is interactive: the file is the whole state, and
running the checker is the only feedback mechanism. There is no
session to lose and no ordering of commands to remember.

## Two more commands

`nova` has a handful of other modes; two are worth knowing early.

```bash
nova run <file> <name>
```

`run` requires the file to be accepted, then evaluates one top-level
definition and prints its normal form. Be warned that it prints in the
kernel's own notation rather than surface syntax — the number four
comes out as `NatIntro1 (NatIntro1 (NatIntro1 (NatIntro1
(NatIntro0))))`. It is a way to confirm that something computes, not a
pretty-printer.

```bash
nova distill <file> <out-dir>
```

`distill` prints the file's modules back out as surface text and
verifies the round trip. You will not need it to write Nova; it exists
because the printer and the elaborator are held to being exact
inverses ([Tooling](#tooling)).

Running `nova` with no arguments lists every mode with a paragraph
each.

## Editor support

There are packaged clients for two editors. Installing either from the
flake bakes in the matching language server, so there is nothing to
configure and the two cannot drift apart:

```bash
nix run .#install-vscode-extension
nix run .#install-nvim-plugin
```

For any other editor, build the server and point a generic LSP client
at the binary for `.nova` files:

```bash
nix build .#nova-lsp        # ./result/bin/nova-lsp
pack build nova-lsp.ipkg    # build/exec/nova-lsp
```

What the server provides:

- **Diagnostics** — errors, obligations and open holes, in place, as
  you save.
- **Hover** — the goal of a `?` hole or of a `⋆`; the type at a binder
  or an implicit; what a blank was solved to, and why. This is the
  fastest way to ask "what goes here?".
- **Go to definition**, including across an import.
- **Document symbols** and **semantic tokens** — the same
  classification that colours the
  [rendered sources](nova/index.html), so your editor and this book
  agree on what is a keyword.

Completion, formatting and rename are deliberately not provided.

## Checking your work against the repository

Under Nix, one command runs every gate CI runs — the golden test
suite, the elaboration gate, the distill round trip, the spec
cross-check, this book's own checks, and the docs site:

```bash
nix flake check
```

Without Nix, the same ground is covered by two scripts: `./test.sh`
for the golden suite and the elaboration gate, and `./check-distill.sh`
for canonical printed form. If you contribute a corpus file, they must
pass either way.

## If it will not build

- **`nix` says the flake is not supported.** Flakes need to be enabled:
  add `experimental-features = nix-command flakes` to your Nix
  configuration.
- **pack cannot resolve the collection.** `pack.toml` pins a package
  collection and a compiler commit; a transient failure is usually a
  third-party host being unreachable, and retrying is the fix. This
  failure mode is the reason the Nix route exists.
- **A stale build directory.** `rm -rf build` and build again.
- **The glyphs come out as boxes.** That is a font problem, not a
  build problem — see [Reading and typing Nova](#notation).
