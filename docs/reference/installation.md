# Installing and running Nova
%stub

Getting a working toolchain, and the edit/check loop you will live in.

## Prerequisites

- Idris2 via [pack](https://github.com/stefan-hoeck/idris2-pack), Chez
  Scheme, GMP.
- [Just-a-Parser](https://github.com/Russoul/Just-a-Parser), resolved by
  `pack.toml`.

## Building

```bash
pack build nova.ipkg
```

## Checking a file

```bash
build/exec/nova elab src/nova/nat.nova
```

- A file is **accepted** iff the run ends with zero obligations.
- Anything else is a report: obligations, holes, or an error. [Reading the report](#report)
  explains how to read it.

## The loop

- Edit, re-run `elab`, read the report, add a lemma, repeat.
- `./test.sh` runs the golden suite and the whole corpus.
- `build/exec/nova distill f.nova out/` re-prints a file's module closure
  from the elaborated artifact and checks the round trip.

## Editor support

- The LSP server (`nova-lsp.ipkg`) provides semantic tokens; the same
  classification colours the [rendered sources](nova/index.html).
- Notation is Unicode-heavy; see [Notation and how to type it](#notation).
