# Tooling
%stub

Everything the repository gives you beyond the checker.

## `nova elab`

- Checking one file, checking the corpus through `all.nova`.

## `nova eliminate`

- Case-splitting from the command line: fill a hole by eliminating a
  variable of its context ([Holes](#holes)).

## The other commands

- `survey`, `implicitize` and `census` — the implicit-argument
  migration tools, which measure what the recovery oracle could elide
  and rewrite a module closure accordingly.
- `rename` — a checked renaming across a module closure.

## `nova distill`

- Re-printing a module closure from its artifact and verifying the round
  trip; `src/nova` is kept in canonical distill form.

## The test suite

- `./test.sh`, the golden framework, and `--only`.
- `./check-elaborations.sh`, `./check-distill.sh` and
  `./normalize-corpus.sh` — the corpus gates, and the script that
  fixes what the distill gate complains about.
- `nix flake check` — the same gates plus the spec cross-check, the
  reference's own checks and the docs site, each as a flake check.
- `nix develop` for a shell where `idris2 --build nova.ipkg` works
  without a bootstrap.

## The LSP server

- Semantic tokens, and what an editor gets today.

## Rendering the documentation

- `tools/render-specs.py` (specs), `nova-docs` (sources),
  `tools/render-reference.py` (this book) — and `nix build .#site`,
  which runs all three into the tree that is published.

## The pipeline

- Elaborator, artifact, kernel: what is trusted and what is not
  (`docs/NovaPipeline.txt`).
