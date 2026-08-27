# Tooling
%stub

Everything the repository gives you beyond the checker.

## `nova elab`

- Checking one file, checking the corpus through `all.nova`.

## `nova distill`

- Re-printing a module closure from its artifact and verifying the round
  trip; `src/nova` is kept in canonical distill form.

## The test suite

- `./test.sh`, the golden framework, and `--only`.
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
