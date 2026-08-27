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

## The LSP server

- Semantic tokens, and what an editor gets today.

## Rendering the documentation

- `tools/render-specs.py` (specs), `nova-docs` (sources),
  `tools/render-reference.py` (this book).

## The pipeline

- Elaborator, artifact, kernel: what is trusted and what is not
  (`docs/NovaPipeline.txt`).
