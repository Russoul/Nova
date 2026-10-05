# Nova

Nova Foundation is a mechanised formal type theory based on
[extensional Martin Lof Type Theory](https://ncatlab.org/nlab/show/extensional+type+theory),
checked by an elaborator/kernel pipeline: surface files elaborate to
derivations that a small trusted kernel reads.
Written in [OCaml](https://ocaml.org).

See `docs/NovaFoundation.nspec` for the theory, `docs/NovaPipeline.txt`
for the architecture and `docs/NovaKernel.nspec` for the kernel rules.
Browse the rendered specs and syntax-highlighted `src/nova/*.nova`
sources online at [russoul.github.io/Nova](https://russoul.github.io/Nova/).

This branch is a fresh start: the kernel and the elaborator are being
written anew, in OCaml, against `docs/NovaKernel.nspec`. The previous
Idris2 pipeline — its elaborator, kernel, language server, golden tests
and gate scripts — is frozen on the `dev-freeze` branch. The surface
corpus in `src/nova/` is kept in full as the acceptance target of the
new one.

### Building

With [dune](https://dune.build):

```
dune build              # the nova executable, _build/default/src/ocaml/bin/main.exe
dune exec -- nova       # run it
make dev                # build, then the spec check
```

With [Nix](https://nixos.org) (flakes):

```
nix build                # the nova executable
nix run . -- <command>
nix flake check          # the build and the spec-format gate
nix develop              # a shell with ocaml, dune, ocaml-lsp, ocamlformat and utop
```

### Editor support

`editors/vscode` and `editors/nvim` are clients for the `nova-lsp`
language server of the frozen pipeline. There is no server on this
branch yet.
