# Nova

Nova Foundation is a mechanised formal type theory based on
[extensional Martin Lof Type Theory](https://ncatlab.org/nlab/show/extensional+type+theory),
checked by an elaborator/kernel pipeline: surface files elaborate to
derivations that a small trusted kernel reads.
Written in [Idris2](https://github.com/idris-lang/Idris2).

See `docs/NovaFoundation.txt` for the theory, `docs/NovaPipeline.txt`
for the architecture and `docs/NovaKernel.txt` for the kernel rules.
Browse the rendered specs and syntax-highlighted `src/nova/*.nova`
sources online at [russoul.github.io/Nova](https://russoul.github.io/Nova/).

This branch is a fresh start: the kernel and the elaborator are being
written anew against `docs/NovaKernel.txt`. The previous pipeline — its
elaborator, kernel, language server, golden tests and gate scripts — is
frozen on the `dev-freeze` branch. The surface corpus in `src/nova/` is
kept in full as the acceptance target of the new one.

### Dependencies

[Just-a-Parser](https://github.com/Russoul/Just-a-Parser)

### Building

With [pack](https://github.com/stefan-hoeck/idris2-pack):

```
make build     # pack build nova.ipkg
make dev       # build, then the spec-rules check
```

With [Nix](https://nixos.org) (flakes) — `pack.toml`'s pins are
mirrored in `flake.nix`, so nothing is bootstrapped or fetched at
build time:

```
nix build                # the nova library
nix flake check          # the spec-rules gate
nix develop              # a shell where `idris2 --build nova.ipkg` just works
```

### Editor support

`editors/vscode` and `editors/nvim` are clients for the `nova-lsp`
language server of the frozen pipeline. There is no server on this
branch yet.
