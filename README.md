# Nova

Nova Foundation is a mechanised formal type theory based on
[extensional Martin Lof Type Theory](https://ncatlab.org/nlab/show/extensional+type+theory),
checked by an elaborator/kernel pipeline: surface files elaborate to
certificate-carrying artifacts that a small trusted kernel re-checks.
Written in [Idris2](https://github.com/idris-lang/Idris2).

See `docs/NovaFoundation.txt` for the theory, `docs/NovaPipeline.txt`
for the architecture, `docs/NovaElaboration.txt` for the surface
syntax and elaborator, and `docs/NovaKernel.txt` for the kernel rules.
Browse the rendered specs and syntax-highlighted `src/nova/*.nova`
sources online at [russoul.github.io/Nova](https://russoul.github.io/Nova/).

### Dependencies

[Just-a-Parser](https://github.com/Russoul/Just-a-Parser)

### Building

With [pack](https://github.com/stefan-hoeck/idris2-pack):

```
make build     # pack build nova.ipkg  ->  build/exec/nova
make test      # golden tests + the elaboration gate
```

With [Nix](https://nixos.org) (flakes) — `pack.toml`'s pins are
mirrored in `flake.nix`, so nothing is bootstrapped or fetched at
build time:

```
nix build                # the nova elaborator
nix run . -- elab src/nova/all.nova
nix flake check          # every CI gate: tests, elaborations, distill, specs, site
nix develop              # a shell where `idris2 --build nova.ipkg` just works
```

Also buildable: `nix build .#nova-lsp` (language server),
`.#nova-docs` (HTML renderer), `.#nova-tests` (golden-test driver),
`.#site` (the rendered specs and corpus published to GitHub Pages),
`.#vscode-extension` (the VS Code extension) and `.#nvim-plugin` (the
neovim plugin).

### Editor support

`nova-lsp` serves diagnostics, hover, go-to-definition, document
symbols and semantic highlighting, and reports each load's elaboration
time as a `nova/elabTime` notification.

`editors/vscode` and `editors/nvim` are clients for it. Installing
either from the flake bakes in the matching `nova-lsp`, so there is
nothing to configure and the two cannot drift apart:

```
nix run .#install-vscode-extension
nix run .#install-nvim-plugin     # then: require("nova").setup()
```

See `editors/nvim/README.md` for options and for using it with a
plugin manager instead.
