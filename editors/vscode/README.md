# Nova for VS Code

Language support for [Nova](https://github.com/Russoul/Nova) `.nova`
files, backed by the `nova-lsp` language server.

* diagnostics — every elaboration error, with its caret range
* hover — the type of the name under the cursor
* go-to-definition — across the file's whole import closure, including
  modules that are not themselves open
* document symbols — the file's top-level items
* semantic highlighting — the server classifies every token, so what
  you see is what the lexer saw
* elaboration time in the status bar, reported by the server after each
  load

## Requirements

A `nova-lsp` executable. The extension looks for one in this order:

1. the `nova.lsp.path` setting
2. the `NOVA_LSP_BIN` environment variable
3. the server it was built against, if it was installed from the Nix
   flake — in which case there is nothing to configure
4. `nova-lsp` on `PATH`

Build one with `nix build .#nova-lsp` or `pack build nova-lsp.ipkg`.

## Installing

From the flake, which bakes in the matching server:

```
nix run github:Russoul/Nova#install-vscode-extension
```

Otherwise build the `.vsix` and install it by hand:

```
nix build github:Russoul/Nova#vscode-extension
code --install-extension ./result/nova.vsix
```

## A note on when checking happens

The server declares `TextDocumentSyncKind.None`: it re-elaborates on
open and on **save**, not on every keystroke. Diagnostics, hover and
highlighting therefore describe the file as last saved. This is
deliberate — elaboration is a whole-module kernel check, not an
incremental parse — and the status bar's timing tells you what that
check cost.

## Settings

| setting | default | meaning |
| --- | --- | --- |
| `nova.lsp.path` | `""` | path to `nova-lsp`; empty means use the ladder above |
| `nova.elabTime.show` | `true` | show elaboration time in the status bar |

## Commands

* **Nova: Restart Language Server**
* **Nova: Show Language Server Log**
