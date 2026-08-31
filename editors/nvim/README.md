# Nova for Neovim

Starts `nova-lsp` for `.nova` buffers and gets out of the way.

* diagnostics, hover, go-to-definition, document symbols — from the
  server
* semantic highlighting — neovim's native support, so the server's
  legend maps straight onto the standard `@lsp.type.*` groups
* elaboration time after each load, as virtual text and in
  `b:nova_elab_time`

Requires neovim 0.9 or newer (native semantic tokens). No plugin
manager and no `nvim-lspconfig` needed — the client is started with
`vim.lsp.start`.

## Installing

From the flake, which bakes in the matching server:

```
nix run github:Russoul/Nova#install-nvim-plugin
```

That links the plugin into `~/.local/share/nvim/site/pack/nova/start/`,
which neovim loads on its own. Then:

```lua
require("nova").setup()
```

With a plugin manager instead, point it at `editors/nvim` in a checkout
— in which case `nova-lsp` must be on `PATH`, or named explicitly:

```lua
require("nova").setup({ cmd = "/path/to/nova-lsp" })
```

## Finding the server

`setup{ cmd = ... }`, then `$NOVA_LSP_BIN`, then the server the plugin
was built against (Nix installs only), then `nova-lsp` on `PATH`. An
absolute path that does not exist is reported directly rather than
left to surface as a spawn error in `:LspLog`.

## Options

```lua
require("nova").setup({
  cmd = nil,             -- path to nova-lsp; nil means use the ladder above
  elabtime = true,       -- false to disable, or a table:
                         --   virtual_text = true,   -- ⌛ at end of line
                         --   hl = "Comment",        -- its highlight group
                         --   notify = false,        -- also vim.notify
  on_attach = nil,       -- function(client, bufnr)
})
```

## Highlighting

The server classifies every token and publishes standard LSP semantic
token types, which neovim maps to `@lsp.type.keyword`,
`@lsp.type.variable`, `@lsp.type.operator`, `@lsp.type.number` and
`@lsp.type.comment`. Most colourschemes style these already. To
override:

```lua
vim.api.nvim_set_hl(0, "@lsp.type.operator.nova", { link = "Operator" })
```

Do not hand-write a mapping from the server's legend to your own
highlight groups: the legend lives in `Nova.LSP.Capabilities` and a
copy of it in Lua goes stale silently, leaving the token types it
forgot with no highlight at all.

## A note on when checking happens

The server declares `TextDocumentSyncKind.None`: it re-elaborates on
open and on **save**, not on every keystroke. Diagnostics, hover and
highlighting therefore describe the file as last saved, and the
elaboration time tells you what that check cost.
