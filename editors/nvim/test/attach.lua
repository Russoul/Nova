-- Headless smoke test: with only this plugin on the runtimepath, does
-- opening a .nova file get a live nova-lsp attached to the buffer, with
-- the capabilities the server advertises?
--
-- Run by the `nvim-plugin` flake check (nix/checks.nix). Expects
-- $NOVA_NVIM_PLUGIN (the built plugin) and one file argument.
--
--   nvim --headless -u editors/nvim/test/attach.lua <file.nova>

vim.opt.runtimepath:prepend(vim.env.NOVA_NVIM_PLUGIN)
vim.cmd("filetype plugin indent on")

local failures = {}

local function check(name, ok, detail)
  if ok then
    io.write(("ok   %s\n"):format(name))
  else
    io.write(("FAIL %s: %s\n"):format(name, detail or ""))
    table.insert(failures, name)
  end
end

require("nova").setup()

-- The plugin was built by nix, so the baked path must have replaced the
-- placeholder; otherwise the test below would silently be exercising
-- whatever nova-lsp happens to be on PATH.
local server = require("nova").server_path()
check("server path is baked in", server:sub(1, 11) == "/nix/store/", server)

vim.cmd.edit(vim.fn.argv(0))

check("filetype detected", vim.bo.filetype == "nova", vim.bo.filetype)

local attached = vim.wait(60000, function()
  return #vim.lsp.get_clients({ bufnr = 0, name = "nova_lsp" }) > 0
end, 100)
check("nova-lsp attached", attached)

if attached then
  local client = vim.lsp.get_clients({ bufnr = 0, name = "nova_lsp" })[1]
  local caps = client.server_capabilities

  check("hover", caps.hoverProvider ~= nil and caps.hoverProvider ~= false)
  check("definition", caps.definitionProvider ~= nil and caps.definitionProvider ~= false)
  check("documentSymbol", caps.documentSymbolProvider ~= nil and caps.documentSymbolProvider ~= false)
  check("semanticTokens", caps.semanticTokensProvider ~= nil)

  -- The legend the plugin deliberately does NOT copy. If this ever
  -- changes, neovim's native mapping follows it and the plugin needs no
  -- edit — but the test should say so out loud.
  local legend = caps.semanticTokensProvider and caps.semanticTokensProvider.legend
  local types = legend and table.concat(legend.tokenTypes, ",") or "<none>"
  io.write(("     legend: %s\n"):format(types))

  -- documentSymbol is the request that lsp-lib's null `deprecated`
  -- used to break for strict clients; assert it actually answers.
  local res = client:request_sync("textDocument/documentSymbol", {
    textDocument = vim.lsp.util.make_text_document_params(0),
  }, 30000, 0)
  check(
    "documentSymbol answers",
    res ~= nil and res.err == nil and type(res.result) == "table" and #res.result > 0,
    res and vim.inspect(res.err) or "no response"
  )
end

if #failures > 0 then
  io.write(("\n%d check(s) failed\n"):format(#failures))
  vim.cmd("cquit 1")
end

io.write("\nall checks passed\n")
vim.cmd("quitall!")
