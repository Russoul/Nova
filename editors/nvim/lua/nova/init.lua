-- Neovim support for Nova: start nova-lsp for .nova buffers, and let
-- the editor's own machinery do the rest.
--
-- Everything shown — diagnostics, hover, go-to-definition, document
-- symbols, semantic highlighting — comes from the server
-- (src/idris/Nova/LSP). Neovim has handled semantic tokens natively
-- since 0.9, including `workspace/semanticTokens/refresh`, so there is
-- no token decoding here: the server's legend maps straight onto the
-- standard @lsp.type.* groups. Keeping that mapping out of Lua is the
-- point — a hand-written copy of the legend silently rots the moment
-- Nova.LSP.Capabilities changes.
--
-- The one Nova-specific addition is `nova/elabTime` (see
-- nova.elabtime).

local M = {}

-- Replaced at build time with the store path of the nova-lsp this
-- plugin was built against (nix/nvim.nix). Left as the literal
-- placeholder in the source tree, where it means "nothing was baked
-- in" — hence the `@` test in resolve_cmd rather than a nil test.
local BAKED_SERVER_PATH = "@novaLspPath@"

--- Four sources, most explicit first. NOVA_LSP_BIN outranks the baked
--- path so that `nix develop` and the test suite — which both already
--- set it — can point the editor at a freshly-built server without
--- editing any config.
---@param configured string|nil
---@return string
local function resolve_cmd(configured)
  if configured ~= nil and configured ~= "" then
    return configured
  end

  local from_env = vim.env.NOVA_LSP_BIN
  if from_env ~= nil and from_env ~= "" then
    return from_env
  end

  if not vim.startswith(BAKED_SERVER_PATH, "@") then
    return BAKED_SERVER_PATH
  end

  return "nova-lsp"
end

--- A .nova file's project is the git repository containing it; failing
--- that, its own directory. The server resolves imports relative to the
--- files it is given, so the root only affects client-side grouping.
---@param bufnr integer
---@return string
local function root_dir(bufnr)
  local fname = vim.api.nvim_buf_get_name(bufnr)
  if fname == "" then
    return vim.uv.cwd()
  end
  local git = vim.fs.root(fname, ".git")
  return git or vim.fs.dirname(fname)
end

local default_opts = {
  -- Path to nova-lsp. Empty means use the ladder in resolve_cmd.
  cmd = nil,
  -- Show each load's elaboration time (see nova.elabtime); pass a
  -- table to configure it, or false to leave it off.
  elabtime = true,
  -- Called with (client, bufnr) on attach, for buffer-local mappings.
  on_attach = nil,
}

--- Start (or reuse) a nova-lsp client for one buffer.
---@param bufnr integer
---@param opts table
local function start(bufnr, opts)
  local cmd = resolve_cmd(opts.cmd)

  -- An absolute path that is not there is worth catching here: the
  -- failure is otherwise a spawn error in :LspLog that does not say
  -- which of the four sources produced the path.
  if cmd:find("/", 1, true) and vim.fn.executable(cmd) == 0 then
    vim.notify(
      ("nova: no nova-lsp at %s. Build one with `nix build .#nova-lsp` "):format(cmd)
        .. "or `pack build nova-lsp.ipkg`, or set opts.cmd.",
      vim.log.levels.ERROR
    )
    return
  end

  vim.lsp.start({
    name = "nova_lsp",
    cmd = { cmd },
    root_dir = root_dir(bufnr),
    on_attach = opts.on_attach,
  }, { bufnr = bufnr })
end

--- Wire nova-lsp to .nova buffers. Safe to call more than once.
---@param opts table|nil
function M.setup(opts)
  opts = vim.tbl_extend("force", default_opts, opts or {})

  -- Also registered in ftdetect/, which covers the case where this
  -- plugin is on the runtimepath at startup and setup() never runs.
  -- Repeating it here is not redundant: ftdetect/ scripts are sourced
  -- once, when `filetype on` executes during startup, so a plugin whose
  -- directory joins the runtimepath later — a plugin manager that
  -- resets 'packpath', an rtp:append from init.lua — never gets its
  -- ftdetect sourced at all. vim.filetype.add is idempotent.
  vim.filetype.add({ extension = { nova = "nova" } })

  if opts.elabtime ~= false then
    require("nova.elabtime").setup(type(opts.elabtime) == "table" and opts.elabtime or {})
  end

  local group = vim.api.nvim_create_augroup("nova", { clear = true })
  vim.api.nvim_create_autocmd("FileType", {
    group = group,
    pattern = "nova",
    callback = function(args)
      start(args.buf, opts)
    end,
    desc = "Start nova-lsp for .nova buffers",
  })

  -- setup() may well run after .nova buffers are already open (a
  -- session restore, a lazy-loaded spec, or simply detection having
  -- been unavailable when they were read). Setting the filetype fires
  -- the autocmd above, so both cases funnel through one path.
  for _, bufnr in ipairs(vim.api.nvim_list_bufs()) do
    if vim.api.nvim_buf_is_loaded(bufnr) then
      local name = vim.api.nvim_buf_get_name(bufnr)
      if vim.bo[bufnr].filetype == "nova" then
        start(bufnr, opts)
      elseif name:sub(-5) == ".nova" then
        vim.bo[bufnr].filetype = "nova"
      end
    end
  end
end

--- The nova-lsp this plugin resolves to, for `:checkhealth`-style
--- questions and for scripting.
---@return string
function M.server_path()
  return resolve_cmd(nil)
end

return M
