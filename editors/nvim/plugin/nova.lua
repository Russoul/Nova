-- Entry point for a package install (pack/*/start/nova).
--
-- Neovim sources init.lua BEFORE it adds packages to 'runtimepath', so
-- `require("nova").setup()` in a user's init.lua cannot work for a
-- packaged plugin — the module is not findable yet. Packages are
-- expected to configure themselves from a variable the user set
-- earlier, which is what this does.
--
--   vim.g.nova = { ... }   -- options, set anywhere in init.lua
--   vim.g.nova = false     -- do not auto-setup; call setup() yourself
--
-- Plugin managers put the plugin on the runtimepath before user code
-- runs, so `require("nova").setup{...}` works there as usual; this
-- file is then a no-op if setup already ran (the guard below), and
-- otherwise applies the same defaults.

if vim.g.loaded_nova then
  return
end
vim.g.loaded_nova = true

if vim.g.nova == false then
  return
end

require("nova").setup(type(vim.g.nova) == "table" and vim.g.nova or {})
