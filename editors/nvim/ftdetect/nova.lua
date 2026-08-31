-- .nova files are Nova surface files. Neovim has no built-in mapping
-- for the extension, and the LSP client is started off this filetype
-- (see lua/nova/init.lua), so detection has to happen even when the
-- user never calls setup().
vim.filetype.add({
  extension = {
    nova = "nova",
  },
})
