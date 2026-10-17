-- :NspecPick, from anywhere: fuzzy-jump to a section or rule of any spec
vim.api.nvim_create_user_command('NspecPick', function() require('nspec.outline').pick() end, { desc = 'Jump to a section or rule of a spec' })
