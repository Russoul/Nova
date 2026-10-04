-- Folding, outline, jump to a rule's definition, and the checker's findings
-- and token colours shown in the buffer. tools/nspec.lua is the one parser.
local tool = vim.fn.fnamemodify(debug.getinfo(1, 'S').source:sub(2), ':h:h:h') .. '/nspec.lua'
package.loaded.nspec = package.loaded.nspec or dofile(tool)
local nspec = package.loaded.nspec
local buf = vim.api.nvim_get_current_buf()

vim.bo.commentstring = '// %s'
vim.bo.comments = '://'
vim.opt_local.foldmethod = 'expr'
vim.opt_local.foldexpr = [[getline(v:lnum)=~'^#\+ '?'>'.matchend(getline(v:lnum),'^#\+'):'=']]
vim.opt_local.foldlevel = 99

-- gO: headings and named rules, in the location list
vim.keymap.set('n', 'gO', function()
  local items = {}
  for n, line in ipairs(vim.api.nvim_buf_get_lines(buf, 0, -1, false)) do
    local text = line:match('^#+ .*') or line:match('^%s*%-%-%-.-(%([^()]*%))')
    if text then
      items[#items + 1] = { bufnr = buf, lnum = n, text = text }
    end
  end
  vim.fn.setloclist(0, {}, ' ', { title = 'Outline', items = items })
  vim.cmd.lopen()
end, { buffer = buf, desc = 'Outline' })

-- gd: the foundation's definition of the rule name under the cursor
vim.keymap.set('n', 'gd', function()
  local name = vim.fn.matchstr(vim.fn.expand('<cWORD>'), [[[a-z][a-z0-9]*\(-[a-z0-9⁼ᴰ₀-₉]\+\)\+]])
  local path, line = nspec.where(name)
  if not path then
    return vim.notify('no foundation rule ' .. name, vim.log.levels.WARN)
  end
  vim.cmd("normal! m'")
  vim.cmd.edit(vim.fn.fnameescape(path))
  vim.api.nvim_win_set_cursor(0, { line, 0 })
  vim.cmd('normal! zv')
end, { buffer = buf, desc = 'Rule definition' })

-- every token in its kind's colour (the one table in tools/nspec.lua), except
-- that headings and prose follow the colourscheme
local theme = { heading = 'Title', prose = 'Comment' }
local namespace = vim.api.nvim_create_namespace('nspec')
local function refresh()
  for kind, colour in pairs(nspec.colours) do
    vim.api.nvim_set_hl(0, 'nspec_' .. kind, theme[kind] and { link = theme[kind] } or { fg = colour })
  end
  local findings, tokens = nspec.analyse(vim.api.nvim_buf_get_lines(buf, 0, -1, false), vim.api.nvim_buf_get_name(buf))
  vim.api.nvim_buf_clear_namespace(buf, namespace, 0, -1)
  for _, token in ipairs(tokens) do
    vim.api.nvim_buf_set_extmark(buf, namespace, token.n - 1, token.from - 1, {
      end_col = token.to,
      hl_group = 'nspec_' .. token.kind,
      priority = token.kind == 'prose' and 100 or 200, -- a rule name inside prose shows through
    })
  end
  for i, finding in ipairs(findings) do
    findings[i] = { lnum = finding.n - 1, col = (finding.col or 1) - 1, message = finding.message }
  end
  vim.diagnostic.set(namespace, buf, findings)
end
vim.api.nvim_create_autocmd({ 'TextChanged', 'InsertLeave', 'BufWritePost' }, { buffer = buf, callback = refresh })
refresh()
