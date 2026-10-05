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

-- Every token in its kind's colour (the one table in tools/nspec.lua), except
-- that headings and prose follow the colourscheme. The analysis runs in
-- slices of a few milliseconds, so the editor never waits for it, and a
-- newer change abandons the one in progress.
local theme = { heading = 'Title', prose = 'Comment' }
local marks = { vim.api.nvim_create_namespace('nspec_1'), vim.api.nvim_create_namespace('nspec_2') }
local diagnostics = vim.api.nvim_create_namespace('nspec')
local latest, shown = 0, 1

local function show(findings, tokens)
  for kind, colour in pairs(nspec.colours) do
    vim.api.nvim_set_hl(0, 'nspec_' .. kind, theme[kind] and { link = theme[kind] } or { fg = colour })
  end
  local fresh = marks[3 - shown] -- the new marks go in before the old ones go: no flicker
  for _, token in ipairs(tokens) do
    vim.api.nvim_buf_set_extmark(buf, fresh, token.n - 1, token.from - 1, {
      end_col = token.to,
      hl_group = 'nspec_' .. token.kind,
      priority = token.kind == 'prose' and 100 or 200, -- a rule name inside prose shows through
    })
  end
  vim.api.nvim_buf_clear_namespace(buf, marks[shown], 0, -1)
  shown = 3 - shown
  for i, finding in ipairs(findings) do
    findings[i] = { lnum = finding.n - 1, col = (finding.col or 1) - 1, message = finding.message }
  end
  vim.diagnostic.set(diagnostics, buf, findings)
end

local function refresh()
  latest = latest + 1
  local job = latest
  local function current()
    return job == latest and vim.api.nvim_buf_is_valid(buf)
  end
  vim.schedule(function() -- several changes at once start one analysis
    if not current() then
      return
    end
    local lines, path, deadline = vim.api.nvim_buf_get_lines(buf, 0, -1, false), vim.api.nvim_buf_get_name(buf), 0
    local work = coroutine.create(function()
      return nspec.analyse(lines, path, function()
        if vim.uv.hrtime() > deadline then coroutine.yield() end
      end)
    end)
    local function step()
      if not current() then
        return
      end
      deadline = vim.uv.hrtime() + 5e6
      local ok, findings, tokens = coroutine.resume(work)
      if not ok then
        vim.notify('nspec: ' .. tostring(findings), vim.log.levels.ERROR)
      elseif coroutine.status(work) ~= 'dead' then
        vim.defer_fn(step, 1)
      elseif vim.deep_equal(lines, vim.api.nvim_buf_get_lines(buf, 0, -1, false)) then
        show(findings, tokens) -- unless the text moved on meanwhile (typing): the next change redoes it
      end
    end
    step()
  end)
end
vim.api.nvim_create_autocmd({ 'TextChanged', 'InsertLeave', 'BufWritePost' }, { buffer = buf, callback = refresh })
refresh()
