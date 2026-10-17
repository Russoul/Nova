-- The outline of a spec: its sections, nested by heading depth, and in each
-- its rules by name. A language server in the editor's own process serves it
-- as document symbols (neo-tree's document_symbols, gO, any symbol picker),
-- and pick() searches the outlines of every spec with fzf-lua.
local tool = vim.fn.fnamemodify(debug.getinfo(1, 'S').source:sub(2), ':h:h:h:h') .. '/nspec.lua'
package.loaded.nspec = package.loaded.nspec or dofile(tool)
local nspec = package.loaded.nspec
local M = {}

-- { name, kind = 'section' | 'rule', n, col, first, last, children }: n and
-- col are where its name is, first..last the lines it spans. A section runs
-- to the next heading as deep or shallower; a rule is its bar and the formal
-- lines around it.
function M.outline(lines)
  local rows, root = nspec.rows(lines), { depth = 0, children = {} }
  local open = { root }
  local function close(last)
    open[#open].last = last
    open[#open] = nil
  end
  for n, row in ipairs(rows) do
    if row.kind == 'head' then
      local depth = #row.formal:match('^#+')
      while open[#open].depth >= depth do close(n - 1) end
      local section = { name = row.formal:sub(depth + 2), kind = 'section', n = n, col = 1, first = n, depth = depth, children = {} }
      table.insert(open[#open].children, section)
      open[#open + 1] = section
    elseif row.kind == 'bar' and #row.names > 0 then
      local first, last = n, n
      while rows[first - 1] and rows[first - 1].kind == 'formal' do first = first - 1 end
      while rows[last + 1] and rows[last + 1].kind == 'formal' do last = last + 1 end
      table.insert(open[#open].children, {
        name = table.concat(row.names, ', '),
        kind = 'rule',
        n = n,
        col = row.formal:find(row.names[1], 1, true),
        first = first,
        last = last,
        children = {},
      })
    end
  end
  while #open > 1 do close(#rows) end
  return root.children
end

-- The outline as LSP document symbols, positions in bytes (utf-8)
local KIND = { section = 3, rule = 12 } -- Namespace, Function
local function symbols(entries, lines)
  local out = {}
  for _, e in ipairs(entries) do
    local at = { line = e.n - 1, character = e.col - 1 }
    out[#out + 1] = {
      name = e.name,
      kind = KIND[e.kind],
      range = { start = { line = e.first - 1, character = 0 }, ['end'] = { line = e.last - 1, character = #lines[e.last] } },
      selectionRange = { start = at, ['end'] = at },
      children = symbols(e.children, lines),
    }
  end
  return out
end

-- Attaches buf to the server, which answers documentSymbol from the buffer's
-- current text and nothing else.
function M.serve(buf)
  vim.lsp.start({
    name = 'nspec',
    root_dir = vim.fs.dirname(vim.api.nvim_buf_get_name(buf)),
    cmd = function(dispatchers)
      local closing, id = false, 0
      return {
        request = function(method, params, callback)
          id = id + 1
          local ok, result = true, nil
          if method == 'initialize' then
            result = { capabilities = { documentSymbolProvider = true, positionEncoding = 'utf-8' } }
          elseif method == 'textDocument/documentSymbol' then
            local lines = vim.api.nvim_buf_get_lines(vim.uri_to_bufnr(params.textDocument.uri), 0, -1, false)
            ok, result = pcall(function() return symbols(M.outline(lines), lines) end)
          end
          vim.schedule(function()
            callback(not ok and { code = -32603, message = tostring(result) } or nil, ok and result or nil)
          end)
          return true, id
        end,
        notify = function(method)
          if method == 'exit' then
            closing = true
            vim.schedule(function() dispatchers.on_exit(0, 0) end)
          end
          return true
        end,
        is_closing = function() return closing end,
        terminate = function()
          if not closing then
            closing = true
            vim.schedule(function() dispatchers.on_exit(0, 0) end)
          end
        end,
      }
    end,
  }, { bufnr = buf })
end

-- Every section and rule of every spec, fuzzy-searched by its trail
-- (NovaKernel › QIITs › Leaves › el-…); a loaded buffer's text counts over
-- its file's.
function M.pick()
  local fzf, ansi = require('fzf-lua'), require('fzf-lua.utils').ansi_codes
  local entries = {}
  for _, path in ipairs(vim.fn.glob(vim.fs.dirname(nspec.foundation()) .. '/*.nspec', false, true)) do
    path = vim.fs.normalize(vim.fn.fnamemodify(path, ':p'))
    local buf = vim.fn.bufnr(path)
    local lines = buf > 0 and vim.api.nvim_buf_is_loaded(buf) and vim.api.nvim_buf_get_lines(buf, 0, -1, false)
      or vim.fn.readfile(path)
    local function walk(entries_, trail)
      for _, e in ipairs(entries_) do
        local shown = e.kind == 'rule' and ansi.magenta(e.name) or e.name
        entries[#entries + 1] = ('%s:%d:%d:%s › %s'):format(path, e.n, e.col, trail, shown)
        walk(e.children, trail .. ' › ' .. e.name)
      end
    end
    walk(M.outline(lines), ansi.grey(vim.fn.fnamemodify(path, ':t:r')))
  end
  fzf.fzf_exec(entries, {
    prompt = 'Spec> ',
    previewer = 'builtin',
    actions = fzf.defaults.actions.files,
    fzf_opts = { ['--delimiter'] = ':', ['--with-nth'] = '4..' },
  })
end

return M
