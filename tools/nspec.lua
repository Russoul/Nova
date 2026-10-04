#!/usr/bin/env luajit
-- The Nova spec format (.nspec): checker and HTML renderer.
--
-- A line is, by how it starts:
--   # Title        a heading; ## nests under #
--   // text        prose
--   --- (names)    a bar: the lines around it are a rule, which the names
--                  define (the foundation) or cite
--   anything else  formal text, verbatim; a trailing // text is prose
-- Prose has no markup. A rule name in it is a reference.
--
-- A formal line with ::= is a grammar production: metavariables on the left,
-- alternatives split by " | " on the right. In an alternative a category is
-- named by its first metavariable and every other token is literal; the
-- alternative <natural number> is a numeral. A subscript or superscript
-- reads as the same text full-size (☐ᵢ is ☐ i), except after a
-- metavariable, where it is part of its name (t₀).
--
-- If the grammar has the category J, every other formal line must be a J:
-- judgements on one line are three spaces apart, an indented line continues
-- the one above, and a metavariable keeps one category throughout its rule
-- (outside a rule, throughout its line).
--
--   nspec.lua [FILE…]            check; a finding is `path:line:col: message`
--   nspec.lua --html OUT FILE…   render
--   nspec.lua --where NAME       where the foundation defines NAME
local M = {}

-- The token kinds, and the colour of each, for Neovim and the HTML page
-- (in Neovim, headings and prose take the colourscheme's colours instead).
M.colours = {
  heading = '#f5f5f5', -- a heading line
  prose = '#a6adc8', -- prose, and a note after formal text
  bar = '#6c7086', -- a rule's bar
  rule = '#a995d6', -- a rule name: on its bar, and where prose cites it
  keyword = '#f9e2af', -- fixed syntax
  nova = '#5c6370', -- a Nova metavariable: term, context, telescope, …
  level = '#fab387', -- a universe level
  index = '#fab387', -- an index: of a variable, of a weakening
  tos = '#53cad4', -- a metavariable of the theory of signatures
  proof = '#cba6f7', -- a proof
}

-- The kind of a metavariable, by its grammar category (the category's first
-- metavariable). A category not listed here is left uncoloured.
M.kinds = {
  nova = 'x l l̄ 𝒰 𝒰̄ Σ I Γ Δ σ e˲ ē t',
  level = 'ℓ',
  index = 'i',
  tos = '𝕤 𝕔 Φ 𝔄 𝕥 𝔽',
  proof = 'α ᾱ π̄ φ',
}

local HERE = debug.getinfo(1, 'S').source:sub(2):match('^(.*)/[^/]*$') or '.'
local DOCS = HERE .. '/../docs'

local function exists(path)
  local f = io.open(path)
  return f and f:close() and true
end
local function read(path)
  local out = {}
  for line in io.lines(path) do out[#out + 1] = line end
  return out
end
function M.foundation()
  local new = DOCS .. '/NovaFoundation.nspec'
  return exists(new) and new or DOCS .. '/NovaFoundation.txt' -- .txt: not yet converted
end

-- Characters ---------------------------------------------------------------

local MACRON = '\204\132'
local PRE = { ['ā'] = 'a', ['ē'] = 'e', ['ī'] = 'i', ['ō'] = 'o', ['ū'] = 'u', ['Ū'] = 'U', ['ᾱ'] = 'α' }

-- the characters of s, precomposed overbars taken apart, and where each starts
local function chars(s)
  local cs, at = {}, {}
  for i, ch in s:gmatch('()([%z\1-\127\194-\244][\128-\191]*)') do
    if PRE[ch] then
      cs[#cs + 1], at[#cs + 1] = PRE[ch], i
      cs[#cs + 1], at[#cs + 1] = MACRON, i
    else
      cs[#cs + 1], at[#cs + 1] = ch, i
    end
  end
  at[#cs + 1] = #s + 1
  return cs, at
end
local function code(ch)
  local b = ch:byte(1)
  if b < 0x80 then return b end
  local n = b >= 0xF0 and 4 or b >= 0xE0 and 3 or 2
  local c = b % 2 ^ (7 - n)
  for i = 2, n do c = c * 64 + ch:byte(i) % 64 end
  return c
end
local function mark(c) return c >= 0x300 and c <= 0x36F or c == 0x2F2 end
local function prime(c) return c == 0x27 or c >= 0x2032 and c <= 0x2034 end

-- subscripts, then superscripts, each before its full-size character
local SMALL, SUBSCRIPT = {}, {}
do
  local subs = '₀0₁1₂2₃3₄4₅5₆6₇7₈8₉9₊+₋-₌=₍(₎)ₐaₑeₒoₓxₕhₖkₗlₘmₙnₚpₛsₜtᵢiᵣrᵤuᵥvⱼj'
  local sups = '⁰0¹1²2³3⁴4⁵5⁶6⁷7⁸8⁹9⁺+⁻-⁼=⁽(⁾)ⁿnⁱi'
  for small, full in subs:gmatch('([\194-\244][\128-\191]*)(.)') do SMALL[small], SUBSCRIPT[small] = full, true end
  for small, full in sups:gmatch('([\194-\244][\128-\191]*)(.)') do SMALL[small] = full end
end
local function letter(ch) return #ch == 1 and ch:match('%a') end
local function alnum(ch) return #ch == 1 and ch:match('%w') end

-- Rule names: el-pi-i, el-sigma-e₁ ------------------------------------------

local function name_char(ch) return alnum(ch) or ch == '-' or ch == '⁼' or ch == 'ᴰ' or ch:match('^\226\130[\128-\137]$') end
local function is_name(s)
  return s:match('^%l[%l%d]*%-') and not s:match('%u') and not s:match('%-%-') and not s:match('%-$')
end
local function names_in(text)
  local out, run = {}, {}
  local cs = chars(text .. ' ')
  for _, ch in ipairs(cs) do
    if name_char(ch) then run[#run + 1] = ch
    else
      local word = table.concat(run):gsub('^%-+', ''):gsub('%-+$', '')
      if is_name(word) then out[#out + 1] = word end
      run = {}
    end
  end
  return out
end

-- Lines --------------------------------------------------------------------

-- { n, kind, formal, prose, names } of each line
function M.rows(lines, mark_)
  local out, under = {}, false -- under: below a bar, in the same block
  for n, line in ipairs(lines) do
    local row = { n = n, kind = 'blank', formal = '', prose = '', names = {} }
    if mark_ == '//' and line:match('^#+ ') then
      row.kind, row.formal = 'head', line
    elseif line:sub(1, #mark_) == mark_ then
      row.kind, row.prose = 'prose', line
    elseif line:match('%S') then
      local cut = line:find('%s' .. mark_, 1, false) and line:find('%s+' .. mark_:gsub('%p', '%%%0'))
      row.formal = cut and line:sub(1, cut - 1) or line:gsub('%s+$', '')
      row.prose = cut and line:sub(cut) or ''
      local bare = row.formal:gsub('%b()', '')
      row.kind = bare:match('^%s*%-%-%-[%-%s]*$') and 'bar' or 'formal'
      local found = {}
      if row.kind == 'bar' then
        for group in row.formal:gmatch('%b()') do
          for x in group:sub(2, -2):gmatch('[^%s,]+') do found[#found + 1] = x end
        end
      elseif under then
        found[1] = row.formal:match('%s%(([^()%s]+)%)$')
      end
      for _, x in ipairs(found) do
        if is_name(x) then row.names[#row.names + 1] = x end
      end
    end
    under = row.kind == 'bar' or under and row.kind == 'formal'
    out[#out + 1] = row
  end
  return out
end

-- name -> the line of the foundation that defines it
local function defined()
  local path, out = M.foundation(), {}
  for _, row in ipairs(M.rows(read(path), path:match('%.nspec$') and '//' or '#')) do
    for _, x in ipairs(row.names) do out[x] = out[x] or row.n end
  end
  return out
end

-- Grammar ------------------------------------------------------------------

local function lex(s, roots)
  local cs, at = chars(s)
  local toks, i = {}, 1
  while i <= #cs do
    if cs[i]:match('^%s$') then
      i = i + 1
    else
      local small = SMALL[cs[i]] ~= nil
      -- character k full-size, if it is in this token's script
      local function full(k)
        if small then return SMALL[cs[k] or ''] end
        return cs[k] and not SMALL[cs[k]] and cs[k] or nil
      end
      local j = i + 1
      if letter(full(i)) or full(i) == '-' and letter(full(j) or '') then
        while full(j) and (alnum(full(j)) or full(j) == '-' and letter(full(j + 1) or '')) do j = j + 1 end
      elseif full(i):match('^%d$') then
        while (full(j) or ''):match('^%d$') do j = j + 1 end
      end
      while not small and cs[j] and mark(code(cs[j])) do j = j + 1 end
      local base = {}
      for k = i, j - 1 do base[#base + 1] = full(k) end
      base = table.concat(base)
      local root = roots[base] and base or nil
      while root and not small and cs[j] and (SUBSCRIPT[cs[j]] or prime(code(cs[j]))) do j = j + 1 end
      toks[#toks + 1] = {
        text = small and base or table.concat(cs, '', i, j - 1),
        root = root,
        number = base:match('^%d+$') and true,
        from = at[i],
        to = at[j] - 1,
      }
      i = j
    end
  end
  return toks
end

-- the productions among the rows: `roots ::= alternative | alternative`
local function grammar(rows)
  local sources, current = {}, nil
  for _, row in ipairs(rows) do
    local lhs, rhs = row.formal:match('^(.-)%s*::=%s*(.*)$')
    if row.kind == 'formal' and lhs then
      current, row.production = { lhs = lhs, rhs = rhs }, true
      sources[#sources + 1] = current
    elseif row.kind == 'formal' and current and row.formal:match('^%s*|') then
      current.rhs, row.production = current.rhs .. ' ' .. row.formal:gsub('^%s+', ''), true
    elseif row.formal ~= '' or row.kind ~= 'formal' then
      current = nil
    end
  end
  local g = { cats = {}, order = {}, roots = {}, lits = {}, key = {} }
  for _, source in ipairs(sources) do
    local cat = { member = {}, alts = {}, prods = {}, index = #g.order + 1 }
    for root in (source.lhs .. ','):gmatch('%s*(.-)%s*,') do
      root = table.concat((chars(root)))
      cat.name = cat.name or root
      cat.member[root], g.roots[root] = true, true
    end
    for alt in (source.rhs .. ' | '):gmatch('(.-)%s|%s') do
      if alt:match('^%s*<natural number>%s*$') then cat.number = true
      elseif alt:match('%S') and not alt:match('^%s*<') then cat.alts[#cat.alts + 1] = alt end
    end
    g.cats[cat.name] = cat
    g.order[#g.order + 1] = cat
    g.key[#g.key + 1] = source.lhs .. '::=' .. source.rhs
  end
  local id = 0
  for _, cat in ipairs(g.order) do
    local function add(rhs)
      id = id + 1
      cat.prods[#cat.prods + 1] = { id = id, lhs = cat.name, rhs = rhs }
    end
    add({ { var = cat.name } })
    if cat.number then add({ { number = cat.name } }) end
    for _, alt in ipairs(cat.alts) do
      local rhs = {}
      for _, tok in ipairs(lex(alt, g.roots)) do
        if tok.root == tok.text and g.cats[tok.text] then rhs[#rhs + 1] = { nt = tok.text }
        else
          rhs[#rhs + 1] = { lit = tok.text }
          g.lits[tok.text] = true
        end
      end
      add(rhs)
    end
  end
  g.key = table.concat(g.key, '\n')
  return g
end

-- Earley recognition of toks as a `start`; pin[k] fixes token k's reading
-- (a category, or 'lit'). Returns true, or false and the last token reached.
local function recognise(g, toks, start, pin)
  local n, sets = #toks, {}
  for k = 0, n do sets[k] = { list = {}, seen = {}, want = {} } end
  local function add(k, prod, dot, origin)
    local key, set = (prod.id * 128 + dot) * 512 + origin, sets[k]
    if set.seen[key] then return end
    set.seen[key] = true
    local item = { prod = prod, dot = dot, origin = origin }
    set.list[#set.list + 1] = item
    local sym = prod.rhs[dot + 1]
    if sym and sym.nt then
      set.want[sym.nt] = set.want[sym.nt] or {}
      table.insert(set.want[sym.nt], item)
    end
  end
  for _, prod in ipairs(g.cats[start].prods) do add(0, prod, 0, 0) end
  local last = 0
  for k = 0, n do
    local set, tok, fixed, i = sets[k], toks[k + 1], pin and pin[k + 1], 1
    if #set.list > 0 then last = k end
    while i <= #set.list do
      local item = set.list[i]
      i = i + 1
      local sym = item.prod.rhs[item.dot + 1]
      if not sym then
        for _, parent in ipairs(sets[item.origin].want[item.prod.lhs] or {}) do
          add(k, parent.prod, parent.dot + 1, parent.origin)
        end
      elseif sym.nt then
        for _, prod in ipairs(g.cats[sym.nt].prods) do add(k, prod, 0, k) end
      elseif tok then
        local fits
        if sym.lit then fits = tok.text == sym.lit and (not fixed or fixed == 'lit')
        elseif sym.number then fits = tok.number and (not fixed or fixed == sym.number)
        else fits = tok.root and g.cats[sym.var].member[tok.root] and (not fixed or fixed == sym.var) end
        if fits then add(k + 1, item.prod, item.dot + 1, item.origin) end
      end
    end
  end
  for _, item in ipairs(sets[n].list) do
    if item.prod.lhs == start and item.origin == 0 and not item.prod.rhs[item.dot + 1] then return true end
  end
  return false, last
end

-- A judgement: its tokens, and for each the readings some parse gives it.
local cache = {}
local function judge(g, parts)
  local key = {}
  for _, part in ipairs(parts) do key[#key + 1] = part.text end
  key = table.concat(key, '\n')
  cache[g.key] = cache[g.key] or {}
  local hit = cache[g.key][key]
  if hit then return hit end
  local toks = {}
  for p, part in ipairs(parts) do
    for _, tok in ipairs(lex(part.text, g.roots)) do
      tok.part = p
      toks[#toks + 1] = tok
    end
  end
  local result = { toks = toks }
  result.ok, result.stuck = recognise(g, toks, 'J')
  for k, tok in ipairs(result.ok and toks or {}) do
    local readings = {} -- fixed syntax first: it is the class shown when both fit
    if g.lits[tok.text] then readings[1] = 'lit' end
    for _, cat in ipairs(g.order) do
      if tok.root and cat.member[tok.root] or tok.number and cat.number then readings[#readings + 1] = cat.name end
    end
    tok.live = {}
    for _, reading in ipairs(readings) do
      if #readings == 1 and tok.root or recognise(g, toks, 'J', { [k] = reading }) then
        tok.live[reading] = true
        tok.class = tok.class or reading
      end
    end
    tok.class = tok.class or 'lit'
  end
  cache[g.key][key] = result
  return result
end

-- The judgements, grouped by what shares metavariables: a rule, or outside
-- a rule one line. A judgement is its parts { n, col, text }, one per line.
local function units(rows)
  local out, block, has_bar = {}, {}, false
  local function close()
    local rule = {}
    for _, line in ipairs(block) do
      if not has_bar then out[#out + 1] = line end
      for _, judgement in ipairs(line) do rule[#rule + 1] = judgement end
    end
    if has_bar then out[#out + 1] = rule end
    block, has_bar = {}, false
  end
  for _, row in ipairs(rows) do
    if row.kind == 'bar' then has_bar = true
    elseif row.kind ~= 'formal' then close()
    elseif row.production then
    elseif row.formal:match('^%s') and #block > 0 then
      local above = block[#block]
      table.insert(above[#above], { n = row.n, col = row.formal:find('%S'), text = row.formal:gsub('^%s+', '') })
    else
      local line, from = {}, 1
      while row.formal:find('%S', from) do
        local a = row.formal:find('%S', from)
        local b = (row.formal:find('%s%s%s', a) or #row.formal + 1) - 1
        line[#line + 1] = { { n = row.n, col = a, text = row.formal:sub(a, b) } }
        from = b + 1
      end
      block[#block + 1] = line
    end
  end
  close()
  return out
end

-- Analysis -----------------------------------------------------------------

-- findings { n, col, message } and tokens { n, from, to, kind } of a file
function M.analyse(lines, path)
  local own = path:match('%.nspec$') and '//' or '#'
  local rows, names = M.rows(lines, own), defined()
  local cites = not path:match('NovaFoundation%.%w+$')
  local findings, tokens = {}, {}
  local function report(n, col, message) findings[#findings + 1] = { n = n, col = col, message = message } end

  local function token(n, from, to, kind) tokens[#tokens + 1] = { n = n, from = from, to = to, kind = kind } end

  local prefixes, level, kinds = {}, 0, {}
  for kind, categories in pairs(M.kinds) do
    for name in categories:gmatch('%S+') do kinds[table.concat((chars(name)))] = kind end
  end
  for name in pairs(names) do prefixes[name:match('^[^-]+')] = true end
  for i, row in ipairs(rows) do
    if row.kind == 'head' then
      local depth = #row.formal:match('^#+')
      if depth > level + 1 then report(row.n, 1, 'heading skips a level') end
      level = depth
      token(row.n, 1, #row.formal, 'heading')
    end
    if row.prose ~= '' then token(row.n, #lines[row.n] - #row.prose + 1, #lines[row.n], 'prose') end
    if row.kind == 'bar' then
      for from, to in row.formal:gmatch('()%-%-%-+()') do token(row.n, from, to - 1, 'bar') end
    end
    local at = 1
    for _, x in ipairs(row.names) do
      local from, to = row.formal:find(x, at, true)
      token(row.n, from, to, 'rule')
      at = to + 1
    end
    if row.kind == 'bar' and not (rows[i + 1] and rows[i + 1].kind == 'formal' and rows[i + 1].formal ~= '') then
      report(row.n, 1, 'bar without a conclusion')
    end
    for _, x in ipairs(row.names) do
      if cites and not names[x] then report(row.n, row.formal:find(x, 1, true), 'no foundation rule ' .. x) end
      if not cites and names[x] ~= row.n then report(row.n, 1, x .. ' is already defined at line ' .. names[x]) end
    end
    local shift, seen = #lines[row.n] - #row.prose, 1
    for _, x in ipairs(names_in(row.prose)) do
      local from, to = row.prose:find(x, seen, true)
      local _, dashes = x:gsub('%-', '')
      if names[x] then
        token(row.n, shift + from, shift + to, 'rule')
      elseif prefixes[x:match('^[^-]+')] and dashes > 1 then
        report(row.n, shift + from, 'no foundation rule ' .. x)
      end
      seen = to + 1
    end
  end

  local sources = rows
  if cites and M.foundation():match('%.nspec$') then
    sources = M.rows(read(M.foundation()), '//')
    for _, row in ipairs(rows) do sources[#sources + 1] = row end
  end
  local g = grammar(sources)
  for _, row in ipairs(rows) do -- a production: its metavariables by kind, the rest fixed syntax
    local left, own, class = row.production and (row.formal:find('::=', 1, true) or 0), nil, false
    for _, tok in ipairs(left and lex(row.formal, g.roots) or {}) do
      own = own or tok.text
      local kind = 'keyword'
      if tok.from < left then kind = tok.root and kinds[own]
      elseif tok.root == tok.text and g.cats[tok.text] then kind = kinds[tok.text] end
      class = tok.text == '<' or class and tok.text ~= '>' -- <a lexical class>: left plain
      if kind and not class and tok.text ~= '>' then token(row.n, tok.from, tok.to, kind) end
    end
  end
  if not g.cats.J then return findings, tokens, rows end
  for _, rule in ipairs(units(rows)) do
    local category = {} -- metavariable -> the readings every site so far allows
    for _, parts in ipairs(rule) do
      local result = judge(g, parts)
      local function place(tok) return parts[tok.part].n, parts[tok.part].col + tok.from - 1 end
      if not result.ok then
        local tok = result.toks[result.stuck + 1]
        local n, col = parts[#parts].n, parts[#parts].col + #parts[#parts].text
        if tok then n, col = place(tok) end
        report(n, col, 'not a judgement' .. (tok and (': unexpected ' .. tok.text) or ': it ends too soon'))
      end
      for _, tok in ipairs(result.ok and result.toks or {}) do
        local n, col = place(tok)
        if tok.root and not (tok.live.lit and next(tok.live, 'lit') == nil and next(tok.live) == 'lit') then
          local seen = category[tok.text]
          if not seen then
            seen = {}
            for c in pairs(tok.live) do seen[c] = true end
            category[tok.text] = seen
          else
            for c in pairs(seen) do
              if not tok.live[c] then seen[c] = nil end
            end
            if not next(seen) then
              report(n, col, tok.text .. ' has another category earlier in this rule')
              category[tok.text] = nil
            end
          end
        end
        local kind = tok.class == 'lit' and 'keyword' or kinds[tok.class]
        if kind then token(n, col, col + tok.to - tok.from, kind) end
      end
    end
  end
  return findings, tokens, rows
end

function M.where(name)
  local line = defined()[name]
  return line and M.foundation(), line
end

-- HTML -----------------------------------------------------------------------

local CSS = [[body{font:14px/1.5 ui-monospace,monospace;margin:2em;background:#1e1e2e;color:#cdd6f4}
div{white-space:pre;min-height:1.5em}
details{margin-left:2ch}
summary{font-weight:bold;margin-left:-2ch;cursor:pointer}
i{font-style:normal}
a{color:inherit;text-decoration:none}
a[href]{border-bottom:1px dotted}
.prose a{color:%RULE%}
:target{outline:1px solid}]]

local function escape(s) return (s:gsub('[&<>"]', { ['&'] = '&amp;', ['<'] = '&lt;', ['>'] = '&gt;', ['"'] = '&quot;' })) end
local function stem(path) return path:match('([^/]*)%.%w+$') end

local function render(paths, out)
  local files, anchors = {}, {}
  for _, path in ipairs(paths) do
    local _, tokens, rows = M.analyse(read(path), path)
    files[#files + 1] = { path = path, rows = rows, tokens = tokens }
    for _, row in ipairs(rows) do
      for _, x in ipairs(row.names) do anchors[x] = anchors[x] or (path .. ':' .. row.n) end
    end
  end
  local function link(text, here)
    local html = escape(text)
    for _, x in ipairs(names_in(text)) do
      if anchors[x] and anchors[x] ~= here then
        html = html:gsub(x:gsub('%p', '%%%0'), ('<a href="#%s">%s</a>'):format(x, x), 1)
      end
    end
    return html
  end
  local body = {}
  local function put(s) body[#body + 1] = s end
  for _, file in ipairs(files) do
    put('<h1>' .. escape(stem(file.path)) .. '</h1>')
    local by_line, level = {}, 0
    for _, tok in ipairs(file.tokens) do
      by_line[tok.n] = by_line[tok.n] or {}
      by_line[tok.n][#by_line[tok.n] + 1] = tok
    end
    for _, row in ipairs(file.rows) do
      local here = file.path .. ':' .. row.n
      if row.kind == 'head' then
        local depth = #row.formal:match('^#+')
        put(('</details>'):rep(math.max(0, level - depth + 1)))
        put('<details open><summary class="heading">' .. escape(row.formal:sub(depth + 2)) .. '</summary>')
        level = depth
      elseif row.kind == 'prose' then
        put('<div class="prose">' .. link(row.prose:sub(4), nil) .. '</div>')
      else
        local text, at = {}, 1
        table.sort(by_line[row.n] or {}, function(x, y) return x.from < y.from end)
        for _, tok in ipairs(by_line[row.n] or {}) do
          if tok.to > #row.formal then break end -- the note's tokens: it is rendered whole, below
          local piece = escape(row.formal:sub(tok.from, tok.to))
          if tok.kind == 'rule' then
            piece = (anchors[piece] == here and '<a id="%s"></a>%s' or '<a href="#%s">%s</a>'):format(piece, piece)
          end
          text[#text + 1] = escape(row.formal:sub(at, tok.from - 1))
          text[#text + 1] = ('<i class="%s">%s</i>'):format(tok.kind, piece)
          at = tok.to + 1
        end
        text[#text + 1] = escape(row.formal:sub(at))
        if row.prose ~= '' then text[#text + 1] = '<span class="prose">' .. link(row.prose, nil) .. '</span>' end
        put('<div>' .. table.concat(text) .. '</div>')
      end
    end
    put(('</details>'):rep(level))
  end
  local titles = {}
  for _, path in ipairs(paths) do titles[#titles + 1] = stem(path) end
  local kinds, css = {}, { (CSS:gsub('%%RULE%%', M.colours.rule)) }
  for kind in pairs(M.colours) do kinds[#kinds + 1] = kind end
  table.sort(kinds)
  for _, kind in ipairs(kinds) do css[#css + 1] = ('.%s{color:%s}'):format(kind, M.colours[kind]) end
  local f = assert(io.open(out, 'w'))
  f:write('<!doctype html><meta charset=utf-8><title>', escape(table.concat(titles, ' · ')), '</title><style>',
    table.concat(css, '\n'), '</style>\n', table.concat(body, '\n'), '\n')
  f:close()
end

-- Command line ---------------------------------------------------------------

local function main(args)
  if args[1] == '--where' then
    local path, line = M.where(args[2])
    io.write(path and (path .. ':' .. line) or '', '\n')
    os.exit(path and 0 or 1)
  elseif args[1] == '--html' then
    render({ unpack(args, 3) }, args[2])
  else
    local paths, bad = { unpack(args) }, false
    if #paths == 0 then
      for path in io.popen('ls "' .. DOCS .. '"/*.nspec 2>/dev/null'):lines() do paths[#paths + 1] = path end
    end
    for _, path in ipairs(paths) do
      for _, f in ipairs((M.analyse(read(path), path))) do
        io.write(('%s:%d:%d: %s\n'):format(path, f.n, f.col or 1, f.message))
        bad = true
      end
    end
    os.exit(bad and 1 or 0)
  end
end

if arg and arg[0] and arg[0]:match('nspec%.lua$') then main(arg) end
return M
