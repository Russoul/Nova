#!/usr/bin/env luajit
-- A long-lived spec checker for the pen relay: tools/nspec.lua's analysis,
-- loaded once. The first analysis builds the grammar and judges every line
-- (~2.5 s on NovaFoundation.nspec); later ones re-judge only lines they have
-- not seen (~40 ms), so a candidate edit is checked against the whole file.
--
-- Requests on stdin, one after another:
--   PATH TAB N NEWLINE, then the file's N lines
-- answered on stdout with
--   K NEWLINE, then K findings `LINE TAB COL TAB MESSAGE`,
--   T NEWLINE, then T tokens `LINE TAB FROM TAB TO TAB KIND`
-- (a token's FROM and TO are bytes of its line, from 1, inclusive; where
-- tokens overlap, a later one is the more specific: a rule cited in prose)
-- PATH is the file the text stands for: it decides whether the foundation's
-- grammar and rules are cited (they are, unless PATH is the foundation).
-- When the text IS the foundation, its rule names are read from the text
-- itself, not from the file on disk: an edit that moves lines must not make
-- every later rule `already defined` at its old line.
local here = debug.getinfo(1, 'S').source:sub(2):match('^(.*)/[^/]*$') or '.'
package.path = here .. '/../?.lua;' .. package.path
local nspec = require('nspec')
local on_disk, scratch = nspec.foundation, os.tmpname()

while true do
  local header = io.read('*l')
  if not header then break end
  local path, n = header:match('^(.*)\t(%d+)$')
  local lines = {}
  for i = 1, tonumber(n) do lines[i] = io.read('*l') end
  nspec.foundation = on_disk
  if path:match('NovaFoundation%.%w+$') then
    local f = assert(io.open(scratch, 'w'))
    f:write(table.concat(lines, '\n'), '\n')
    f:close()
    nspec.foundation = function() return scratch end
  end
  local findings, tokens = nspec.analyse(lines, path)
  io.write(#findings, '\n')
  for _, f in ipairs(findings) do
    io.write(f.n, '\t', f.col or 1, '\t', (f.message:gsub('[\t\n]', ' ')), '\n')
  end
  local shown = {}
  for _, t in ipairs(tokens) do
    if t.from and t.to then shown[#shown + 1] = t end
  end
  io.write(#shown, '\n')
  for _, t in ipairs(shown) do io.write(t.n, '\t', t.from, '\t', t.to, '\t', t.kind, '\n') end
  io.flush()
end
os.remove(scratch)
