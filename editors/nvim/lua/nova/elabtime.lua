-- Render nova-lsp's `nova/elabTime` notification.
--
-- The server sends, after each successful load (didOpen / didSave):
--   method: "nova/elabTime"
--   params: { uri: string, millis: number, modules: number }
-- following the file's diagnostics, so the timing always describes the
-- state on screen.
--
-- Configured through nova.setup{ elabtime = { ... } }:
--
--   virtual_text = true,     -- ⌛ at the end of the cursor's line
--                            -- (first line when the cursor is in
--                            -- another file)
--   hl = "Comment",          -- highlight group for the virtual text
--   notify = false,          -- also vim.notify each report
--
-- The formatted time is always stored in `vim.b[bufnr].nova_elab_time`
-- (e.g. "1.3s" / "245ms"), for statusline components:
--
--   %{get(b:, 'nova_elab_time', '')}

local M = {}

local ns = vim.api.nvim_create_namespace("nova-elabtime")

--- Matches the VS Code client's formatting, so the two editors report
--- the same number the same way.
---@param millis number
---@return string
local function fmt(millis)
  if millis >= 1000 then
    return string.format("%.1fs", millis / 1000)
  end
  return string.format("%dms", millis)
end

---@param opts table|nil
function M.setup(opts)
  opts = opts or {}
  vim.lsp.handlers["nova/elabTime"] = function(_, result, _)
    if not (result and result.uri and result.millis) then
      return
    end
    local bufnr = vim.uri_to_bufnr(result.uri)
    if not vim.api.nvim_buf_is_loaded(bufnr) then
      return
    end

    local time = fmt(result.millis)
    local label = ("⌛ type checked in %s (%d modules)"):format(time, result.modules or 0)

    vim.b[bufnr].nova_elab_time = time

    vim.api.nvim_buf_clear_namespace(bufnr, ns, 0, -1)
    if opts.virtual_text ~= false then
      -- at the cursor's line when the cursor is still in the file that
      -- was type checked; the first line otherwise
      local line = 0
      if vim.api.nvim_get_current_buf() == bufnr then
        line = vim.api.nvim_win_get_cursor(0)[1] - 1
      end
      vim.api.nvim_buf_set_extmark(bufnr, ns, line, 0, {
        virt_text = { { label, opts.hl or "Comment" } },
        virt_text_pos = "eol",
      })
    end

    if opts.notify then
      vim.notify(label, vim.log.levels.INFO)
    end
  end
end

return M
