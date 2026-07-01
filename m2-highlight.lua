-- m2-highlight.lua
-- Syntax highlighting for Macaulay2 session transcripts in Pandoc/Quarto.
-- Processes CodeBlock elements with class "default" or "macaulay2".

local KEYWORDS = {
  "listLocalSymbols", "listUserSymbols", "breakpoint", "pseudocode",
  "disassemble", "errorDepth", "installPackage", "needsPackage",
  "continue", "return", "finish", "break", "step", "code", "load",
  "help", "peek", "value", "print", "use", "end", "new"
}
-- longer keywords first so they match before shorter prefixes
table.sort(KEYWORDS, function(a, b) return #a > #b end)

local function esc(s)
  return (s:gsub("&", "&amp;"):gsub("<", "&lt;"):gsub(">", "&gt;"))
end

local function sp(cls, text)
  return '<span class="m2-' .. cls .. '">' .. text .. '</span>'
end

-- Character-level tokenizer for M2 code snippets.
-- comments_ok: allow -- to start a comment (only in input prompt lines).
local function tokenize(raw, comments_ok)
  local out, pos, len = {}, 1, #raw
  while pos <= len do
    local c = raw:sub(pos, pos)

    if c == '"' then
      -- string literal: scan for closing quote
      local e = raw:find('"', pos + 1, true) or len
      out[#out + 1] = sp("str", esc(raw:sub(pos, e)))
      pos = e + 1

    elseif c == '-' then
      local nc = raw:sub(pos + 1, pos + 1)
      if comments_ok and nc == '-' then
        -- comment: rest of line
        out[#out + 1] = sp("cmt", esc(raw:sub(pos)))
        pos = len + 1
      elseif nc == '>' then
        out[#out + 1] = sp("op", "-&gt;")
        pos = pos + 2
      else
        out[#out + 1] = esc(c); pos = pos + 1
      end

    elseif c == ':' and raw:sub(pos + 1, pos + 1) == '=' then
      out[#out + 1] = sp("op", ":=")
      pos = pos + 2

    elseif c:match('[%a_]') then
      -- try each keyword (sorted longest-first)
      local matched = false
      for _, kw in ipairs(KEYWORDS) do
        if raw:sub(pos, pos + #kw - 1) == kw then
          local nc = raw:sub(pos + #kw, pos + #kw)
          if nc == '' or not nc:match('[%w_]') then
            out[#out + 1] = sp("kw", kw)
            pos = pos + #kw
            matched = true
            break
          end
        end
      end
      if not matched then out[#out + 1] = esc(c); pos = pos + 1 end

    else
      out[#out + 1] = esc(c); pos = pos + 1
    end
  end
  return table.concat(out)
end

local function processLine(line)
  -- debugger input prompt:  ii7 :
  local dp, dc = line:match("^(ii%d+ : ?)(.*)")
  if dp then return sp("dbgi", esc(dp)) .. tokenize(dc, true) end

  -- debugger output prompt: oo7 =
  local dop, dor = line:match("^(oo%d+ = ?)(.*)")
  if dop then return sp("dbgo", esc(dop)) .. esc(dor) end

  -- normal input prompt: i1 :
  local ip, ic = line:match("^(i%d+ : ?)(.*)")
  if ip then return sp("inp", esc(ip)) .. tokenize(ic, true) end

  -- normal output prompt: o1 =
  local op, or_ = line:match("^(o%d+ = ?)(.*)")
  if op then return sp("out", esc(op)) .. esc(or_) end

  -- error lines (with or without file:line prefix)
  if line:match("error:") then return sp("err", esc(line)) end

  -- entering debugger banner
  if line:match("entering debugger") then return sp("dbg", esc(line)) end

  -- plain code / output continuation (no comment highlighting here
  -- to avoid coloring "------" table separators in output as comments)
  return tokenize(line, false)
end

local block_id = 0

function CodeBlock(block)
  local cls = block.classes and block.classes[1]
  if cls ~= "default" and cls ~= "macaulay2" then return nil end

  block_id = block_id + 1
  local lines = {}
  for line in (block.text .. "\n"):gmatch("([^\n]*)\n") do
    lines[#lines + 1] = "<span>" .. processLine(line) .. "</span>"
  end

  local html = string.format(
    '<div class="sourceCode m2-code" id="m2cb%d">'
    .. '<pre class="sourceCode code-with-copy">'
    .. '<code class="sourceCode">%s</code>'
    .. '</pre></div>',
    block_id,
    table.concat(lines, "\n")
  )
  return pandoc.RawBlock("html", html)
end
