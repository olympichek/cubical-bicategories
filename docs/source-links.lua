-- Turn links to project source into links to Agda's highlighted HTML.
function Link(link)
  local file, suffix = link.target:match("^([^?#]+)(.*)$")
  if not file or file:match("^%a[%w+.-]*:") or file:match("^/") then return end
  local base = pandoc.path.directory(os.getenv("AGDA_DOC_SOURCE"))
  -- Module names follow the repository tree, including relative links to siblings.
  local parts = {}
  for part in pandoc.path.join({base, file}):gmatch("[^/]+") do
    if part == ".." then
      if #parts == 0 then return end
      table.remove(parts)
    elseif part ~= "." then
      table.insert(parts, part)
    end
  end
  local source = table.concat(parts, "/")
  local name = source:match("^src/(.+)%.lagda%.md$") or source:match("^src/(.+)%.agda$")
  if not name then return end

  local fragment = suffix:match("(#.*)$") or ""
  local line_number = fragment:match("^#L(%d+)$")
  if line_number then
    local input = assert(io.open(source, "r"))
    local offset = 1
    for _ = 1, tonumber(line_number) - 1 do
      local line = assert(input:read("*l"), "Invalid source line in " .. link.target)
      offset = offset + utf8.len(line) + 1
    end
    local line = assert(input:read("*l"), "Invalid source line in " .. link.target)
    input:close()
    -- Agda uses one-based Unicode character positions, including the literate prose.
    fragment = "#" .. (offset + utf8.len(line:match("^%s*")))
  end
  link.target = name:gsub("/", ".") .. ".html" .. fragment
  return link
end

-- The repository's link to the rendered site is redundant on the site itself.
function Para(paragraph)
  if os.getenv("AGDA_DOC_SOURCE") ~= "README.md" or #paragraph.content ~= 1 then return end
  local link = paragraph.content[1]
  if link.t == "Link" and pandoc.utils.stringify(link) == "Rendered documentation" then
    return {}
  end
end
