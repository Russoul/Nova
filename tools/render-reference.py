#!/usr/bin/env python3
"""Render the language reference in docs/reference/ to one HTML page.

The reference is written FOR HUMAN READERS — it is a tutorial and a
guide, not a rule list; docs/*.txt remain the normative specs and this
page links into them rather than restating them. Sources are a small,
fixed Markdown subset (see BLOCK GRAMMAR below); the chapter order and
the part titles live in PARTS here, so chapters are files named by
slug and never by number.

A chapter whose second line is `%stub` is an OUTLINE, not prose: it
renders with a stub badge and is counted in the progress line, so the
page is honest about what is written and what is only planned.

Nova code fences (```nova) are highlighted with the same token classes
the LSP sends an editor (Nova.LSP.Capabilities' legend: keyword,
variable, operator, number, comment) and the same palette the rendered
sources page uses, so a snippet here looks exactly like the same line
in src/nova.

Snippets are QUOTATIONS, not copies: every ```nova block must appear
verbatim in src/nova, which `--check` enforces (see check_snippets).
The corpus is elaborated by the test suite and kept in canonical
distill form, so a faithful quote is a snippet the implementation has
already accepted — and a language change that re-distills the corpus
breaks the quote instead of silently rotting the book. A snippet that
is genuinely illustrative rather than lifted (a grammar skeleton, a
deliberately wrong spelling) uses the ```nova-sketch fence: same
highlighting, exempt from the check, and visible as an exemption in
the source.

BLOCK GRAMMAR
  # Title            chapter heading (first line of every file)
  %stub              outline marker (second line, optional)
  ## / ###           section / subsection
  ```lang … ```      code fence (nova = highlighted AND checked against
                     src/nova; nova-sketch = highlighted, not checked;
                     anything else verbatim)
  - / 1.             bullet / numbered list, one nesting level (2 sp)
  > text             callout
  | a | b |          table (header row, ---- separator, body rows)
  blank-line-        paragraph
    separated text

INLINE
  `code`  **strong**  *em*  [text](href)

Usage:
  python3 tools/render-reference.py [--out build/docs/reference.html]
  python3 tools/render-reference.py --check
"""
import argparse
import html
import importlib.util
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "docs" / "reference"

# The book's spine. Order and grouping are HERE; chapter files are
# named by slug so inserting a chapter never renumbers the corpus.
PARTS = [
    ("Getting started", [
        "introduction",
        "installation",
        "first-file",
        "first-proofs",
    ]),
    ("Lexical structure and items", [
        "lexical",
        "items",
        "modules",
        "operators",
    ]),
    ("Types and terms", [
        "universes",
        "functions",
        "bidirectional",
        "implicits",
        "pairs",
        "sums",
        "naturals",
        "let",
    ]),
    ("Equality and propositions", [
        "equality",
        "coherence",
        "propositions",
        "calc-chains",
        "quotients",
    ]),
    ("Defining your own types", [
        "data",
        "clausal-defs",
        "coinduction",
    ]),
    ("Proving in Nova", [
        "discharge",
        "using-clauses",
        "report",
        "recipes",
        "pitfalls",
    ]),
    ("Reference", [
        "grammar",
        "precedence",
        "notation",
        "generated-names",
        "library",
        "tooling",
        "glossary",
    ]),
]

# ----- Nova code highlighting -------------------------------------------
#
# Classes match tools/nova-docs.css (tok-keyword / tok-variable /
# tok-operator / tok-number / tok-comment), which in turn mirror the
# LSP legend, so the reference and the rendered sources agree.

# alphabetic and eliminator keywords — every token the parser reads
# with `kw` that starts with a letter-ish character
KEYWORDS = [
    "𝟘-elim", "ℕ-elim", "⊎-elim", "quot-elim", "squash-elim",
    "import", "infixl", "infixr", "using", "class", "corec", "coind",
    "data", "type", "def", "let", "in", "out", "Prf", "El", "K", "U",
    "inj₁", "inj₂", "S", "Z",
]

# fixed theory syntax that is NOT identifier-shaped. Longest first —
# the alternation is tried in order.
SYMBOLS = [
    "≡⟨", "⟩", ".π₁", ".π₂", "≔", "→", "⨯", "⊎", "≡", "∈", "λ", "ν",
    "𝕏", "𝕌", "Ω", "ℕ", "𝟘", "𝟙", "∥", "⋆", "/",
]

OPCHARS = "+-*<>=&!?%^~@#⊕⊗⊙⊞⊟∙∘·≤≥∸⧺⊥⊤∧∨⊃¬↔"

IDENT = r"[A-Za-z_][A-Za-z0-9_'′₀-₉]*"

NOVA_RE = re.compile(
    "(?P<comment>--[^\n]*)"
    "|(?P<keyword>" + "|".join(re.escape(k) for k in KEYWORDS) + r")(?![A-Za-z0-9_'])"
    "|(?P<symbol>" + "|".join(re.escape(s) for s in SYMBOLS) + ")"
    r"|(?P<number>\b\d+\b)"
    "|(?P<operator>[" + re.escape(OPCHARS) + "]+)"
    "|(?P<ident>" + IDENT + ")"
)

CLASS = {"comment": "tok-comment", "keyword": "tok-keyword",
         "symbol": "tok-keyword", "number": "tok-number",
         "operator": "tok-operator", "ident": "tok-variable"}


def highlight_nova(code):
    """Classify a Nova snippet. Anything the lexer does not recognise
    falls through as plain escaped text — a misclassification degrades
    to uncoloured source, never to lost source."""
    out, pos = [], 0
    for m in NOVA_RE.finditer(code):
        if m.start() > pos:
            out.append(html.escape(code[pos:m.start()]))
        kind = m.lastgroup
        text = html.escape(m.group())
        out.append(f'<span class="{CLASS[kind]}">{text}</span>')
        pos = m.end()
    out.append(html.escape(code[pos:]))
    return "".join(out)


# ----- inline markup -----------------------------------------------------

CODE_SPAN = re.compile(r"`([^`]+)`")
LINK = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")
STRONG = re.compile(r"\*\*([^*]+)\*\*")
EM = re.compile(r"(?<![*\w])\*([^*\n]+)\*(?!\*)")


def inline(text):
    """Code spans are lifted out FIRST and put back last, so markup
    characters inside them are never interpreted."""
    spans = []

    def stash(m):
        spans.append(html.escape(m.group(1)))
        return f"\x00{len(spans) - 1}\x00"

    text = CODE_SPAN.sub(stash, text)
    text = html.escape(text)
    text = LINK.sub(lambda m: f'<a href="{m.group(2)}">{m.group(1)}</a>', text)
    text = STRONG.sub(lambda m: f"<strong>{m.group(1)}</strong>", text)
    text = EM.sub(lambda m: f"<em>{m.group(1)}</em>", text)
    return re.sub(r"\x00(\d+)\x00", lambda m: f"<code>{spans[int(m.group(1))]}</code>", text)


# ----- block parsing -----------------------------------------------------

def anchorize(slug, text):
    a = re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-")
    return f"{slug}--{a}" if a else slug


class Chapter:
    def __init__(self, slug, path):
        self.slug = slug
        lines = path.read_text().rstrip("\n").split("\n")
        if not lines or not lines[0].startswith("# "):
            sys.exit(f"{path}: first line must be '# Chapter title'")
        self.title = lines[0][2:].strip()
        # the TOC is plain text; the heading keeps its inline markup
        self.title_text = self.title.replace("`", "")
        self.title_html = inline(self.title)
        self.stub = len(lines) > 1 and lines[1].strip() == "%stub"
        self.lines = lines[2:] if self.stub else lines[1:]
        self.sections = []          # (text, anchor) for every ##
        self.snippets = []          # (lang, code) for every code fence
        self.body = self.render()

    # -- one dispatch over the block grammar; `i` walks the line list
    def render(self):
        out, i, ls = [], 0, self.lines
        while i < len(ls):
            l = ls[i]
            if not l.strip():
                i += 1
            elif l.startswith("```"):
                lang = l[3:].strip()
                j = i + 1
                while j < len(ls) and not ls[j].startswith("```"):
                    j += 1
                code = "\n".join(ls[i + 1:j])
                self.snippets.append((lang, code))
                nova = lang in ("nova", "nova-sketch")   # `report` is plain
                body = highlight_nova(code) if nova else html.escape(code)
                cls = "code nova-source" if nova else "code"
                out.append(f'<pre class="{cls}">{body}</pre>')
                i = j + 1
            elif l.startswith("### "):
                out.append(f"<h3>{inline(l[4:].strip())}</h3>")
                i += 1
            elif l.startswith("## "):
                text = l[3:].strip()
                a = anchorize(self.slug, text)
                self.sections.append((text.replace("`", ""), a))
                out.append(f'<h2 id="{a}">{inline(text)}</h2>')
                i += 1
            elif l.startswith("> "):
                j = i
                buf = []
                while j < len(ls) and ls[j].startswith(">"):
                    buf.append(ls[j][2:] if ls[j].startswith("> ") else ls[j][1:])
                    j += 1
                out.append(f'<blockquote>{inline(" ".join(buf).strip())}</blockquote>')
                i = j
            elif l.startswith("|"):
                j = i
                rows = []
                while j < len(ls) and ls[j].startswith("|"):
                    rows.append([c.strip() for c in ls[j].strip().strip("|").split("|")])
                    j += 1
                out.append(self.table(rows))
                i = j
            elif re.match(r"\s*(-|\d+\.) ", l):
                j = i
                while j < len(ls) and (re.match(r"\s*(-|\d+\.) ", ls[j])
                                       or (ls[j].startswith("  ") and ls[j].strip())):
                    j += 1
                out.append(self.list_block(ls[i:j]))
                i = j
            else:
                j = i
                while j < len(ls) and ls[j].strip() and not re.match(
                        r"(```|#{2,3} |> |\||\s*(-|\d+\.) )", ls[j]):
                    j += 1
                out.append(f'<p>{inline(" ".join(x.strip() for x in ls[i:j]))}</p>')
                i = j
        return "\n".join(out)

    @staticmethod
    def table(rows):
        if len(rows) >= 2 and all(re.fullmatch(r":?-{2,}:?", c) for c in rows[1]):
            head, body = rows[0], rows[2:]
        else:
            head, body = None, rows
        h = ("<thead><tr>" + "".join(f"<th>{inline(c)}</th>" for c in head)
             + "</tr></thead>") if head else ""
        b = "".join("<tr>" + "".join(f"<td>{inline(c)}</td>" for c in r) + "</tr>"
                    for r in body)
        return f"<table>{h}<tbody>{b}</tbody></table>"

    @staticmethod
    def list_block(lines):
        """One nesting level: a `-`/`1.` at indent 0 opens an item, an
        indented marker opens a nested list, any other indented line
        continues the item above it."""
        ordered = bool(re.match(r"\s*\d+\. ", lines[0]))
        items, nested = [], None
        for l in lines:
            m = re.match(r"(\s*)(?:-|\d+\.) (.*)", l)
            if m and len(m.group(1)) == 0:
                if nested is not None:
                    items[-1] += "<ul>" + "".join(f"<li>{inline(x)}</li>"
                                                  for x in nested) + "</ul>"
                    nested = None
                items.append(inline(m.group(2)))
            elif m:
                nested = (nested or []) + [m.group(2)]
            elif items:
                if nested is not None:
                    nested[-1] += " " + l.strip()
                else:
                    items[-1] += " " + inline(l.strip())
        if nested is not None and items:
            items[-1] += "<ul>" + "".join(f"<li>{inline(x)}</li>" for x in nested) + "</ul>"
        tag = "ol" if ordered else "ul"
        return f"<{tag}>" + "".join(f"<li>{x}</li>" for x in items) + f"</{tag}>"


# ----- page assembly -----------------------------------------------------

CSS = """
:root {
  --paper:#f7f8fa; --ink:#20242d; --faint:#5c6472; --hair:#d8dce2;
  --panel:#eef0f4; --tos:#0e7c86; --nova:#2f5fc0; --meta:#7862a8;
  --link:#0e7c86; --gold:#92700c; --natc:#b03a70; --hilite:#d9e4f8;
}
@media (prefers-color-scheme: dark) { :root {
  --paper:#191b20; --ink:#dcdee4; --faint:#9aa1ae; --hair:#33373f;
  --panel:#20232a; --tos:#53cad4; --nova:#82a5ea; --meta:#a995d6;
  --link:#53cad4; --gold:#d8b45e; --natc:#e592bb; --hilite:#2d3a55;
}}
:root[data-theme="dark"] {
  --paper:#191b20; --ink:#dcdee4; --faint:#9aa1ae; --hair:#33373f;
  --panel:#20232a; --tos:#53cad4; --nova:#82a5ea; --meta:#a995d6;
  --link:#53cad4; --gold:#d8b45e; --natc:#e592bb; --hilite:#2d3a55;
}
:root[data-theme="light"] {
  --paper:#f7f8fa; --ink:#20242d; --faint:#5c6472; --hair:#d8dce2;
  --panel:#eef0f4; --tos:#0e7c86; --nova:#2f5fc0; --meta:#7862a8;
  --link:#0e7c86; --gold:#92700c; --natc:#b03a70; --hilite:#d9e4f8;
}
* { box-sizing:border-box; }
body {
  margin:0; background:var(--paper); color:var(--ink);
  font-family:"Iowan Old Style","Palatino Linotype",Palatino,"Book Antiqua",Georgia,serif;
  font-size:17px; line-height:1.6;
}
#wrap { display:flex; gap:2.5rem; max-width:1240px; margin:0 auto; padding:0 1.25rem; }
#toc {
  flex:0 0 250px; position:sticky; top:0; align-self:flex-start;
  max-height:100vh; overflow-y:auto; padding:1.2rem 0 2rem;
  font-family:ui-sans-serif,system-ui,sans-serif; font-size:12.5px; line-height:1.35;
}
#toc .home { display:block; font-weight:700; font-size:14px; color:var(--nova);
  text-decoration:none; margin-bottom:.9rem; letter-spacing:.02em; }
#toc details { margin:.4rem 0; }
#toc summary { cursor:pointer; font-weight:700; font-size:12px; padding:.15rem 0;
  letter-spacing:.06em; text-transform:uppercase; color:var(--faint); }
.toc-ch { display:block; margin:.3rem 0 .1rem; color:var(--ink);
  text-decoration:none; font-weight:600; }
.toc-sec { display:block; margin:.05rem 0 .05rem .8rem; color:var(--faint);
  text-decoration:none; }
.toc-ch:hover, .toc-sec:hover { color:var(--link); }
.toc-ch.stub::after { content:"outline"; float:right; font-size:9.5px;
  letter-spacing:.05em; text-transform:uppercase; color:var(--faint);
  border:1px solid var(--hair); border-radius:3px; padding:0 .25rem;
  font-weight:400; }
main { flex:1; min-width:0; max-width:72ch; padding:1.2rem 0 6rem; }
header.book { margin:.6rem 0 2.4rem; }
header.book h1 { font-size:2.1rem; margin:0 0 .3rem; border:none; padding:0; }
header.book h1 .nova { color:var(--nova); }
header.book p { color:var(--faint); margin:.2rem 0; }
.progress { font-family:ui-sans-serif,system-ui,sans-serif; font-size:12.5px;
  color:var(--faint); border:1px solid var(--hair); border-radius:6px;
  padding:.5rem .8rem; margin-top:1.2rem; }
.part { margin:4rem 0 0; font-family:ui-sans-serif,system-ui,sans-serif;
  font-size:.8rem; letter-spacing:.16em; text-transform:uppercase;
  color:var(--faint); border-bottom:1px solid var(--hair); padding-bottom:.4rem; }
h1 { font-size:1.7rem; line-height:1.2; text-wrap:balance;
  margin:2.6rem 0 .5rem; padding-top:1.4rem; border-top:3px double var(--hair); }
.part + section h1 { border-top:none; padding-top:0; margin-top:1.4rem; }
h1 .num { color:var(--faint); font-size:1.1rem; margin-right:.5rem;
  font-family:ui-sans-serif,system-ui,sans-serif; }
h2 { font-size:1.22rem; line-height:1.25; text-wrap:balance; margin:2.1rem 0 .6rem; }
h3 { font-size:.9rem; letter-spacing:.07em; text-transform:uppercase;
  font-family:ui-sans-serif,system-ui,sans-serif; color:var(--faint);
  margin:1.7rem 0 .5rem; }
p { margin:.7rem 0; }
ul, ol { margin:.6rem 0; padding-left:1.4rem; }
li { margin:.3rem 0; }
li > ul { margin:.25rem 0; }
a { color:var(--link); }
code {
  font-family:ui-monospace,"SF Mono","Cascadia Code",Menlo,Consolas,monospace;
  font-size:.85em; background:var(--panel); border-radius:3px; padding:.05em .3em;
}
pre.code {
  font-family:ui-monospace,"SF Mono","Cascadia Code",Menlo,Consolas,monospace;
  font-size:13.5px; line-height:1.55; margin:1rem 0; overflow-x:auto;
  background:var(--panel); border:1px solid var(--hair); border-left:2px solid var(--hair);
  border-radius:0 5px 5px 0; padding:.8rem 1rem; white-space:pre;
}
blockquote { margin:1rem 0; padding:.6rem .95rem; border-left:3px solid var(--meta);
  background:var(--panel); border-radius:0 5px 5px 0; font-size:.95em; }
blockquote p { margin:0; }
table { border-collapse:collapse; margin:1rem 0; font-size:.9em; width:100%; }
th, td { text-align:left; padding:.35rem .6rem; border-bottom:1px solid var(--hair);
  vertical-align:top; }
th { font-family:ui-sans-serif,system-ui,sans-serif; font-size:.85em;
  letter-spacing:.05em; text-transform:uppercase; color:var(--faint); }
.stubnote { font-family:ui-sans-serif,system-ui,sans-serif; font-size:12.5px;
  color:var(--faint); border:1px dashed var(--hair); border-radius:6px;
  padding:.45rem .8rem; margin:.6rem 0 1.2rem; }
/* Real corpus lines run past a comfortable prose measure, so on a wide
   screen code bleeds to the right of the text column rather than
   scrolling inside it. The breakpoint is set so the bleed always fits
   in the slack between main's 72ch cap and #wrap — the page body must
   never scroll sideways. Narrower than that, pre's own overflow-x
   handles it. */
@media (min-width: 1200px) { pre.code { margin-right:-8rem; } }
:target { scroll-margin-top:1rem; }
a:focus-visible { outline:2px solid var(--link); outline-offset:2px; }
/* code token classes — the LSP legend, as in tools/nova-docs.css */
.tok-keyword  { color:var(--gold); font-weight:600; }
.tok-variable { color:var(--ink); }
.tok-operator { color:var(--nova); }
.tok-number   { color:var(--natc); }
.tok-comment  { color:var(--faint); font-style:italic; }
@media (max-width: 900px) { #toc { display:none; } }
"""


# ----- the checks (--check) ----------------------------------------------
#
# Three things can silently rot as the theory and the implementation
# move: a quoted snippet, a cited file, a cited rule name. All three
# are checkable against the sources, so all three are checked, and the
# suite runs it (tests/nova/docs/reference-snippets).

# Snippets may be quoted from anything the suite already checks: the
# corpus, and the golden tests' inputs — the latter is where a
# DELIBERATELY failing example has to come from, since by construction
# it cannot live in the accepted corpus. Tool transcripts (```report)
# are quoted from the goldens' expected output, so a change to the
# report printer breaks the book instead of outliving it.
SOURCES = ["src/nova/*.nova", "tests/**/input.nova"]
TRANSCRIPTS = ["tests/**/expected"]
CITED_PATH = re.compile(r"\b(docs/[A-Za-z]+\.txt"
                        r"|src/nova/[A-Za-z0-9]+\.nova"
                        r"|tools/[a-z-]+\.(?:py|css))\b")
# rule names are cited in code spans, which are <code> by the time the
# body is built — match the rendered form, not the backticks
RULE_TOKEN = re.compile(r"<code>([a-z][a-z0-9]*(?:-[a-z0-9⁼ᴰ]+)+)</code>")


def lines_of(globs):
    return {str(p.relative_to(ROOT)): [l.rstrip() for l in p.read_text().split("\n")]
            for g in globs for p in sorted(ROOT.glob(g))}


def dedent(lines):
    """Strip the deepest common indent, ignoring blank lines — a quote
    may be dedented out of its item, but not reflowed."""
    ind = [len(l) - len(l.lstrip()) for l in lines if l.strip()]
    n = min(ind) if ind else 0
    return tuple(l[n:] if l.strip() else "" for l in lines)


def check_snippets(chapters, problems):
    """Every ```nova block is a QUOTATION of src/nova. A block may elide
    whole items (blank-line-separated chunks are matched one by one),
    but each chunk must occur verbatim, as a contiguous run of lines,
    in some corpus file."""
    corpus = lines_of(SOURCES)
    transcripts = lines_of(TRANSCRIPTS)
    if not corpus or not transcripts:
        problems.append("no checkable sources found — wrong tree?")
        return
    for c in chapters:
        for lang, code in c.snippets:
            if lang not in ("nova", "report"):    # nova-sketch is exempt
                continue
            corpus_ = corpus if lang == "nova" else transcripts
            for chunk in re.split(r"\n\s*\n", code.strip("\n")):
                want = dedent([l.rstrip() for l in chunk.split("\n")])
                n = len(want)
                if not any(dedent(ls[i:i + n]) == want
                           for ls in corpus_.values()
                           for i in range(len(ls) - n + 1)):
                    where = ("src/nova or a golden input" if lang == "nova"
                             else "a golden's expected output")
                    problems.append(
                        f"{c.slug}.md: {lang} snippet is not verbatim in "
                        f"{where}:\n"
                        + "\n".join("      | " + l for l in want[:4])
                        + ("\n      | …" if n > 4 else ""))


def check_paths(chapters, problems):
    """A cited file must exist — this is how the book noticed it was
    still naming vect.nova after the corpus renamed it."""
    for c in chapters:
        for rel in sorted(set(CITED_PATH.findall(c.body))):
            if not (ROOT / rel).exists():
                problems.append(f"{c.slug}.md: cites missing file {rel}")


def check_rules(chapters, problems):
    """A backticked, hyphenated, rule-shaped token whose first segment
    is one a real rule uses must name a rule the specs define — so a
    rule renamed in docs/*.txt breaks the book instead of outliving it.
    The rulemap comes from render-specs.py; there is one definition of
    what a rule name is."""
    spec = importlib.util.spec_from_file_location(
        "render_specs", ROOT / "tools" / "render-specs.py")
    rs = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(rs)
    rulemap, _, _ = rs.collect(rs.FILES)
    prefixes = {n.split("-")[0] for n in rulemap if "-" in n}
    for c in chapters:
        for tok in sorted(set(RULE_TOKEN.findall(c.body))):
            if tok.split("-")[0] in prefixes and tok not in rulemap:
                problems.append(f"{c.slug}.md: cites unknown rule '{tok}' "
                                "— renamed or mistyped?")


def check(parts):
    chapters = sum((cs for _, cs in parts), [])
    problems = []
    check_xrefs(chapters, problems)
    check_snippets(chapters, problems)
    check_paths(chapters, problems)
    check_rules(chapters, problems)
    if problems:
        print(f"reference check FAILED ({len(problems)}):")
        for p in problems:
            print(f"  {p}")
        return 1
    # stable on purpose: adding a chapter or a snippet must not churn
    # the golden, only a STALE one may fail it
    print("reference check: snippets, paths and rule citations OK")
    return 0


XREF = re.compile(r'href="#([^"]+)"')


def check_xrefs(chapters, problems=None):
    """Cross-references are anchors, never chapter numbers — inserting a
    chapter must not be able to rot a link. A dead one fails the build."""
    ids = {c.slug for c in chapters}
    ids |= {a for c in chapters for _, a in c.sections}
    dead = sorted({(c.slug, t) for c in chapters
                   for t in XREF.findall(c.body) if t not in ids})
    if problems is not None:
        problems.extend(f"{src}.md: dead cross-reference #{t}" for src, t in dead)
    elif dead:
        sys.exit("dead cross-references:\n"
                 + "\n".join(f"  {src}.md -> #{t}" for src, t in dead))


def assemble(parts, out_path):
    chapters = sum((cs for _, cs in parts), [])
    check_xrefs(chapters)
    written = sum(1 for c in chapters if not c.stub)

    nav = ['<nav id="toc"><a class="home" href="index.html">← Nova</a>']
    for title, chs in parts:
        nav.append(f"<details open><summary>{html.escape(title)}</summary>")
        for c in chs:
            cls = "toc-ch stub" if c.stub else "toc-ch"
            nav.append(f'<a class="{cls}" href="#{c.slug}">'
                       f"{c.num}. {html.escape(c.title_text)}</a>")
            for text, a in c.sections:
                nav.append(f'<a class="toc-sec" href="#{a}">{html.escape(text)}</a>')
        nav.append("</details>")
    nav.append("</nav>")

    main = ['<header class="book">',
            '<h1><span class="nova">Nova</span> language reference</h1>',
            "<p>A guided tour of the surface language: how to write it, how to "
            "read it, and how proofs get discharged.</p>",
            f'<p class="progress">Draft — {written} of {len(chapters)} chapters '
            "written; the rest are outlines. The normative documents are the "
            '<a href="specs.html">theory specs</a>; where this book and a spec '
            "disagree, the spec is right.</p>",
            "</header>"]
    for title, chs in parts:
        main.append(f'<p class="part">{html.escape(title)}</p>')
        for c in chs:
            main.append(f'<section id="{c.slug}">')
            main.append(f'<h1><span class="num">{c.num}</span>'
                        f"{c.title_html}</h1>")
            if c.stub:
                main.append('<p class="stubnote">Outline only — this chapter '
                            "sketches what it will cover.</p>")
            main.append(c.body)
            main.append("</section>")

    doc = ("<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n"
           '<meta name="viewport" content="width=device-width,initial-scale=1">\n'
           "<title>Nova language reference</title>\n"
           f"<style>{CSS}</style>\n</head>\n<body>\n"
           f'<div id="wrap">\n{"".join(nav)}\n<main>\n'
           + "\n".join(main) + "\n</main>\n</div>\n</body>\n</html>\n")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(doc)
    return written, len(chapters)


def load():
    parts, n = [], 0
    seen = set()
    for title, slugs in PARTS:
        chs = []
        for slug in slugs:
            path = SRC / f"{slug}.md"
            if not path.exists():
                sys.exit(f"missing chapter source: {path}")
            seen.add(path.name)
            c = Chapter(slug, path)
            n += 1
            c.num = n
            chs.append(c)
        parts.append((title, chs))
    orphans = sorted(p.name for p in SRC.glob("*.md") if p.name not in seen)
    if orphans:
        sys.exit("chapter files not listed in PARTS: " + ", ".join(orphans))
    return parts


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="build/docs/reference.html")
    ap.add_argument("--check", action="store_true",
                    help="verify snippets, cited paths and rule names "
                         "against the sources; write nothing")
    args = ap.parse_args()
    parts = load()
    if args.check:
        sys.exit(check(parts))
    out = ROOT / args.out
    written, total = assemble(parts, out)
    langs = [l for _, cs in parts for c in cs for l, _ in c.snippets]
    quoted = sum(1 for l in langs if l in ("nova", "report"))
    sketch = sum(1 for l in langs if l == "nova-sketch")
    print(f"{out}: {total} chapters, {written} written, "
          f"{total - written} outlines; {quoted} snippets quoted from the "
          f"sources, {sketch} illustrative")


if __name__ == "__main__":
    main()
