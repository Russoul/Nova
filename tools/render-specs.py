#!/usr/bin/env python3
"""Render the plain-text specs in docs/ to a single self-contained HTML page.

The specs' existing conventions ARE the DSL — this tool parses them as
found; the .txt files remain the sole source of truth. Fallback-first:
anything unrecognized renders verbatim in monospace, exactly as in the
source, so a misparse degrades to the plain text, never to garbage.

Recognized structure:
  * ////////// section headers //////////
  * inference rules: premise lines, a ---- bar (optionally named
    "(rule-name)"), conclusion lines; trailing // comments become
    annotations
  * prose regions (plain or //-prefixed): paragraphs, * bullets with
    continuation lines, indented display blocks (grammars, tables,
    diagrams), ALL-CAPS lead phrases promoted to headings
  * rule names cited anywhere autolink to their defining rule,
    across files; §N cites link to the section within the same file

Modes:
  render (default)       write the HTML page (--out PATH)
  --check                cross-check rule names against src/idris:
                           - duplicate rule definitions in the specs
                           - rule-shaped tokens cited in Idris sources
                             that no spec defines (likely typos) — FATAL
                           - spec rules never cited in the sources
                             (coverage report) — informational
"""
import argparse
import html
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

FILES = [
    ("foundation", "docs/NovaFoundation.txt", "Nova Foundation"),
    ("model", "docs/NovaModel.txt", "Nova Model"),
    ("kernel", "docs/NovaKernel.txt", "Nova Kernel"),
    ("elaboration", "docs/NovaElaboration.txt", "Nova Elaboration"),
    ("pipeline", "docs/NovaPipeline.txt", "Nova Pipeline"),
    ("derivations", "docs/NovaDerivations.txt", "Nova Derivations"),
]

# ----- symbol colouring --------------------------------------------------
#
# Classification is SEMANTIC, table-driven: `#! highlight <class>:`
# declarations in the spec files are the syntax tables (the defaults
# below apply only for a class no file declares). `keywords` is the
# FIXED syntax — judgement-level (⊦ : ≐ type) and object-level
# (⬡ ▷ El ☐ λ →) alike; the other classes are the METAVARIABLE
# alphabets by kind. Every token in a judgement context is classified
# by table lookup; a token in no table renders ink. The special token
# `latin` in the nova class marks bare Latin letters (with
# decorations: t₀, A′, ē, e˲, C̄) as Nova metavariables — judgement
# contexts only; running prose is never highlighted.

DIRECTIVE_RE = re.compile(r"^#!\s*highlight\s+(keywords|tos|nova|meta|indexed):\s*(.*)$")

DEFAULT_VOCAB = {
    # FIXED syntax — judgement-level and object-level alike
    "keywords": ("⊦ : ; , · [ ] ‖ .π₁ .π₂ ∈ ∋ ≐ ≜ ≔ ⇒ ⇐ ⇓ = ⬡ ⬦ ▷ ◁ ⇛ ⇑ 𝕚𝕕 El U ☐ ε ↑ ∘ ⁺ id "
                 "λ → × ≡ ∥ / Ω 𝕌 ℕ 𝟘 𝟙 Z S Refl ⋆ Prf class ⌊ ⌋ ⟦ ⟧ ⋈ ⋉ ᴰ "
                 "𝟘-elim ℕ-elim quot-elim squash-elim sigma-elim sum-elim ≡-elim -elim "
                 "qctx qty qsig ctx type tel mot dalg eprob sect norm small "
                 "sig nf qpath").split(),
    # metavariable alphabets, by kind
    "tos": "𝔄 𝔅 𝕥 𝕦 𝕧 𝕤 𝕔 𝕜 𝕘 𝕒 𝕓 𝕞 Φ 𝒮 ς 𝔎".split(),
    "nova": "Γ Δ Ξ Σ σ τ δ θ latin".split(),
    "meta": "𝑤 ρ υ π 𝒞 ℰ".split(),
    # index-taking operators: their subscripts are META-LEVEL NATURALS
    # (☐ₙ, ⬡ᵢ, Γ‖ₙ₊₁), coloured separately from name-tick subscripts
    # on metavariables (Γ₀, t₁)
    "indexed": "☐ ⬡ ‖".split(),
}

def collect_vocab(files):
    vocab = {}
    for _, rel, _ in files:
        for l in (ROOT / rel).read_text().splitlines():
            m = DIRECTIVE_RE.match(l.strip())
            if m:
                vocab.setdefault(m.group(1), []).extend(m.group(2).split())
    for k, v in DEFAULT_VOCAB.items():
        vocab.setdefault(k, v)
    return vocab

# decorations that travel with a token: combining marks, primes,
# sub/superscripts (t₀, A′, ē is precomposed Latin, Γ̂, e˲, ⌊·⌋ᵗ)
DECOR = "\u0300-\u036f'′″‴˲ᵢⱼₖₗₘₙₚᵣₛₜ₀-₉₊₋⁻⁼ᵈᵗᵖᵉᴺ"

class Highlighter:
    def __init__(self, vocab):
        self.latin_nova = "latin" in vocab.get("nova", [])
        self.indexed = set(vocab.get("indexed", []))
        words, mtoks, chars = [], [], []   # (token, cls)
        for cls, k in (("kw", "keywords"), ("tos", "tos"),
                       ("nova", "nova"), ("meta", "meta")):
            for tok in vocab.get(k, []):
                if tok == "latin":
                    continue
                if tok.isascii() and tok.isalnum():
                    words.append((tok, cls))
                elif len(tok) > 1:
                    mtoks.append((tok, cls))
                else:
                    chars.append((tok, cls))
        self.cls_of = {t: c for t, c in words + mtoks + chars}
        # core math symbols for prose-vs-display disambiguation in
        # comment regions: declared class chars minus prose-common
        # punctuation
        self.core = {t for t, _ in chars} - set(",;:·[]()/=")
        wpat = "|".join(re.escape(t) for t, _ in
                        sorted(words, key=lambda x: -len(x[0])))
        mpat = "|".join(re.escape(t) for t, _ in
                        sorted(mtoks, key=lambda x: -len(x[0])))
        cpat = "[" + "".join(re.escape(t) for t, _ in chars) + "]"
        dec = "[" + DECOR + "]*"
        # order matters: declared words | multi-char symbols | plain
        # English (2+ letters, left ink) | declared chars | Latin
        # metavariables
        # escaping happens BEFORE painting, so the text contains HTML
        # entities — skip them whole lest a keyword char (the ; of
        # &lt;) break them apart
        self.math_re = re.compile(
            "(?P<ent>&(?:amp|lt|gt);)"
            f"|(?P<word>(?<![\\w-])(?:{wpat})(?![\\w-]))"
            f"|(?P<mtok>{mpat})"
            "|(?P<eng>[A-Za-z]{2,})"
            f"|(?P<sym>{cpat}{dec})"
            f"|(?P<lat>[A-Za-z\u0100-\u017f]{dec})")

    def _wrap(self, cls, text):
        return f'<span class="{cls}">{text}</span>'

    def paint(self, escaped, prose=False):
        # running prose is left unhighlighted: token classification is
        # only reliable inside judgement contexts (rules, display
        # panels), where the notation discipline holds
        if prose:
            return escaped
        rx = self.math_re
        def rep(m):
            g = m.lastgroup
            t = m.group(0)
            if g in ("eng", "ent"):
                return t
            # an absorbed apostrophe followed by s is a POSSESSIVE
            # (𝔄's), not a prime decoration (Γ') — leave it outside
            tail = ""
            if t.endswith("'") and re.match(r"s\b", m.string[m.end():]):
                t, tail = t[:-1], "'"
            if g == "lat":
                if not self.latin_nova:
                    return t
                # plural/possessive suffix, not a metavariable: Πs, ⌊𝔄⌋ᵗ's
                prev = m.string[m.start() - 1] if m.start() > 0 else ""
                if prev == "'" or prev.isalpha():
                    return t
                # the article 'a': followed by an English word (2+ letters)
                if t == "a":
                    rest = m.string[m.end():]
                    if re.match(r"\s+[A-Za-z]{2,}(?![\w-]*[₀-₉′])", rest):
                        return t
                return self._wrap("nova", t) + tail
            base = m.group(g) if g != "sym" else t[0]
            cls = self.cls_of.get(base if g != "word" else m.group("word"),
                                  None)
            if g == "sym":
                cls = self.cls_of.get(t[0])
                # after an index-taking operator the subscript run is a
                # meta-level natural — its own class
                if t[0] in self.indexed and len(t) > 1 and cls:
                    return (self._wrap(cls, t[0])
                            + self._wrap("nat", t[1:]) + tail)
            return (self._wrap(cls, t) if cls else t) + tail
        return rx.sub(rep, escaped)

HL = None   # installed in main() once the vocabulary is collected

# a comment starts at a whitespace-preceded (or line-initial) `//` —
# `https://` never matches
CMT_RE = re.compile(r"(?:^|(?<=\s))#")

def math(text: str, prose: bool = False) -> str:
    if prose:
        return HL.paint(html.escape(text, quote=False), prose=True)
    out = []
    for line in text.split("\n"):
        m = CMT_RE.search(line)
        if m:
            code, cmt = line[:m.start()], line[m.start():]
            out.append(HL.paint(html.escape(code, quote=False))
                       + '<span class="cmt">' + html.escape(cmt, quote=False)
                       + "</span>")
        else:
            out.append(HL.paint(html.escape(line, quote=False)))
    return "\n".join(out)

# ----- shared regexes ----------------------------------------------------

HEADER_RE = re.compile(r"^/{5,}\s*(.*?)\s*/{5,}$")
NAMED_BAR_RE = re.compile(r"^\s*-{4,}\s*\(([^()]+)\)\s*(?:#\s*(.*))?$")
RULE_TOKEN_RE = re.compile(r"^[a-zA-Z0-9⁼ᴰ-]+$")

def split_aliases(name):
    """(a, b, c) is a set of aliases only when every part is rule-shaped;
    otherwise the tail is an annotation: (el-nat-e, motive A)."""
    parts = [p.strip() for p in name.split(",")]
    if len(parts) > 1 and all(RULE_TOKEN_RE.match(p) for p in parts):
        return parts, None
    note = ", ".join(parts[1:]) if len(parts) > 1 else None
    return [parts[0]], note
BARE_BAR_RE = re.compile(r"^\s*-{4,}\s*(?:#\s*(.*))?$")
# a conclusion line may carry its own rule name: at least two spaces,
# then a parenthesized hyphenated lowercase rule id at end of line
CONCL_NAME_RE = re.compile(
    r"^(.*?)\s{2,}\(([a-z][a-z0-9⁼ᴰ]*(?:-[a-z0-9⁼ᴰ]+)+)\)\s*$")
TRAIL_RE = re.compile(r"^(.*?)\s*#\s*(.*)$")
CAPS_RE = re.compile(r"^([A-Z][A-Z0-9\- ⌊⌋·⟦⟧ᴰ]{4,}?)\s*(?=[.(:—])")
STRONG_MATH = re.compile(r"≜|::=|▷|‖|│|▼|⇘|-{4,}")
SEC_NUM_RE = re.compile(r"^(\d+)\.\s")
SECREF_RE = re.compile(r"§(\d+)")

def is_bar(line):
    return bool(NAMED_BAR_RE.match(line) or BARE_BAR_RE.match(line))

def blocks(lines):
    buf = []
    for l in lines:
        if l.strip() == "":
            if buf:
                yield buf
                buf = []
        else:
            buf.append(l)
    if buf:
        yield buf

def anchor_of(key, name):
    return f"{key}-r-" + re.sub(r"[^a-zA-Z0-9\-⁼ᴰ]", "", name)

# ----- pass 1: collect rule names + section numbers ---------------------

def collect(files):
    """rulemap: name -> (filekey, anchor); rules_by_file; sections."""
    rulemap, order, dups = {}, [], []
    def reg(key, names, a):
        for al in names:
            if al in rulemap:
                dups.append(al)
            else:
                rulemap[al] = (key, a)
                order.append(al)
    for key, rel, _ in files:
        for b in blocks((ROOT / rel).read_text().splitlines()):
            if not any(is_bar(l) for l in b):
                continue
            seen_bar = False
            for l in b:
                m = NAMED_BAR_RE.match(l)
                if m and not seen_bar:
                    seen_bar = True
                    aliases, _ = split_aliases(m.group(1).strip())
                    reg(key, aliases, anchor_of(key, aliases[0]))
                    continue
                if BARE_BAR_RE.match(l) and not seen_bar:
                    seen_bar = True
                    continue
                if seen_bar:
                    cm = CONCL_NAME_RE.match(l)
                    if cm:
                        n = cm.group(2)
                        reg(key, [n], anchor_of(key, n))
    return rulemap, order, dups

# ----- renderer ----------------------------------------------------------

class FileRenderer:
    def __init__(self, key, title, rulemap):
        self.key = key
        self.title = title
        self.rulemap = rulemap
        self.toc = []          # ("H2"|"H3"|"R", text, anchor)
        self.body = []
        self.hseq = 0
        names = sorted(rulemap, key=len, reverse=True)
        self.link_re = re.compile(
            r"\b(" + "|".join(map(re.escape, names)) + r")\b") if names else None

    def autolink(self, html_text):
        out = html_text
        if self.link_re:
            def rep(m):
                name = m.group(1)
                _, a = self.rulemap[name]
                return f'<a class="rref" href="#{a}">{name}</a>'
            out = self.link_re.sub(rep, out)
        out = SECREF_RE.sub(
            lambda m: f'<a class="rref" href="#{self.key}-sec-{m.group(1)}">§{m.group(1)}</a>',
            out)
        return out

    # -- rules ------------------------------------------------------------

    def rule(self, b):
        """Trailing comments render WHERE THEY ARE in the source: a
        bar-line comment sits beside the bar (after the rule name);
        premise/conclusion comments stay on their own lines, styled by
        the painter."""
        pre, concl, bnotes = [], [], []
        name = None
        seen_bar = False
        for l in b:
            nm = NAMED_BAR_RE.match(l)
            bm = BARE_BAR_RE.match(l)
            if (nm or bm) and not seen_bar:
                seen_bar = True
                if nm:
                    name = nm.group(1).strip()
                    aliases, extra = split_aliases(name)
                    if extra:
                        name = aliases[0]
                        bnotes.append(extra)
                    if nm.group(2):
                        bnotes.append(nm.group(2).strip())
                elif bm.group(1):
                    bnotes.append(bm.group(1).strip())
                continue
            body = l
            if seen_bar:
                cm = CONCL_NAME_RE.match(body.rstrip())
                if cm:
                    concl.append((cm.group(1).rstrip(), cm.group(2)))
                else:
                    concl.append((body.rstrip(), None))
            else:
                pre.append(body.rstrip())
        cnamed = [n for _, n in concl if n]
        a = (anchor_of(self.key, name.split(",")[0].strip()) if name
             else anchor_of(self.key, cnamed[0]) if cnamed else "")
        aid = f' id="{a}"' if name else ""
        out = [f'<div class="rule"{aid}>', '<div class="rule-box">']
        prem = "\n".join(pre).strip("\n")
        if prem:
            out.append(f'<pre class="premises">{math(prem)}</pre>')
        parts = []
        if name:
            parts.append(f'<a href="#{a}">{html.escape(name)}</a>')
        if bnotes:
            note_html = self.autolink(math(" ".join(bnotes), prose=True))
            parts.append(f'<span class="bnote"># {note_html}</span>')
        tag = f'<span class="rname">{"".join(parts)}</span>' if parts else ""
        out.append(f'<div class="bar">{tag}</div>')
        if cnamed:
            # each conclusion line carries its own rule name
            for text, n in concl:
                if not text and not n:
                    continue
                if n:
                    ca = anchor_of(self.key, n)
                    out.append(
                        f'<div class="crow" id="{ca}">'
                        f'<pre class="conclusion">{math(text)}</pre>'
                        f'<span class="cname"><a href="#{ca}">{html.escape(n)}</a></span></div>')
                else:
                    out.append(f'<pre class="conclusion">{math(text)}</pre>')
        else:
            conc = "\n".join(t for t, _ in concl).strip("\n")
            out.append(f'<pre class="conclusion">{math(conc)}</pre>')
        out.append("</div>")
        out.append("</div>")
        self.body.append("\n".join(out))
        if name:
            self.toc.append(("R", name, a))
        for n in cnamed:
            self.toc.append(("R", n, anchor_of(self.key, n)))

    # -- prose regions ------------------------------------------------------

    def region(self, inner, comment):
        """inner: prefix-stripped lines ('' = paragraph break)."""
        out = []
        para, disp, bullets = [], [], []
        in_bullet = False
        in_disp_run = False   # the previous line joined a display

        def flush_para():
            nonlocal para
            if para:
                out.append("<p>" + self.autolink(math(" ".join(para), prose=True)) + "</p>")
                para = []

        def flush_disp():
            nonlocal disp
            if disp:
                out.append('<pre class="display">' + math("\n".join(disp)) + "</pre>")
                disp = []

        def flush_bullets():
            nonlocal bullets, in_bullet
            if bullets:
                items = "".join(
                    "<li>" + self.autolink(math(t, prose=True)) + "</li>" for t in bullets)
                out.append("<ul>" + items + "</ul>")
                bullets = []
            in_bullet = False

        first_prose = True
        for s in inner:
            # a column-0 # line inside a mixed (formal) block is PROSE —
            # strip the marker (BEFORE the blank check, so an empty "#"
            # line separates paragraphs) and classify it as comment
            # content. An INDENTED # line is part of the snippet (a
            # wrapped trailing comment aligned with the code); it stays
            # verbatim and the painter styles it.
            is_cmt = comment
            if not comment and s.startswith("#"):
                s = re.sub(r"^# ?", "", s)
                is_cmt = True
            if s.strip() == "":
                flush_para(); flush_disp(); flush_bullets()
                first_prose = True
                in_disp_run = False
                continue
            indent = len(s) - len(s.lstrip())
            bm = re.match(r"^\s{0,3}\*\s+(.*)$", s)
            if bm:
                flush_para(); flush_disp()
                in_bullet = True
                bullets.append(bm.group(1))
                continue
            if in_bullet and indent >= 2 and not STRONG_MATH.search(s):
                bullets[-1] += " " + s.strip()
                continue
            # in comment prose, strong-math tokens only mark a display
            # when the line is indented — prose sentences may contain
            # inline math (ω ≜ λx. x x) at indent 0. And in comment
            # regions, indentation alone is not enough: a display line
            # must also carry a core math symbol, so indented prose
            # continuations ("through ToS syntax (below);") stay prose
            mathy = (any(ch in HL.core for ch in s)
                     or s.lstrip().startswith(("* ", "| ", "; "))
                     or in_disp_run)
            if (STRONG_MATH.search(s) and (indent >= 2 or not is_cmt)) or (
                    indent >= (4 if is_cmt else 2) and (mathy or not is_cmt)):
                flush_para(); flush_bullets()
                disp.append(s)
                in_disp_run = True
                continue
            in_disp_run = False
            flush_disp(); flush_bullets()
            if first_prose:
                cm = CAPS_RE.match(s.strip())
                if cm:
                    h = cm.group(1).strip()
                    self.hseq += 1
                    a = f"{self.key}-h-{self.hseq}"
                    out.append(f'<h3 id="{a}">{html.escape(h)}</h3>')
                    self.toc.append(("H3", h.title(), a))
                    s = s.strip()[cm.end():].lstrip(".—: ")
                    if not s:
                        first_prose = False
                        continue
            first_prose = False
            para.append(s.strip())
        flush_para(); flush_disp(); flush_bullets()
        self.body.append("\n".join(out))

    def header(self, text):
        m = SEC_NUM_RE.match(text)
        a = f"{self.key}-sec-{m.group(1)}" if m else f"{self.key}-sec-x{self.hseq}"
        self.hseq += 1
        self.body.append(f'<h2 id="{a}">{html.escape(text)}</h2>')
        self.toc.append(("H2", text, a))

    def render(self, lines):
        lines = [l for l in lines if not DIRECTIVE_RE.match(l.strip())]
        for b in blocks(lines):
            hm = HEADER_RE.match(b[0].strip())
            if hm:
                self.header(hm.group(1))
                b = b[1:]
                if not b:
                    continue
            if any(is_bar(l) for l in b):
                self.rule(b)
                continue
            if all(l.lstrip().startswith("#") for l in b):
                inner = [re.sub(r"^\s*#? ?", "", l) for l in b]
                self.region(inner, comment=True)
            else:
                self.region(list(b), comment=False)

# ----- page assembly -----------------------------------------------------

CSS = """
:root {
  --paper:#f7f8fa; --ink:#20242d; --faint:#5c6472; --hair:#d8dce2;
  --panel:#eef0f4; --tos:#0e7c86; --nova:#2f5fc0; --meta:#7862a8;
  --rname:#7862a8; --link:#0e7c86; --gold:#92700c; --natc:#b03a70;
}
@media (prefers-color-scheme: dark) { :root {
  --paper:#191b20; --ink:#dcdee4; --faint:#9aa1ae; --hair:#33373f;
  --panel:#20232a; --tos:#53cad4; --nova:#82a5ea; --meta:#a995d6;
  --rname:#a995d6; --link:#53cad4; --gold:#d8b45e; --natc:#e592bb;
}}
:root[data-theme="dark"] {
  --paper:#191b20; --ink:#dcdee4; --faint:#9aa1ae; --hair:#33373f;
  --panel:#20232a; --tos:#53cad4; --nova:#82a5ea; --meta:#a995d6;
  --rname:#a995d6; --link:#53cad4; --gold:#d8b45e; --natc:#e592bb;
}
:root[data-theme="light"] {
  --paper:#f7f8fa; --ink:#20242d; --faint:#5c6472; --hair:#d8dce2;
  --panel:#eef0f4; --tos:#0e7c86; --nova:#2f5fc0; --meta:#7862a8;
  --rname:#7862a8; --link:#0e7c86; --gold:#92700c; --natc:#b03a70;
}
* { box-sizing:border-box; }
body {
  margin:0; background:var(--paper); color:var(--ink);
  font-family:"Iowan Old Style","Palatino Linotype",Palatino,"Book Antiqua",Georgia,serif;
  font-size:17px; line-height:1.55;
}
#wrap { display:flex; gap:2.5rem; max-width:1240px; margin:0 auto; padding:0 1.25rem; }
#toc {
  flex:0 0 240px; position:sticky; top:0; align-self:flex-start;
  max-height:100vh; overflow-y:auto; padding:1.2rem 0 2rem;
  font-family:ui-sans-serif,system-ui,sans-serif; font-size:12.5px; line-height:1.35;
}
#toc details { margin:.35rem 0; }
#toc summary { cursor:pointer; font-weight:700; font-size:13px; padding:.15rem 0; }
.toc-h2 { display:block; margin:.45rem 0 .1rem; color:var(--ink);
  text-decoration:none; font-weight:600; }
.toc-h3 { display:block; margin:.05rem 0 .05rem .7rem; color:var(--faint);
  text-decoration:none; }
.toc-r { display:block; margin-left:1.4rem; color:var(--faint); text-decoration:none;
  font-family:ui-monospace,Menlo,Consolas,monospace; font-size:11px; padding:.04rem 0; }
.toc-r:hover, .toc-h2:hover, .toc-h3:hover { color:var(--link); }
main { flex:1; min-width:0; max-width:74ch; padding:1.2rem 0 5rem; }
h1 { font-size:1.75rem; line-height:1.2; text-wrap:balance;
  margin:3rem 0 .4rem; padding-top:1.6rem; border-top:3px double var(--hair); }
main > section:first-of-type h1 { margin-top:.8rem; border-top:none; padding-top:0; }
h2 { font-size:1.3rem; line-height:1.25; text-wrap:balance; margin:2.2rem 0 .7rem; }
h3 { font-size:.92rem; letter-spacing:.07em; text-transform:uppercase;
  font-family:ui-sans-serif,system-ui,sans-serif; color:var(--faint);
  margin:2rem 0 .55rem; border-bottom:1px solid var(--hair); padding-bottom:.3rem; }
p { margin:.6rem 0; }
ul { margin:.5rem 0; padding-left:1.3rem; }
li { margin:.35rem 0; }
pre {
  font-family:ui-monospace,"SF Mono","Cascadia Code",Menlo,Consolas,monospace;
  font-size:13.5px; line-height:1.5; margin:0; overflow-x:auto;
}
pre.display { background:var(--panel); border-left:2px solid var(--hair);
  padding:.7rem .9rem; border-radius:0 4px 4px 0; margin:.8rem 0; }
.rule { margin:1.4rem 0; overflow-x:auto; }
.rule-box { display:inline-block; min-width:16rem; }
.premises, .conclusion { padding:.15rem .25rem; }
.bar { border-top:1.5px solid var(--ink); position:relative; margin:.2rem 0; }
.rname { position:absolute; right:-.25rem; top:50%; transform:translate(100%,-50%);
  padding-left:.7rem; white-space:nowrap;
  font-family:ui-monospace,Menlo,Consolas,monospace; font-size:11.5px; }
.rname a { color:var(--rname); text-decoration:none; }
.rname a:hover { text-decoration:underline; }
.note { color:var(--faint); font-style:italic; font-size:14px; max-width:60ch;
  margin-top:.25rem; }
.bnote { color:var(--faint); font-style:italic; display:inline-block;
  max-width:44ch; white-space:normal; padding-left:.9em;
  vertical-align:middle; font-size:11.5px;
  font-family:"Iowan Old Style","Palatino Linotype",Palatino,Georgia,serif;
  font-size:13px; }
.crow { display:flex; align-items:baseline; gap:.9rem; }
.cname { font-family:ui-monospace,Menlo,Consolas,monospace; font-size:11.5px;
  white-space:nowrap; }
.cname a { color:var(--rname); text-decoration:none; }
.cname a:hover { text-decoration:underline; }
.crow:target { background:var(--panel); border-radius:3px; }
.tos { color:var(--tos); } .nova { color:var(--nova); } .meta { color:var(--meta); }
.kw { color:var(--gold); font-weight:600; }
.nat { color:var(--natc); }
.cmt { color:var(--faint); font-style:italic; }
a.rref { color:var(--rname); text-decoration:none; border-bottom:1px dotted var(--rname); }
:target { scroll-margin-top:1rem; }
:target > .rule-box > .bar { border-top-color:var(--rname); }
a:focus-visible { outline:2px solid var(--link); outline-offset:2px; }
#legend { display:grid; grid-template-columns:max-content 1fr;
  gap:.35rem 1.1rem; align-items:baseline;
  font-family:ui-sans-serif,system-ui,sans-serif; font-size:12.5px; color:var(--faint);
  border:1px solid var(--hair); border-radius:6px; padding:.6rem .9rem; margin:1rem 0 1.2rem; }
#legend .sw { font-family:ui-monospace,Menlo,monospace; font-size:13.5px; }
#legend .lglabel { white-space:nowrap; }
#legend .lgtoks { min-width:0; overflow-wrap:anywhere; }
#legend .lgnote { font-style:italic; }
.provenance { font-family:ui-sans-serif,system-ui,sans-serif; font-size:12.5px;
  color:var(--faint); margin:.1rem 0 0; }
@media (max-width: 900px) { #toc { display:none; } }
"""

def legend(vocab):
    """The complete declared tables — the legend IS the notation
    reference, so nothing is sampled or elided."""
    def toks(k, cls):
        ts = [t for t in vocab.get(k, []) if t != "latin"]
        return f'<span class="sw {cls}">' + html.escape(" ".join(ts)) + "</span>"
    latin = ('&ensp;<span class="lgnote">+ any bare Latin letter '
             "(t₀, A′, ē)</span>") if "latin" in vocab.get("nova", []) else ""
    rows = [
        ("fixed syntax", toks("keywords", "kw")),
        ("ToS metavariables", toks("tos", "tos")),
        ("Nova metavariables", toks("nova", "nova") + latin),
        ("walk / certificate metavariables", toks("meta", "meta")),
        ("meta-level naturals (indices)",
         '<span class="sw"><span class="kw">☐</span><span class="nat">ₙ</span> '
         '<span class="kw">⬡</span><span class="nat">ᵢ</span> '
         '<span class="kw">‖</span><span class="nat">ₙ₊₁</span></span>'),
        ("links to its rule",
         '<span class="sw" style="color:var(--rname)">rule-name</span>'),
        ("comment, unhighlighted", '<span class="sw cmt"># prose</span>'),
    ]
    body = "".join(f'<div class="lglabel">{lbl}</div><div class="lgtoks">{tk}</div>'
                   for lbl, tk in rows)
    return f'<div id="legend">{body}</div>'


def assemble(renderers, vocab, out_path):
    nav = ['<nav id="toc">']
    for r, (_, rel, title) in zip(renderers, FILES):
        nav.append(f'<details {"open" if r.key == "foundation" else ""}>'
                   f"<summary>{html.escape(title)}</summary>")
        for kind, text, a in r.toc:
            cls = {"H2": "toc-h2", "H3": "toc-h3", "R": "toc-r"}[kind]
            nav.append(f'<a class="{cls}" href="#{a}">{html.escape(text)}</a>')
        nav.append("</details>")
    nav.append("</nav>")

    main = []
    for r, (_, rel, title) in zip(renderers, FILES):
        main.append(f'<section id="{r.key}">')
        main.append(f"<h1>{html.escape(title)}</h1>")
        main.append(f'<p class="provenance">Rendered from <code>{rel}</code> — '
                    "the plain text remains the source of truth.</p>")
        if r.key == "foundation":
            main.append(legend(vocab))
        main.append("\n".join(r.body))
        main.append("</section>")

    doc = (f"<title>Nova Specs</title>\n<style>{CSS}</style>\n"
           f'<div id="wrap">\n{"".join(nav)}\n<main>\n'
           + "\n".join(main) + "\n</main>\n</div>\n")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(doc)

# ----- cross-check -------------------------------------------------------

def crosscheck(rulemap, dups):
    """Rules cited in src/idris vs rules defined in docs/."""
    src_text = ""
    for p in sorted((ROOT / "src" / "idris").rglob("*.idr")):
        src_text += p.read_text()

    ok = True
    if dups:
        ok = False
        print(f"DUPLICATE rule definitions ({len(dups)}):")
        for d in dups:
            print(f"  {d}")

    # citation tokens: hyphenated, first segment must be a prefix some
    # rule actually uses (filters ordinary hyphenated English)
    prefixes = {n.split("-")[0] for n in rulemap if "-" in n}
    token_re = re.compile(r"\b([a-z][a-z0-9]*(?:-[a-z0-9⁼ᴰ]+)+)\b")
    cited = set()
    unknown = set()
    for t in token_re.findall(src_text):
        if t in rulemap:
            cited.add(t)
        elif t.split("-")[0] in prefixes and len(t.split("-")) >= 3:
            unknown.add(t)

    if unknown:
        ok = False
        print(f"\nUNKNOWN rule-shaped citations in src/idris ({len(unknown)}) — "
              "typo or undocumented rule:")
        for t in sorted(unknown):
            print(f"  {t}")

    uncited = [n for n in rulemap if n not in cited]
    print(f"\ncoverage: {len(cited)}/{len(rulemap)} spec rules cited in src/idris")
    if uncited:
        print(f"uncited rules ({len(uncited)}) — informational:")
        for n in sorted(uncited):
            key, _ = rulemap[n]
            print(f"  [{key}] {n}")
    return ok

# ----- main ---------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="build/docs/specs.html")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()

    global HL
    HL = Highlighter(collect_vocab(FILES))
    rulemap, order, dups = collect(FILES)

    if args.check:
        sys.exit(0 if crosscheck(rulemap, dups) else 1)

    renderers = []
    for key, rel, title in FILES:
        r = FileRenderer(key, title, rulemap)
        r.render((ROOT / rel).read_text().splitlines())
        renderers.append(r)
    out = ROOT / args.out
    assemble(renderers, collect_vocab(FILES), out)
    total_rules = len(rulemap)
    print(f"{out}: {total_rules} rules across {len(FILES)} files"
          + (f", {len(dups)} DUPLICATE names" if dups else ""))

if __name__ == "__main__":
    main()
