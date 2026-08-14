#!/usr/bin/env python3
"""De-blank a Nova corpus: splice the elaborator's inferred hole
solutions back over the `_` tokens (the inverse of blank-indices.py).

Usage:
  1. NOVA_AUDIT=1 nova elab all.nova 2> deblank.txt   # DEBLANK lines
  2. python3 tools/deblank.py splice deblank.txt      # paste solutions
  3. python3 tools/deblank.py refold FILE...          # fold delta-normal
                                                      # +/* renderings
  4. repeat elab until the DEBLANK census is zero; a few inlined-def
     renderings (motive-less eliminators beyond +/*) need hand repair —
     see PerfNotes "The hole-free corpus".

The emitter lives in Nova.Elaboration (deblankLines): one line per
solved hole occurrence — module | start | end | solution, rendered in
surface syntax at the hole's own binder environment.
"""
import sys

MODE = sys.argv[1] if len(sys.argv) > 1 else ""

# ===== refold =====
import re, pathlib

def tokenize(s):
    toks, i = [], 0
    while i < len(s):
        c = s[i]
        if c in "() ":
            if c != " ": toks.append(c)
            i += 1
        else:
            j = i
            while j < len(s) and s[j] not in "() ": j += 1
            toks.append(s[i:j]); i = j
    return toks

def parse(toks):
    out = []; stack = [out]
    for t in toks:
        if t == "(":
            new = []; stack[-1].append(("p", new)); stack.append(new)
        elif t == ")": stack.pop()
        else: stack[-1].append(t)
    return out

def render(ns):
    return " ".join(n if isinstance(n, str) else "(" + render(n[1]) + ")" for n in ns)

def strip1(ns):
    while len(ns) == 1 and isinstance(ns[0], tuple): ns = ns[0][1]
    return ns

def binder_split(node):
    """('p', [a, 'b.', body...]) -> (binders, body) or None"""
    if not isinstance(node, tuple): return None
    inner = node[1]
    for k, t in enumerate(inner):
        if isinstance(t, str) and t.endswith(".") and t != ".":
            return inner[:k] + [t[:-1]], inner[k+1:]
    return None

def refold(ns):
    ns = [("p", refold(n[1])) if isinstance(n, tuple) else n for n in ns]
    out, i = [], 0
    while i < len(ns):
        if ns[i] == "ℕ-elim" and i + 3 < len(ns) + 0 or (ns[i] == "ℕ-elim" and i + 3 <= len(ns) - 1):
            z, s, t = ns[i+1], ns[i+2], ns[i+3]
            bs = binder_split(s) if isinstance(s, tuple) else None
            if bs and len(bs[0]) == 2:
                binders, body = bs
                b2 = binders[1]
                body = strip1(body)
                # plus: body = S b2
                if body == ["S", b2]:
                    out.append(("p", [z, "+", t])); i += 4; continue
                # mult: z = Z, body = A + b2
                if z == "Z" and len(body) == 3 and body[1] == "+" and body[2] == b2:
                    out.append(("p", [body[0], "*", t])); i += 4; continue
        out.append(ns[i]); i += 1
    return out

def fix_line(line):
    changed = True
    while changed:
        changed = False
        for m in re.finditer(r"\(ℕ-elim ", line):
            start = m.start()
            depth, j = 0, start
            while j < len(line):
                if line[j] == "(": depth += 1
                elif line[j] == ")":
                    depth -= 1
                    if depth == 0: break
                j += 1
            if depth != 0: continue
            group = line[start:j+1]
            tree = parse(tokenize(group))
            folded = refold(tree)
            new = render(folded)
            if new != render(tree):
                line = line[:start] + new + line[j+1:]
                changed = True
                break
    return line

def refold_files(files):
  for f in files:
      p = pathlib.Path(f)
      lines = p.read_text().split("\n")
      n = 0
      for i, ln in enumerate(lines):
          if "ℕ-elim" in ln:
              new = fix_line(ln)
              if new != ln: lines[i] = new; n += 1
      p.write_text("\n".join(lines))
      print(f, "fixed lines:", n)


# ===== splice =====
if MODE == "refold":
  refold_files(sys.argv[2:])
elif MODE == "splice":
  import re, collections, pathlib
  
  # ---- mini reader over rendered surface text: atoms, parens, binder groups ----
  def tokenize(s):
      toks, i = [], 0
      while i < len(s):
          c = s[i]
          if c in "() ": 
              if c != " ": toks.append(c)
              i += 1
          else:
              j = i
              while j < len(s) and s[j] not in "() ": j += 1
              toks.append(s[i:j]); i = j
      return toks
  
  def parse(toks):
      """returns list of nodes; node = str atom | ('paren', [nodes])"""
      out = []
      stack = [out]
      for t in toks:
          if t == "(":
              new = []
              stack[-1].append(("paren", new))
              stack.append(new)
          elif t == ")":
              stack.pop()
          else:
              stack[-1].append(t)
      return out
  
  def render(nodes):
      parts = []
      for n in nodes:
          if isinstance(n, str): parts.append(n)
          else: parts.append("(" + render(n[1]) + ")")
      return " ".join(parts)
  
  def is_binder_body(node, nbinders, bodycheck):
      """node = ('paren', [b1..bn, 'x.', ...]) — binder groups render as (n ih. body)"""
      if not (isinstance(node, tuple)): return None
      inner = node[1]
      # find the token ending with '.'
      for k, t in enumerate(inner):
          if isinstance(t, str) and t.endswith("."):
              binders = inner[:k] + [t[:-1]]
              if len(binders) != nbinders: return None
              body = inner[k+1:]
              return bodycheck(binders, body)
      return None
  
  def refold(nodes):
      """bottom-up: fold ℕ-elim plus/mult shapes into + / *"""
      nodes = [ ("paren", refold(n[1])) if isinstance(n, tuple) else n for n in nodes ]
      out, i = [], 0
      while i < len(nodes):
          n = nodes[i]
          if n == "ℕ-elim" and i + 3 < len(nodes) + 1 and i + 3 <= len(nodes) - 0:
              if i + 3 < len(nodes) or i + 3 == len(nodes) - 0:
                  pass
          if n == "ℕ-elim" and i + 3 < len(nodes) + 1 and (i + 3) <= len(nodes) - 1 + 1 and i + 3 <= len(nodes):
              pass
          if n == "ℕ-elim" and i + 3 < len(nodes) + 1:
              try:
                  z, s, t = nodes[i+1], nodes[i+2], nodes[i+3]
              except IndexError:
                  out.append(n); i += 1; continue
              # plus: s = (a b. S b)
              def plusish(binders, body):
                  return body == ["S", binders[1]] or body == [("paren", ["S", binders[1]])] or \
                         (len(body) == 1 and isinstance(body[0], tuple) and body[0][1] == ["S", binders[1]]) or \
                         (len(body) == 2 and body[0] == "S" and body[1] == binders[1])
              def multish(binders, body):
                  # body = (A + ih) with ih the second binder
                  b = body
                  if len(b) == 1 and isinstance(b[0], tuple): b = b[0][1]
                  return len(b) == 3 and b[1] == "+" and b[2] == binders[1] and z == "Z"
              def multarg(binders, body):
                  b = body
                  if len(b) == 1 and isinstance(b[0], tuple): b = b[0][1]
                  return b[0]
              if isinstance(s, tuple) and is_binder_body(s, 2, lambda bs, bd: plusish(bs, bd)):
                  za = z if isinstance(z, str) else ("paren", z[1])
                  ta = t if isinstance(t, str) else ("paren", t[1])
                  out.append(("paren", [za, "+", ta])); i += 4; continue
              if z == "Z" and isinstance(s, tuple) and is_binder_body(s, 2, lambda bs, bd: multish(bs, bd)):
                  A = is_binder_body(s, 2, lambda bs, bd: multarg(bs, bd))
                  ta = t if isinstance(t, str) else ("paren", t[1])
                  out.append(("paren", [A, "*", ta])); i += 4; continue
          out.append(n); i += 1
      return out
  
  def transform(term, mod):
      if mod:
          term = re.sub(r"(?<![A-Za-z0-9_.'])" + re.escape(mod) + r"\.", "", term)
      if "ℕ-elim" in term:
          term = render(refold(parse(tokenize(term))))
      return term
  
  # ---- collect and splice ----
  splices = collections.defaultdict(dict)   # file -> (l0,c0,l1,c1) -> term
  for ln in open(sys.argv[2]):
      if not ln.startswith("DEBLANK"): continue
      kind, mod, s0, s1, term = ln.rstrip("\n").split("|", 4)
      l0, c0 = map(int, s0.split(":")); l1, c1 = map(int, s1.split(":"))
      f = f"src/nova/{mod}.nova" if mod else "src/nova/all.nova"
      splices[f][(l0, c0, l1, c1)] = transform(term, mod)
  
  total, bad = 0, 0
  for f, m in splices.items():
      lines = pathlib.Path(f).read_text().split("\n")
      for (l0, c0, l1, c1), term in sorted(m.items(), reverse=True):
          if l0 != l1 or lines[l0][c0:c1] != "_":
              print(f"BADSPAN {f}:{l0}:{c0} {lines[l0][c0:c1]!r}"); bad += 1; continue
          lines[l0] = lines[l0][:c0] + "(" + term + ")" + lines[l0][c1:]
          total += 1
      pathlib.Path(f).write_text("\n".join(lines))
  print(f"spliced {total}, bad {bad}")
