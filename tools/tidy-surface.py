#!/usr/bin/env python3
"""Tidy machine-pasted surface syntax (the inverse artifacts of
tools/deblank.py): infix the `(nat.+)`/`(nat.*)` prefix renderings,
unqualify names the file already imports (or defines itself), collapse
doubled parens, unwrap parens around lone atoms, and drop parens the
`infixl 6 +` / `infixl 7 *` precedences make redundant (left operands
of the same operator, `*`-groups beside `+`, either beside `≡`/`∈`).

Conservative by construction: every removal is licensed by a local
neighbor test; anything unclassifiable is left alone. Comments and
`using (...)` clauses are masked out first. Idempotent.

Usage: tidy-surface.py FILE...   (rewrites in place, reports changes)
"""
import re
import sys
import pathlib

WS = " \t\n"
# depth-0 tokens that disqualify a group from the +/* fragment
OTHER_OPS = {"≡", "∈", "→", "↔", "⊃", "∨", "∧", "⨯", ",", "≔", "⊞",
             "≤", "<", ":", "/", "|", "∥"}


def scan_unit(s, i):
    """Next balanced unit at or after i: a (...) group or a bare token.
    Returns (start, end) or None."""
    n = len(s)
    while i < n and s[i] in WS:
        i += 1
    if i >= n or s[i] == ")":
        return None
    if s[i] == "(":
        d, j = 0, i
        while j < n:
            if s[j] == "(":
                d += 1
            elif s[j] == ")":
                d -= 1
                if d == 0:
                    return (i, j + 1)
            j += 1
        raise ValueError("unbalanced parens")
    j = i
    while j < n and s[j] not in WS + "()":
        j += 1
    return (i, j)


def mask(text):
    """Replace comments and `using (...)` clauses with opaque
    placeholders so no pass touches them."""
    stash = []

    def put(m):
        stash.append(m.group(0))
        return f"\x00{len(stash) - 1}\x00"

    # import lists may span lines: mask the balanced (...) span
    out, i = [], 0
    for m in re.finditer(r"^import\s+[A-Za-z][A-Za-z0-9']*\s*\(", text, re.M):
        if m.start() < i:
            continue
        d, j = 0, m.end() - 1
        while True:
            if text[j] == "(":
                d += 1
            elif text[j] == ")":
                d -= 1
                if d == 0:
                    break
            j += 1
        stash.append(text[m.start():j + 1])
        out.append(text[i:m.start()] + f"\x00{len(stash) - 1}\x00")
        i = j + 1
    text = "".join(out) + text[i:]
    text = re.sub(r"--[^\n]*", put, text)
    text = re.sub(r"using \([^)]*\)", put, text)
    return text, stash


def unmask(text, stash):
    return re.sub(r"\x00(\d+)\x00", lambda m: stash[int(m.group(1))], text)


# every operator declared infix anywhere in the corpus, plus its
# possibly-qualified section spelling; sections of these must keep
# their parens, and saturated section applications get infixed
INFIX_OPS = {"+", "*", "⊞", "∧", "⊃", "∨", "↔"}
SECTION = re.compile(
    r"\((?:[A-Za-z][A-Za-z0-9']*\.)?([" + "".join(INFIX_OPS) + r"])\)")


def infixize(s):
    """((op) A B) -> (A op B) for declared infix op, qualified or not;
    an unsaturated section keeps its parens."""
    pos = 0
    while True:
        m = SECTION.search(s, pos)
        if m is None:
            return s
        op = m.group(1)
        u1 = scan_unit(s, m.end())
        u2 = scan_unit(s, u1[1]) if u1 else None
        if u1 is None or u2 is None:
            pos = m.end()
            continue
        a, b = s[u1[0]:u1[1]], s[u2[0]:u2[1]]
        s = s[:m.start()] + f"({a} {op} {b})" + s[u2[1]:]
        pos = m.start()


def parse_imports(orig):
    """mod -> names imported unqualified from it."""
    avail = {}
    for m in re.finditer(r"^import\s+([A-Za-z][A-Za-z0-9']*)\s*\(", orig, re.M):
        i = m.end() - 1
        d, j = 0, i
        while True:
            if orig[j] == "(":
                d += 1
            elif orig[j] == ")":
                d -= 1
                if d == 0:
                    break
            j += 1
        names = {n.strip() for n in orig[i + 1:j].split(",")}
        avail.setdefault(m.group(1), set()).update(n for n in names if n)
    return avail


def unqualify(s, avail, selfmod, selfdefs):
    def repl(m):
        mod, name = m.group(1), m.group(2)
        if name in avail.get(mod, ()):
            return name
        if mod == selfmod and name in selfdefs:
            return name
        return m.group(0)

    return re.sub(r"\b([A-Za-z][A-Za-z0-9']*)\.([A-Za-z][A-Za-z0-9']*|[+*¬⊥∧∨↔⊃⊞])",
                  repl, s)


def collapse_doubles(s):
    """((X)) -> (X) wherever the two opens/closes pair with each other."""
    while True:
        out, changed, i, n = [], False, 0, len(s)
        while i < n:
            if s[i] == "(" and i + 1 < n and s[i + 1] == "(":
                u = scan_unit(s, i + 1)
                if u and u[0] == i + 1 and s[u[1]:u[1] + 1] == ")":
                    out.append(s[i + 1:u[1]])
                    i = u[1] + 1
                    changed = True
                    continue
            out.append(s[i])
            i += 1
        s = "".join(out)
        if not changed:
            return s


def unwrap_atoms(s):
    """(tok) -> tok for a lone space-free token that isn't a binder."""
    def repl(m):
        tok = m.group(1)
        if tok.endswith(".") or tok.startswith(("λ", "Λ")):
            return m.group(0)
        if tok in INFIX_OPS or tok.split(".")[-1] in INFIX_OPS:
            return m.group(0)  # operator section: parens are the syntax
        return tok

    while True:
        s2 = re.sub(r"\(([^\s()]+)\)", repl, s)
        if s2 == s:
            return s
        s = s2


def classify(content):
    """'mul' if depth-0 ops are only *, 'add' if only +/* with a +,
    else None."""
    i, n, ops = 0, len(content), set()
    while i < n:
        if content[i] in WS:
            i += 1
            continue
        u = scan_unit(content, i)
        if u is None:
            return None
        tok = content[u[0]:u[1]]
        if not tok.startswith("("):
            if tok in ("+", "*"):
                ops.add(tok)
            elif tok in OTHER_OPS or tok.endswith(".") or \
                    tok.startswith(("λ", "Λ")) or \
                    any(c in OTHER_OPS for c in tok):
                return None
        i = u[1]
    if ops == {"*"}:
        return "mul"
    if "+" in ops and ops <= {"+", "*"}:
        return "add"
    return None


def prev_token(s, i):
    """Token before position i. None = start or an opening paren
    (group is first in its enclosure); ')' = a preceding unit, i.e.
    application context."""
    j = i
    while j > 0 and s[j - 1] in WS:
        j -= 1
    if j == 0 or s[j - 1] == "(":
        return None
    if s[j - 1] == ")":
        return ")"
    k = j
    while k > 0 and s[k - 1] not in WS + "()":
        k -= 1
    return s[k:j]


def next_token(s, i):
    """Token after position i. None = end or a closing paren; '(' = a
    following unit, i.e. the group would capture it as an argument."""
    n = len(s)
    while i < n and s[i] in WS:
        i += 1
    if i >= n or s[i] == ")":
        return None
    if s[i] == "(":
        return "("
    j = i
    while j < n and s[j] not in WS + "()":
        j += 1
    return s[i:j]


PREC = {"*": 7, "+": 6, "≡": 2, "∈": 1}


def precedence_unwrap(s):
    """Drop parens the fixities make redundant, but ONLY when both
    neighbors are operator context — an identifier neighbor means the
    group is an application argument (or head) and its parens are
    load-bearing. infixl: as a LEFT operand of an equal-precedence
    operator the group unwraps, as a RIGHT one it does not."""
    while True:
        changed = False
        i = 0
        while i < len(s):
            if s[i] != "(":
                i += 1
                continue
            u = scan_unit(s, i)
            cls = classify(s[u[0] + 1:u[1] - 1])
            if cls is None:
                i += 1
                continue
            gprec = 7 if cls == "mul" else 6
            prev, nxt = prev_token(s, u[0]), next_token(s, u[1])
            prev_safe = (prev is None or prev in PREC or prev == "≔"
                         or prev.endswith("."))
            next_safe = nxt is None or nxt in PREC
            ok = prev_safe and next_safe
            if ok and prev in PREC:      # right operand of prev: strict
                ok = gprec > PREC[prev]
            if ok and nxt in PREC:       # left operand of nxt: infixl
                ok = gprec >= PREC[nxt]
            if ok:
                s = s[:u[0]] + s[u[0] + 1:u[1] - 1] + s[u[1]:]
                changed = True
            else:
                i += 1
        if not changed:
            return s


def tidy_file(path):
    orig = path.read_text()
    avail = parse_imports(orig)
    selfmod = path.stem
    selfdefs = set(re.findall(r"^(?:def|type)\s+(\S+)", orig, re.M))
    s, stash = mask(orig)
    s = infixize(s)
    s = unqualify(s, avail, selfmod, selfdefs)
    for _ in range(8):
        before = s
        s = collapse_doubles(s)
        s = unwrap_atoms(s)
        s = precedence_unwrap(s)
        if s == before:
            break
    s = unmask(s, stash)
    if s != orig:
        path.write_text(s)
        return True
    return False


if __name__ == "__main__":
    changed = [p for p in map(pathlib.Path, sys.argv[1:]) if tidy_file(p)]
    print(f"tidied {len(changed)} file(s):")
    for p in changed:
        print(f"  {p}")
