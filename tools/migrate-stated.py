#!/usr/bin/env python3
"""Migration by the measure (docs/NovaStrategy.txt, the engine
programme, step 3): read the SEARCH-NEEDED lines of a
`NOVA_NOSEARCH=measure NOVA_AUDIT=1` run and write the stated form
into the source at the sites where it is mechanical — a ⋆ whose proof
the search found as ONE lemma instance at the root becomes that
instance. Everything else is left for the author. Usage:

  NOVA_NOSEARCH=measure NOVA_AUDIT=1 build/exec/nova elab src/nova/all.nova 2> audit.txt >/dev/null
  python3 tools/migrate-stated.py audit.txt        # edits src/nova in place
  ./normalize-corpus.sh                            # canonical form
"""
import re, sys, collections

def short_name(qual, module, imports):
    """The surface spelling of a Σ name at a site in `module`: its
    last segment when the module defines it or imports it by name,
    else left as it is (the elaborator will say)."""
    if '.' not in qual: return qual
    mod, _, name = qual.rpartition('.')
    if mod == module: return name
    for imod, names in imports:
        if imod == mod and (names is None or name in names): return name
    return qual

def imports_of(text):
    out = []
    for m in re.finditer(r'^import\s+([A-Za-z0-9_.]+)(?:\s*\(([^)]*)\))?', text, re.M):
        names = None if m.group(2) is None else [n.strip() for n in m.group(2).split(',')]
        out.append((m.group(1), names))
    return out

def render(inst, module, imports, needed):
    """The instance in surface spelling: every Σ name shortened to its
    last segment; a name from another module not yet opened by name is
    recorded in `needed` (module -> names) for the import list — a
    term cannot spell a qualified name."""
    def one(m):
        qual = m.group(1)
        mod, _, name = qual.rpartition('.')
        s = short_name(qual, module, imports)
        if s == qual and mod != module:
            needed[mod].add(name); return name
        return s
    # a Σ name: module segments, then the item — which may be an
    # operator (Core.prop.¬), so the last segment is any non-delimiter run
    return re.sub(r"(?<![\w.'])([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\.[^\s().{},]+)", one, inst)

def add_imports(src, needed):
    """Open the needed names: appended to an existing `import M (…)`
    list, or a new `import M (…)` line after the last import."""
    out = list(src)
    last_import = max((i for i, l in enumerate(out) if l.startswith('import ')), default=None)
    for mod, names in needed.items():
        done = False
        for i, l in enumerate(out):
            m = re.match(r'^import\s+' + re.escape(mod) + r'\s*\(([^)]*)\)\s*$', l)
            if m:
                have = [n.strip() for n in m.group(1).split(',') if n.strip()]
                out[i] = f"import {mod} ({', '.join(have + sorted(n for n in names if n not in have))})"
                done = True; break
            if re.match(r'^import\s+' + re.escape(mod) + r'\s*$', l):
                done = True; break
        if not done:
            line = f"import {mod} ({', '.join(sorted(names))})"
            if last_import is None: out.insert(0, line); last_import = 0
            else: last_import += 1; out.insert(last_import, line)
    return out

def main():
    lines = [l.rstrip('\n') for l in open(sys.argv[1]) if l.startswith('SEARCH-NEEDED')]
    edits = collections.defaultdict(list)   # file -> [(line, c0, c1, text)]
    skipped = collections.Counter()
    for l in lines:
        parts = [p.strip() for p in l.split(' | ')]
        if len(parts) < 7: skipped['malformed'] += 1; continue
        head, item, site, proof, at, shape, insts = parts[0], parts[1], parts[2], parts[3], parts[4], parts[5], parts[6]
        kind = site.split(': ')[-1]
        m = re.match(r'at (\S+):(\d+):(\d+)-(\d+):(\d+)$', at)
        if not m: skipped['no span'] += 1; continue
        f, l0, c0, l1, c1 = m.group(1), int(m.group(2)), int(m.group(3)), int(m.group(4)), int(m.group(5))
        if l0 != l1: skipped[f'multi-line span / {kind}'] += 1; continue
        if kind.startswith('chain, step'): skipped['chain step'] += 1; continue
        if c0 == 0: skipped['whole item (a generated item\'s site)'] += 1; continue
        module = item.split(':')[0]
        edits[f].append((l0, c0, c1, shape, kind, [i.strip() for i in insts.split(';;') if i.strip()], module))
    done = collections.Counter()
    for f, es in edits.items():
        original = open(f, encoding='utf-8').read()
        dropped = set()
        while True:
            skipped_f = collections.Counter()
            done_f = apply_file(f, original, es, dropped, skipped_f)
            err_line = elab_error_line(f)
            if err_line is None:
                for k, v in done_f.items(): done[k] += v
                for k, v in skipped_f.items(): skipped[k] += v
                break
            # the site at or nearest above the failing line is left to
            # the author; the file is rewritten without it
            cands = [e for e in es if e[0] + 1 <= err_line and (e[0], e[1], e[2]) not in dropped]
            if not cands:
                open(f, 'w', encoding='utf-8').write(original); skipped['file reverted (error not at a site)'] += 1; break
            worst = max(cands, key=lambda e: e[0])
            dropped.add((worst[0], worst[1], worst[2])); skipped['does not elaborate after the edit'] += 1
    print(f"migrated {dict(done)} in {len(edits)} files; left: {dict(skipped)}")

def elab_error_line(f):
    import subprocess
    r = subprocess.run(['build/exec/nova', 'elab', f], capture_output=True, text=True)
    out = r.stdout + r.stderr
    m = re.search(re.escape(f) + r':(\d+):\d+: error:', out)
    if m: return int(m.group(1))
    # an open obligation or hole after the edit: acceptance lost — its
    # site line names the culprit
    m = re.search(r'at: ' + re.escape(f) + r':(\d+):\d+:', out)
    if m: return int(m.group(1))
    if 'error' in out.lower(): return 10**9
    return None

def apply_file(f, original, es, dropped, skipped):
    done = collections.Counter()
    if True:
        text = original; src = text.split('\n')
        imps = imports_of(text); needed = collections.defaultdict(set)
        # one edit per span: sites sharing a span pool their instances
        by_span = collections.OrderedDict()
        for (l0, c0, c1, shape, kind, insts, module) in es:
            key = (l0, c0, c1)
            if key not in by_span: by_span[key] = (shape, kind, [], module)
            for i in insts:
                if i not in by_span[key][2]: by_span[key][2].append(i)
        # overlapping spans on one line are left to the author
        spans = sorted(by_span)
        clash = set()
        for i, a in enumerate(spans):
            for b in spans[i+1:]:
                if a[0] == b[0] and not (a[2] <= b[1] or b[2] <= a[1]): clash.add(a); clash.add(b)
        counter = [0]
        for key in sorted(by_span, reverse=True):
            l0, c0, c1 = key; shape, kind, insts, module = by_span[key]
            if key in dropped: continue
            if key in clash: skipped['overlapping spans'] += 1; continue
            line = src[l0]   # positions are 0-based
            span = line[c0:c1]
            if kind == 'checking ⋆' and shape == 'root' and len(insts) == 1:
                if span != '⋆': skipped['span is not ⋆'] += 1; continue
                inst = render(insts[0], module, imps, needed)
                if ' ' in inst: inst = f'({inst})'
                src[l0] = line[:c0] + inst + line[c1:]
                done['⋆ := instance'] += 1
                continue
            rendered = []; unusable = False
            for i in insts:
                r = render(i, module, imps, needed)
                if kind.startswith('well-definedness'):
                    # the wd binders (x, x′, h of the quot-elim's case)
                    # are the hypothesis's own: an instance applied to
                    # them at the end stays quantified over them; one
                    # that mentions them inside its arguments cannot be
                    # stated outside the eliminator — left to the author
                    mb = re.search(r'quot-elim\s*\(\s*([^\s.]+)\s*\.', span)
                    if mb:
                        an = mb.group(1); toks = r.split(' ')
                        binders = {an, an + "'", 'h', '{' + an + '}', '{' + an + "'}", '{h}'}
                        while toks and toks[-1] in binders: toks.pop()
                        r = ' '.join(toks)
                        if not r or any(re.search(r'(?<![A-Za-z0-9_\'])' + re.escape(b) + r'(?![A-Za-z0-9_\'])', r) for b in (an, an + "'", 'h')):
                            unusable = True
                # an unnamed binder, or a core-only spelling (a carried
                # signature 𝒮, a bracketed spine) the surface has no word for
                if not r or re.search(r'\?\d|𝒮|\[|\]', r): unusable = True
                rendered.append(r)
            if unusable: skipped['claim mentions the case binders or an unnamed binder'] += 1; continue
            lets = ''
            for r in rendered:
                counter[0] += 1
                lets += f'let claim{counter[0]} = {r} in '
            src[l0] = line[:c0] + '(' + lets + span + ')' + line[c1:]
            done[f'let-wrapped / {kind}'] += 1
        src = add_imports(src, needed)
        open(f, 'w', encoding='utf-8').write('\n'.join(src))
    return done

if __name__ == '__main__':
    main()
