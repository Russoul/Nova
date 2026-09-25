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
    return re.sub(r'\b([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+)\b', one, inst)

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
        if not site.endswith('checking ⋆') or shape != 'root': skipped[f'{shape} / {site.split(": ")[-1]}'] += 1; continue
        m = re.match(r'at (\S+):(\d+):(\d+)-(\d+):(\d+)$', at)
        if not m: skipped['no span'] += 1; continue
        f, l0, c0, l1, c1 = m.group(1), int(m.group(2)), int(m.group(3)), int(m.group(4)), int(m.group(5))
        if l0 != l1: skipped['multi-line span'] += 1; continue
        module = item.split(':')[0]
        edits[f].append((l0, c0, c1, insts, module))
    done = 0
    for f, es in edits.items():
        text = open(f, encoding='utf-8').read(); src = text.split('\n')
        imps = imports_of(text); needed = collections.defaultdict(set)
        for (l0, c0, c1, insts, module) in sorted(es, key=lambda e: (e[0], e[1]), reverse=True):
            line = src[l0]   # positions are 0-based
            if line[c0:c1] != '⋆': skipped['span is not ⋆'] += 1; continue
            inst = render(insts, module, imps, needed)
            if ' ' in inst: inst = f'({inst})'
            src[l0] = line[:c0] + inst + line[c1:]
            done += 1
        src = add_imports(src, needed)
        open(f, 'w', encoding='utf-8').write('\n'.join(src))
    print(f"migrated {done} sites in {len(edits)} files; left: {dict(skipped)}")

if __name__ == '__main__':
    main()
