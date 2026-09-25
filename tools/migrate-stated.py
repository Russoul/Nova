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
import re, sys, os, collections

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
        if kind.startswith('chain, step'): skipped['chain step'] += 1; continue
        if c0 == 0: skipped['whole item (a generated item\'s site)'] += 1; continue
        module = item.split(':')[0]
        env = parts[7].replace('env:', '').split() if len(parts) > 7 else []
        claim = parts[8].replace('claim:', '', 1).strip() if len(parts) > 8 else ''
        edits[f].append((l0, c0, l1, c1, shape, kind, [i.strip() for i in insts.split(';;') if i.strip()], module, env, claim))
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
            cands = [e for e in es if e[0] + 1 <= err_line and (e[0], e[1], e[2], e[3]) not in dropped]
            if not cands:
                open(f, 'w', encoding='utf-8').write(original); skipped['file reverted (error not at a site)'] += 1; break
            worst = max(cands, key=lambda e: e[0])
            dropped.add((worst[0], worst[1], worst[2], worst[3])); skipped['does not elaborate after the edit'] += 1
    print(f"migrated {dict(done)} in {len(edits)} files; left: {dict(skipped)}")

def elab_error_line(f):
    import subprocess
    r = subprocess.run(['build/exec/nova', 'elab', f], capture_output=True, text=True)
    out = r.stdout + r.stderr
    m = re.search(re.escape(f) + r':(\d+):\d+: error:(.*)', out)
    if m:
        if os.environ.get('MIGRATE_DEBUG'): print(f"  [{f}:{m.group(1)}] {m.group(2).strip()[:200]}")
        return int(m.group(1))
    # an open obligation or hole after the edit: acceptance lost — its
    # site line names the culprit
    m = re.search(r'at: ' + re.escape(f) + r':(\d+):\d+:(.*)', out)
    if m:
        if os.environ.get('MIGRATE_DEBUG'): print(f"  [{f}:{m.group(1)}] open: {m.group(2).strip()[:160]}")
        return int(m.group(1))
    if 'error' in out.lower(): return 10**9
    return None

def apply_file(f, original, es, dropped, skipped):
    done = collections.Counter()
    if True:
        text = original; src = text.split('\n')
        imps = imports_of(text); needed = collections.defaultdict(set)
        # one edit per span: sites sharing a span pool their instances
        by_span = collections.OrderedDict()
        for (l0, c0, l1, c1, shape, kind, insts, module, env, claim) in es:
            key = (l0, c0, l1, c1)
            if key not in by_span: by_span[key] = (shape, kind, [], module, [])
            for i in insts:
                if i not in by_span[key][2]: by_span[key][2].append(i)
            by_span[key][4].append((kind, insts, env, claim))
        # a span inside another: its instances join the outer one's
        # claims (the claim is in scope there too); a partial overlap
        # is left to the author
        def contains(a, b):
            return (a[0], a[1]) <= (b[0], b[1]) and (b[2], b[3]) <= (a[2], a[3]) and a != b
        def overlaps(a, b):
            return not ((a[2], a[3]) <= (b[0], b[1]) or (b[2], b[3]) <= (a[0], a[1]))
        spans = sorted(by_span)
        merged = set(); clash = set()
        for a in spans:
            for b in spans:
                if a == b: continue
                if contains(a, b):
                    sa, ka, ia, ma, ssa = by_span[a]; sb, kb, ib, mb, ssb = by_span[b]
                    for i in ib:
                        if i not in ia: ia.append(i)
                    if kb.startswith('well-definedness') and not ka.startswith('well-definedness'):
                        ssa.extend(ssb)
                    merged.add(b)
                elif overlaps(a, b): clash.add(a); clash.add(b)
        clash -= merged
        counter = [0]
        for key in sorted(by_span, reverse=True):
            l0, c0, l1, c1 = key; shape, kind, insts, module, sites = by_span[key]
            if key in dropped or key in merged: continue
            if key in clash: skipped['overlapping spans'] += 1; continue
            line = src[l0]   # positions are 0-based
            if l1 != l0:
                if line[:c0].strip() != '': skipped['multi-line span not at a line start'] += 1; continue
                span = None
            else:
                span = line[c0:c1]
            def wrap(lets):
                if span is None:
                    # the span starts its line: the bindings become a let
                    # BLOCK above it at its column, the span the block's
                    # last item (docs/NovaElaboration.txt, Layout — LET)
                    if line[:c0].strip() != '' or not lets.endswith(' in '): raise ValueError('multi-line span not at a line start')
                    binds = [b.strip() for b in lets.split(' in ') if b.strip()]
                    first = 'let ' + binds[0][4:] if binds[0].startswith('let ') else 'let ' + binds[0]
                    rest = [(' ' * (c0 + 4)) + b[4:] for b in binds[1:]]
                    src[l0:l0] = [(' ' * c0) + first] + rest
                else:
                    src[l0] = line[:c0] + '(' + lets + span + ')' + line[c1:]
            if kind == 'checking ⋆' and shape == 'root' and len(insts) == 1:
                if span != '⋆': skipped['span is not ⋆'] += 1; continue
                inst = render(insts[0], module, imps, needed)
                env0 = sites[0][2] if sites else []
                if '_' in env0 and re.search(r'(?<![\w])_(?![\w])', inst): skipped['instance names an unnamed binder'] += 1; continue
                if ' ' in inst: inst = f'({inst})'
                src[l0] = line[:c0] + inst + line[c1:]
                done['⋆ := instance'] += 1
                continue
            if kind.startswith('well-definedness') and all(c.startswith('wd ') for (_, _, _, c) in sites):
                # each well-definedness obligation at this eliminator: a
                # claim QUANTIFIED over the case's binders (x x′ h), its
                # type the measure's rendering of the statement, its
                # proof the instance as a λ over them
                lets = ''; ok = True
                for (k2, ins2, env2, claim2) in sites:
                    if len(ins2) != 1 or not claim2 or len(env2) < 3 or re.search(r'\?\d|𝒮|\[|\]', ins2[0] + claim2): ok = False; break
                    x, x1, h = env2[-3], env2[-2], env2[-1]
                    # an unnamed binder the instance or the claim refers to
                    # (printed `_`, unspellable), or a case binder shadowing
                    # an earlier name (the λ would capture the wrong one)
                    if ('_' in env2 and re.search(r'(?<![\w])_(?![\w])', ins2[0] + ' ' + claim2)) or len({x, x1, h}) < 3 or any(n in env2[:-3] for n in (x, x1, h)):
                        ok = False; break
                    r = render(ins2[0], module, imps, needed)
                    ct = render(claim2[3:], module, imps, needed)
                    counter[0] += 1
                    lets += f'let claim{counter[0]} : {ct} = λ{x} {x1} {h}. {r} in '
                if not ok: skipped['well-definedness: not one instance, or unspellable'] += 1; continue
                wrap(lets)
                done['λ-claim / well-definedness'] += 1
                continue
            rendered = []; unusable = False
            env0 = sites[0][2] if sites else []
            for i in insts:
                r = render(i, module, imps, needed)
                if '_' in env0 and re.search(r'(?<![\w])_(?![\w])', r): unusable = True
                if kind.startswith('well-definedness'):
                    # the wd binders (x, x′, h of the quot-elim's case)
                    # are the hypothesis's own: an instance applied to
                    # them at the end stays quantified over them; one
                    # that mentions them inside its arguments cannot be
                    # stated outside the eliminator — left to the author
                    mb = re.search(r'quot-elim\s*\(\s*([^\s.]+)\s*\.', span or line[c0:])
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
            wrap(lets)
            done[f'let-wrapped / {kind}'] += 1
        src = add_imports(src, needed)
        open(f, 'w', encoding='utf-8').write('\n'.join(src))
    return done

if __name__ == '__main__':
    main()
