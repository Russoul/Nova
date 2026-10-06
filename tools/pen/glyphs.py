#!/usr/bin/env python3
"""Extract centreline stroke glyphs from a monospace font, for the pen
editor, which draws text as strokes rather than with a font.

Each glyph is rasterised, thinned to a one-pixel skeleton (Guo-Hall),
traced into polylines split at junctions, pruned of the short spurs that
serifs and corners leave, and simplified (Ramer-Douglas-Peucker). The
result is one JSON file:

  {"font": NAME, "units": "em", "y": "up",
   "cell": {"width": W, "ascent": A, "descent": D}, "pen": P,
   "glyphs": {CHAR: [STROKE, ...], ...}}

A STROKE is a polyline [[x, y], ...] in em units from the cell's origin
on the baseline, y up. P is the font's stem width: drawn with a round pen
that wide, the strokes keep the font's weight. A dot wider than the pen
is a stroke from its centre out and once around its rim. A combining
mark is keyed alone and placed for its base character's cell. A
character the font lacks, or one that extracts badly, is taken from the
overrides file (a JSON object CHAR -> [STROKE, ...]).

A glyph whose strokes cover under half of the font's ink is reported:
it has failed (a solid shape has no centreline) and wants an override.

Usage: glyphs.py [--font TTF] [--overrides JSON] [--out JSON] [--sheet PNG]
                 [SPEC...]
  SPEC     files whose characters to cover (default: docs/*.nspec);
           printable ASCII is always covered
  --sheet  also draw every glyph, its strokes laid over the font's
           rendering, for review
"""
import argparse
import glob
import json
import os
import struct
import sys
import unicodedata

import numpy as np
from PIL import Image, ImageDraw, ImageFont

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..'))
FONT = os.path.expanduser('~/Library/Fonts/EversonMonoNerdFont-Regular.ttf')
EM = 512  # raster pixels per em
SPUR = 1.5  # a branch from a free end to a junction shorter than SPUR pens is a spur
TOLERANCE = 1.5  # simplification tolerance, in raster pixels
COVER = 0.5  # below this share of the font's ink covered, a glyph has failed (a solid shape, a lost branch)

# The 8 neighbours, clockwise from north, as (dy, dx).
RING = [(-1, 0), (-1, 1), (0, 1), (1, 1), (1, 0), (1, -1), (0, -1), (-1, -1)]
# The same, orthogonal ones first: a walk then follows a staircase instead of cutting it.
NEAR = RING[0::2] + RING[1::2]


def cmap(path):
    """The code points a TrueType font maps (cmap formats 4 and 12)."""
    data = open(path, 'rb').read()
    count = struct.unpack('>H', data[4:6])[0]
    tables = {}
    for i in range(count):
        entry = data[12 + 16 * i:28 + 16 * i]
        tables[entry[:4].decode('latin1')] = struct.unpack('>I', entry[8:12])[0]
    base, points = tables['cmap'], set()
    for i in range(struct.unpack('>H', data[base + 2:base + 4])[0]):
        sub = base + struct.unpack('>I', data[base + 8 + 8 * i:base + 12 + 8 * i])[0]
        fmt = struct.unpack('>H', data[sub:sub + 2])[0]
        if fmt == 4:
            segs = struct.unpack('>H', data[sub + 6:sub + 8])[0] // 2
            ends = struct.unpack('>%dH' % segs, data[sub + 14:sub + 14 + 2 * segs])
            starts = struct.unpack('>%dH' % segs, data[sub + 16 + 2 * segs:sub + 16 + 4 * segs])
            for start, end in zip(starts, ends):
                points.update(range(start, end + 1))
        elif fmt == 12:
            for g in range(struct.unpack('>I', data[sub + 12:sub + 16])[0]):
                start, end, _ = struct.unpack('>III', data[sub + 16 + 12 * g:sub + 28 + 12 * g])
                points.update(range(start, end + 1))
    points.discard(0xFFFF)
    return points


def raster(font, ch):
    """The glyph as a boolean array, and the array position of the cell's origin."""
    origin = (EM, 2 * EM)  # (x, y): room on every side, a combining mark may sit left of it
    img = Image.new('L', (3 * EM, 3 * EM), 0)
    ImageDraw.Draw(img).text(origin, ch, font=font, fill=255, anchor='ls')
    return np.array(img) >= 128, origin


def thin(img):
    """Guo-Hall thinning: a one-pixel wide, 8-connected skeleton. (Zhang-Suen,
    the usual choice, deletes a diagonal stroke outright once it is two
    pixels thick: an arrowhead loses a barb.)"""
    a = np.pad(img, 1)
    while True:
        changed = False
        for step in (0, 1):
            p2, p3, p4, p5, p6, p7, p8, p9 = [a[1 + dy:a.shape[0] - 1 + dy, 1 + dx:a.shape[1] - 1 + dx]
                                              for dy, dx in RING]
            c = ((~p2 & (p3 | p4)).astype(np.uint8) + (~p4 & (p5 | p6)) + (~p6 & (p7 | p8)) + (~p8 & (p9 | p2)))
            n1 = (p9 | p2).astype(np.uint8) + (p3 | p4) + (p5 | p6) + (p7 | p8)
            n2 = (p2 | p3).astype(np.uint8) + (p4 | p5) + (p6 | p7) + (p8 | p9)
            n = np.minimum(n1, n2)
            m = ((p2 | p3 | ~p5) & p4) if step else ((p6 | p7 | ~p9) & p8)
            gone = a[1:-1, 1:-1] & (c == 1) & (n >= 2) & (n <= 3) & ~m
            if gone.any():
                a[1:-1, 1:-1][gone] = False
                changed = True
        if not changed:
            return a[1:-1, 1:-1]


def crossings(sk, y, x):
    """How many skeleton branches meet at (y, x): 0 alone, 1 an end, 2 a path, 3+ a junction."""
    ring = [sk[y + dy, x + dx] for dy, dx in RING]
    return sum(1 for i in range(8) if not ring[i] and ring[(i + 1) % 8])


def trace(sk):
    """The skeleton as a graph: node centres, and edges (a, b, pixels) between them.
    A node is a cluster of touching end/junction pixels; b is None for a closed loop."""
    pixels = set(zip(*(c.tolist() for c in np.nonzero(sk))))

    def near(p):
        return [(p[0] + dy, p[1] + dx) for dy, dx in NEAR if (p[0] + dy, p[1] + dx) in pixels]

    nodes = {p for p in pixels if crossings(sk, *p) != 2}
    owner, centres = {}, []
    for p in nodes:
        if p in owner:
            continue
        owner[p], stack, members = len(centres), [p], []
        while stack:
            q = stack.pop()
            members.append(q)
            for r in near(q):
                if r in nodes and r not in owner:
                    owner[r] = owner[p]
                    stack.append(r)
        centres.append((sum(m[0] for m in members) / len(members), sum(m[1] for m in members) / len(members)))

    edges, seen = [], set()

    def walk(start, cur, home):
        path, prev = [cur], start
        seen.add(cur)
        while True:
            ahead = [r for r in near(cur) if r != prev]
            stop = [r for r in ahead if r in nodes and (owner[r] != home or len(path) > 2)]
            if stop:
                return path, owner[stop[0]]
            step = [r for r in ahead if r not in nodes and r not in seen]
            if not step:
                return path, None
            prev, cur = cur, step[0]
            path.append(cur)
            seen.add(cur)

    for p in nodes:
        for q in near(p):
            if q not in nodes and q not in seen:
                path, end = walk(p, q, owner[p])
                edges.append([owner[p], end, path])
    for p in sorted(pixels - nodes - seen):  # closed loops, with no node on them
        if p not in seen:
            path, _ = walk(p, p, None)
            edges.append([None, None, path])
    return centres, edges


def points(centres, edge):
    """An edge as (y, x) points, from its start node's centre to its end node's."""
    a, b, path = edge
    pts = ([centres[a]] if a is not None else []) + [tuple(map(float, p)) for p in path]
    if b is not None:
        pts.append(centres[b])
    elif a is None:
        pts.append(pts[0])  # a closed loop
    return pts


def length(pts):
    return sum(np.hypot(p[0] - q[0], p[1] - q[1]) for p, q in zip(pts, pts[1:]))


def prune(centres, edges, spur):
    """Drop spurs (short branches from a free end to a junction), then join the
    two edges at every node that is left with exactly two."""
    edges = [[a, b, points(centres, [a, b, path])] for a, b, path in edges]
    while True:
        degree = {}
        for a, b, _ in edges:
            for n in (a, b):
                if n is not None:
                    degree[n] = degree.get(n, 0) + 1
        ends = [[1 if n is None else degree[n] for n in e[:2]] for e in edges]  # no node: a free end
        short = [e for e, d in zip(edges, ends) if length(e[2]) < spur and e[0] != e[1] and
                 min(d) == 1 and max(d) >= 3]
        if not short:
            break
        edges.remove(min(short, key=lambda e: length(e[2])))
    while True:
        degree = {}
        for i, (a, b, _) in enumerate(edges):
            for n in (a, b):
                if n is not None:
                    degree.setdefault(n, []).append(i)
        joint = next((n for n, at in degree.items() if len(at) == 2 and at[0] != at[1]), None)
        if joint is None:
            return [pts for _, _, pts in edges]
        i, j = degree[joint]
        (a, b, p), (c, d, q) = edges[i], edges[j]
        if b != joint:
            a, b, p = b, a, p[::-1]
        if c != joint:
            c, d, q = d, c, q[::-1]
        edges = [e for k, e in enumerate(edges) if k not in (i, j)] + [[a, d, p + q[1:]]]


def simplify(pts, tol):
    """Ramer-Douglas-Peucker."""
    if len(pts) < 3:
        return pts
    (y0, x0), (y1, x1) = pts[0], pts[-1]
    dy, dx = y1 - y0, x1 - x0
    norm = np.hypot(dy, dx)
    if norm == 0:
        dists = [np.hypot(p[0] - y0, p[1] - x0) for p in pts]
    else:
        dists = [abs(dx * (p[0] - y0) - dy * (p[1] - x0)) / norm for p in pts]
    k = int(np.argmax(dists))
    if dists[k] <= tol:
        return [pts[0], pts[-1]]
    return simplify(pts[:k + 1], tol)[:-1] + simplify(pts[k:], tol)


def runs(line):
    """Lengths of the runs of set pixels along a boolean line."""
    edges = np.flatnonzero(np.diff(np.concatenate(([0], line.astype(np.int8), [0]))))
    return list(edges[1::2] - edges[0::2])


def pen_width(font):
    """The font's stem width in pixels: vertical stems of l and I, bars of - and =."""
    widths = []
    for ch, vertical in (('l', True), ('I', True), ('-', False), ('=', False)):
        img, _ = raster(font, ch)
        ys, xs = np.nonzero(img)
        if vertical:
            widths += runs(img[(ys.min() + ys.max()) // 2])
        else:
            widths += runs(img[:, (xs.min() + xs.max()) // 2])
    return float(np.median(widths))


def strokes(font, ch, pen):
    """The centreline strokes of ch, in em units from the cell's origin, y up.
    A combining mark is drawn over a space: alone, the font sets it on a dotted circle."""
    img, (ox, oy) = raster(font, ' ' + ch if unicodedata.combining(ch) else ch)
    if not img.any():
        return []
    ys, xs = np.nonzero(img)
    y0, x0 = max(ys.min() - 2, 0), max(xs.min() - 2, 0)
    sk = np.zeros_like(img)
    sk[y0:ys.max() + 3, x0:xs.max() + 3] = thin(img[y0:ys.max() + 3, x0:xs.max() + 3])
    centres, edges = trace(sk)
    lines = prune(centres, edges, SPUR * pen)
    lone = [c for i, c in enumerate(centres) if not any(i in e[:2] for e in edges)]
    out = [simplify(p, TOLERANCE) for p in lines] + [[c] for c in lone]
    out = [dot(img, sk, s, pen) if length(s) < pen else s for s in out]
    return [[[round((x - ox) / EM, 4), round((oy - y) / EM, 4)] for y, x in s] for s in out]


def dot(img, sk, stroke, pen):
    """A dot as wide as the font draws it. Its skeleton is a point, but a font's
    dots are wider than its stems: one stroke from the centre out to the rim
    and once around it fills the whole disc. A short stroke is a dot only if
    its ink is small and holds no more skeleton than a dot's own few pixels;
    otherwise it is a short piece of a bigger shape (between the junctions of
    # or *, at the crossing of x)."""
    start = tuple(int(round(v)) for v in stroke[0])
    if not img[start]:
        return stroke
    blob, stack, most = {start}, [start], (4 * pen) ** 2
    while stack:  # the dot's ink: the pixels connected to its skeleton
        y, x = stack.pop()
        for dy, dx in RING:
            q = (y + dy, x + dx)
            if q not in blob and img[q]:
                blob.add(q)
                stack.append(q)
        if len(blob) > most:
            return stroke
    if sum(1 for p in blob if sk[p]) > pen:
        return stroke
    cy, cx = np.mean([p[0] for p in blob]), np.mean([p[1] for p in blob])
    rim = np.sqrt(len(blob) / np.pi) - pen / 2  # where the pen's centre runs
    if rim <= pen / 4:
        return stroke
    turn = [(cy + rim * np.sin(a), cx + rim * np.cos(a)) for a in np.linspace(0, 2 * np.pi, 17)]
    return [(cy, cx)] + turn


def coverage(font, ch, strokes_, pen):
    """The share of ch's ink that its strokes, drawn with the pen, cover."""
    ink, (ox, oy) = raster(font, ' ' + ch if unicodedata.combining(ch) else ch)
    img = Image.new('L', (ink.shape[1], ink.shape[0]), 0)
    draw = ImageDraw.Draw(img)
    for s in strokes_:
        pts = [(ox + x * EM, oy - y * EM) for x, y in s]
        if len(pts) > 1:
            draw.line(pts, fill=255, width=round(pen), joint='curve')
        for x, y in pts:
            draw.ellipse([x - pen / 2, y - pen / 2, x + pen / 2, y + pen / 2], fill=255)
    drawn = np.array(img) >= 128
    return (ink & drawn).sum() / ink.sum() if ink.any() else 1.0


def sheet(path, font_path, data, scale=96, cols=16):
    """Every glyph: the font's rendering in grey, the pen strokes over it in red,
    the centrelines in blue. A character the font lacks has no rendering to
    show (only the font's missing-glyph box): its strokes stand alone."""
    mapped = cmap(font_path)
    glyphs = sorted(data['glyphs'].items(), key=lambda kv: ord(kv[0]))
    box_w, box_h = int(scale * 1.6), int(scale * 1.9)
    img = Image.new('RGB', (cols * box_w, -(-len(glyphs) // cols) * box_h), 'white')
    draw = ImageDraw.Draw(img, 'RGBA')
    big = ImageFont.truetype(font_path, scale)
    small = ImageFont.truetype(font_path, 14)
    pen = data['pen'] * scale
    for i, (ch, strokes_) in enumerate(glyphs):
        bx, by = (i % cols) * box_w, (i // cols) * box_h
        ox, oy = bx + int(scale * 0.4), by + int(scale * 1.35)
        cw = data['cell']['width'] * scale
        draw.rectangle([ox, oy - data['cell']['ascent'] * scale, ox + cw, oy + data['cell']['descent'] * scale],
                       outline=(225, 225, 225))
        if ord(ch) in mapped:
            base = '◌' + ch if unicodedata.combining(ch) else ch  # a mark over a dotted circle
            draw.text((ox, oy), base, font=big, fill=(200, 200, 200), anchor='ls')
        for s in strokes_:
            pts = [(ox + x * scale, oy - y * scale) for x, y in s]
            if len(pts) > 1:
                draw.line(pts, fill=(220, 40, 40, 110), width=max(1, round(pen)), joint='curve')
            for x, y in (pts[0], pts[-1]):
                draw.ellipse([x - pen / 2, y - pen / 2, x + pen / 2, y + pen / 2], fill=(220, 40, 40, 110))
            if len(pts) > 1:
                draw.line(pts, fill=(20, 40, 160), width=1)
        draw.text((bx + 4, by + 4), 'U+%04X %d' % (ord(ch), len(strokes_)), font=small, fill=(90, 90, 90))
    img.save(path)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('--font', default=FONT)
    ap.add_argument('--overrides', default=os.path.join(HERE, 'glyph-overrides.json'))
    ap.add_argument('--out', default=os.path.join(HERE, 'glyphs.json'))
    ap.add_argument('--sheet')
    ap.add_argument('specs', nargs='*')
    args = ap.parse_args()

    chars = {chr(c) for c in range(0x20, 0x7F)}
    for path in args.specs or sorted(glob.glob(os.path.join(ROOT, 'docs', '*.nspec'))):
        chars |= {c for c in open(path, encoding='utf-8').read() if c not in '\n\r'}
    overrides = json.load(open(args.overrides, encoding='utf-8')) if os.path.exists(args.overrides) else {}
    mapped = cmap(args.font)
    font = ImageFont.truetype(args.font, EM)
    ascent, descent = font.getmetrics()
    cell = font.getlength('M') / EM
    pen = pen_width(font)

    glyphs, missing, thin_ = {}, [], []
    for ch in sorted(chars, key=ord):
        if ch in overrides:
            glyphs[ch] = overrides[ch]
        elif ord(ch) in mapped:
            glyphs[ch] = strokes(font, ch, pen)
            share = coverage(font, ch, glyphs[ch], pen)
            if share < COVER:
                thin_.append((share, ch))
        else:
            missing.append(ch)
    data = {'font': font.getname()[0], 'units': 'em', 'y': 'up',
            'cell': {'width': round(cell, 4), 'ascent': round(ascent / EM, 4), 'descent': round(descent / EM, 4)},
            'pen': round(pen / EM, 4), 'glyphs': glyphs}

    with open(args.out, 'w', encoding='utf-8') as f:  # one glyph per line, for readable diffs
        head = {k: v for k, v in data.items() if k != 'glyphs'}
        f.write(json.dumps(head, ensure_ascii=False)[:-1] + ', "glyphs": {\n')
        f.write(',\n'.join('  %s: %s' % (json.dumps(ch, ensure_ascii=False), json.dumps(s, separators=(',', ':')))
                           for ch, s in glyphs.items()))
        f.write('\n}}\n')
    if args.sheet:
        sheet(args.sheet, args.font, data)
    print('%d glyphs, pen %.4f em, cell %.4f em -> %s' % (len(glyphs), data['pen'], data['cell']['width'], args.out))
    if thin_:
        print('strokes cover too little of the font\'s ink (check the sheet; override if bad): ' +
              ' '.join('%s U+%04X %.0f%%' % (c, ord(c), 100 * s) for s, c in sorted(thin_)))
    if missing:
        print('missing from the font, with no override: ' + ' '.join('%s U+%04X' % (c, ord(c)) for c in missing),
              file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
