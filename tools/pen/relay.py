#!/usr/bin/env python3
"""The pen editor's relay: the Mac side of the iPad pen editor.

It serves one spec file to the iPad, applies the iPad's edits to it, turns
handwritten edits into text with `claude -p` (the user's Claude login), and
checks every candidate with the spec checker before offering it.

  GET  /file       {"text", "version"}; a version is the SHA-256 of the file
  POST /edit       {"base", "replacements": [{"first", "last", "lines"}]}
                   -> {"version"}, or 409 {"version"} if the file is not at base
  POST /recognise  {"base", "requests": [{"spans": [{"first", "last", "image"}]}]}
                   -> {"results": [{"chosen", "candidates", ...}]}, or 409
  GET  /events     a WebSocket: {"version"} now, and whenever the file changes

Lines are numbered from 1; a replacement swaps lines first..last (inclusive)
for `lines`, and first = last + 1 inserts. A span's image is a base64 PNG:
the original text in grey, erasures in red, new ink in blue. All spans of
one request belong to one rule and are read together; recognition never
writes the file (the iPad applies a result through /edit).

A candidate is accepted if, put in place, it adds no checker finding the
file did not already have (compared by message and line text, as line
numbers shift) and uses only characters the specs use. If none is
accepted, Claude is asked once more with the checker's messages.

It listens on localhost; `tailscale serve --bg 8765` publishes it to the
tailnet over HTTPS. Every recognition is logged (request, images,
candidates, choice) under --log.

Usage: relay.py FILE [--port 8765] [--model MODEL] [--log DIR]
"""
import argparse
import asyncio
import base64
import collections
import glob
import hashlib
import json
import os
import shutil
import tempfile
import time
import unicodedata

from aiohttp import WSMsgType, web

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..'))
FOUNDATION = os.path.join(ROOT, 'docs', 'NovaFoundation.nspec')
CONTEXT = 6  # lines of context on each side of a request's spans
CANDIDATES = 5
# Characters a reader of handwriting returns for the spec's own.
LOOKALIKES = {'⊢': '⊦', '□': '☐', '○': '∘', '−': '-', '‐': '-', '≑': '≐'}

SCHEMA = json.dumps({
    'type': 'object',
    'properties': {'candidates': {
        'type': 'array', 'maxItems': CANDIDATES,
        'items': {'type': 'array', 'items': {'type': 'string'}}}},
    'required': ['candidates']})


# The file -------------------------------------------------------------------

def load(path):
    """The file's lines, whether it ends in a newline, and its version."""
    data = open(path, 'rb').read()
    text = data.decode('utf-8')
    final = text.endswith('\n')
    return (text[:-1] if final else text).split('\n'), final, hashlib.sha256(data).hexdigest()


def store(path, lines, final):
    data = ('\n'.join(lines) + ('\n' if final else '')).encode('utf-8')
    tmp = path + '.pen-tmp'
    with open(tmp, 'wb') as f:
        f.write(data)
    os.replace(tmp, path)
    return hashlib.sha256(data).hexdigest()


def apply(lines, replacements):
    """lines with each replacement made; they must not overlap."""
    out, last_first = list(lines), None
    for r in sorted(replacements, key=lambda r: r['first'], reverse=True):
        first, last = r['first'], r['last']
        if not (1 <= first <= last + 1 <= len(out) + 1) or (last_first is not None and last >= last_first):
            raise ValueError('bad or overlapping replacement %d..%d' % (first, last))
        out[first - 1:last] = r['lines']
        last_first = first
    return out


# The checker ----------------------------------------------------------------

class Checker:
    """tools/pen/check.lua kept running: the grammar is built once, and each
    later check re-judges only the lines it has not seen."""

    def __init__(self):
        self.proc, self.lock = None, asyncio.Lock()

    async def findings(self, path, lines):
        async with self.lock:
            if self.proc is None or self.proc.returncode is not None:
                self.proc = await asyncio.create_subprocess_exec(
                    'luajit', os.path.join(HERE, 'check.lua'),
                    stdin=asyncio.subprocess.PIPE, stdout=asyncio.subprocess.PIPE)
            body = '%s\t%d\n' % (path, len(lines)) + ''.join(line + '\n' for line in lines)
            self.proc.stdin.write(body.encode('utf-8'))
            await self.proc.stdin.drain()
            out = []
            for _ in range(int(await self.proc.stdout.readline())):
                n, col, message = (await self.proc.stdout.readline()).decode('utf-8').rstrip('\n').split('\t', 2)
                out.append((int(n), int(col), message))
            return out


def by_content(findings, lines):
    """Findings as (message, line text): what survives a shift of line numbers."""
    return collections.Counter((m, lines[n - 1] if 0 < n <= len(lines) else '') for n, _, m in findings)


# What Claude is told --------------------------------------------------------

def inventory():
    """Every character the specs use, and printable ASCII."""
    chars = {chr(c) for c in range(0x20, 0x7F)}
    for path in glob.glob(os.path.join(ROOT, 'docs', '*.nspec')):
        chars |= set(open(path, encoding='utf-8').read()) - {'\n', '\r'}
    return chars


def normalise(text, known):
    """Look-alikes replaced, and each mark composed onto its base exactly when
    the specs write that pair precomposed (they write ē, but l̄)."""
    out = []
    for c in unicodedata.normalize('NFD', ''.join(LOOKALIKES.get(c, c) for c in text)):
        if out and unicodedata.combining(c):
            pair = unicodedata.normalize('NFC', out[-1] + c)
            if len(pair) == 1 and pair in known:
                out[-1] = pair
                continue
        out.append(c)
    return ''.join(out)


def system_prompt(path, known):
    """The static part of every request: the same for every call, so cached."""
    sources = [FOUNDATION] + ([path] if os.path.abspath(path) != FOUNDATION else [])
    grammar, rules = [], []
    for source in sources:
        lines = open(source, encoding='utf-8').read().split('\n')
        for i, line in enumerate(lines):
            if ('::=' in line or ' |= ' in line) and not line.startswith('//'):
                grammar.append(line)
                grammar.extend(l for l in lines[i + 1:i + 8] if l.lstrip().startswith('|'))
            if line.startswith('---') and len(rules) < 16:
                a = i
                while a > 0 and lines[a - 1].strip() and not lines[a - 1].startswith('//'):
                    a -= 1
                b = i + 1
                while b < len(lines) and lines[b].strip() and not lines[b].startswith('//'):
                    b += 1
                rules.append('\n'.join(lines[a:b]))
    symbols = '\n'.join('%s U+%04X %s' % (c, ord(c), unicodedata.name(c, '?'))
                        for c in sorted(known, key=ord) if ord(c) > 0x7F)
    return '\n\n'.join([
        'You transcribe handwritten edits to lines of a formal specification written in the '
        '.nspec format. Each image shows the original text drawn in grey; red marks what the '
        'writer erased, blue is what they wrote. You are also given the original text exactly. '
        'Apply the edit: keep every character the writer did not touch, and write what they '
        'wrote in the characters the specification uses. Keep spacing and indentation as in the '
        'original unless the writer changed it: judgements on one line are three spaces apart, '
        'and an indented line continues the one above. Answer only through the structured '
        'output: up to %d candidates, most likely first.' % CANDIDATES,
        'THE GRAMMAR (productions `category ::= alternative | ...`):\n' + '\n'.join(grammar),
        'EXAMPLE RULES (premises, a bar with the rule name, the conclusion):\n' + '\n\n'.join(rules),
        'THE ONLY CHARACTERS THE SPECIFICATION USES besides ASCII:\n' + symbols])


def user_prompt(path, lines, spans, notes):
    a = max(1, min(s['first'] for s in spans) - CONTEXT)
    b = min(len(lines), max(s['last'] for s in spans) + CONTEXT)
    parts = ['The file is %s. Lines %d-%d, for context (the numbers are not part of the text):' %
             (os.path.basename(path), a, b),
             '\n'.join('%5d| %s' % (n, lines[n - 1]) for n in range(a, b + 1))]
    for k, s in enumerate(spans, 1):
        original = lines[s['first'] - 1:s['last']]
        parts.append('Span %d: lines %d-%d, image span%d.png. Its original text, between the markers:\n'
                     '<<<\n%s\n>>>' % (k, s['first'], s['last'], k, '\n'.join(original)))
    parts.append('Read every span image. Each candidate is a list with one string per span, in order: '
                 'the span\'s new text, its lines joined by newlines.')
    if notes:
        parts.append('Earlier candidates were rejected by the checker:\n' + notes)
    return '\n\n'.join(parts)


# Recognition ----------------------------------------------------------------

async def ask(cfg, system, prompt, images):
    """One `claude -p` call in a fresh empty directory; the candidates, and what it took."""
    work = tempfile.mkdtemp(prefix='pen-')
    try:
        for k, png in enumerate(images, 1):
            with open(os.path.join(work, 'span%d.png' % k), 'wb') as f:
                f.write(png)
        args = ['claude', '-p', prompt, '--system-prompt', system, '--tools', 'Read',
                '--allowedTools', 'Read', '--json-schema', SCHEMA, '--output-format', 'json',
                '--no-session-persistence', '--strict-mcp-config']
        if cfg.model:
            args += ['--model', cfg.model]
        proc = await asyncio.create_subprocess_exec(*args, cwd=work, stdout=asyncio.subprocess.PIPE,
                                                    stderr=asyncio.subprocess.PIPE)
        out, err = await asyncio.wait_for(proc.communicate(), timeout=cfg.timeout)
        reply = json.loads(out or b'{}')
        if reply.get('is_error') or 'structured_output' not in reply:
            raise RuntimeError(reply.get('result') or err.decode('utf-8', 'replace')[-500:] or 'no answer')
        cost = {k: reply.get(k) for k in ('duration_ms', 'num_turns', 'total_cost_usd', 'usage')}
        return reply['structured_output'].get('candidates', []), cost
    finally:
        shutil.rmtree(work, ignore_errors=True)


async def judge(cfg, lines, baseline, spans, candidate):
    """A candidate in place: does it fit? (No new finding, no foreign character.)"""
    texts = [normalise(t, cfg.known) for t in candidate]
    new_lines = [[l.rstrip() for l in t.split('\n')] for t in texts]
    foreign = sorted({c for t in texts for c in t if c not in cfg.known and c != '\n'})
    edited = apply(lines, [{'first': s['first'], 'last': s['last'], 'lines': nl} for s, nl in zip(spans, new_lines)])
    found = await cfg.checker.findings(cfg.path, edited)
    new = by_content(found, edited) - baseline
    return {'spans': new_lines, 'fits': not new and not foreign,
            'new_findings': [m + ': ' + t for m, t in new.elements()], 'foreign': foreign}


async def recognise_one(cfg, lines, baseline, request):
    spans = request['spans']
    images = [base64.b64decode(s['image']) for s in spans]
    system = cfg.system
    started, judged, costs, notes = time.time(), [], [], ''
    for _ in range(2):  # a second try, told why the first candidates failed
        candidates, cost = await ask(cfg, system, user_prompt(cfg.path, lines, spans, notes), images)
        costs.append(cost)
        for c in candidates:
            if isinstance(c, list) and len(c) == len(spans) and all(isinstance(t, str) for t in c):
                judged.append(await judge(cfg, lines, baseline, spans, c))
        if any(j['fits'] for j in judged):
            break
        notes = '\n'.join('%s -> %s' % (json.dumps(j['spans'], ensure_ascii=False),
                                        '; '.join(j['new_findings'] + ['foreign: ' + ''.join(j['foreign'])] * bool(j['foreign'])))
                          for j in judged[-CANDIDATES:])
    chosen = next((i for i, j in enumerate(judged) if j['fits']), None)
    return {'chosen': chosen, 'candidates': judged, 'seconds': round(time.time() - started, 2), 'calls': costs}


def log(cfg, entry, requests):
    stamp = time.strftime('%Y%m%d-%H%M%S') + '-%03d' % (int(time.time() * 1000) % 1000)
    os.makedirs(cfg.log, exist_ok=True)
    for i, request in enumerate(requests):
        for k, s in enumerate(request['spans'], 1):
            with open(os.path.join(cfg.log, '%s-r%d-s%d.png' % (stamp, i, k)), 'wb') as f:
                f.write(base64.b64decode(s['image']))
    entry = dict(entry, stamp=stamp, file=cfg.path)
    with open(os.path.join(cfg.log, 'recognitions.jsonl'), 'a', encoding='utf-8') as f:
        f.write(json.dumps(entry, ensure_ascii=False) + '\n')


# HTTP -----------------------------------------------------------------------

async def get_file(request):
    cfg = request.app['cfg']
    lines, final, version = load(cfg.path)
    return web.json_response({'text': '\n'.join(lines) + ('\n' if final else ''), 'version': version})


async def post_edit(request):
    cfg = request.app['cfg']
    body = await request.json()
    async with cfg.write_lock:
        lines, final, version = load(cfg.path)
        if body.get('base') != version:
            return web.json_response({'version': version}, status=409)
        try:
            edited = apply(lines, body['replacements'])
        except (ValueError, KeyError, TypeError) as e:
            return web.json_response({'error': str(e)}, status=400)
        return web.json_response({'version': store(cfg.path, edited, final)})


async def post_recognise(request):
    cfg = request.app['cfg']
    body = await request.json()
    lines, _, version = load(cfg.path)
    if body.get('base') != version:
        return web.json_response({'version': version}, status=409)
    if version not in cfg.baselines:
        cfg.baselines = {version: by_content(await cfg.checker.findings(cfg.path, lines), lines)}
    baseline = cfg.baselines[version]
    results = await asyncio.gather(*(recognise_one(cfg, lines, baseline, r) for r in body['requests']),
                                   return_exceptions=True)
    results = [{'error': str(r)} if isinstance(r, BaseException) else r for r in results]
    log(cfg, {'base': version, 'spans': [[{k: s[k] for k in ('first', 'last')} for s in r['spans']]
                                         for r in body['requests']], 'results': results}, body['requests'])
    return web.json_response({'results': results})


async def events(request):
    cfg = request.app['cfg']
    ws = web.WebSocketResponse(heartbeat=30)
    await ws.prepare(request)
    cfg.sockets.add(ws)
    try:
        await ws.send_json({'version': load(cfg.path)[2]})
        async for msg in ws:  # nothing is expected from the iPad; wait for it to go
            if msg.type == WSMsgType.ERROR:
                break
    finally:
        cfg.sockets.discard(ws)
    return ws


async def watch(cfg):
    """Tell every connected iPad when the file's version changes."""
    seen, version = None, load(cfg.path)[2]
    while True:
        await asyncio.sleep(0.5)
        try:
            st = os.stat(cfg.path)
        except FileNotFoundError:
            continue
        if (st.st_mtime_ns, st.st_size) == seen:
            continue
        seen = (st.st_mtime_ns, st.st_size)
        now = load(cfg.path)[2]
        if now != version:
            version = now
            for ws in list(cfg.sockets):
                await ws.send_json({'version': version})


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('file')
    ap.add_argument('--port', type=int, default=8765)
    ap.add_argument('--model', help='a model for claude -p (default: its own)')
    ap.add_argument('--timeout', type=float, default=180, help='seconds a claude -p call may take')
    ap.add_argument('--log', default=os.path.expanduser('~/.local/state/nova-pen'))
    cfg = ap.parse_args()
    cfg.path = os.path.abspath(cfg.file)
    cfg.known = inventory() | set(open(cfg.path, encoding='utf-8').read()) - {'\n', '\r'}
    cfg.system = system_prompt(cfg.path, cfg.known)
    cfg.checker, cfg.write_lock, cfg.sockets, cfg.baselines = Checker(), asyncio.Lock(), set(), {}

    app = web.Application(client_max_size=64 * 1024 * 1024)
    app['cfg'] = cfg
    app.router.add_get('/file', get_file)
    app.router.add_post('/edit', post_edit)
    app.router.add_post('/recognise', post_recognise)
    app.router.add_get('/events', events)

    async def start(app):
        app['watch'] = asyncio.create_task(watch(cfg))
        lines = load(cfg.path)[0]  # build the checker's grammar now, not on the first recognition
        await cfg.checker.findings(cfg.path, lines)

    app.on_startup.append(start)
    print('relay for %s on http://127.0.0.1:%d (system prompt %d chars)' % (cfg.path, cfg.port, len(cfg.system)),
          flush=True)
    web.run_app(app, host='127.0.0.1', port=cfg.port, print=None)


if __name__ == '__main__':
    main()
