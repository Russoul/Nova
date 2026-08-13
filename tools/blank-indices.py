#!/usr/bin/env python3
"""Greedily replace inferable INDEX arguments with `_`, keeping only
changes that leave the file `Accepted.`  Bisects on failure."""
import subprocess, sys, re

# head name -> zero-based argument positions that are indices (blankable)
TABLE = {
    "trans": [0, 1, 2, 3], "sym": [0, 1, 2], "refl": [0, 1],
    "cong": [0, 1, 3, 4], "transportP": [0, 2, 3], "transport": [0, 2, 3],
    "mulCongL": [0, 1, 2], "mulCongR": [0, 1, 2],
    "addCongL": [0, 1, 2], "addCongR": [0, 1, 2],
    "plusCongL": [0, 1, 2], "plusCongR": [0, 1, 2],
    "intAddCong2": [0, 1, 2, 3], "intMulCong2": [0, 1, 2, 3],
    "classCong2": [0, 1, 2, 3], "pairEq2": [0, 1, 2, 3],
    "clsEqOfRel": [0, 1], "pairEtaG": [0, 1], "pairEta": [0, 1],
    "notIntro": [0], "notApply": [0], "absurdP": [0],
    "intNeqOfNotRel": [0, 1], "intMulCancel": [0, 1, 2],
    "intNoZeroDiv": [0, 1], "intEffective": [0, 1],
    "zNotS": [0], "predEq": [0, 1], "sucInj": [0, 1],
    "invTrans": [0, 1, 2, 3], "invSym": [0, 1, 2], "invEtaR": [0],
    "qInvUniqueVal": [0, 1, 2], "invPairCong": [0, 1, 2],
    "iffIntro": [0, 1], "andIntro": [0, 1], "andFst": [0, 1], "andSnd": [0, 1],
    "impIntro": [0, 1], "impApply": [0, 1], "eqNComplete": [0, 1],
    "eqNSound": [0, 1], "classPairEta": [], "intCanonProdZero": [],
    "crossAddWD": [0, 1, 2, 3, 4, 5], "crossAssocNum": [0, 1, 2, 3, 4, 5],
    "assocRep": [0, 1, 2, 3, 4, 5], "sum4Distrib": [0, 1, 2, 3, 4, 5],
    "sum4DistribR": [0, 1, 2, 3, 4, 5], "collectL": [0, 1, 2, 3, 4],
    "distribBack": [0, 1, 2], "distribBackR": [0, 1, 2],
    "swap4": [0, 1, 2, 3], "swap4b": [0, 1, 2, 3],
    "mulSwapHead": [0, 1, 2], "mulSwapInner": [0, 1, 2],
    "mulSwapOuter": [0, 1, 2, 3], "mulHoist": [0, 1, 2, 3],
    "mulShiftL": [0, 1, 2], "mulSwapRight": [0, 1, 2],
    "magAssoc": [0, 1, 2], "sucMulSuc": [0, 1], "mulComm2": [0, 1, 2, 3],
    "plusSwapRight": [0, 1, 2], "mulPlusComm": [0, 1],
    "intMulWD": [0, 1, 2, 3, 4, 5], "intMulWDRep": [0, 1, 2, 3, 4, 5],
    "ratAddNumMul": [0, 1], "ratAddDenMul": [0, 1],
    "nzToIntMul": [0, 1], "intScaleIsMul": [0, 1],
    "normProdZero": [0, 1], "nzOfPairD": [0, 1], "nzOfPair": [0, 1],
    "intMulDistribL": [0, 1, 2], "intMulDistribR": [0, 1, 2],
    "intMulAssoc": [0, 1, 2], "intMulComm": [0, 1],
    "intAddAssoc": [0, 1, 2], "intAddComm": [0, 1],
    "intMulOneL": [0], "intMulOneR": [0], "intMulZeroL": [0], "intMulZeroR": [0],
    "intAddZeroL": [0], "intAddZeroR": [0], "intAddNegL": [0], "intAddNegR": [0],
    "intMulNegL": [0, 1], "intMulNegR": [0, 1], "intNegNeg": [0],
    "multAssoc": [0, 1, 2], "multComm": [0, 1], "plusComm": [0, 1],
    "multSucId": [0, 1], "sucPlus": [0, 1], "zeroPlusId": [0], "plusZeroId": [0],
    "nzMulOneL": [0], "nzMulOneR": [0], "nzMulComm": [0, 1], "nzMulAssoc": [0, 1, 2],
    "ratEta": [0], "ratAddComm": [0, 1], "ratAddZeroL": [0], "ratAddZeroR": [0],
    "ratMulComm": [0, 1], "ratMulAssoc": [0, 1, 2], "ratMulOneR": [0],
    "ratAddAssocNum": [0, 1, 2], "ratAddAssocDen": [0, 1, 2],
    "ratAddNumMulL": [0, 1, 2], "ratAddNumMulR": [0, 1, 2],
    "intCanonClass": [0], "nzToIntNonZero": [0], "numNonZero": [0],
    "ratZeroOfNumZero": [0], "numZeroOfRatZero": [0], "qOfNzqNonZero": [0],
    "qMulInv": [0], "qMulZeroL": [0], "qMulOneL": [0], "qMulOneR": [0],
    "qMulComm": [0, 1], "qMulAssoc": [0, 1, 2], "qAddComm": [0, 1],
    "intScaleOne": [0], "intScaleZero": [0], "intAddScaleZeroL": [0, 1],
    "intAddScaleZeroR": [0, 1], "intScaleNOne": [0], "intScaleNSuc": [0, 1],
    "qEffective": [0, 1], "qNonZeroIsNzq": [0], "qInvExists": [0],
    "intNZViewAt": [0, 1], "nzOfIntAt": [0, 1], "invRepAt": [0],
    "qInvIsPropAt": [0, 1, 2], "invRepWDAt": [0, 1],
}

IDENT = re.compile(r"[A-Za-z][A-Za-z0-9']*")

def atoms_after(s, i, n):
    """read up to n atoms starting at index i; return list of (start,end)."""
    out = []
    while len(out) < n:
        while i < len(s) and s[i] in " \n":
            i += 1
        if i >= len(s):
            break
        if s[i] == "(":
            d, j = 0, i
            while j < len(s):
                if s[j] == "(":
                    d += 1
                elif s[j] == ")":
                    d -= 1
                    if d == 0:
                        j += 1
                        break
                j += 1
            out.append((i, j)); i = j
        elif s[i] in ")," or s[i] == "." :
            break
        else:
            j = i
            while j < len(s) and s[j] not in " \n(),":
                j += 1
            # absorb trailing projections written with a space: `p .π₁`
            k = j
            while True:
                m = k
                while m < len(s) and s[m] == " ":
                    m += 1
                if s.startswith(".π", m):
                    k = m + 3
                    while k < len(s) and s[k] not in " \n(),":
                        k += 1
                else:
                    break
            out.append((i, k)); i = k
    return out

def mask_comments(text):
    """replace every comment character with a space, preserving offsets"""
    out = list(text)
    i = 0
    while True:
        j = text.find("--", i)
        if j == -1:
            break
        k = text.find("\n", j)
        if k == -1:
            k = len(text)
        for m in range(j, k):
            out[m] = " "
        i = k
    return "".join(out)

def candidates(raw):
    """spans of index arguments inside def BODIES only (comments masked)"""
    text = mask_comments(raw)
    bodies = []
    for m in re.finditer(r"(?m)^def ", text):
        start = m.start()
        nxt = text.find("\ndef ", start + 1)
        nxt2 = text.find("\ntype ", start + 1)
        end = min(x for x in [nxt, nxt2, len(text)] if x != -1)
        seg = text[start:end]
        d = 0
        for i, ch in enumerate(seg):
            if ch == "(":
                d += 1
            elif ch == ")":
                d -= 1
            elif ch == "≔" and d == 0:
                bodies.append((start + i + 1, end))
                break
    spans = []
    groups = []
    for b0, b1 in bodies:
        body = text[b0:b1]
        for m in IDENT.finditer(body):
            name = m.group(0)
            if name not in TABLE:
                continue
            if m.start() > 0 and body[m.start() - 1] in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789'.":
                continue
            positions = TABLE[name]
            if not positions:
                continue
            got = atoms_after(body, m.end(), max(positions) + 1)
            for p in positions:
                if p < len(got):
                    s0, s1 = got[p]
                    frag = body[s0:s1]
                    if frag == "_" or frag.startswith("λ"):
                        continue
                    spans.append((b0 + s0, b0 + s1))
    # de-duplicate / drop nested spans (keep outermost)
    spans.sort()
    out = []
    for s0, s1 in spans:
        if out and s0 < out[-1][1]:
            continue
        out.append((s0, s1))
    return out, bodies

def apply(text, spans, chosen):
    parts, prev = [], 0
    for idx, (s0, s1) in enumerate(spans):
        if idx not in chosen:
            continue
        parts.append(text[prev:s0]); parts.append("_"); prev = s1
    parts.append(text[prev:])
    return "".join(parts)

def ok(path, content):
    open(path, "w").write(content)
    r = subprocess.run(["build/exec/nova", "elab", path], capture_output=True, text=True)
    return r.stdout.rstrip().endswith("Accepted.")

def main(path):
    orig = open(path).read()
    spans, bodies = candidates(orig)
    print(f"{path}: {len(spans)} candidates", flush=True)
    accepted = set()
    def attempt(idxs):
        return ok(path, apply(orig, spans, accepted | set(idxs)))
    def rec(idxs):
        if not idxs:
            return
        if attempt(idxs):
            accepted.update(idxs)
            print(f"  +{len(idxs)}", flush=True)
            return
        if len(idxs) == 1:
            return
        mid = len(idxs) // 2
        rec(idxs[:mid]); rec(idxs[mid:])
    # per-def groups: a failure in one def never forces re-probing another
    groups = []
    for b0, b1 in bodies:
        g = [i for i, (s0, _) in enumerate(spans) if b0 <= s0 < b1]
        if g:
            groups.append(g)
    if attempt(list(range(len(spans)))):
        accepted.update(range(len(spans)))
        print("  all at once", flush=True)
    else:
        for g in groups:
            rec(g)
    final = apply(orig, spans, accepted)
    cmts = lambda t: [l for l in t.split("\n") if l.lstrip().startswith("--")]
    assert cmts(final) == cmts(orig), "comment text changed!"
    open(path, "w").write(final)
    print(f"{path}: blanked {len(accepted)}/{len(spans)}", flush=True)
    return sorted(set(range(len(spans))) - accepted), spans, orig

if __name__ == "__main__":
    rest, spans, orig = main(sys.argv[1])
    for i in rest:
        s0, s1 = spans[i]
        line = orig[:s0].count("\n") + 1
        print(f"  kept L{line}: {orig[s0:s1][:60]}")
