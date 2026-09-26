#!/usr/bin/env python3
"""The mechanical half of the roles audit (docs/NovaStrategy.txt, "The
audit"): what the author–engine–kernel division says about the tree
that can be read off the tree.

  K1  the kernel closure: kernel modules import only each other and
      the base libraries
  K2  no escape hatches in the kernel (believe_me, assert_total, …,
      no environment or clock reads); an assert_total that wraps a
      deliberate crash is allowed — it fabricates nothing
  K3  no backtracking in the kernel: no kOrElse / <|>; every kCatch
      re-raises
  K4  the kernel's exported kCheck* functions are exactly the entry
      points, and the Σ-extending ones return the entry they admit
  S1  Σ owned by construction: the entry constructors are private to
      the kernel; the engine keeps ONE signature; the admitting entry
      points are called inside kernelAccept only, whose admitted entry
      is what the mirror sites extend Σ with (S2 — no engine-built
      entry passes for an admitted one — is the type checker's)
  E1  every engine site that extends Σ is the mirror of an admission
      or an assumption site (obligation, hole, written declaration)
  E2  no kernel module imports an engine module (the dual of K1)

Exit status 1 on any failure. Run as ./check-roles.sh.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "src" / "idris" / "Nova"

KERNEL_MODULES = {
    "Nova.Kernel": SRC / "Kernel.idr",
    "Nova.Kernel.Syntax": SRC / "Kernel" / "Syntax.idr",
    "Nova.Kernel.Subst": SRC / "Kernel" / "Subst.idr",
    "Nova.Kernel.QIIT": SRC / "Kernel" / "QIIT.idr",
    "Nova.Kernel.Derivation": SRC / "Kernel" / "Derivation.idr",
}
# imports a kernel module may have besides the kernel modules
ALLOWED_IMPORT_PREFIXES = ("Data.", "Control.", "Prelude", "Decidable.")
ALLOWED_IMPORTS = set()  # nothing outside the kernel and the base libraries

# K2: escape hatches and effects
ESCAPES = ["believe_me", "assert_total", "assert_smaller", "unsafePerformIO",
           "%foreign", "prim__", "getEnv", "nowNs", "bump ", "timed "]

# K3: functions allowed to catch without re-raising — none
AUDIT_FUNCTIONS = set()

# K4: the entry points, by name, and which of them admit an entry
# admit: returns the entry Σ is extended with, called on ksig inside
# kernelAccept only; assume: returns an entry marked assumed, called
# inside the two counting helpers only; check: a verdict
ENTRY_POINTS = {"kCheckDefDrv": "admit", "kCheckTyDefDrv": "admit", "kAssumeDecl": "assume", "kAssumeDef": "assume", "kCheckEqDrv": "check"}

failures = []


def fail(check, msg):
    failures.append(f"{check}: {msg}")


def ok(check, msg):
    print(f"  {check}  OK   {msg}")


def code_lines(path):
    """(lineno, text) for lines that are code: comments and doc
    comments stripped, blank lines dropped."""
    out = []
    for i, l in enumerate(path.read_text().splitlines(), 1):
        s = l.split("--", 1)[0] if "--" in l and not l.lstrip().startswith("|||") else l
        if l.lstrip().startswith("|||"):
            continue
        if s.strip():
            out.append((i, s))
    return out


DEF_RE = re.compile(r"^(\s*)([a-zA-Z][A-Za-z0-9_']*)\s*:")


def enclosing_names(path):
    """lineno -> name of the enclosing definition (a signature line at
    indentation 0 or 1 under `mutual`), for K3."""
    names = {}
    cur = None
    for i, l in enumerate(path.read_text().splitlines(), 1):
        m = DEF_RE.match(l)
        if m and len(m.group(1)) <= 2 and not l.lstrip().startswith(("|||", "--")):
            cur = m.group(2)
        names[i] = cur
    return names


def engine_files():
    for p in sorted((ROOT / "src" / "idris").rglob("*.idr")):
        if p not in KERNEL_MODULES.values():
            yield p


# ----- K1 / E2 -------------------------------------------------------------

def check_k1():
    bad = []
    for name, path in KERNEL_MODULES.items():
        for i, l in code_lines(path):
            m = re.match(r"^import\s+(?:public\s+)?([\w.]+)", l)
            if not m:
                continue
            mod = m.group(1)
            if mod in KERNEL_MODULES or mod in ALLOWED_IMPORTS or mod.startswith(ALLOWED_IMPORT_PREFIXES):
                continue
            bad.append(f"{path.relative_to(ROOT)}:{i}: import {mod}")
    if bad:
        for b in bad:
            fail("K1/E2", f"kernel module imports outside its closure — {b}")
    else:
        ok("K1/E2", f"{len(KERNEL_MODULES)} kernel modules import only the kernel and the base libraries")


# ----- K2 ------------------------------------------------------------------

def check_k2():
    bad = []
    for name, path in KERNEL_MODULES.items():
        for i, l in code_lines(path):
            for e in ESCAPES:
                if e in l:
                    # a deliberate abort fabricates nothing: a crash is
                    # verdict-free (an ill-typed input the theory rules
                    # out is reported by stopping, never by a value)
                    if e == "assert_total" and "idris_crash" in l:
                        continue
                    bad.append(f"{path.relative_to(ROOT)}:{i}: {e.strip()}")
    if bad:
        for b in bad:
            fail("K2", f"escape hatch or effect in the kernel — {b}")
    else:
        ok("K2", "no escape hatch, environment read or clock in the kernel")


# ----- K3 ------------------------------------------------------------------

def check_k3():
    bad = []
    for name, path in KERNEL_MODULES.items():
        names = enclosing_names(path)
        for i, l in code_lines(path):
            if "<|>" in l:
                bad.append(f"{path.relative_to(ROOT)}:{i}: <|>")
            if "kOrElse" in l and not l.startswith("kOrElse"):
                bad.append(f"{path.relative_to(ROOT)}:{i}: kOrElse used")
            if "kCatch" in l and not l.startswith("kCatch"):
                reraises = re.search(r"\\\s*\w+\s*=>\s*kerr", l) is not None
                if not reraises and names.get(i) not in AUDIT_FUNCTIONS:
                    bad.append(f"{path.relative_to(ROOT)}:{i}: kCatch whose handler does not re-raise (in {names.get(i)})")
    if bad:
        for b in bad:
            fail("K3", f"backtracking in the kernel — {b}")
    else:
        ok("K3", "no kOrElse, no <|>, every kCatch re-raises")


# ----- K4 ------------------------------------------------------------------

def check_k4():
    path = KERNEL_MODULES["Nova.Kernel"]
    lines = path.read_text().splitlines()
    found = {}
    for i, l in enumerate(lines):
        m = re.match(r"^(k(?:Check|Assume)\w*)\s*:\s*(.*)$", l)
        if m:
            exported = i > 0 and lines[i - 1].strip() == "export"
            found[m.group(1)] = (exported, m.group(2))
    names = set(found)
    if names != set(ENTRY_POINTS):
        fail("K4", f"the kernel's kCheck*/kAssume* functions are {sorted(names)}, the entry points on record are {sorted(ENTRY_POINTS)} — update docs/NovaStrategy.txt and this check together")
        return
    for n, kind in ENTRY_POINTS.items():
        exported, ty = found[n]
        if not exported:
            fail("K4", f"{n} is not exported")
        if kind in ("admit", "assume") and not ty.rstrip().endswith("Either KErr SigEntry"):
            fail("K4", f"{n} does not return the entry it produces: {ty}")
        if kind == "check" and not ty.rstrip().endswith("Either KErr ()"):
            fail("K4", f"{n} should return a verdict only: {ty}")
    if not any(f.startswith("K4") for f in failures):
        ok("K4", f"entry points {', '.join(sorted(ENTRY_POINTS))}; the admitting and assuming ones return the entry")


# ----- S1 / S2 -------------------------------------------------------------

def check_s1():
    """Σ owned by construction: the entry constructors are private to
    the kernel module (a grep here; the type checker is the guard);
    the engine keeps ONE signature (no kernelSig); the admitting
    entry points are called on ksig inside kernelAccept only, whose
    admitted entry is what every mirror site extends Σ with."""
    bad = []
    admitting = [n for n, k in ENTRY_POINTS.items() if k == "admit"]
    assuming = [n for n, k in ENTRY_POINTS.items() if k == "assume"]
    mirrors = 0
    for path in engine_files():
        names = enclosing_names(path)
        for i, l in code_lines(path):
            for n in assuming:
                if re.search(rf"\b{n}\b", l) and names.get(i) not in ("assumeDeclK", "assumeDefK"):
                    bad.append(f"{path.relative_to(ROOT)}:{i}: {n} called outside assumeDeclK/assumeDefK")
            if re.search(r"\bSig(Def|Decl)\b", l):
                bad.append(f"{path.relative_to(ROOT)}:{i}: names a signature-entry constructor")
            if "kernelSig" in l:
                bad.append(f"{path.relative_to(ROOT)}:{i}: a second signature")
            for n in admitting:
                if re.search(rf"\b{n}\b", l) and not re.search(rf"\b{n}\s+ksig\b", l):
                    bad.append(f"{path.relative_to(ROOT)}:{i}: {n} called outside kernelAccept (not on ksig)")
            if re.search(r"sig\s*\$=\s*\(:<\s*fromMaybe \(assumeDefK", l):
                mirrors += 1
            # the raw (unread) constructors: only inside the two helpers
            # that count their use
            if re.search(r"\bassumeDe(f|cl)\b(?!K)", l) and names.get(i) not in ("assumeDeclK", "assumeDefK"):
                bad.append(f"{path.relative_to(ROOT)}:{i}: raw assumption constructor outside assumeDeclK/assumeDefK")
    for b in bad:
        fail("S1", b)
    if not any(f.startswith("S1") for f in failures):
        ok("S1/S2", f"one signature; entry constructors private to the kernel; admitting entry points called on ksig only; {mirrors} mirror sites extend Σ with the admitted entry or an assumed one")


# ----- E1 ------------------------------------------------------------------

def check_e1():
    """Every site that extends Σ is either the mirror of an admission
    (the kernel's entry, or an assumed definition when the item was
    not clean) or an assumption site (obligation, hole, written
    declaration), and nothing else."""
    sites = []
    for path in engine_files():
        lines = path.read_text().splitlines()
        names = enclosing_names(path)
        for i, l in enumerate(lines, 1):
            if re.search(r"\bsig\s*\$=\s*\(:<", l):
                window = "\n".join(lines[max(0, i - 26):i - 1])
                if "fromMaybe (assumeDefK" in l and "kernelAccept" in window:
                    kind = "mirror of an admission (assumed, type read, when the item was not clean)"
                elif "assumeDeclK" in l and "oblName" in l:
                    kind = "assumed obligation (open, statement read)"
                elif "assumeDeclK" in l and names.get(i) == "mintHole":
                    kind = "hole (open, type read)"
                elif "assumeDeclK" in l and "SDeclDef" in window:
                    kind = "written declaration (open, type read)"
                else:
                    kind = None
                sites.append((path, i, names.get(i), kind))
    for p, i, f, kind in sites:
        if kind is None:
            fail("E1", f"engine extends Σ at {p.relative_to(ROOT)}:{i} ({f}) neither as a mirror of an admission nor as an assumption")
    if not any(f.startswith("E1") for f in failures):
        kinds = {}
        for _, _, _, k in sites:
            kinds[k] = kinds.get(k, 0) + 1
        ok("E1", "engine Σ sites: " + ", ".join(f"{n} × {k}" for k, n in sorted(kinds.items())))


# ----- E3 ------------------------------------------------------------------

SEARCH_REMNANTS = ['"rw:"', "statedOnly", "addLemma", "candCs", "NOVA_NOSEARCH", "SEARCH-NEEDED", "resolveRwName", "scopedMode", "NOVA_GLOBAL_STORE"]


def check_e3():
    """The engine places no lemma: the search is deleted (the engine
    programme, 3′) and stays deleted — no rewrite-licence marker, no
    stated-only flag, no Σ-lemma candidate store, no measure mode."""
    bad = []
    for path in engine_files():
        for i, l in code_lines(path):
            for w in SEARCH_REMNANTS:
                if w in l:
                    bad.append(f"{path.relative_to(ROOT)}:{i}: {w}")
    for b in bad:
        fail("E3", f"a remnant of the search in the engine — {b}")
    if not any(f.startswith("E3") for f in failures):
        ok("E3", "no Σ-lemma store, rewrite licence or search mode in the engine")


def main():
    print("check-roles: the mechanical half of the roles audit (docs/NovaStrategy.txt)")
    check_k1()
    check_k2()
    check_k3()
    check_k4()
    check_s1()
    check_e1()
    check_e3()
    if failures:
        print(f"\ncheck-roles: FAILED ({len(failures)})")
        for f in failures:
            print(f"  {f}")
        return 1
    print("check-roles: the author–engine–kernel division holds")
    return 0


if __name__ == "__main__":
    sys.exit(main())
