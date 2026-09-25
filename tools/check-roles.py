#!/usr/bin/env python3
"""The mechanical half of the roles audit (docs/NovaStrategy.txt, "The
audit"): what the author–engine–kernel division says about the tree
that can be read off the tree.

  K1  the kernel closure: kernel modules import only each other, the
      base libraries, and Nova.Profile (diagnostics hooks)
  K2  no escape hatches in the kernel (believe_me, assert_total, …,
      no environment or clock reads); an assert_total that wraps a
      deliberate crash is allowed — it fabricates nothing
  K3  no backtracking in the kernel: no kOrElse / <|>; every kCatch
      re-raises, except inside the named audit function
  K4  the kernel's exported kCheck* functions are exactly the entry
      points, and the Σ-extending ones return the entry they admit
  S1  the kernel's signature is extended at exactly one engine site,
      by the entry a kernel entry point returned; every call of a
      Σ-extending entry point outside the kernel passes the kernel's
      signature (S2 — no engine-built entry reaches it — follows)
  E1  the engine's Σ-extending sites that bypass the kernel are
      exactly the assumption sites (obligations, holes, declarations)
      or the mirror of an item the kernel just accepted
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
ALLOWED_IMPORTS = {"Nova.Profile"}  # diagnostics hooks only (drvCanary, audit)

# K2: escape hatches and effects
ESCAPES = ["believe_me", "assert_total", "assert_smaller", "unsafePerformIO",
           "%foreign", "prim__", "getEnv", "nowNs", "bump ", "timed "]

# K3: the one function allowed to catch without re-raising (it prints)
AUDIT_FUNCTIONS = {"dWhnfAudit"}

# K4: the entry points, by name, and which of them admit an entry
ENTRY_POINTS = {"kCheckDefDrv": True, "kCheckTyDefDrv": True, "kCheckEqDrv": False}

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
        ok("K1/E2", f"{len(KERNEL_MODULES)} kernel modules import only the kernel, the base libraries and Nova.Profile")


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
        ok("K3", "no kOrElse, no <|>, every kCatch re-raises (audit function excepted)")


# ----- K4 ------------------------------------------------------------------

def check_k4():
    path = KERNEL_MODULES["Nova.Kernel"]
    lines = path.read_text().splitlines()
    found = {}
    for i, l in enumerate(lines):
        m = re.match(r"^(kCheck\w*)\s*:\s*(.*)$", l)
        if m:
            exported = i > 0 and lines[i - 1].strip() == "export"
            found[m.group(1)] = (exported, m.group(2))
    names = set(found)
    if names != set(ENTRY_POINTS):
        fail("K4", f"the kernel's kCheck* functions are {sorted(names)}, the entry points on record are {sorted(ENTRY_POINTS)} — update docs/NovaStrategy.txt and this check together")
        return
    for n, admits in ENTRY_POINTS.items():
        exported, ty = found[n]
        if not exported:
            fail("K4", f"{n} is not exported")
        if admits and not ty.rstrip().endswith("Either KErr SigEntry"):
            fail("K4", f"{n} does not return the entry it admits: {ty}")
        if not admits and not ty.rstrip().endswith("Either KErr ()"):
            fail("K4", f"{n} should return a verdict only: {ty}")
    if not any(f.startswith("K4") for f in failures):
        ok("K4", f"entry points {', '.join(sorted(ENTRY_POINTS))}; the admitting ones return the entry")


# ----- S1 / S2 -------------------------------------------------------------

def check_s1():
    ext_sites = []
    bad_calls = []
    admitting = [n for n, a in ENTRY_POINTS.items() if a]
    for path in engine_files():
        names = enclosing_names(path)
        for i, l in code_lines(path):
            if re.search(r"kernelSig\s*(\$=|:=)", l):
                ext_sites.append((path, i, l.strip(), names.get(i)))
            for n in admitting:
                if re.search(rf"\b{n}\b", l) and not re.search(rf"\b{n}\s+ksig\b", l):
                    bad_calls.append(f"{path.relative_to(ROOT)}:{i}: {n} called outside kernelAccept (not on ksig)")
    if len(ext_sites) != 1:
        for p, i, l, f in ext_sites:
            fail("S1", f"kernel signature extended at {p.relative_to(ROOT)}:{i} ({f}): {l}")
        if not ext_sites:
            fail("S1", "no site extends the kernel signature")
    else:
        p, i, l, f = ext_sites[0]
        if f != "kernelAccept" or not re.search(r"kernelSig\s*\$=\s*\(:<\s*entry\)", l):
            fail("S1", f"the one extension site is not kernelAccept's `entry`: {p.relative_to(ROOT)}:{i} ({f}): {l}")
    for b in bad_calls:
        fail("S1", b)
    if not any(f.startswith("S1") for f in failures):
        ok("S1/S2", "kernelSig extended once, in kernelAccept, by the entry a kernel entry point returned; admitting entry points are called on ksig only")


# ----- E1 ------------------------------------------------------------------

def check_e1():
    sites = []
    for path in engine_files():
        lines = path.read_text().splitlines()
        names = enclosing_names(path)
        for i, l in enumerate(lines, 1):
            if re.search(r"\bsig\s*\$=\s*\(:<\s*Sig(Def|Decl)\b", l):
                window = "\n".join(lines[max(0, i - 26):i - 1])
                if "kernelAccept" in window:
                    kind = "mirror of an item the kernel accepted"
                elif "oblName" in l:
                    kind = "assumed obligation (open)"
                elif names.get(i) == "mintHole":
                    kind = "hole (open)"
                elif "SDeclDef" in window:
                    kind = "written declaration (open)"
                else:
                    kind = None
                sites.append((path, i, names.get(i), kind))
    for p, i, f, kind in sites:
        if kind is None:
            fail("E1", f"engine extends its Σ at {p.relative_to(ROOT)}:{i} ({f}) neither after a kernel acceptance nor as an assumption")
    if not any(f.startswith("E1") for f in failures):
        kinds = {}
        for _, _, _, k in sites:
            kinds[k] = kinds.get(k, 0) + 1
        ok("E1", "engine Σ sites: " + ", ".join(f"{n} × {k}" for k, n in sorted(kinds.items())))


def main():
    print("check-roles: the mechanical half of the roles audit (docs/NovaStrategy.txt)")
    check_k1()
    check_k2()
    check_k3()
    check_k4()
    check_s1()
    check_e1()
    if failures:
        print(f"\ncheck-roles: FAILED ({len(failures)})")
        for f in failures:
            print(f"  {f}")
        return 1
    print("check-roles: the author–engine–kernel division holds")
    return 0


if __name__ == "__main__":
    sys.exit(main())
