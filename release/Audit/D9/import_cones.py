#!/usr/bin/env python3
"""D9: transitive import-cone sizes for every module in the release + its deps.

Modules are resolved against Lean package roots (toolchain src/lean, mathlib and
the other .lake/packages). Reachability is computed with Python big-int bitsets
in topological order, so cone size = popcount.
"""
import json
import os
import re
import sys
from collections import defaultdict, deque

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from d9_scanner import code_mask  # comment/string-aware masking

ROOT = "/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-adversarial-audit-release"
RELEASE = os.path.join(ROOT, "release")
ELAN = "/data/home/guoshaoyang/workdir/lean_poincare/elan"
PKGS = os.path.join(RELEASE, ".lake", "packages")

ROOTS = [
    os.path.join(ELAN, "toolchains", "leanprover--lean4---v4.34.0-rc2", "src", "lean"),
    os.path.join(ELAN, "toolchains", "leanprover--lean4---v4.34.0-rc2", "src", "lean", "lake"),
    os.path.join(PKGS, "mathlib"),
    os.path.join(PKGS, "batteries"),
    os.path.join(PKGS, "aesop"),
    os.path.join(PKGS, "Qq"),
    os.path.join(PKGS, "proofwidgets"),
    os.path.join(PKGS, "Cli"),
    os.path.join(PKGS, "importGraph"),
    os.path.join(PKGS, "LeanSearchClient"),
    os.path.join(PKGS, "plausible"),
    RELEASE,
]

IMPORT_RE = re.compile(
    r"^[ \t]*(?:public[ \t]+|private[ \t]+|protected[ \t]+)?import[ \t]+"
    r"([A-Za-z0-9_.\u00ab\u00bb]+)[ \t]*$", re.M)


def module_path(mod):
    rel = mod.replace(".", os.sep) + ".lean"
    for r in ROOTS:
        p = os.path.join(r, rel)
        if os.path.exists(p):
            return p
    return None


def main():
    # 1. discover module files
    mods = {}
    for r in ROOTS:
        for dp, dn, fn in os.walk(r):
            dn[:] = [d for d in dn if d not in (".lake", ".git")]
            for f in fn:
                if not f.endswith(".lean"):
                    continue
                p = os.path.join(dp, f)
                mod = os.path.relpath(p, r)[:-5].replace(os.sep, ".")
                if mod.endswith(".lean"):
                    mod = mod[:-5]
                mods.setdefault(mod, p)
    # release modules take precedence for names that clash
    for dp, dn, fn in os.walk(RELEASE):
        dn[:] = [d for d in dn if d not in (".lake", ".git")]
        for f in fn:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dp, f)
            mod = os.path.relpath(p, RELEASE)[:-5].replace(os.sep, ".")
            mods[mod] = p
    # 2. edges
    deps = {}
    missing = set()
    for mod, p in mods.items():
        try:
            text = open(p, encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        d = set(IMPORT_RE.findall(code_mask(text)))
        for x in d:
            if x not in mods:
                missing.add(x)
        deps[mod] = d
    # 3. topological order (Kahn on dependency edges)
    indeg = {m: 0 for m in mods}
    rdeps = defaultdict(set)
    for m, d in deps.items():
        for x in d:
            if x in mods:
                indeg[m] += 1
                rdeps[x].add(m)
    q = deque([m for m in mods if indeg[m] == 0])
    order = []
    while q:
        m = q.popleft()
        order.append(m)
        for r in rdeps[m]:
            indeg[r] -= 1
            if indeg[r] == 0:
                q.append(r)
    cyclic = [m for m in mods if m not in set(order)]
    # 4. bitsets
    idx = {m: i for i, m in enumerate(mods)}
    bits = {}
    for m in order:
        b = 0
        for x in deps[m]:
            if x in mods:
                b |= bits[x] | (1 << idx[x])
        bits[m] = b
    for m in cyclic:
        bits[m] = 0
    cone = {m: bits[m].bit_count() for m in mods}
    out = {
        "schema": "d9-adversarial-audit/import-cones-v1",
        "roots": ROOTS,
        "modules_total": len(mods),
        "missing_imports": sorted(missing),
        "cyclic_modules": cyclic,
        "cones": cone,
    }
    out["release_cones"] = {m: cone[m] for m, p in mods.items()
                            if os.path.abspath(p).startswith(RELEASE + os.sep)}
    dst = os.path.join(RELEASE, "Audit", "D9", "logs", "import_cones.json")
    json.dump(out, open(dst, "w"), indent=1)
    print("modules:", len(mods), "missing:", len(missing), "cyclic:", len(cyclic))
    print("wrote", dst)
    top = sorted(out["release_cones"].items(), key=lambda kv: -kv[1])[:20]
    for m, c in top:
        print(f"{c:6d}  {m}")


if __name__ == "__main__":
    sys.exit(main())
