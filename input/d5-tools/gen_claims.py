#!/usr/bin/env python3
"""
D5-clean-rebuild: extract every fully-qualified Lean declaration name claimed by the
D1-D4 machine-readable result cards and generate ReleaseClaims.lean with `#check @name`.

This is an *informational* completeness check (not part of the forbidden-dependency gate):
a failing `#check` means a result card names a declaration that does not resolve in the
clean package (typo, renamed, or never delivered).
"""
import json
import os
import re
import sys

ROOT = "/data3/guoshaoyang/workdir/lean_poincare"
RESULTS = os.path.join(ROOT, "longrun", "results")
D5 = os.path.join(ROOT, "longrun", "worktrees", "D5_clean_rebuild")
RELEASE = os.path.join(D5, "release")
MANIFEST = os.path.join(D5, "manifest")

CARDS = [
    "D1-mathlib-geometry-map.json", "D1-pde-api-map.json", "D1-perelman-ledger.json",
    "D2-geometry-foundation.json", "D2-pde-foundation.json", "D2-ricci-ode-cluster.json",
    "D3-entropy-interface.json", "D3-kappa-ledger.json", "D3-surgery-ledger.json",
    "D4-evolution-theorem.json", "D4-counterexample-audit.json",
]

NAME_RE = re.compile(r"^(Poincare|Probe|Ledger|Perelman|D4Audit)\.[A-Za-z_][A-Za-z0-9_'.]*"
                     r"(\.[A-Za-z_][A-Za-z0-9_']*)*$")


def module_names():
    """Module names of every .lean file in the release package (path -> dotted name)."""
    mods = set()
    for dirpath, dirnames, filenames in os.walk(RELEASE):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        for fn in filenames:
            if fn.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dirpath, fn), RELEASE)
                mods.add(rel[:-5].replace("/", "."))
    return mods


def walk_strings(o):
    if isinstance(o, str):
        yield o
    elif isinstance(o, dict):
        for v in o.values():
            yield from walk_strings(v)
    elif isinstance(o, list):
        for v in o:
            yield from walk_strings(v)


def main():
    mods = module_names()
    names = {}          # name -> [cards]
    for card in CARDS:
        path = os.path.join(RESULTS, card)
        if not os.path.exists(path):
            continue
        data = json.load(open(path))
        for s in walk_strings(data):
            if NAME_RE.match(s) and s not in mods:
                names.setdefault(s, set()).add(card)
    ordered = sorted(names)
    body = ["/-\nD5-clean-rebuild — claim-resolution probe (generated).\n\n"
            "Each `#check @name` below is a declaration named by a D1-D4 result card.\n"
            "Errors here are recorded as informational claim discrepancies, not gate failures.\n-/\n",
            "import ReleaseCheck\n"]
    for n in ordered:
        body.append(f"#check @{n}")
    open(os.path.join(RELEASE, "ReleaseClaims.lean"), "w").write("\n".join(body) + "\n")
    out = {
        "schema": "d5-clean-rebuild/claims-v1",
        "claim_count": len(ordered),
        "module_names_excluded": sorted(mods),
        "claims": [{"name": n, "cards": sorted(names[n])} for n in ordered],
    }
    with open(os.path.join(MANIFEST, "claims.json"), "w") as fh:
        json.dump(out, fh, indent=1)
    print(f"generated ReleaseClaims.lean with {len(ordered)} claimed declaration names")
    return 0


if __name__ == "__main__":
    sys.exit(main())
