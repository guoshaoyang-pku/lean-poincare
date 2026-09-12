#!/usr/bin/env python3
"""Exact source drift of the A1 patched tree against the frozen release tree.

Hashes both trees (excluding `.lake`), lists added / removed / changed files with both
hashes, asserts that the drift equals the expected A1 patch set, and writes
`baseline/a1/patched-drift.json`.

Exit 0 iff the drift is exactly the expected set (7 modified + 1 added + 0 removed).
"""
import hashlib
import json
import os
import sys
import time

WT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
FROZEN = os.path.join(WT, "release")
PATCHED = os.path.join(WT, "baseline", "a1", "patched-release")
OUT = os.path.join(WT, "baseline", "a1", "patched-drift.json")

EXPECTED_CHANGED = {
    "Audit/CounterexampleAudit.lean",
    "Poincare/D7/EvolutionSharp/AxiomAudit.lean",
    "Poincare/D7/EvolutionSharp/GibbsSharp.lean",
    "Poincare/D7/EvolutionSharp/Implications.lean",
    "Poincare/Longrun/Evolution.lean",
    "Poincare/Longrun/Evolution/Discrete.lean",
    "Poincare/Longrun/Evolution/Gibbs.lean",
}
EXPECTED_ADDED = {"Poincare/D7/EvolutionSharp/SharpOnlyConsumers.lean"}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def tree(root):
    out = {}
    for dirpath, dirnames, filenames in os.walk(root):
        if ".lake" in dirpath.split(os.sep):
            continue
        for f in filenames:
            p = os.path.join(dirpath, f)
            if os.path.islink(p) or not os.path.isfile(p):
                continue
            out[os.path.relpath(p, root)] = sha256(p)
    return out


def main():
    a, b = tree(FROZEN), tree(PATCHED)
    added = sorted(set(b) - set(a))
    removed = sorted(set(a) - set(b))
    changed = sorted(p for p in set(a) & set(b) if a[p] != b[p])
    report = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "frozen_tree": FROZEN, "frozen_files": len(a),
        "patched_tree": PATCHED, "patched_files": len(b),
        "added": [{"path": p, "sha256": b[p]} for p in added],
        "removed": [{"path": p, "sha256": a[p]} for p in removed],
        "changed": [{"path": p, "frozen": a[p], "patched": b[p]} for p in changed],
        "expected_changed": sorted(EXPECTED_CHANGED),
        "expected_added": sorted(EXPECTED_ADDED),
    }
    json.dump(report, open(OUT, "w"), indent=1)
    print("frozen=%d patched=%d added=%d removed=%d changed=%d"
          % (len(a), len(b), len(added), len(removed), len(changed)))
    for p in added:
        print("  A %s" % p)
    for p in removed:
        print("  R %s" % p)
    for p in changed:
        print("  C %s" % p)
    print("  report: %s" % OUT)
    ok = set(added) == EXPECTED_ADDED and not removed and set(changed) == EXPECTED_CHANGED
    print("verdict: %s" % ("EXPECTED-DRIFT" if ok else "UNEXPECTED-DRIFT"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
