#!/usr/bin/env python3
"""SEMREV-L5: independent source-hash replay of the L5 audit.

Recomputes sha256 for every .lean file under the L5 union release and compares:
  * current files   vs  L5 audit-evidence/source-hashes.txt
  * source-hashes   vs  L5 audit-evidence/union-release-hashes.txt (pre-audit baseline)
  * also hashes the L5 card + checkpoint + key evidence files for citation.
"""
import hashlib
import json
import os

L5 = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L5-topology-audit"
REL = os.path.join(L5, "release")
OUT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "evidence")


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def load(p):
    d = {}
    for line in open(p):
        line = line.rstrip("\n")
        if not line.strip():
            continue
        h, path = line.split("  ", 1)
        d[path] = h
    return d


def main():
    cur = {}
    for root, dirs, files in os.walk(REL):
        dirs[:] = [d for d in dirs if d != ".lake"]
        for f in files:
            if f.endswith(".lean"):
                p = os.path.join(root, f)
                cur["./" + os.path.relpath(p, REL)] = sha(p)

    src = load(os.path.join(L5, "audit-evidence/source-hashes.txt"))
    base = load(os.path.join(L5, "audit-evidence/union-release-hashes.txt"))
    base_lean = {p: h for p, h in base.items() if p.endswith(".lean")}

    report = {
        "current_lean_files": len(cur),
        "source_hash_entries": len(src),
        "baseline_entries": len(base),
        "baseline_lean_entries": len(base_lean),
        "mismatch_current_vs_sourcehashes": sorted(p for p in src if cur.get(p) != src[p]),
        "missing_current": sorted(p for p in src if p not in cur),
        "current_not_in_sourcehashes": sorted(p for p in cur if p not in src),
        "diff_sourcehashes_vs_baseline_lean": sorted(
            p for p in src if p in base_lean and src[p] != base_lean[p]
        ),
        "hashes_of_l5_artifacts": {
            "longrun/results/L5-topology-audit.md": sha(os.path.join(L5, "longrun/results/L5-topology-audit.md")),
            "longrun/results/L5-topology-audit.json": sha(os.path.join(L5, "longrun/results/L5-topology-audit.json")),
            "checkpoint.json": sha(os.path.join(L5, "checkpoint.json")),
            "research-brief-2026-09-11.md": sha(os.path.join(L5, "research-brief-2026-09-11.md")),
            "audit-evidence/audit-summary.json": sha(os.path.join(L5, "audit-evidence/audit-summary.json")),
            "audit-evidence/collisions.json": sha(os.path.join(L5, "audit-evidence/collisions.json")),
            "audit-evidence/forbidden-scan.json": sha(os.path.join(L5, "audit-evidence/forbidden-scan.json")),
            "audit-evidence/perfile-check.json": sha(os.path.join(L5, "audit-evidence/perfile-check.json")),
        },
        "release_tree_hash": hashlib.sha256(
            "\n".join(f"{p} {h}" for p, h in sorted(cur.items())).encode()
        ).hexdigest(),
    }
    with open(os.path.join(OUT, "hash-replay.json"), "w") as f:
        json.dump(report, f, indent=1)
    print(json.dumps({k: v for k, v in report.items() if k != "hashes_of_l5_artifacts"}, indent=1))
    print(json.dumps(report["hashes_of_l5_artifacts"], indent=1))


if __name__ == "__main__":
    main()
