#!/usr/bin/env python3
"""Independent replay of the parent card's recorded release hashes.

For every card: recompute sha256 over the transported snapshot release tree and over the
origin worktree release tree, then compare both against the parent's recorded
audit/evidence/<task>/release-hashes.txt entries.
"""
import hashlib
import json
import os
import sys

PARENT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-ophis-cards"
REV = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/SEMREV-D13-cross-audit-ophis"
ORIGIN = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees"
TASKS = [
    "D13-integrated-kernel-audit", "D13-critical-path-review", "D13-upstream-adapter-audit",
    "D13-morgan-tian-adapter-plan", "D13-topping-ricci-adapter-plan",
    "D13-manifold-ibp-volume-form", "D13-deturck-shorttime-producer",
    "D13-vankampen-recognition", "D13-heatkernel-bridge-d10-d7", "D13-cross-audit-360-cards",
]


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def tree(root):
    out = {}
    if not os.path.isdir(root):
        return out
    for dp, dn, fn in os.walk(root):
        dn[:] = [d for d in dn if d != ".lake"]
        for f in fn:
            full = os.path.join(dp, f)
            out["./" + os.path.relpath(full, root)] = sha256(full)
    return out


def read_manifest(path):
    out = {}
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            parts = line.split()
            if len(parts) >= 2:
                out[parts[-1]] = parts[0]
    return out


report = {}
for task in TASKS:
    tr = tree(f"{PARENT}/audit/ophis/{task}/release")
    orr = tree(f"{ORIGIN}/{task}/release")
    rec = read_manifest(f"{PARENT}/audit/evidence/{task}/release-hashes.txt")
    def cmp(a, b):
        keys = set(a) | set(b)
        mism = [k for k in sorted(keys) if a.get(k) != b.get(k)]
        return mism
    m_tr_rec = cmp(tr, rec)
    m_or_rec = cmp(orr, rec)
    m_tr_or = cmp(tr, orr)
    report[task] = {
        "recorded": len(rec), "transported": len(tr), "origin": len(orr),
        "transported_vs_recorded_mismatch": len(m_tr_rec),
        "origin_vs_recorded_mismatch": len(m_or_rec),
        "transported_vs_origin_mismatch": len(m_tr_or),
        "examples_transported_vs_origin": m_tr_or[:10],
        "examples_transported_vs_recorded": m_tr_rec[:10],
        "examples_origin_vs_recorded": m_or_rec[:10],
    }
    print(task, json.dumps(report[task])[:400], flush=True)

with open(f"{REV}/review/evidence/hash-replay-independent.json", "w") as f:
    json.dump(report, f, indent=1)
print("WROTE hash-replay-independent.json")
