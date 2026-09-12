#!/usr/bin/env python3
"""Independent transport-fidelity check: transported ophis snapshot vs origin worktrees.

For every file in the transported audit/ophis/<task> tree, find the same relative path in the
origin worktree and compare sha256. Also report origin files that were not transported, with
their size and mtime, so exclusions can be judged against the documented transport policy.
"""
import hashlib
import json
import os
import sys

PARENT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-ophis-cards"
TRANSPORT = os.path.join(PARENT, "audit", "ophis")
ORIGIN_BASE = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees"
TASKS = [
    "D13-integrated-kernel-audit",
    "D13-critical-path-review",
    "D13-manifold-ibp-volume-form",
    "D13-heatkernel-bridge-d10-d7",
    "D13-cross-audit-360-cards",
    "D13-upstream-adapter-audit",
    "D13-morgan-tian-adapter-plan",
    "D13-topping-ricci-adapter-plan",
    "D13-deturck-shorttime-producer",
    "D13-vankampen-recognition",
]

# Documented exclusions from the transport policy (parent card section 0).
EXCLUDE_TOP = {".lake", "third_party", "tmp", ".git"}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def walk(root):
    out = {}
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in EXCLUDE_TOP]
        for fn in filenames:
            full = os.path.join(dirpath, fn)
            rel = os.path.relpath(full, root)
            out[rel] = full
    return out


report = {}
for task in TASKS:
    tr_root = os.path.join(TRANSPORT, task)
    or_root = os.path.join(ORIGIN_BASE, task)
    tr = walk(tr_root)
    orr = walk(or_root)
    mism = []
    missing_in_origin = []
    for rel, trp in sorted(tr.items()):
        orp = orr.get(rel)
        if orp is None:
            missing_in_origin.append(rel)
            continue
        a, b = sha256(trp), sha256(orp)
        if a != b:
            mism.append({"rel": rel, "transported": a, "origin": b,
                         "tr_mtime": os.path.getmtime(trp), "or_mtime": os.path.getmtime(orp)})
    not_transported = []
    for rel, orp in sorted(orr.items()):
        if rel not in tr:
            not_transported.append({"rel": rel, "size": os.path.getsize(orp),
                                    "mtime": os.path.getmtime(orp)})
    report[task] = {
        "transported_files": len(tr),
        "origin_files": len(orr),
        "hash_mismatches": mism,
        "transported_not_in_origin": missing_in_origin,
        "not_transported": not_transported,
        "verdict": "MATCH" if not mism and not missing_in_origin else "MISMATCH",
    }
    print(f"{task}: transported={len(tr)} origin={len(orr)} mismatches={len(mism)} "
          f"missing_in_origin={len(missing_in_origin)} not_transported={len(not_transported)}",
          flush=True)

with open(sys.argv[1] if len(sys.argv) > 1 else "transport-compare.json", "w") as f:
    json.dump(report, f, indent=1)
print("WROTE", sys.argv[1] if len(sys.argv) > 1 else "transport-compare.json")
