#!/usr/bin/env python3
"""Regenerate baseline/MANIFEST.json over the L1 evidence tree.

Scope (same as the first invocation's manifest):
  baseline/**  except  baseline/MANIFEST.json and the preserved Lake build trees under
                       baseline/pre-rebuild/build-tree*/**
  comms/**
  longrun/**
  research-brief-*.md at the worktree root
Excluded: checkpoint.json, MANIFEST.json, the preserved 1.7 GB Lake build trees
(recorded separately by baseline/pre-rebuild/build-artifact-inventory.txt and
baseline/pre-rebuild/build-tree-inv1-20260912T0118Z.inventory.txt),
and transient runner temp files.
"""
import hashlib
import json
import os
import time

WT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
_pre = os.path.join(WT, "baseline/pre-rebuild")
SKIP_DIRS = {os.path.join(_pre, d) for d in os.listdir(_pre)
             if d.startswith("build-tree") and os.path.isdir(os.path.join(_pre, d))}
SKIP_FILES = {os.path.join(WT, "checkpoint.json"),
              os.path.join(WT, "baseline/MANIFEST.json"),
              # self-referential: verify_baseline.py writes this report after hashing the tree
              os.path.join(WT, "baseline/logs/verify-baseline.json")}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def included(path):
    if path in SKIP_FILES:
        return False
    if any(os.path.commonpath([path, d]) == d for d in SKIP_DIRS):
        return False
    rel = os.path.relpath(path, WT)
    if rel.startswith(("baseline/", "comms/", "longrun/")):
        return True
    return rel.startswith("research-brief-") and rel.endswith(".md")


def main():
    files = []
    for dirpath, dirnames, filenames in os.walk(WT):
        dirnames[:] = [d for d in dirnames
                       if d not in (".lake", ".git") and os.path.join(dirpath, d) not in SKIP_DIRS]
        for fn in filenames:
            p = os.path.join(dirpath, fn)
            if ".tmp." in fn:
                continue
            if not included(p):
                continue
            files.append({"path": os.path.relpath(p, WT), "sha256": sha256(p),
                          "bytes": os.path.getsize(p)})
    files.sort(key=lambda e: e["path"])
    man = {
        "schema": "l1-lean-baseline/evidence-manifest-v1",
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "note": ("sha256 of L1 baseline evidence; checkpoint.json, MANIFEST.json and the "
                 "self-referential verify report baseline/logs/verify-baseline.json are "
                 "excluded; release/ source manifest is "
                 "baseline/reconcile/source-hash-drift.json (462 files)"),
        "files": files,
    }
    out = os.path.join(WT, "baseline/MANIFEST.json")
    json.dump(man, open(out, "w"), indent=1)
    print(f"wrote {len(files)} entries to {out}")


if __name__ == "__main__":
    main()
