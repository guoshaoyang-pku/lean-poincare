#!/usr/bin/env python3
"""Source-integrity check for the D7-sphere-recognition worktree.

Compares every file of the worktree (excluding `.lake`, `longrun/` and the new
`release/Poincare/D7/Recognition/` directory, and skipping symlinks) against the stable
dependency scaffold `../D7-canonical-neighborhood` by sha256.  Writes JSON to stdout.

The task's documented scaffold source `../D7-surgery-neck-extinction` was empty at worktree
creation (its own `cp -al` had failed with EXDEV and it is running concurrently); the
effective scaffold is therefore the queue dependency `../D7-canonical-neighborhood`, which
contains the full D6 base plus the seven accepted D7 dependency layers.
"""
import hashlib
import json
import os

SRC = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-canonical-neighborhood"
DST = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-sphere-recognition"
NEW_DIR = "release/Poincare/D7/Recognition/"


def collect(root):
    out = {}
    for dirpath, dirnames, filenames in os.walk(root):
        rel = os.path.relpath(dirpath, root)
        pruned = []
        for d in list(dirnames):
            r = os.path.join(rel, d) if rel != "." else d
            if d in (".lake", ".git") or r == "longrun" or r.startswith("release/.lake"):
                continue
            pruned.append(d)
        dirnames[:] = pruned
        for f in filenames:
            r = os.path.normpath(os.path.join(rel, f)) if rel != "." else f
            if r.startswith(NEW_DIR):
                continue
            p = os.path.join(dirpath, f)
            if os.path.islink(p):
                out[r] = "SYMLINK:" + os.readlink(p)
            else:
                with open(p, "rb") as fh:
                    out[r] = hashlib.sha256(fh.read()).hexdigest()
    return out


a = collect(SRC)
b = collect(DST)
changed = sorted(k for k in a if k in b and a[k] != b[k])
removed = sorted(k for k in a if k not in b)
added = sorted(k for k in b if k not in a)
print(json.dumps({
    "schema": "d7-sphere-recognition/source-integrity-v1",
    "scaffold": SRC,
    "worktree": DST,
    "files_checked": len(a),
    "changed": changed,
    "removed": removed,
    "added_outside_new_dir": added,
}, indent=1))
