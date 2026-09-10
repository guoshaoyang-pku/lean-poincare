#!/usr/bin/env python3
"""
D5-clean-rebuild: prove that no source artifact was modified.

Re-hashes every origin file recorded in manifest/provenance.json and compares with the
hash captured before the release build. Exit code 1 if any artifact changed.
"""
import hashlib
import json
import os
import sys

D5 = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D5_clean_rebuild"
MANIFEST = os.path.join(D5, "manifest")


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    prov = json.load(open(os.path.join(MANIFEST, "provenance.json")))
    changed = []
    checked = 0
    for c in prov["clusters"]:
        for f in c["files"]:
            checked += 1
            if not os.path.exists(f["origin"]):
                changed.append({"path": f["origin"], "status": "missing"})
                continue
            now = sha256(f["origin"])
            if now != f["sha256"]:
                changed.append({"path": f["origin"], "expected": f["sha256"], "actual": now})
    for b in prov["base_dependencies"]:
        checked += 1
        now = sha256(b["origin"])
        if now != b["sha256"]:
            changed.append({"path": b["origin"], "expected": b["sha256"], "actual": now})
    out = {
        "schema": "d5-clean-rebuild/source-integrity-v1",
        "origin_files_checked": checked,
        "changed": changed,
        "unchanged": not changed,
    }
    json.dump(out, open(os.path.join(MANIFEST, "source-integrity.json"), "w"), indent=1)
    print(json.dumps(out, indent=1))
    return 1 if changed else 0


if __name__ == "__main__":
    sys.exit(main())
