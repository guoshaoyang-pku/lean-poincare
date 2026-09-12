#!/usr/bin/env python3
"""Compare two Lean build trees (.olean files) by sha256 and size.

Usage:
    python3 baseline/tools/compare_build_trees.py OLD_ROOT NEW_ROOT OUT.json [--label-old X --label-new Y]

Reports: identical / differing (with size delta and whether each side embeds its own
absolute path) / only-in-old / only-in-new.  Read-only over both trees.
"""
import hashlib
import json
import os
import sys


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def collect(root):
    out = {}
    for dirpath, _dirnames, filenames in os.walk(root):
        for fn in filenames:
            if not fn.endswith(".olean"):
                continue
            p = os.path.join(dirpath, fn)
            rel = os.path.relpath(p, root)
            out[rel] = (sha256(p), os.path.getsize(p))
    return out


def embeds(path, needle):
    try:
        with open(path, "rb") as f:
            return needle.encode() in f.read()
    except OSError:
        return None


def main():
    old_root, new_root, out_path = sys.argv[1], sys.argv[2], sys.argv[3]
    label_old = "old"
    label_new = "new"
    if "--label-old" in sys.argv:
        label_old = sys.argv[sys.argv.index("--label-old") + 1]
    if "--label-new" in sys.argv:
        label_new = sys.argv[sys.argv.index("--label-new") + 1]
    old = collect(old_root)
    new = collect(new_root)
    identical, differing = [], []
    for rel in sorted(set(old) & set(new)):
        if old[rel][0] == new[rel][0]:
            identical.append(rel)
        else:
            po, pn = os.path.join(old_root, rel), os.path.join(new_root, rel)
            differing.append({
                "module": rel,
                "sha256_old": old[rel][0],
                "sha256_new": new[rel][0],
                "size_old": old[rel][1],
                "size_new": new[rel][1],
                "size_delta": new[rel][1] - old[rel][1],
                "old_root_embedded_old": embeds(po, old_root),
                "old_root_embedded_new": embeds(pn, old_root),
                "new_root_embedded_old": embeds(po, new_root),
                "new_root_embedded_new": embeds(pn, new_root),
            })
    report = {
        "old_root": os.path.abspath(old_root),
        "new_root": os.path.abspath(new_root),
        "label_old": label_old,
        "label_new": label_new,
        "olean_count_old": len(old),
        "olean_count_new": len(new),
        "identical": len(identical),
        "differing": len(differing),
        "only_in_old": sorted(set(old) - set(new)),
        "only_in_new": sorted(set(new) - set(old)),
        "differing_detail": differing,
        "unexplained_differences": [
            d for d in differing
            if not (d["size_delta"] in (-16, -8, 0, 8, 16, 24, -24)
                    and (d["old_root_embedded_old"] and d["new_root_embedded_new"]))
        ],
    }
    with open(out_path, "w") as f:
        json.dump(report, f, indent=1)
    print(json.dumps({k: v for k, v in report.items() if k != "differing_detail"}, indent=1))
    print("report ->", out_path)


if __name__ == "__main__":
    main()
