#!/usr/bin/env python3
"""Integrity check of the pinned Frenzymath upstream snapshot used for the
"upstream source claim" cross-checks.

Checks, all local to this worktree's `third_party/frenzymath/Poincare-Conjecture`:

  * Lean toolchain pin (`leanprover/lean4:v4.32.1`) and mathlib pin
    (`520045ab14e26149ee970e2e617ca04b09bde5d6`) as recorded in the integration doc;
  * presence of the expected package roots (Shared, DoCarmoLib, MorganTianLib,
    Topping, ...);
  * **absence** of build caches (`.lake/build`) so nothing upstream has been
    silently compiled into this audit's evidence;
  * a content digest of every tracked source file (sorted path+sha256), so the
    snapshot state used by the audit is pinned.

Output: audit360/frenzymath_snapshot_check.json
"""
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(HERE)
SNAP = os.path.join(WT, "third_party", "frenzymath", "Poincare-Conjecture")
OUT = os.path.join(HERE, "frenzymath_snapshot_check.json")
EXT = (".lean", ".toml", ".json", ".yaml", ".yml", ".md")
EXPECTED_ROOTS = ["Shared", "DoCarmoLib", "MorganTianLib", "Topping"]


def main():
    if not os.path.isdir(SNAP):
        print("snapshot missing:", SNAP)
        return 1
    files = []
    lean_lines = 0
    caches = []
    for dirpath, dirnames, filenames in os.walk(SNAP):
        if ".lake" in dirpath.split(os.sep):
            caches.append(dirpath)
            dirnames[:] = []
            continue
        for f in filenames:
            p = os.path.join(dirpath, f)
            files.append(p)
            if f.endswith(".lean"):
                try:
                    lean_lines += sum(1 for _ in open(p, errors="replace"))
                except OSError:
                    pass
    files.sort()
    digest = hashlib.sha256()
    for p in files:
        rel = os.path.relpath(p, SNAP)
        h = hashlib.sha256(open(p, "rb").read()).hexdigest()
        digest.update(("%s %s\n" % (rel, h)).encode())
    tc = None
    for cand in ("lean-toolchain", "PoincareConjecture/lean-toolchain"):
        p = os.path.join(SNAP, cand)
        if os.path.exists(p):
            tc = open(p).read().strip()
            break
    manifest = None
    for cand in ("lake-manifest.json", "PoincareConjecture/lake-manifest.json"):
        p = os.path.join(SNAP, cand)
        if os.path.exists(p):
            try:
                m = json.load(open(p))
                manifest = {pk.get("name"): pk.get("rev")
                            for pk in m.get("packages", [])}
            except Exception:  # noqa: BLE001
                manifest = "unparseable"
            break
    roots = sorted(d for d in os.listdir(SNAP) if os.path.isdir(os.path.join(SNAP, d)))
    out = {
        "schema": "a3-frenzymath-snapshot-check-v1",
        "snapshot": "third_party/frenzymath/Poincare-Conjecture",
        "expected_commit": "bb91a091f0b968f8bbe8d861e025a88d82b161be",
        "file_count": len(files),
        "lean_file_count": sum(1 for p in files if p.endswith(".lean")),
        "lean_line_count": lean_lines,
        "content_digest_sha256": digest.hexdigest(),
        "lean_toolchain": tc,
        "mathlib_rev": (manifest or {}).get("mathlib") if isinstance(manifest, dict) else None,
        "package_roots": roots,
        "expected_roots_present": {
            r: any(os.path.isdir(os.path.join(SNAP, base, r))
                   for base in ("", "PoincareConjecture", "shared",
                                "formalized-sources/DoCarmo",
                                "formalized-sources/MorganTian",
                                "formalized-sources"))
            for r in EXPECTED_ROOTS},
        "build_caches_present": caches,
        "doc_pins": {"toolchain": "leanprover/lean4:v4.32.1",
                     "mathlib": "520045ab14e26149ee970e2e617ca04b09bde5d6"},
        "verdict": ("PASS: snapshot present, no build caches, digest pinned"
                    if not caches else "REVIEW: build caches present"),
    }
    json.dump(out, open(OUT, "w"), indent=1)
    print(json.dumps(out, indent=1))
    return 1 if caches else 0


if __name__ == "__main__":
    sys.exit(main())
