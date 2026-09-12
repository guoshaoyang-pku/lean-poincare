#!/usr/bin/env python3
"""P5 release hash gate (fail-closed, read-only).

P5 (D6 integration, re-confirmed by D12 and by the L1 baseline) is a *process obligation*:
"any future release must re-run the hash check".  This script turns that obligation into an
executable gate.  It

  * hashes every regular file under the audited tree (default ``release/``), excluding
    ``.lake/`` (the build tree is not a released source);
  * compares against every historical accepted manifest in this project:
      - D13 ``final-release-hashes.txt``            (462 files, post-integration)
      - D13 ``base-release-hashes-preintegration``  (286 files)
      - D6  ``weekly-release-manifest.json``        (63 files)
      - D12 ``d12-semantic-ledger.json``            (66 lean files)
  * verifies the pins (``lean-toolchain``, ``lakefile.toml``, ``lake-manifest.json``);
  * writes a JSON report and a human summary;
  * exits **0** only when no recorded file is changed or absent, **1** on any drift
    (changed / absent / unreadable), **2** on usage or IO error.

Extra files that appear after a baseline are reported as ``added_since_baseline`` and are
not fatal by default, because a release is allowed to grow; ``--fail-on-added`` makes them
fatal, which is the right mode when auditing a *frozen* snapshot (e.g. the M1 baseline).

Usage:
    python3 baseline/tools/p5_hash_gate.py                       # frozen release/ -> 0
    python3 baseline/tools/p5_hash_gate.py --fail-on-added       # frozen release/ -> 0
    python3 baseline/tools/p5_hash_gate.py --tree baseline/a1/patched-release
                                                                 # A1 patch -> 1 (drift)

Nothing outside this worktree is written; the shared manifests are read-only inputs.
"""
import argparse
import hashlib
import json
import os
import re
import sys
import time

WT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LONGRUN = "/data3/guoshaoyang/workdir/lean_poincare/longrun"
WORKTREES = os.path.join(LONGRUN, "worktrees")
D13 = os.path.join(WORKTREES, "D13-integrated-kernel-audit/audit-evidence")
D6M = os.path.join(WORKTREES, "D6_weekly_release/manifest/weekly-release-manifest.json")
D12M = os.path.join(WORKTREES, "D12-semantic-ledger/manifest/d12-semantic-ledger.json")

PINS = {
    "lean-toolchain": "8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88",
    "lakefile.toml": "da970151371760d04c15987e8b5cfbe426d835b581da5fba611df9d4473d22e1",
    "lake-manifest.json": "cbc45ee0bd591606b3bb5ba38c38e41f3d317c59f99cb2dfb0adc7d33b32c3d0",
}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def tree_files(root):
    out = {}
    for dirpath, dirnames, filenames in os.walk(root):
        if ".lake" in dirpath.split(os.sep):
            continue
        for f in filenames:
            p = os.path.join(dirpath, f)
            if os.path.islink(p) or not os.path.isfile(p):
                continue
            rel = os.path.relpath(p, root)
            out[rel] = sha256(p)
    return out


def parse_hashfile(path):
    res = {}
    if not os.path.exists(path):
        return res
    with open(path, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            m = re.match(r"^([0-9a-f]{64})\s+\.?/?(.+)$", line)
            if m:
                res[m.group(2)] = m.group(1)
    return res


def load_json(path):
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh)
    except Exception:
        return None


def manifests():
    """Return [(name, {relpath: sha256})] for the four accepted historical manifests."""
    out = []
    out.append(("D13-integrated-kernel-audit/final-release-hashes.txt",
                parse_hashfile(os.path.join(D13, "final-release-hashes.txt"))))
    out.append(("D13-integrated-kernel-audit/base-release-hashes-preintegration.txt",
                parse_hashfile(os.path.join(D13, "base-release-hashes-preintegration.txt"))))
    d6 = load_json(D6M) or {}
    d6f = {}
    for e in (d6.get("package", {}) or {}).get("files", []) or []:
        if isinstance(e, dict) and "path" in e:
            d6f[e["path"]] = e.get("sha256")
    out.append(("D6-weekly-release/package.files", d6f))
    d12 = load_json(D12M) or {}
    d12f = dict((d12.get("source_hashes", {}) or {}).get("package_lean_files", {}) or {})
    out.append(("D12-semantic-ledger/package_lean_files", d12f))
    return out


def main():
    ap = argparse.ArgumentParser(description="P5 fail-closed release hash gate")
    ap.add_argument("--tree", default=os.path.join(WT, "release"),
                    help="source tree to audit (default: <worktree>/release)")
    ap.add_argument("--out", default=os.path.join(WT, "baseline/logs/p5-hash-gate.json"),
                    help="JSON report path")
    ap.add_argument("--fail-on-added", action="store_true",
                    help="treat files not recorded by any manifest as fatal drift")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()

    root = os.path.abspath(args.tree)
    if not os.path.isdir(root):
        print("p5-hash-gate: ERROR tree not found: %s" % root, file=sys.stderr)
        return 2

    t0 = time.time()
    current = tree_files(root)
    comparisons = []
    drift = []

    for name, recorded in manifests():
        if not recorded:
            drift.append({"kind": "manifest-unreadable", "manifest": name})
            comparisons.append({"manifest": name, "recorded": 0, "readable": False})
            continue
        changed, absent, matched = [], [], 0
        for rel, h in sorted(recorded.items()):
            cur = current.get(rel)
            if cur is None:
                absent.append(rel)
            elif cur != h:
                changed.append({"path": rel, "recorded": h, "current": cur})
            else:
                matched += 1
        added = sorted(set(current) - set(recorded))
        comparisons.append({
            "manifest": name,
            "recorded": len(recorded),
            "matched": matched,
            "changed": changed,
            "absent": absent,
            "added_count": len(added),
        })
        for c in changed:
            drift.append({"kind": "changed", "manifest": name, "path": c["path"],
                          "recorded": c["recorded"], "current": c["current"]})
        for a in absent:
            drift.append({"kind": "absent", "manifest": name, "path": a})

    pins = []
    for rel, expected in sorted(PINS.items()):
        p = os.path.join(root, rel)
        if not os.path.isfile(p):
            actual = None
        else:
            actual = sha256(p)
        ok = actual == expected
        pins.append({"path": rel, "expected": expected, "current": actual, "ok": ok})
        if not ok:
            drift.append({"kind": "pin-mismatch", "path": rel,
                          "expected": expected, "current": actual})

    # added relative to the *union* of all manifests, plus per-manifest counts above
    union = set()
    for _, recorded in manifests():
        union |= set(recorded)
    added_vs_union = sorted(set(current) - union)
    if args.fail_on_added and added_vs_union:
        for a in added_vs_union:
            drift.append({"kind": "added", "path": a})

    report = {
        "gate": "P5-source-hash",
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "tree": root,
        "file_count": len(current),
        "fail_on_added": bool(args.fail_on_added),
        "comparisons": comparisons,
        "pins": pins,
        "added_vs_union_of_manifests": added_vs_union,
        "drift": drift,
        "verdict": "PASS" if not drift else "FAIL",
        "wall_seconds": round(time.time() - t0, 2),
    }
    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    with open(args.out, "w", encoding="utf-8") as fh:
        json.dump(report, fh, indent=1)

    if not args.quiet:
        print("p5-hash-gate tree=%s files=%d -> %s (%d drift items)"
              % (root, len(current), report["verdict"], len(drift)))
        for c in comparisons:
            print("  %-58s recorded=%-4d matched=%-4d changed=%-3d absent=%-3d added=%d"
                  % (c["manifest"], c["recorded"], c["matched"], len(c["changed"]),
                     len(c["absent"]), c["added_count"]))
        for d in drift[:40]:
            if d["kind"] == "changed":
                print("  DRIFT changed  %s" % d["path"])
            elif d["kind"] == "absent":
                print("  DRIFT absent   %s (%s)" % (d["path"], d["manifest"]))
            elif d["kind"] == "pin-mismatch":
                print("  DRIFT pin      %s" % d["path"])
            else:
                print("  DRIFT %s %s" % (d["kind"], d.get("path", d.get("manifest", ""))))
        print("  report: %s" % args.out)
    return 0 if not drift else 1


if __name__ == "__main__":
    sys.exit(main())
