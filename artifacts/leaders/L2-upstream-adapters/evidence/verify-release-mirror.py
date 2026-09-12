#!/usr/bin/env python3
"""Verify a local release mirror against a reference sha256 manifest.

Usage:
  verify-release-mirror.py <release-root> <reference-manifest.json> [out.json]

The reference manifest must contain a `current_hashes` object mapping
path-relative-to-release-root -> sha256 (the schema used by
L1-lean-baseline/baseline/reconcile/source-hash-drift.json).  The whole local
tree is hashed (excluding `.lake`, `.git` and `logs`), so both changed files and
extra/missing files are reported.  Exit code is non-zero on any difference.

This is a *read-only* check of the L2 worktree's own release mirror; it never
writes to the reference worktree.
"""
import hashlib
import json
import sys
from pathlib import Path

EXCLUDE_DIRS = {".lake", ".git", "logs"}


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def walk(root: Path) -> dict:
    out = {}
    for p in sorted(root.rglob("*")):
        if not p.is_file():
            continue
        rel = p.relative_to(root)
        if any(part in EXCLUDE_DIRS for part in rel.parts):
            continue
        out[str(rel)] = sha256(p)
    return out


def main() -> int:
    root = Path(sys.argv[1]).resolve()
    ref = json.loads(Path(sys.argv[2]).read_text())
    expected = ref["current_hashes"]
    actual = walk(root)

    missing = sorted(set(expected) - set(actual))
    extra = sorted(set(actual) - set(expected))
    changed = sorted(k for k in set(expected) & set(actual) if expected[k] != actual[k])

    report = {
        "release_root": str(root),
        "reference_manifest": str(Path(sys.argv[2]).resolve()),
        "reference_generated_at": ref.get("generated_at"),
        "reference_file_count": len(expected),
        "mirror_file_count": len(actual),
        "matched": len(expected) - len(missing) - len(changed),
        "changed": changed,
        "missing": missing,
        "extra": extra,
        "local_hashes": actual,
    }
    if len(sys.argv) > 3:
        Path(sys.argv[3]).write_text(json.dumps(report, indent=2) + "\n")

    print(f"release mirror: {root}")
    print(f"reference files: {len(expected)}, mirror files: {len(actual)}, matched: {report['matched']}")
    for kind in ("changed", "missing", "extra"):
        if report[kind]:
            print(f"{kind.upper()} ({len(report[kind])}):")
            for k in report[kind][:20]:
                print(f"  {k}")
    if changed or missing or extra:
        print("RELEASE-MIRROR CHECK FAILED")
        return 1
    print("RELEASE-MIRROR CHECK PASSED: byte-identical to the reference manifest")
    return 0


if __name__ == "__main__":
    sys.exit(main())
