#!/usr/bin/env python3
"""Record source hashes for the adapter package and the upstream snapshot.

Building the upstream packages *in place* creates ignored `.lake` build
directories inside the snapshot.  This script proves that no tracked source
file changed: it hashes every file below the snapshot except paths containing a
`.lake` component, and compares the `.lean` file/line counts against
`third_party/frenzymath/SOURCE.json`.

It also hashes the authored adapter/evidence files so the result card can cite
exact inputs.

Usage: source-hashes.py <worktree-root> <out-json>
"""
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(sys.argv[1]).resolve()
OUT = Path(sys.argv[2]).resolve()
SNAP = ROOT / "third_party" / "frenzymath" / "Poincare-Conjecture"
META = json.loads((ROOT / "third_party" / "frenzymath" / "SOURCE.json").read_text())


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def tracked_files(root: Path):
    for p in sorted(root.rglob("*")):
        if not p.is_file():
            continue
        if ".lake" in p.parts:
            continue
        yield p


def main():
    lean_files, lean_lines, all_files = 0, 0, 0
    digest = hashlib.sha256()
    for p in tracked_files(SNAP):
        all_files += 1
        rel = str(p.relative_to(SNAP))
        digest.update(rel.encode())
        digest.update(sha256(p).encode())
        if p.suffix == ".lean":
            lean_files += 1
            # SOURCE.json counts newline bytes (matching the original
            # verify_frenzymath_snapshot.py), so files without a trailing
            # newline are not double-counted.
            lean_lines += p.read_bytes().count(b"\n")
    authored = {}
    for pattern in ("adapters/**/*.lean", "adapters/lakefile.lean", "adapters/lake-manifest.json",
                    "adapters/lean-toolchain", "evidence/*.py", "evidence/*.sh",
                    "checkpoint.json", "research-brief-2026-09-11.md"):
        for p in sorted(ROOT.glob(pattern)):
            if p.is_file() and ".lake" not in p.parts:
                authored[str(p.relative_to(ROOT))] = sha256(p)
    out = {
        "upstream": {
            "root": "third_party/frenzymath/Poincare-Conjecture",
            "commit": META["commit"],
            "tracked_file_count": all_files,
            "expected_tracked_file_count": META["tracked_file_count"],
            "lean_file_count": lean_files,
            "expected_lean_file_count": META["lean_file_count"],
            "lean_line_count": lean_lines,
            "expected_lean_line_count": META["lean_line_count"],
            "source_tree_sha256": digest.hexdigest(),
            "sources_untouched": (
                all_files == META["tracked_file_count"]
                and lean_files == META["lean_file_count"]
                and lean_lines == META["lean_line_count"]),
            "note": ".lake build artifacts are excluded; they are ignored by upstream .gitignore and are the output of building in place.",
        },
        "authored": authored,
    }
    OUT.write_text(json.dumps(out, indent=1))
    up = out["upstream"]
    print(json.dumps(up, indent=1))
    print(f"authored files hashed: {len(authored)}")
    return 0 if up["sources_untouched"] else 1


if __name__ == "__main__":
    sys.exit(main())
