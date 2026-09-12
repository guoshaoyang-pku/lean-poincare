#!/usr/bin/env python3
"""D13 integrated kernel audit: build a collision-checked integrated snapshot.

Copies D11 additions (from the six D11 sibling worktrees) and D12 additions
(from the fourteen D12 terminal input snapshots) into ./release/, without
touching any pre-existing file.  Every copied file is byte-verified against
its source and recorded in a provenance manifest with sha256.

Refuses to overwrite an existing file.  Refuses conflicting same-path sources.
"""
import hashlib
import json
import os
import shutil
import sys
from pathlib import Path

WT = Path("/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-integrated-kernel-audit")
REL = WT / "release"
SIB = Path("/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees")
TERMINAL = WT / "input" / "terminal"
EVID = WT / "audit-evidence"

D11_SOURCES = {
    "D11-bochner-manifold": "BochnerManifold",
    "D11-comparison-geometry-models": "ComparisonModels",
    "D11-heat-kernel-manifold-bridge": "HeatKernelBridge",
    "D11-maximum-principle-tensor": "MaximumPrincipleTensor",
    "D11-reduced-volume-euclidean": "ReducedVolume",
    "D11-spectral-torus": "SpectralTorus",
}


def sha256(p: Path) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main() -> int:
    plan = []  # (src, dst_rel, origin)
    for wt, sub in D11_SOURCES.items():
        srcroot = SIB / wt / "release" / "Poincare" / "D11" / sub
        if not srcroot.is_dir():
            print(f"FATAL: missing D11 source {srcroot}")
            return 2
        for f in sorted(srcroot.rglob("*.lean")):
            plan.append((f, Path("Poincare") / "D11" / sub / f.relative_to(srcroot), f"D11:{wt}"))

    for taskdir in sorted(TERMINAL.iterdir()):
        if not taskdir.name.startswith("D12-"):
            continue
        srcroot = taskdir / "release" / "Poincare" / "D12"
        if not srcroot.is_dir():
            print(f"FATAL: missing D12 source {srcroot}")
            return 2
        for f in sorted(srcroot.rglob("*.lean")):
            plan.append((f, Path("Poincare") / "D12" / f.relative_to(srcroot), f"D12:{taskdir.name}"))

    # collision + conflict detection
    by_dst = {}
    conflicts = []
    for src, dst, origin in plan:
        s = sha256(src)
        if dst in by_dst:
            prev_src, prev_hash, prev_origin = by_dst[dst]
            if prev_hash != s:
                conflicts.append({"dst": str(dst), "a": prev_origin, "b": origin,
                                  "hash_a": prev_hash, "hash_b": s})
        else:
            by_dst[dst] = (src, s, origin)
    if conflicts:
        print("FATAL: conflicting sources for same destination:")
        for c in conflicts:
            print(" ", c)
        return 3

    existing = []
    for dst in by_dst:
        tgt = REL / dst
        if tgt.exists():
            existing.append(str(dst))
    if existing:
        print("FATAL: refusing to overwrite existing files:")
        for e in existing:
            print(" ", e)
        return 4

    # copy + verify
    records = []
    for dst, (src, s, origin) in sorted(by_dst.items(), key=lambda kv: str(kv[0])):
        tgt = REL / dst
        tgt.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, tgt)
        t2 = sha256(tgt)
        if t2 != s:
            print(f"FATAL: copy hash mismatch {dst}")
            return 5
        records.append({"path": str(dst), "sha256": s, "origin": origin,
                        "source_path": str(src.relative_to(SIB)) if str(src).startswith(str(SIB)) else str(src.relative_to(WT))})

    EVID.mkdir(parents=True, exist_ok=True)
    out = {
        "schema": "d13-integrated-snapshot-provenance-v1",
        "file_count": len(records),
        "origins": sorted({r["origin"] for r in records}),
        "files": records,
    }
    (EVID / "snapshot-provenance.json").write_text(json.dumps(out, indent=1) + "\n")
    print(f"OK: copied {len(records)} files, no collisions, all hashes verified.")
    from collections import Counter
    for k, v in sorted(Counter(r["origin"] for r in records).items()):
        print(f"  {k}: {v}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
