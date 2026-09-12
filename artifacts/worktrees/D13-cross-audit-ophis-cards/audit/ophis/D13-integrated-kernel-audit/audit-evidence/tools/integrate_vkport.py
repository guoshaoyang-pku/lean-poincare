#!/usr/bin/env python3
"""D13 audit — relay-gap recovery of the VKPort van Kampen cluster.

The D12-surgery-recognition result card reports a ported frenzymath van Kampen cluster
("release/Poincare/VKPort, 9 files, sorry-free, axioms clean") but the terminal input
snapshot relayed to D13 contains only Poincare/D12/SurgeryRecognition.  The 10 Lean files
(9 ported + VKProbe) are recovered byte-identically from the sibling worktree and appended
to the snapshot provenance with a distinct origin class so the report can separate them
from the 153 terminal-release files.

Refuses to proceed if a destination already exists with different bytes.
"""
import hashlib
import json
import shutil
import sys
from pathlib import Path

WT = Path("/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-integrated-kernel-audit")
REL = WT / "release"
SRC = Path("/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D12-surgery-recognition/release/Poincare/VKPort")
EVID = WT / "audit-evidence"
ORIGIN = "D12:D12-surgery-recognition/relay-gap:VKPort"


def sha256(p: Path) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def main() -> int:
    prov_path = EVID / "snapshot-provenance.json"
    prov = json.loads(prov_path.read_text())
    known = {r["path"] for r in prov["files"]}
    srcs = sorted(SRC.rglob("*.lean"))
    if not srcs:
        print("FATAL: no VKPort sources")
        return 2
    records = []
    for s in srcs:
        rel = Path("Poincare") / "VKPort" / s.relative_to(SRC)
        tgt = REL / rel
        h = sha256(s)
        if tgt.exists():
            if sha256(tgt) != h:
                print(f"FATAL: existing {rel} differs")
                return 3
        else:
            tgt.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(s, tgt)
            assert sha256(tgt) == h
        if str(rel) not in known:
            records.append({"path": str(rel), "sha256": h, "origin": ORIGIN,
                            "source_path": str(s.relative_to(SRC.parent.parent.parent))})
    prov["files"].extend(records)
    prov["files"].sort(key=lambda r: r["path"])
    prov["file_count"] = len(prov["files"])
    prov["origins"] = sorted({r["origin"] for r in prov["files"]})
    prov["relay_gap_note"] = (
        "The 10 VKPort Lean files are present in the D12-surgery-recognition sibling "
        "worktree and referenced by its result card, but absent from the relayed terminal "
        "release; the worktree README calls them 'EXPERIMENTAL, not part of the D12 audit "
        "deliverable'. They are copied byte-identically and audited with a distinct origin tag.")
    prov_path.write_text(json.dumps(prov, indent=1) + "\n")
    print(f"appended {len(records)} VKPort files; total {prov['file_count']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
