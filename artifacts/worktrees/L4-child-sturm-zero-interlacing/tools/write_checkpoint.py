#!/usr/bin/env python3
"""
Append a checkpoint to checkpoint.json (history is preserved, never rewritten).

Usage: write_checkpoint.py "<label>" [status]

Reads the current evidence bundle, appends a checkpoint entry with the deliverable
source hashes, gate verdict, axiom-audit summary and compile exits.
"""
import hashlib
import json
import os
import sys
from datetime import datetime, timezone

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EV = os.path.join(ROOT, "evidence")
CP = os.path.join(ROOT, "checkpoint.json")

DELIVERABLES = [
    "release/Poincare/L4/GeodesicComparison/SturmInterlacing.lean",
    "release/Poincare/L4/GeodesicComparison/SturmInterlacingConjugateCrossCheck.lean",
    "release/Poincare/L4/GeodesicComparison/SturmInterlacingAxiomAudit.lean",
    "negcontrol/SturmInterlacingNegativeControl.lean",
    "tools/run_sturm_gates.py",
    "tools/make_result_card.py",
    "tools/final_integrity_check.py",
    "longrun/results/L4-child-sturm-zero-interlacing.md",
    "longrun/results/L4-child-sturm-zero-interlacing.json",
]


def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for c in iter(lambda: f.read(1 << 16), b""):
            h.update(c)
    return h.hexdigest()


def main():
    label = sys.argv[1] if len(sys.argv) > 1 else "checkpoint"
    status = sys.argv[2] if len(sys.argv) > 2 else "in-progress"
    ver = json.load(open(os.path.join(EV, "verification.json")))
    ax = json.load(open(os.path.join(EV, "axiom-report.json")))
    old = json.load(open(CP)) if os.path.exists(CP) else {"checkpoints": []}
    entries = old.get("checkpoints", [])
    n = len(entries) + 1
    hashes = {}
    for rel in DELIVERABLES:
        p = os.path.join(ROOT, rel)
        hashes[rel] = sha(p) if os.path.exists(p) else None
    entry = {
        "id": f"cp{n}",
        "at": datetime.now(timezone.utc).isoformat(),
        "label": label,
        "status": status,
        "deliverable_hashes": hashes,
        "gates": ver["verdict"],
        "failures": ver["failures"],
        "compile_exits": {s["step"]: s.get("exit_code") for s in ver["steps"]},
        "axiom_audit": {
            "verdict": ax["verdict"],
            "declarations": ax["reported_declarations"],
            "missing": ax["missing"],
            "violations": ax["violations"],
            "allowed_cone": ax["allowed_cone"],
        },
        "input_hash_verdict": json.load(
            open(os.path.join(EV, "input-hash-verification.json")))["verdict"],
    }
    entries.append(entry)
    out = {
        "schema": "l4-child-sturm-zero-interlacing/checkpoint-v1",
        "task_id": "L4-child-sturm-zero-interlacing",
        "worktree": ROOT,
        "checkpoints": entries,
        "current": {"latest": entry["id"], "status": status, "gates": ver["verdict"]},
    }
    with open(CP, "w") as f:
        json.dump(out, f, indent=1)
    print(json.dumps({"wrote": CP, "id": entry["id"], "gates": ver["verdict"],
                      "axioms": ax["reported_declarations"]}, indent=1))


if __name__ == "__main__":
    main()
