#!/usr/bin/env python3
"""
Final integrity check: cross-verify the result card, checkpoint history, evidence bundle
and the on-disk sources.  Writes evidence/final-integrity.json and exits nonzero on any
mismatch.
"""
import hashlib
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EV = os.path.join(ROOT, "evidence")


def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for c in iter(lambda: f.read(1 << 16), b""):
            h.update(c)
    return h.hexdigest()


checks = []


def check(name, ok, detail=""):
    checks.append({"check": name, "ok": bool(ok), "detail": detail})
    print(f"[{'OK ' if ok else 'FAIL'}] {name} {detail}")


card_md = os.path.join(ROOT, "longrun", "results", "L4-child-sturm-zero-interlacing.md")
card_json = os.path.join(ROOT, "longrun", "results", "L4-child-sturm-zero-interlacing.json")
cp = json.load(open(os.path.join(ROOT, "checkpoint.json")))
card = json.load(open(card_json))
ver = json.load(open(os.path.join(EV, "verification.json")))
ax = json.load(open(os.path.join(EV, "axiom-report.json")))

check("card_md_exists", os.path.exists(card_md))
md = open(card_md).read()
check("card_ends_task_done", md.rstrip().endswith("**TASK_DONE**"))
check("card_json_verdict", card["verdict"] == "TASK_DONE", card["verdict"])
check("gates_verdict", ver["verdict"] == "PASS", str(ver["failures"]))
check("axiom_verdict", ax["verdict"] == "PASS",
      f"{ax['reported_declarations']} declarations, missing={ax['missing']}, "
      f"violations={ax['violations']}")

# every audited declaration reported exactly once
audit_src = open(os.path.join(ROOT, "release", "Poincare", "L4", "GeodesicComparison",
                              "SturmInterlacingAxiomAudit.lean")).read()
expected = re.findall(r"#print axioms (\S+)", audit_src)
check("axiom_audit_covers_all",
      len(expected) == ax["expected_declarations"] == ax["reported_declarations"]
      and not ax["missing"] and not ax["violations"],
      f"expected={len(expected)}")

# card module hashes match disk
MODULE_PATHS = {
    "core": "release/Poincare/L4/GeodesicComparison/SturmInterlacing.lean",
    "cross_check": "release/Poincare/L4/GeodesicComparison/SturmInterlacingConjugateCrossCheck.lean",
    "axiom_audit": "release/Poincare/L4/GeodesicComparison/SturmInterlacingAxiomAudit.lean",
    "negative_control": "negcontrol/SturmInterlacingNegativeControl.lean",
    "gate_driver": "tools/run_sturm_gates.py",
}
bad = []
for key, h in card["module_hashes"].items():
    p = os.path.join(ROOT, MODULE_PATHS[key])
    if not os.path.exists(p) or sha(p) != h:
        bad.append(key)
check("card_module_hashes_current", not bad, str(bad))

# latest checkpoint records the card hashes
latest = cp["checkpoints"][-1]
card_hashes = {k: v for k, v in latest["deliverable_hashes"].items()
               if k.startswith("longrun/results/")}
bad2 = [rel for rel, h in card_hashes.items()
        if h is None or sha(os.path.join(ROOT, rel)) != h]
check("checkpoint_records_final_card", not bad2, f"{latest['id']} {bad2}")
check("checkpoint_history_grows", len(cp["checkpoints"]) >= 4,
      f"{len(cp['checkpoints'])} entries")
check("checkpoint_latest_gates", latest["gates"] == "PASS", latest["gates"])

# forbidden scan
scan = json.load(open(os.path.join(EV, "forbidden-scan.json")))
check("forbidden_scan_clean", scan["hard_match_count"] == 0 and scan["soft_match_count"] == 0,
      f"hard={scan['hard_match_count']} soft={scan['soft_match_count']}")

out = {"checks": checks, "all_ok": all(c["ok"] for c in checks)}
with open(os.path.join(EV, "final-integrity.json"), "w") as f:
    json.dump(out, f, indent=1)
print(json.dumps({"all_ok": out["all_ok"]}, indent=1))
sys.exit(0 if out["all_ok"] else 1)
