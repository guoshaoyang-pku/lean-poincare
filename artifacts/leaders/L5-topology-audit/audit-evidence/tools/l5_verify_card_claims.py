#!/usr/bin/env python3
"""L5 topology audit — fail-closed self-check of the result card's headline numbers.

Compares `longrun/results/L5-topology-audit.json` against the machine-produced evidence
(`audit-evidence/audit-summary.json`, `perfile-check.json`, `collisions.json`,
`forbidden-scan.json`) and fails on any mismatch.  This makes the card's claims
re-checkable without trusting the prose.

Usage: python3 l5_verify_card_claims.py <worktree-root>
"""
import json
import pathlib
import sys

wt = pathlib.Path(sys.argv[1]).resolve()
ev = wt / "audit-evidence"
card = json.loads((wt / "longrun" / "results" / "L5-topology-audit.json").read_text())
summary = json.loads((ev / "audit-summary.json").read_text())
perfile = json.loads((ev / "perfile-check.json").read_text())
coll = json.loads((ev / "collisions.json").read_text())
scan = json.loads((ev / "forbidden-scan.json").read_text())

checks = {
    "verdict_recorded": card["verdict"] in ("TASK_DONE", "TASK_BLOCKED"),
    "audit_assertions_ok": summary["assertions_ok"] is True,
    "passA_declarations": card["axiom_audit"]["pass_A"]["declarations"] == int(summary["package_A"]["declarations"]),
    "passB_declarations": card["axiom_audit"]["pass_B"]["declarations"] == int(summary["package_B"]["declarations"]),
    "passA_failures_zero": int(summary["package_A"]["unexpected_project_axioms"]
                               if "unexpected_project_axioms" in summary["package_A"]
                               else summary["package_A"]["project_axiom_declarations_unexpected"]) == 0,
    "passB_failures_zero": int(summary["package_B"]["project_axiom_declarations_unexpected"]) == 0,
    "union_462": summary["module_coverage"]["modules_total"] == 462
                 and summary["module_coverage"]["union_covers_all"],
    "perfile_464_zero_failures": perfile["files"] == 464 and perfile["failures"] == 0,
    "collisions_58": coll["duplicate_declaration_names"] == 58 and len(coll["colliding_module_pairs"]) == 3,
    "scan_14_hits": scan["total_hits"] == 14,
    "blockers_open": card["blockers_open"] == ["M8", "A3", "I6", "I7"],
    "no_blocker_closed": card["blockers_closed"] == [],
    "poincare_not_proved": card["poincare_proved"] is False,
    "outbox_12": len(list((wt / "comms" / "outbox").glob("*.imported")))
                 + len(list((wt / "comms" / "outbox").glob("*.json"))) >= 12,
}
for k, v in checks.items():
    print(f"{'OK ' if v else 'FAIL'}  {k}")
print("ALL OK" if all(checks.values()) else "MISMATCH")
raise SystemExit(0 if all(checks.values()) else 1)
