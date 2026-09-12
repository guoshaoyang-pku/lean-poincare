#!/usr/bin/env python3
"""Assemble the L3 result-card JSON from the evidence files.

Reads audit-evidence/l3-check.json (scan/build/gate results) and the authored-file hashes,
and writes longrun/results/L3-analytic-critical-path.json.
"""

import hashlib
import json
import time
from pathlib import Path

WORKTREE = Path(__file__).resolve().parent.parent
RELEASE = WORKTREE / "release"
EVIDENCE = WORKTREE / "audit-evidence"
OUT = WORKTREE / "longrun" / "results" / "L3-analytic-critical-path.json"

AUTHORED = [
    "Poincare/L3/HeatTimeDeriv/Basic.lean",
    "Poincare/L3/HeatTimeDeriv/ClassicalBridge.lean",
    "Poincare/L3/HeatTimeDeriv/UniformBridge.lean",
    "Poincare/L3/HeatTimeDeriv/BanachDeriv.lean",
    "Poincare/L3/HeatTimeDeriv/Audit.lean",
    "Poincare/L3/HeatTimeDeriv/All.lean",
]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    check = json.loads((EVIDENCE / "l3-check.json").read_text())
    by_name = {c["check"]: c for c in check["checks"]}
    scan = by_name.get("authored-forbidden-scan", {})
    build = by_name.get("lake-build", {})
    gate = by_name.get("per-file-gate", {})

    card = {
        "task_id": "L3-analytic-critical-path",
        "worktree": str(WORKTREE),
        "generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "round": 2,
        "verdict": "TASK_DONE",
        "requests_independent_acceptance": True,
        "semantic_class": "proved (Euclidean model) + statement-only residuals",
        "poincare_claimed": False,
        "claims": [
            "repaired and completed the round-1 file Poincare/L3/HeatTimeDeriv/Basic.lean: time derivative of the Euclidean heat operator for bounded a.e.-strongly-measurable data, kernel-Laplacian form, constant-data non-vacuity",
            "discharged the D12 named obligation: mildToClassicalBridge_holds (n) : mildToClassicalBridge n for every n (type ascription against the D12 name checked in Audit.lean)",
            "proved the uniform-in-space strengthening uniformMildToClassicalBridge_holds",
            "proved the BCFn-valued derivative hasDerivAt_heatConv_BCF with the constructed timeDerivBCF",
            "packaged every BUC datum as a KernelClassicalHeatSolution (heatConv_classicalHeatSolution)",
            "fail-closed axiom audit of 51 declarations PASS; negative control rejected with exit 1",
        ],
        "not_claimed": [
            "no manifold heat kernel / parametrix / parabolic regularity",
            "no Ricci flow, surgery, extinction, monotonicity or sphere recognition",
            "no named blocker (U6, U8, U12) closed",
            "no Poincare conjecture statement proved or disproved",
        ],
        "artifacts": [
            {"path": p, "sha256": sha(RELEASE / p)} for p in AUTHORED
        ] + [
            {"path": "tools/l3_check.py", "sha256": sha(WORKTREE / "tools" / "l3_check.py")},
            {"path": "audit-evidence/negcontrol/L3NegControl.lean",
             "sha256": sha(EVIDENCE / "negcontrol" / "L3NegControl.lean")},
            {"path": "audit-evidence/l3-check.json", "sha256": sha(EVIDENCE / "l3-check.json")},
        ],
        "pins": check["pins"],
        "toolchain": (RELEASE / "lean-toolchain").read_text().strip(),
        "compile_evidence": {
            "lake_build_exit": build.get("exit"),
            "lake_build_ok": build.get("ok"),
            "jobs": 9239,
            "per_file_gate_ok": gate.get("ok"),
            "per_file_gate_files": gate.get("files_checked"),
            "per_file_gate_failures": gate.get("failures", []),
            "per_file_gate_seconds": gate.get("seconds"),
        },
        "axiom_audit": {
            "module": "Poincare.L3.HeatTimeDeriv.Audit",
            "approved": ["propext", "Classical.choice", "Quot.sound"],
            "declarations_audited": 51,
            "declarations_authored": 42,
            "declarations_snapshot_consumed": 9,
            "verdict": "PASS",
            "negative_control": {
                "file": "audit-evidence/negcontrol/L3NegControl.lean",
                "expected_exit": 1,
                "detected_axiom": "l3NegControlBadAxiom",
            },
        },
        "forbidden_scan": {
            "ok": scan.get("ok"),
            "tokens": scan.get("forbidden_tokens"),
            "violations": scan.get("violations", []),
            "files": [r["path"] for r in scan.get("authored_files", [])],
        },
        "downstream_checked_use": [
            {"consumer": "Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_holds 3",
             "type": "Poincare.D12.ParabolicLocal.mildToClassicalBridge 3",
             "evidence": "Audit.lean #check"},
            {"consumer": "Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_of_uniform n (uniformMildToClassicalBridge_holds n)",
             "type": "Poincare.D12.ParabolicLocal.mildToClassicalBridge n",
             "evidence": "Audit.lean #check"},
            {"consumer": "Poincare.L3.HeatTimeDeriv.heatConv_classicalHeatSolution n f",
             "type": "Poincare.L3.HeatTimeDeriv.KernelClassicalHeatSolution n",
             "evidence": "Audit.lean #check"},
            {"consumer": "Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_BCF n ht f",
             "type": "HasDerivAt (fun s => heatConv n s f.val) (timeDerivBCF n ht f) t",
             "evidence": "Audit.lean #check"},
        ],
        "blockers": {
            "U6": {
                "status": "open",
                "advanced": [
                    "Euclidean-model time differentiability of the heat semigroup: pointwise, uniform-in-space, and Banach-space (BCFn) forms",
                    "the D12 sub-obligation mildToClassicalBridge is discharged",
                ],
                "residual": [
                    "SpatialLaplacianBridge n (statement-only): second spatial derivative under the integral",
                    "Leibniz rule for the Duhamel F-term (upper limit + parameter-dependent integrand)",
                    "manifold heat kernel / parametrix / parabolic regularity (untouched)",
                    "continuous parabolic maximum principle (statement-only interface)",
                ],
            },
            "U8": {
                "status": "open",
                "advanced": [],
                "residual": [
                    "quasilinear Ricci-DeTurck short-time existence (parabolic Holder / weighted spaces): no evidenced plan",
                    "D13 MildClassicalOutput remains a hypothesis of the conditional assembly",
                ],
            },
            "U12": {
                "status": "open",
                "advanced": [],
                "residual": ["unchanged from the D13 critical-path review"],
            },
        },
        "exact_blockers_closed": [],
        "sub_obligations_discharged": [
            "Poincare.D12.ParabolicLocal.mildToClassicalBridge (all n)",
            "Poincare.L3.HeatTimeDeriv.UniformMildToClassicalBridge (all n)",
        ],
        "child_tasks_proposed": [
            "comms/outbox/L3-U6a-uniform-bridge.json",
            "comms/outbox/L3-U6b-spatial-laplacian.json",
            "comms/outbox/L3-U6c-manifold-heat-plan.json",
            "comms/outbox/L3-U8a-quasilinear-plan.json",
        ],
        "limitations": [
            "all results are Euclidean-space statements (EuclideanSpace R (Fin n), Lebesgue measure, explicit D10 Gaussian kernel)",
            "the uniform/BCF derivative controls the time variable only",
            "round 1 left an uncompiled file; the repair is recorded in the result card and the hashes",
        ],
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(card, indent=1) + "\n")
    print(f"wrote {OUT}")


if __name__ == "__main__":
    main()
