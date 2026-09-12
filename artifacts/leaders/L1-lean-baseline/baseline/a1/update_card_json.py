#!/usr/bin/env python3
"""Update longrun/results/L1-lean-baseline.json for the third invocation.

Adds the A1 restatement / P5 gate / independent replay evidence and refreshes the
blocker, acceptance and evidence sections.  Idempotent: re-running replaces the
`third_invocation` block rather than duplicating it.
"""
import hashlib
import json
import os
import time

WT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CARD = os.path.join(WT, "longrun", "results", "L1-lean-baseline.json")
A1E = os.path.join(WT, "baseline", "a1", "a1-evidence.json")
REPLAY = os.path.join(WT, "baseline", "c1", "replay-comparison.json")
A1 = os.path.join(WT, "baseline", "a1")


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def main():
    d = json.load(open(CARD))
    a1 = json.load(open(A1E))
    rp = json.load(open(REPLAY))

    d["updated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    d["verdict_scope"] = ("M1 baseline deliverable; A1 upstream restatement and P5 gate delivered as "
                          "constructed inputs pending independent semantic review/adoption; no "
                          "Poincare/Perelman claim made")

    d["third_invocation"] = {
        "invocation": ("third invocation, same worktree, no restart; entry re-verification 29/29; "
                       "executed the construction work of the queued children L1-C1/C2/C4"),
        "started_local": "2026-09-12T00:41+08:00",
        "a1_restatement": {
            "patch": "baseline/a1/a1-restatement.patch",
            "patch_sha256": a1["restatement"]["patch_sha256"],
            "patched_tree": "baseline/a1/patched-release (463 files: 462 frozen + SharpOnlyConsumers.lean)",
            "changed_files": a1["restatement"]["changed"],
            "added_files": a1["restatement"]["added"],
            "frozen_release_untouched": True,
            "restated_signatures": a1["restated_signatures"],
            "patched_build": a1["patched_build"],
            "patched_audits": a1["audits"],
            "downstream_consumers": {k: len(v) for k, v in a1["downstream_consumers"].items()},
            "sharp_only_consumer": ("Poincare.D7.EvolutionSharp.perelmanF_step_lt_at_threshold_one "
                                    "(c == 1) is untypeable against the old 1 < c hypothesis"),
            "evidence_bundle": "baseline/a1/a1-evidence.json",
            "closure_legs": a1["closure_legs"],
        },
        "p5_gate": {
            "script": "baseline/tools/p5_hash_gate.py",
            "frozen_run": {"verdict": "PASS", "drift": 0, "report": "baseline/logs/p5-hash-gate.json"},
            "patched_run": {"verdict": "FAIL", "changed": 7, "removed": 0,
                            "report": "baseline/a1/logs/p5-hash-gate-patched.json"},
        },
        "independent_replay": {
            "script": "baseline/c1/compare_replay.py",
            "report": "baseline/c1/replay-comparison.json",
            "replay_tree": "baseline/c1/replay-release",
            "build": rp["build"],
            "declarations": {"frozen": rp["declarations"]["frozen_rows"],
                             "replay": rp["declarations"]["replay_rows"],
                             "field_differences": len(rp["declarations"]["field_differences"])},
            "declaration_types": {"frozen": rp["types"]["frozen"], "replay": rp["types"]["replay"],
                                  "differences": len(rp["types"]["differences"])},
            "oleans": {"frozen": rp["oleans"]["frozen"], "replay": rp["oleans"]["replay"],
                       "byte_identical": rp["oleans"]["byte_identical"],
                       "path_embedded_differences": len(rp["oleans"]["path_embedded_differences"]),
                       "unexplained_differences": len(rp["oleans"]["unexplained_differences"])},
            "verdict": "REPLAY-IDENTICAL",
        },
        "queue_reconciliation": {
            "generated_at": "2026-09-11T16:48Z",
            "tasks_total": 135, "verified": 86, "running": 7, "queued": 40, "paused": 1,
            "blocked": 1, "with_card": 95, "without_card": 40, "flags": 8,
            "drift_report": "baseline/reconcile/queue-drift-20260911T164848Z.json",
        },
    }

    d["blockers"]["A1"] = {
        "status": "closure_ready_pending_independent_semantic_review_and_adoption",
        "restatement_delivered": a1["restatement"],
        "sharp_only_downstream_consumer": "Poincare.D7.EvolutionSharp.perelmanF_step_lt_at_threshold_one",
        "independent_rebuild": ("patched tree built from scratch: lake build exit 0, 9340 jobs; frozen "
                                "AxiomAudit_G{1,2} and D7 ReleaseAudit re-run PASS"),
        "semantic_review": "NOT self-certified; requested from the independent acceptor",
        "child": "L1-C2",
        "handoff": "comms/outbox/2026-09-12-L1-a1-restatement-handoff.md",
        "note": ("the D12 ledger closes A1 on upstream restatement; the restatement is constructed and "
                 "verified but not self-certified, and adoption into the accepted upstream release is "
                 "the remaining step"),
    }
    d["blockers"]["P5"] = {
        "status": "gate_delivered_recurring_obligation_now_executable",
        "gate": "baseline/tools/p5_hash_gate.py",
        "frozen_verdict": "PASS (0 drift, --fail-on-added)",
        "patched_verdict": "FAIL (exactly the 7 A1-changed files; fail-closed)",
        "child": "L1-C4",
        "note": "not self-closed: the gate must be adopted and re-run by the integrator on any future release",
    }
    d["blockers"]["M1"]["third_invocation"] = {
        "independent_replay_verdict": "REPLAY-IDENTICAL",
        "declaration_rows_identical": 12361,
        "declaration_types_identical": 12361,
        "oleans_byte_identical": 422,
        "oleans_path_embedded": 32,
        "oleans_unexplained": 0,
        "report": "baseline/c1/replay-comparison.json",
        "status": "replay evidence complete; available for independent acceptance (L1-C1)",
    }

    acc = d["acceptance"]
    acc["pinned_release_clean_build"]["third_invocation_second_tree"] = (
        "baseline/c1/replay-release: lake build exit 0, 9339 jobs, from the frozen sources")
    acc["fail_closed_axiom_audit"]["patched_tree_rerun"] = a1["audits"]["axiom_G1"]
    acc["fail_closed_axiom_audit"]["replay_tree_rerun"] = (
        "AxiomAudit_G1 PASS 12,071 declarations / G2 PASS 472 declarations (baseline/c1/logs/)")
    acc["downstream_checked_use_recorded"]["a1_sharp_only_consumer"] = (
        "Poincare.D7.EvolutionSharp.perelmanF_step_lt_at_threshold_one uses "
        "Poincare.Longrun.Evolution.perelmanF_step_lt (13 A1USE edges in baseline/a1/logs/a1-consumer-cone.log)")
    acc["source_hashes_recorded"]["p5_gate"] = "baseline/logs/p5-hash-gate.json (frozen PASS) + baseline/a1/logs/p5-hash-gate-patched.json (patched FAIL, expected)"

    d["findings"].append(
        "F8: olean bytes embed the absolute source path; a rebuild in a different directory is not "
        "byte-reproducible for the 32/454 modules that embed it (size delta 16/24 = 8-byte alignment "
        "of the 19-char path difference), while the other 422 are byte-identical and all 12,361 "
        "declaration rows and declaration types are identical. Same-path byte determinism re-confirmed "
        "(377/377 prior; Compat.lean reproduced byte-for-byte with the exact lake flags). No soundness impact.")

    ev = d["evidence_files"]
    ev["a1_patch"] = "baseline/a1/a1-restatement.patch"
    ev["a1_patch_sha256"] = a1["restatement"]["patch_sha256"]
    ev["a1_patched_drift"] = "baseline/a1/patched-drift.json"
    ev["a1_evidence_bundle"] = "baseline/a1/a1-evidence.json"
    ev["a1_patched_build_log"] = "baseline/a1/logs-patched-build.log"
    ev["a1_patched_axiom_audit_G1"] = "baseline/a1/logs/a1-axiom-audit-G1.log"
    ev["a1_patched_axiom_audit_G2"] = "baseline/a1/logs/a1-axiom-audit-G2.log"
    ev["a1_d7_release_audit"] = "baseline/a1/logs/a1-d7-release-audit.log"
    ev["a1_probe"] = "baseline/a1/logs/a1-probe.log"
    ev["a1_consumer_cone"] = "baseline/a1/logs/a1-consumer-cone.log"
    ev["p5_gate_script"] = "baseline/tools/p5_hash_gate.py"
    ev["p5_gate_frozen"] = "baseline/logs/p5-hash-gate.json"
    ev["p5_gate_patched"] = "baseline/a1/logs/p5-hash-gate-patched.json"
    ev["replay_comparison"] = "baseline/c1/replay-comparison.json"
    ev["replay_tree"] = "baseline/c1/replay-release"
    ev["replay_audit_logs"] = ["baseline/c1/logs/replay-axiom-audit-G1.log",
                               "baseline/c1/logs/replay-axiom-audit-G2.log"]
    ev["type_audit_drivers"] = ["baseline/c1/typeaudit/TypeAudit_G1.lean",
                                "baseline/c1/typeaudit/TypeAudit_G2.lean"]
    ev["type_audit_logs"] = ["baseline/c1/logs/frozen-type-audit-G1.log",
                             "baseline/c1/logs/frozen-type-audit-G2.log",
                             "baseline/c1/logs/replay-type-audit-G1.log",
                             "baseline/c1/logs/replay-type-audit-G2.log"]

    d["non_claims"] = [
        "no theorem of Riemannian geometry, Ricci flow, surgery, extinction or sphere recognition is proved, strengthened or promoted by this task",
        "no named blocker (M1, A1, P5) is self-certified closed; A1/P5 are closure-ready pending independent semantic review and adoption",
        "the frozen release/ tree was not modified; the A1 restatement lives on a byte-copy (baseline/a1/patched-release) plus a patch",
        "the semantic classifications marked (upstream) are prior-task claims, not re-derived here",
    ]

    json.dump(d, open(CARD, "w"), indent=1)
    print("updated", CARD)
    print("card sha256", sha256(CARD))


if __name__ == "__main__":
    main()
