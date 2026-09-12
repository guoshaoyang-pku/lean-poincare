#!/usr/bin/env python3
"""Apply the fourth-invocation update to longrun/results/L1-lean-baseline.json.

Nested merges (adds only, never deletes prior invocation content).
"""
import json
import os

WT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CARD = os.path.join(WT, "longrun/results/L1-lean-baseline.json")

with open(CARD) as f:
    card = json.load(f)

card["verdict_scope"] = (
    "M1 baseline deliverable complete and independently replayed (V1) with an independent "
    "semantic review (V4; corrections C1-C5 adopted), A1 upstream restatement independently "
    "reviewed (V2) as closure-ready for adoption, P5 gate independently reproduced (V3); no named "
    "blocker self-certified closed; no Poincare/Perelman claim made"
)
card["updated_at"] = "2026-09-11T17:35:00Z"

card["fourth_invocation"] = {
    "invocation": "fourth invocation of L1-lean-baseline, same worktree; prior deliverable preserved, nothing restarted",
    "started_local": "2026-09-12T01:08+08:00",
    "entry_reverification": {
        "script": "baseline/tools/verify_baseline.py",
        "report": "baseline/logs/verify-baseline-entry-20260912T0118Z.json",
        "checks": 29,
        "passed": 27,
        "failed": 2,
        "failures_explained_and_repaired": ["F9a stale MANIFEST entry for baseline/logs/p5-hash-gate.json",
                                             "F9b accidental clobber of baseline/logs/forbidden-scan.json (repaired byte-for-byte)"],
        "note": "the two failures were artifact-state defects, not evidence drift; release/ was 462/462 throughout"
    },
    "repaired_defects": {
        "F9a": {
            "severity": "artifact-state",
            "what": "baseline/logs/p5-hash-gate.json was written 21 s after MANIFEST.json at the end of invocation 3, leaving its recorded sha256 stale; only generated_at differs, verdict unchanged PASS/0-drift",
            "repair": "report regenerated before the final MANIFEST regeneration in this invocation"
        },
        "F9b": {
            "severity": "self-inflicted artifact clobber, fully repaired",
            "what": "an accidental `forbidden_scan.py --help` invocation treated --help as the tree path and overwrote baseline/logs/forbidden-scan.json with a 0-file report at 01:10:44",
            "repair": "original bytes recovered exactly by exhaustive search over the only varying field (generated_at; window 15:00-15:59Z 2026-09-11); recovered timestamp 2026-09-11T15:19:38Z; sha256 again 07e579597c18fdc36786215bf044554384830b7f04e9a2173208c359d7da9891 (matches the first-invocation record); no evidence lost"
        }
    },
    "fresh_same_path_rebuild": {
        "moved_aside": "baseline/pre-rebuild/build-tree-inv1-20260912T0118Z (454 oleans preserved)",
        "cmd": "lake build",
        "cwd": "release/",
        "exit": 0,
        "jobs": 9339,
        "wall": "2m26s",
        "errors": 0,
        "sorry_lines": 0,
        "lint_warnings": 170,
        "log": "baseline/logs/fourth/clean-build.log",
        "olean_same_path_comparison": {
            "report": "baseline/logs/fourth/olean-same-path-comparison.json",
            "oleans": 454,
            "identical": 454,
            "differing": 0,
            "unexplained": 0,
            "note": "upgrades the determinism claim from 377/377 (invocation 1) to 454/454 at the same path"
        },
        "drivers": {
            "D6LedgerProbe": {"exit": 0, "checks": 262, "log": "baseline/logs/fourth/lean-D6LedgerProbe.log"},
            "ReleaseClaims": {"exit": 0, "checks": 193, "log": "baseline/logs/fourth/lean-ReleaseClaims.log"},
            "note": "outputs byte-identical to the frozen logs apart from trailing time(1) lines"
        },
        "in_build_gates": {
            "D6AUDIT": "VERDICT PASS",
            "D13FULLVERDICT": "PASS - every package declaration depends only on {propext, Classical.choice, Quot.sound}",
            "D13STMT": {"theorems_scanned": 3196, "hyp_eq_concl": 0, "hyp_defeq_concl": 0, "concl_in_hyp": 0,
                        "scope": "Poincare.D11/D12/VKPort only (see finding F10)"},
            "D7SharpReleaseAudit": {"exit": 0, "verdict": "PASS", "log": "baseline/logs/fourth/d7-release-audit.log"}
        }
    },
    "fresh_audits": {
        "forbidden_scan": {"files_scanned": 456, "declaration_form_hits": 2, "verdict": "REVIEW",
                           "log": "baseline/logs/fourth/forbidden-scan.json",
                           "note": "exactly the two documented negative controls; counts identical to the frozen scan (only generated_at differs)"},
        "axiom_audit_G1": {"exit": 0, "verdict": "L1AXVERDICT PASS", "declarations": 12071, "modules_with_declarations": 333,
                           "declared_modules_imported": 440, "dep_edges": 47098, "unexpected_violations": 0,
                           "expected_negative_controls_seen": 3, "sorry": 0, "unsafe": 0, "native": 0, "collect_failures": 0,
                           "log": "baseline/logs/fourth/axiom-audit-G1.log"},
        "axiom_audit_G2": {"exit": 0, "verdict": "L1AXVERDICT PASS", "declarations": 472, "modules_with_declarations": 10,
                           "declared_modules_imported": 14, "dep_edges": 1749, "unexpected_violations": 0,
                           "log": "baseline/logs/fourth/axiom-audit-G2.log"},
        "note": "both fresh audit logs are byte-identical to the frozen logs apart from trailing time(1) lines"
    },
    "independent_verification": {
        "note": "four fresh verifier-agent contexts, read-only against the frozen artifacts, outputs under their own directories; these supply the independent legs of the four-part closure rule",
        "V1_m1_replay": {
            "verdict": "INDEPENDENT-REPLAY-IDENTICAL",
            "report_json": "baseline/v1-independent/independent-report.json",
            "report_json_sha256": "308c3fa8a7cc26e79f0edd7454f1c7b8829b981ff9b92c25f6730faf18dac3e0",
            "highlights": {"fresh_copy_files": 462, "fresh_copy_lean": 456, "build_exit": 0, "jobs": 9339, "oleans": 454,
                           "declaration_rows_matched": 12361, "rows_total": 12361, "independent_parser": True,
                           "type_dumps_byte_identical": True, "olean_identical_vs_c1": 422, "olean_path_embedded": 32,
                           "olean_unexplained": 0, "print_axioms_compared": 610, "print_axioms_agreements": 610,
                           "print_axioms_disagreements": 0}
        },
        "V2_a1_semantic_review": {
            "verdict": "INDEPENDENT-REVIEW-PASS",
            "report_json": "baseline/a1/review-independent/review.json",
            "report_json_sha256": "1f26bc993ff2140f77c5ce5f604d9938518bd620f7daae018f5b41b0579bde34",
            "framing_corrections_adopted": [
                "the c=1 propositions already existed in the frozen release (D7.EvolutionSharp.gibbsTerm_strictAnti_one, D4Audit.*_of_one_le, strict_step_positive_control, Witnesses.sharpWitness_strict_decrease), so the A1 patch adds no new mathematical content - its value is upstream alignment of the promoted declarations, which is what the D12 closure rule requires",
                "the patched-tree P5 FAIL in a1-evidence.json is EXPECTED source-hash drift (7 changed x 4 manifests + 1 added = 22 manifest-level entries), not an unresolved gate"
            ],
            "independently_reproduced": "patch re-applied to a fresh byte-copy (exit 0; byte-identical to patched-release), c=1 gluing proof re-derived, sum step re-derived, consumer unification failure confirmed, IndepReviewProbe.lean exit 0, cones {propext, Classical.choice, Quot.sound}"
        },
        "V3_p5_hash_and_patch": {
            "verdicts": ["INDEPENDENT-HASH-CHECK-PASS", "INDEPENDENT-PATCH-DRIFT-MATCH"],
            "report_json": "baseline/v3-independent/report.json",
            "report_json_sha256": "0488d203fafe6eb0d6e006d2c47fe2df6d487aea571f2d8b476cf7ced415a487",
            "highlights": {"own_checker_written_before_reading_gate": True, "manifests": {"D13_final": [462, 462, 0, 0], "D13_base": [286, 286, 0, 0], "D6": [63, 63, 0, 0], "D12": [66, 66, 0, 0]},
                           "pins_match": True, "patch_replay": "7 changed + 1 added + 0 removed", "whole_tree_diff_vs_patched_release": "empty",
                           "gate_agreement": "exact, 0 disagreements"}
        },
        "V4_card_semantic_review": {
            "verdict_pre_correction": "INDEPENDENT-SEMANTIC-REVIEW-FAIL",
            "report_json": "baseline/v4-independent/review.json",
            "basis": "narrow/non-semantic: 3 misstated strings (C1-C3) plus 2 citation/scope clarifications (C4-C5); all 10 semantic classifications defensible, all checked cones/counts reproduce, F1/F2/F6/F7 supported, section-5 disclaimer honest",
            "corrections_adopted": ["C1 manifest hash count 913/913 -> 3270/3270",
                                    "C2 13 A1USE edges -> 13 A1USEN consumer declarations over 1,106 raw A1USE lines",
                                    "C3 patched-tree gate FAIL -> 7 distinct paths + 1 added, 22 manifest-level drift entries",
                                    "C4 declarations.tsv name-deduplicated (12,361 rows; 340 TSV modules vs 343 raw); upstream hyp_eq_concl screen scoped to 3,196 D11/D12/VKPort theorems",
                                    "C5 statement-only cluster re-grounded on in-tree Statements.lean modules; P-LONG/P-HARNACK marked external-unverifiable"],
            "new_finding": "F10",
            "independent_cone_recheck": "15 declarations across 7 cone values and both partitions: 15/15 match"
        }
    },
    "reconciliation": {
        "report": "baseline/reconcile/queue-card-reconciliation-20260911T172206Z.json",
        "drift_report": "baseline/reconcile/queue-drift-20260911T172206Z.json",
        "frozen_16_48Z": {"tasks_total": 135, "verified": 86, "running": 7, "queued": 40, "paused": 1, "blocked": 1,
                          "with_card": 95, "without_card": 40, "flagged": 8},
        "current_17_22Z": {"tasks_total": 139, "verified": 91, "running": 6, "queued": 39, "paused": 1, "blocked": 2,
                           "with_card": 99, "without_card": 40, "flagged": 6},
        "added": 4,
        "removed": 0,
        "status_transitions": 7,
        "card_or_flag_changes": 6,
        "source_hashes": "0 changed / 0 removed against all four accepted manifests",
        "flags_current": ["D9-adversarial-audit-release verified_but_card_blocked",
                          "L1-lean-baseline queue_lagging_card_done",
                          "L2-upstream-adapters queue_lagging_card_done",
                          "L4-geometric-critical-path queue_lagging_card_done",
                          "SEMREV-L3-analytic-critical-path queue_lagging_card_done",
                          "SEMREV-L4-C4-constant-curvature-rauch queue_lagging_card_done"]
    },
    "new_child_task": "comms/outbox/L1-child-self-implication-audit.json (verifier lane, parent M1, kernel isDefEq screen over all 12,543 declaration rows)",
    "verdict_unchanged": "TASK_DONE for the M1 baseline deliverable; no named blocker self-certified closed; no Poincare/Perelman claim"
}

card.setdefault("acceptance", {})["fourth_invocation_fresh_evidence"] = {
    "pinned_release_clean_build": {"status": "PASS", "cwd": "release/", "exit": 0, "jobs": 9339, "wall": "2m26s",
                                   "log": "baseline/logs/fourth/clean-build.log",
                                   "same_path_olean_determinism": "454/454 byte-identical"},
    "authored_file_checks": {"status": "REVIEW", "files_scanned": 456, "declaration_form_hits": 2,
                             "log": "baseline/logs/fourth/forbidden-scan.json"},
    "fail_closed_axiom_audit": {"status": "PASS", "G1": {"exit": 0, "declarations": 12071, "unexpected": 0},
                                "G2": {"exit": 0, "declarations": 472, "unexpected": 0},
                                "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
                                "logs": ["baseline/logs/fourth/axiom-audit-G1.log", "baseline/logs/fourth/axiom-audit-G2.log"]},
    "downstream_checked_use_recorded": {"drivers": {"D6LedgerProbe": 262, "ReleaseClaims": 193},
                                        "v2_proof_level_graph": "baseline/audit/dep-edges-v2.tsv (unchanged; release frozen)"},
    "semantic_class_recorded": {"classification": "baseline/audit/semantic-classes.json",
                                "independent_review": "baseline/v4-independent/review.json (10/10 clusters defensible; C4/C5 corrections adopted)"},
    "source_hashes_recorded": {"status": "PASS", "manifests": "0 changed / 0 removed",
                               "independent_checker": "baseline/v3-independent/independent-hash-check.json"},
    "queue_card_reconciliation": "baseline/reconcile/queue-card-reconciliation-20260911T172206Z.json (+4 tasks, 0 removed, 7 status transitions, 6 card/flag changes)"
}

card.setdefault("blockers", {}).setdefault("M1", {})["fourth_invocation"] = {
    "status": "all_four_legs_supplied_by_independent_contexts_pending_external_acceptance",
    "constructed_input": "baseline (invocations 1-2) + v2 dependency graph + probe sweep + fresh same-path rebuild (this invocation)",
    "downstream_consumer": "replay audits, type dumps, declaration ledger consumed by L1-C1/L1-C4",
    "independent_rebuild": ["V1 fresh-directory from-scratch rebuild (9339 jobs, 454 oleans, 12,361/12,361 rows)",
                            "this invocation's same-path clean rebuild (454/454 olean-identical)"],
    "semantic_review": "V4 independent semantic/traceability review; C1-C5 corrections adopted in this card; re-review of the corrected text recorded in the card",
    "note": "not self-certified closed; external acceptance is child L1-C1"
}

card.setdefault("blockers", {}).setdefault("A1", {})["fourth_invocation"] = {
    "status": "all_four_legs_supplied_pending_integrator_adoption",
    "independent_rebuild": "V2 re-applied the patch to a fresh byte-copy (byte-identical to patched-release) and re-ran the probes",
    "semantic_review": "V2 INDEPENDENT-REVIEW-PASS (baseline/a1/review-independent/review.json); framing corrections adopted: the c=1 propositions pre-existed in the frozen release, so the patch's value is upstream alignment, not new mathematical content",
    "remaining": "adoption into the accepted upstream release (child L1-C2, integrator)"
}

card.setdefault("blockers", {}).setdefault("P5", {})["fourth_invocation"] = {
    "status": "all_four_legs_supplied_pending_integrator_adoption",
    "independent_rebuild": "V3 wrote its own hash checker before reading the gate and reproduced all four manifest comparisons, the pins and the patch drift",
    "semantic_review": "V3 INDEPENDENT-HASH-CHECK-PASS / INDEPENDENT-PATCH-DRIFT-MATCH (baseline/v3-independent/report.json)",
    "remaining": "adoption as the pre-promotion gate (child L1-C4, integrator)"
}

new_findings = [
    {"id": "F9a", "severity": "artifact-state", "title": "stale MANIFEST entry for baseline/logs/p5-hash-gate.json at the end of invocation 3",
     "detail": "report written 21 s after MANIFEST.json; only generated_at differed; repaired by report-then-manifest ordering in the fourth invocation"},
    {"id": "F9b", "severity": "process (self-inflicted, fully repaired)", "title": "accidental clobber of baseline/logs/forbidden-scan.json by `forbidden_scan.py --help`",
     "detail": "overwritten with a 0-file report at 01:10:44; original bytes recovered exactly by exhaustive search over generated_at (recovered 2026-09-11T15:19:38Z); sha256 restored to 07e579597c18fdc36786215bf044554384830b7f04e9a2173208c359d7da9891"},
    {"id": "F10", "severity": "disclosure (statement-level)", "title": "one self-implication tautology outside the D13 statement screen",
     "declaration": "Poincare.D7.SurgeryFlow.realLineProcedureChain_simplyConnected",
     "module": "Poincare/D7/SurgeryFlow/Basic.lean:277-279",
     "type": "toyLedger.SimplyConnected realLineTop -> toyLedger.SimplyConnected realLineTop",
     "classification": "tautology, cone {propext, Classical.choice, Quot.sound}, 0 proof-level downstream consumers, no soundness impact",
     "screen": "baseline/v4-independent/fake_screen2.py over all 7,655 theorem types (textual; cannot decide definitional equality; 5,409 types without a top-level printed arrow)",
     "child": "L1-child-self-implication-audit"}
]
existing_ids = {f.get("id") for f in card.get("findings", []) if isinstance(f, dict)}
for nf in new_findings:
    if nf["id"] not in existing_ids:
        card["findings"].append(nf)

card.setdefault("evidence_files", {}).update({
    "fourth_clean_build_log": "baseline/logs/fourth/clean-build.log",
    "fourth_forbidden_scan": "baseline/logs/fourth/forbidden-scan.json",
    "fourth_axiom_audit_G1_log": "baseline/logs/fourth/axiom-audit-G1.log",
    "fourth_axiom_audit_G2_log": "baseline/logs/fourth/axiom-audit-G2.log",
    "fourth_olean_same_path_comparison": "baseline/logs/fourth/olean-same-path-comparison.json",
    "fourth_p5_entry_gate": "baseline/logs/fourth/p5-hash-gate-entry.json",
    "v1_independent_replay": "baseline/v1-independent/independent-report.json",
    "v2_a1_semantic_review": "baseline/a1/review-independent/review.json",
    "v3_hash_independent_check": "baseline/v3-independent/report.json",
    "v4_card_semantic_review": "baseline/v4-independent/review.json",
    "fourth_queue_card_reconciliation": "baseline/reconcile/queue-card-reconciliation-20260911T172206Z.json",
    "fourth_queue_drift": "baseline/reconcile/queue-drift-20260911T172206Z.json",
    "self_implication_child_task": "comms/outbox/L1-child-self-implication-audit.json"
})

with open(CARD, "w") as f:
    json.dump(card, f, indent=1)
    f.write("\n")
print("card json updated; findings:", len(card["findings"]), "; evidence_files:", len(card["evidence_files"]))
