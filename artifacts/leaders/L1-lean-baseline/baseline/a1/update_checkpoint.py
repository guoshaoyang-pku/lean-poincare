#!/usr/bin/env python3
"""Update checkpoint.json for the end of the third invocation (JSON-safe, idempotent)."""
import hashlib
import json
import os
import time

WT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CP = os.path.join(WT, "checkpoint.json")


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def main():
    d = json.load(open(CP))
    d["status"] = "third_invocation_complete_awaiting_independent_acceptance"
    d["phase"] = "a1_restatement_and_p5_gate_delivered_replay_clean"
    d["updated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())

    ti = d["third_invocation"]
    ti["status"] = "complete"
    ti["completed_local"] = "2026-09-12T01:25+08:00"
    ti["work_done"] = ti["work_done"] + [
        "L1-C1 independent replay complete: baseline/c1/replay-release built from scratch (lake build exit 0, 9339 jobs); frozen AxiomAudit_G{1,2} re-run there PASS (12,071 + 472 declarations, 0 unexpected); 12,361/12,361 declaration rows field-identical to baseline/audit/declarations.tsv; 12,361/12,361 declaration TYPES character-identical (independent TypeAudit_G{1,2} dumps); 454 oleans: 422 byte-identical, 32 differ only by the embedded absolute source path, 0 unexplained -> baseline/c1/replay-comparison.json verdict REPLAY-IDENTICAL",
        "F8 found and explained: olean bytes embed the absolute source path (32/454 modules; size delta 16/24 = 8-byte alignment of the 19-char path difference). Same-path lake rebuild determinism re-confirmed byte-for-byte on Compat.lean with the exact lake flags. No soundness impact (all declaration rows and types identical).",
        "A1 evidence bundle: baseline/a1/a1-evidence.json; handoff note comms/outbox/2026-09-12-L1-a1-restatement-handoff.md",
        "card (md+json) rewritten with the third-invocation section; MANIFEST regenerated; verify_baseline re-run",
    ]
    ti["in_progress"] = []
    ti["not_yet_done"] = [
        "independent semantic review of the A1 restatement and adoption of the patch (L1-C2 / integrator)",
        "adoption of the P5 gate by the integrator (L1-C4)",
    ]

    d["result_card"]["md_sha256"] = sha256(os.path.join(WT, "longrun/results/L1-lean-baseline.md"))
    d["result_card"]["json_sha256"] = sha256(os.path.join(WT, "longrun/results/L1-lean-baseline.json"))
    d["result_card"]["scope"] = ("M1 baseline deliverable; A1 restatement and P5 gate closure-ready pending "
                                 "independent semantic review/adoption; no Poincare claim")
    d["result_card"]["note"] = "hashes are of the final card content at the end of the third invocation"

    d["named_blockers"]["M1"]["status"] = "evidence_delivered_replay_clean_not_closed"
    d["named_blockers"]["M1"]["note"] = (
        "clean build exit 0 plus 29/29 read-only checks plus the third invocation's independent replay "
        "(from-scratch rebuild in a separate directory; 12,361 declaration rows AND types identical; "
        "422/454 oleans byte-identical, 32 path-embedded, 0 unexplained); closure still requires "
        "independent acceptance (L1-C1) and integrator adoption (L1-C4)")
    d["named_blockers"]["A1"]["status"] = "closure_ready_pending_independent_semantic_review_and_adoption"
    d["named_blockers"]["A1"]["note"] = (
        "upstream restatement constructed and verified on a byte-copy (baseline/a1/patched-release): the "
        "three promoted theorems now carry 1 <= c / forall i, 1 <= c i; patch baseline/a1/a1-restatement.patch; "
        "patched build exit 0 (9340 jobs) with frozen G1/G2 + D7 ReleaseAudit PASS; sharp-only downstream "
        "consumer perelmanF_step_lt_at_threshold_one at c == 1; frozen release/ untouched; independent "
        "semantic review and adoption are the remaining legs")
    d["named_blockers"]["P5"]["status"] = "gate_delivered_pending_adoption"
    d["named_blockers"]["P5"]["note"] = (
        "baseline/tools/p5_hash_gate.py is an executable fail-closed gate: frozen release/ PASS 0 drift "
        "(462/462 D13-final, 286/286 D13-base, 63/63 D6, 66/66 D12, pins match); A1-patched tree FAIL "
        "with exactly the 7 changed files (fail-closed demonstration); the recurring obligation still "
        "needs integrator adoption")

    d["compile_checks"]["a1_restatement"] = {
        "patch": "baseline/a1/a1-restatement.patch (sha256 %s)" % sha256(os.path.join(WT, "baseline/a1/a1-restatement.patch")),
        "patched_tree": "baseline/a1/patched-release",
        "cmd": "lake build",
        "exit": 0,
        "jobs": 9340,
        "log": "baseline/a1/logs-patched-build.log",
        "note": "0 errors, 0 declaration-uses-sorry, 170 lint warnings; 7 files restated + 1 new module",
        "axiom_audit_G1": {"exit": 0, "verdict": "PASS", "declarations": 12072,
                           "unexpected_violations": 0, "log": "baseline/a1/logs/a1-axiom-audit-G1.log"},
        "axiom_audit_G2": {"exit": 0, "verdict": "PASS", "log": "baseline/a1/logs/a1-axiom-audit-G2.log"},
        "d7_release_audit": {"exit": 0, "project_declarations": 880,
                             "log": "baseline/a1/logs/a1-d7-release-audit.log"},
    }
    d["compile_checks"]["independent_replay"] = {
        "cmd": "lake build (in baseline/c1/replay-release, a fresh byte-copy of the frozen sources)",
        "exit": 0,
        "jobs": 9339,
        "log": "baseline/c1/logs-replay-build.log",
        "comparison": "baseline/c1/replay-comparison.json",
        "verdict": "REPLAY-IDENTICAL",
        "declaration_rows_identical": 12361,
        "declaration_types_identical": 12361,
        "oleans_byte_identical": 422,
        "oleans_path_embedded": 32,
        "oleans_unexplained": 0,
    }
    d["compile_checks"]["p5_hash_gate"] = {
        "script": "baseline/tools/p5_hash_gate.py",
        "frozen": {"exit": 0, "verdict": "PASS", "report": "baseline/logs/p5-hash-gate.json"},
        "patched": {"exit": 1, "verdict": "FAIL", "changed": 7,
                    "report": "baseline/a1/logs/p5-hash-gate-patched.json"},
    }

    d["findings"].append(
        "F8: olean bytes embed the absolute source path; 32/454 oleans differ by 16/24 bytes between two "
        "build directories (8-byte alignment of the 19-char path difference), 422/454 byte-identical, all "
        "12,361 declaration rows and types identical across the two builds; same-path byte determinism "
        "re-confirmed. No soundness impact.")

    d["source_state"]["third_invocation_recheck"] = (
        "462/462 unchanged at 2026-09-12 00:41+08:00; A1 restatement applied only to byte-copies "
        "(baseline/a1/patched-release, baseline/c1/replay-release)")
    d["queue_snapshot"]["third_recheck"] = {
        "report": "baseline/reconcile/queue-card-reconciliation-20260911T164848Z.json",
        "tasks_total": 135, "verified": 86, "running": 7, "queued": 40, "paused": 1, "blocked": 1,
        "with_card": 95, "without_card": 40, "flags": 8,
        "drift_report": "baseline/reconcile/queue-drift-20260911T164848Z.json",
    }
    d["evidence_manifest_entries"] = None  # refreshed after gen_manifest below
    d["research_briefs"] = sorted(set(d["research_briefs"] + ["research-brief-2026-09-12.md"]))
    d["next_step"] = ("await independent acceptance of M1 (L1-C1 replay evidence in "
                      "baseline/c1/replay-comparison.json), independent semantic review + adoption of the A1 "
                      "restatement, and adoption of the P5 gate; no further work claimed")

    json.dump(d, open(CP, "w"), indent=1)
    print("checkpoint updated")


if __name__ == "__main__":
    main()
