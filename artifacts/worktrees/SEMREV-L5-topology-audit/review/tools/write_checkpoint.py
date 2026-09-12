#!/usr/bin/env python3
"""SEMREV-L5: write a compile-checked checkpoint with hashes of all evidence."""
import hashlib
import json
import os
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # review/
WT = os.path.dirname(ROOT)


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def main():
    ev = {}
    for sub in ("evidence", "logs", "probes"):
        d = os.path.join(ROOT, sub)
        for f in sorted(os.listdir(d)):
            p = os.path.join(d, f)
            if os.path.isfile(p):
                ev[f"{sub}/{f}"] = sha(p)

    cp = {
        "task_id": "SEMREV-L5-topology-audit",
        "kind": "independent semantic review of parent artifact L5-topology-audit",
        "status": "review_complete",
        "verdict": "TASK_DONE",
        "verdict_scope": "independent semantic review complete; parent audit confirmed with corrections C1-C3; no mathematical blocker closed; Poincare not proved",
        "review_is_not_a_poincare_proof": True,
        "parent_artifact": "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L5-topology-audit",
        "parent_card_sha256": "bab8e022a3d2828a4ae3945093ec6235635c576561d5bd41644191e2a2acc213",
        "parent_json_sha256": "bd9d975964db2ec166fd5f7a26b4db5fb6cc20cad1a767e8fcc2aadec2d1feea",
        "parent_checkpoint_sha256": "f863293deb11299e5df67735c660aaeb1fa0f1a037e1d6c387a5265d64bdd192",
        "toolchain": "leanprover/lean4:v4.34.0-rc2 (direct toolchain binary)",
        "mathlib_rev": "7974e751bece493b6ff508039423ca9fa2452fa8",
        "replay_environment": "LEAN_PATH = L5 release .lake/build/lib/lean + shared mathlib packages (read-only)",
        "verified_this_invocation": {
            "cited_declaration_fail_closed_audit": {
                "log": "logs/SemRevAxioms.log",
                "cited": 51,
                "missing": 0,
                "unsafe": 0,
                "sorryAx": 0,
                "unapproved_axiom_cones": 0,
                "registered_neg_controls_with_forbidden_cone": 5,
                "verdict": "PASS",
            },
            "exact_type_replay": {"log": "logs/SemRevTypes.log", "declarations": 51},
            "printed_definitions": {"log": "logs/SemRevShapes.log"},
            "whole_release_pass_A": {
                "log": "logs/PassA.log",
                "decls": 12136,
                "theorems": 7483,
                "unsafe": 0,
                "partial": 22,
                "sorryAx_unexpected": 0,
                "native_decide_unexpected": 0,
                "unapproved_axiom_unexpected": 0,
                "proof_wanted": 0,
            },
            "whole_release_pass_B": {
                "log": "logs/PassB.log",
                "decls": 12091,
                "theorems": 7464,
                "unsafe": 0,
                "partial": 19,
                "sorryAx_unexpected": 0,
                "native_decide_unexpected": 0,
                "unapproved_axiom_unexpected": 0,
                "proof_wanted": 0,
            },
            "negative_control_fresh_forbidden": {
                "log": "logs/SemRevNegControl.log",
                "observed_exit": 1,
                "violations": ["semrevFreshBadAxiom", "semrevFreshBadTheorem", "semrevFreshSorry", "semrevFreshNative"],
            },
            "per_file_elaboration_replay": {
                "log": "logs/perfile-replay.json",
                "files": 464,
                "failures": 0,
                "wall_seconds": 151.0,
            },
            "forbidden_token_scan": {
                "log": "logs/forbidden-replay.log",
                "sorry": 0,
                "admit": 0,
                "axiom": 3,
                "unsafe": 10,
                "native_decide": 0,
                "proof_wanted": 0,
                "sorryAx_name_literals": 14,
            },
            "collisions_and_consumers": {
                "log": "evidence/collisions-replay.json, evidence/consumers-replay.json",
                "duplicate_names": 58,
                "colliding_pairs": 3,
                "passes": "A=448, B=437, union=462/462",
                "consumer_counts_reproduce_L5": True,
            },
            "source_hash_replay": {
                "log": "evidence/hash-replay.json",
                "mismatch_current_vs_sourcehashes": 0,
                "diff_sourcehashes_vs_baseline": 0,
            },
            "a3_screen_replay": {"log": "logs/L5A3Screen-replay.log", "summary_lines_identical_to_L5": True},
        },
        "card_md": "longrun/results/SEMREV-L5-topology-audit.md",
        "card_json": "longrun/results/SEMREV-L5-topology-audit.json",
        "card_sha256": {
            "longrun/results/SEMREV-L5-topology-audit.md": sha(os.path.join(WT, "longrun/results/SEMREV-L5-topology-audit.md")),
            "longrun/results/SEMREV-L5-topology-audit.json": sha(os.path.join(WT, "longrun/results/SEMREV-L5-topology-audit.json")),
        },
        "review_findings": [
            "L5 card §8 'no inhabitant of any of the three exists' is refuted by the release's own D4 non-vacuity witnesses for FiniteMeshConvergence and FiniteRepresentsContinuousPerelman (and ContinuousPerelmanFMonotonicity); I7 still OPEN.",
            "L5 card §10 M8 'the only occurrence in the project is docs/orchestration_reuse.md §4' is inaccurate: leader-registry.json lists M8 in named_blockers and the L5 prompt names it; M8 still has no definition/manifest entry (still UNBOUND).",
            "L5 card §9 EQUIV finding is lane-scoped; a whole-package rerun adds 6 conclusion-equivalent-hypothesis hits outside the audited lane (D9 DeTurck toy x3, D7 Compactness x1, D10 MaximumPrincipleRN x1, D11 MaximumPrincipleTensor x1).",
        ],
        "no_promotion_check": "L5 card/JSON declare poincare_proved=false, promotions=[]; release D6/D12 cards classify recognition as conditional; no artifact promotes conditional/model to proved.",
        "evidence_sha256": ev,
        "updated_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
    }
    with open(os.path.join(WT, "checkpoint.json"), "w") as f:
        json.dump(cp, f, indent=1)
    with open(os.path.join(ROOT, "checkpoint.json"), "w") as f:
        json.dump(cp, f, indent=1)
    print("wrote checkpoint.json with", len(ev), "evidence hashes")


if __name__ == "__main__":
    main()
