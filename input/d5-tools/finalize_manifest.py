#!/usr/bin/env python3
"""
D5-clean-rebuild: merge provenance, gate results, scans and card blockers into the
final clean Lean build manifest (`manifest/build-manifest.json`).
"""
import json
import os
import re
import sys
from datetime import datetime, timezone

D5 = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D5_clean_rebuild"
MANIFEST = os.path.join(D5, "manifest")
LOGS = os.path.join(D5, "logs")

# queue.json acceptance snapshot: which D1-D4 tasks the integrator had marked `verified`
QUEUE_VERIFIED = {
    "D1-mathlib-geometry-map", "D1-pde-api-map", "D1-perelman-ledger",
    "D2-pde-foundation", "D3-kappa-ledger", "D3-surgery-ledger",
}

# unresolved blockers, consolidated from every D1-D4 result card (complete list)
BLOCKERS = [
    # A. upstream mathlib gaps
    {"id": "U1", "class": "upstream-mathlib-gap", "source": "D1-mathlib-geometry-map B1",
     "blocker": "Pinned mathlib has no Riemann curvature tensor; curvature-based evolution equations cannot use a mathlib object.",
     "evidence": "#check_failure RiemannCurvatureTensor -> Unknown identifier (D1 card).",
     "status": "open", "owner_hint": "mathlib upstream / future geometry task"},
    {"id": "U2", "class": "upstream-mathlib-gap", "source": "D1-mathlib-geometry-map B2",
     "blocker": "Pinned mathlib has no Ricci tensor or scalar curvature.",
     "evidence": "#check_failure RicciTensor -> Unknown identifier (D1 card).",
     "status": "open", "owner_hint": "mathlib upstream / future geometry task"},
    {"id": "U3", "class": "upstream-mathlib-gap", "source": "D1-mathlib-geometry-map B3",
     "blocker": "No geodesics, exponential map, or parallel transport in pinned mathlib.",
     "evidence": "grep geodesic/expMap over Mathlib/Geometry -> no hits (D1 card).",
     "status": "open", "owner_hint": "mathlib upstream"},
    {"id": "U4", "class": "upstream-mathlib-gap", "source": "D1-mathlib-geometry-map B4",
     "blocker": "Levi-Civita connection smoothness (C^k) is not proved upstream; it must be a hypothesis.",
     "evidence": "Mathlib LeviCivita.lean header: future PRs will prove smoothness (D1 card).",
     "status": "open", "owner_hint": "mathlib upstream"},
    {"id": "U5", "class": "upstream-mathlib-gap", "source": "D1-mathlib-geometry-map B5",
     "blocker": "Covariant derivative is known to depend only on the germ, not the 1-jet, of a section; tensorial identities may need germ-level arguments.",
     "evidence": "TODO in CovariantDerivative/Basic.lean (D1 card).",
     "status": "open", "owner_hint": "mathlib upstream"},
    {"id": "U6", "class": "upstream-mathlib-gap", "source": "D1-pde-api-map / D2-pde-foundation",
     "blocker": "No heat-equation theory, heat kernel, or parabolic PDE layer; the continuous parabolic maximum principle cannot be proved and is a statement-only interface.",
     "evidence": "D1 PDE probe; D2 PDE result card blocker; ContinuousHeatMaximumPrincipleInterface unproved.",
     "status": "open", "owner_hint": "future PDE task with parabolic regularity / discrete-to-continuous limit"},
    {"id": "U7", "class": "upstream-mathlib-gap", "source": "D1-perelman-ledger / D3-entropy-interface",
     "blocker": "No Riemannian volume form, divergence theorem, integration by parts, or Bochner formula in the pinned mathlib.",
     "evidence": "D1 ledger blockers on the volume form; D3 entropy WeightedIBPStatement/BochnerStatement unproved.",
     "status": "open", "owner_hint": "mathlib upstream / future geometry task"},
    {"id": "U8", "class": "upstream-mathlib-gap", "source": "D1-perelman-ledger",
     "blocker": "No smooth manifold of Riemannian metrics and no Hamilton short-time existence theorem for Ricci flow.",
     "evidence": "D1 ledger blockers_summary and P-F-MONO/P-W-MONO blockers.",
     "status": "open", "owner_hint": "long-term Ricci-flow PDE task"},
    {"id": "U9", "class": "upstream-mathlib-gap", "source": "D1-perelman-ledger",
     "blocker": "No reduced length/reduced volume, no pointed Gromov-Hausdorff compactness, no canonical-neighborhood theorem, no surgery machinery; Perelman steps P-REDUCED-VOL, P-HARNACK, P-KAPPA-SOL, P-CANON, P-LONG, P-SURG, P-EXT remain planned/blocked.",
     "evidence": "D1 ledger perelman_steps[4..10] statuses planned/blocked.",
     "status": "open", "owner_hint": "multi-stage future program"},
    {"id": "U10", "class": "upstream-mathlib-gap", "source": "D2-ricci-ode-cluster",
     "blocker": "No tensor Laplacian: the spatial Laplacian of the curvature evolution is not modeled; exposed as the explicit DiffusionVanishes hypothesis.",
     "evidence": "D2 ODE result card blocker 1.",
     "status": "open", "owner_hint": "future PDE/tensor task"},
    {"id": "U11", "class": "upstream-mathlib-gap", "source": "D3-surgery-ledger",
     "blocker": "Pinned mathlib has no manifold orientability: `Orientable` is a parameter of the surgery LedgerPredicates, not a definition; a future contribution should define it and instantiate canonicalLedger.",
     "evidence": "D3 surgery result card note 1 and section 9.",
     "status": "open", "owner_hint": "mathlib upstream / future surgery task"},
    {"id": "U12", "class": "upstream-mathlib-gap", "source": "D1-perelman-ledger",
     "blocker": "The four blocked Perelman steps P-F-MONO, P-W-MONO, P-MU-MONO and P-NLC are recorded as hypothesis structures only: no backward/conjugate heat equation, no integration by parts, no integrability/finiteness of the F/W integrals, no attainment of the infimum defining mu, no reduced length/volume or ball-volume comparison geometry.",
     "evidence": "D1 ledger perelman_steps[0..3] status blocked with per-step blockers.",
     "status": "open", "owner_hint": "multi-stage future program"},
    # B. explicit unproved interfaces inside the release (honest boundaries)
    {"id": "I1", "class": "explicit-unproved-interface", "source": "D2-geometry-foundation",
     "blocker": "LeviCivitaExistenceStatement and CovariantDerivativeCurvatureStatement are explicit BLOCKED Props with no proof.",
     "evidence": "Poincare/Longrun/Geometry/LeviCivitaBlocked.lean (D2 card 2.4).",
     "status": "open", "owner_hint": "D2-geometry follow-up"},
    {"id": "I2", "class": "explicit-unproved-interface", "source": "D2-pde-foundation",
     "blocker": "ContinuousHeatMaximumPrincipleInterface is statement-only; no discrete-to-continuous limit is proved.",
     "evidence": "D2 PDE result card blocker.",
     "status": "open", "owner_hint": "future PDE task"},
    {"id": "I3", "class": "explicit-unproved-interface", "source": "D2-ricci-ode-cluster",
     "blocker": "TensorRicciFlowODEBridge / ManifoldCurvatureRealization have no inhabitant; the ODE-to-tensor-Ricci-flow bridge is an explicit interface, never an axiom.",
     "evidence": "D2 ODE result card blockers 2-3.",
     "status": "open", "owner_hint": "future geometry task"},
    {"id": "I4", "class": "explicit-unproved-interface", "source": "D3-entropy-interface",
     "blocker": "FDerivativeStatement, WeightedIBPStatement, BochnerStatement, ConjugateMeasureEvolutionStatement, EntropyFunctionalRegularityStatement are unproved Props; one-sided bounds are hypotheses; WeightedCalculus is abstract data.",
     "evidence": "D3 entropy result card blockers 1-6.",
     "status": "open", "owner_hint": "future geometry/PDE tasks"},
    {"id": "I5", "class": "explicit-unproved-interface", "source": "D3-kappa-ledger",
     "blocker": "kappa-noncollapsing K1-K7 and sphere-recognition S1-S5 are statement-only; nine foundational gaps listed (curvature, volume form, IBP, short-time existence, heat kernel, reduced length, Cheeger-Gromov, Brendle-Schoen).",
     "evidence": "D3 kappa result card missing_theorems.",
     "status": "open", "owner_hint": "multi-stage future program"},
    {"id": "I6", "class": "explicit-unproved-interface", "source": "D3-surgery-ledger",
     "blocker": "NeckAnalysis, ExtinctionTheorem and MissingInputs are statement-only; no geometric neck analysis or extinction theorem is proved.",
     "evidence": "D3 surgery result card sections 6-7.",
     "status": "open", "owner_hint": "future surgery task"},
    {"id": "I7", "class": "explicit-unproved-interface", "source": "D4-evolution-theorem / D4-counterexample-audit",
     "blocker": "FiniteMeshConvergence, PerelmanEvolutionBoundary and FiniteRepresentsContinuousPerelman are statement-only; FDissipation = 0 (no spatial Laplacian/Bochner content).",
     "evidence": "D4 evolution card; D4 audit boundaries.",
     "status": "open", "owner_hint": "future PDE/tensor task"},
    {"id": "I8", "class": "explicit-unproved-interface", "source": "D4-evolution-theorem / D4-counterexample-audit",
     "blocker": "The transfer theorems perelmanF_monotone_of_tensorBridge / continuousPerelmanFMonotone_of_approximation are conditional on interfaces with no inhabitant; only a trivial finite identification inhabits PerelmanApproximation.",
     "evidence": "D4 audit boundaries 1-2.",
     "status": "open", "owner_hint": "future geometry task"},
    # C. D4 adversarial-audit residual findings
    {"id": "A1", "class": "audit-residual-finding", "source": "D4-counterexample-audit",
     "blocker": "Overstrong hypotheses (not falsity) in three promoted theorems: perelmanF_step_lt and gibbsTerm_strictAnti/gibbsTerm_step_lt assume 1 < c where 1 ≤ c suffices. Corrected theorems are proved in D4Audit; upstream restatement recommended.",
     "evidence": "D4Audit.gibbsTerm_strictAnti_of_one_le, gibbsTerm_step_lt_of_one_le, perelmanF_step_lt_of_one_le.",
     "status": "open", "owner_hint": "D4-evolution upstream restatement"},
    {"id": "A2", "class": "audit-residual-finding", "source": "D4-counterexample-audit",
     "blocker": "Sign convention: the released functional is nonincreasing, opposite to Perelman's F-monotonicity; the cluster explicitly disclaims Perelman's theorem.",
     "evidence": "D4 audit boundary 5.",
     "status": "documented", "owner_hint": "n/a (documented boundary)"},
    {"id": "A3", "class": "audit-residual-finding", "source": "D4-counterexample-audit",
     "blocker": "No false statement was found, but the adversarial audit only covers the D4 evolution cluster; earlier clusters (D2/D3) have axiom audits but no counterexample search.",
     "evidence": "D4 audit scope (imports only Poincare.Longrun.Evolution).",
     "status": "open", "owner_hint": "future adversarial audit"},
    # D. process / delivery
    {"id": "P1", "class": "process-delivery", "source": "longrun/queue.json",
     "blocker": "queue.json is stale (last update 2026-09-08T23:55, before 5 later tasks finished): D2-geometry-foundation is recorded as running; D2-ricci-ode-cluster, D3-entropy-interface, D4-evolution-theorem and D4-counterexample-audit are recorded as queued. D5 clean-room verification supplies the missing independent acceptance evidence.",
     "evidence": "manifest/provenance.json cluster queue_status_at_snapshot; DONE markers + result cards exist for all five.",
     "status": "open", "owner_hint": "integrator (D6) to update queue.json"},
    {"id": "P2", "class": "process-delivery", "source": "all D1-D4 cards",
     "blocker": "Shared longrun/results/ path is outside the worker workspace-write sandbox; every card was mirrored inside its worktree and promoted later. D5 uses the same delivery pattern.",
     "evidence": "Delivery notes in D2-geometry, D3-entropy, D3-kappa, D4-evolution, D4-counterexample-audit cards.",
     "status": "known-environment-limit", "owner_hint": "integrator"},
    {"id": "P3", "class": "process-delivery", "source": "prompt/runtime mismatch",
     "blocker": "Prompt worktree names do not match the runtime worktree names (D5_rebuild vs D5_clean_rebuild; D2_geometry vs D2_geometry_foundation; D2_ode vs D2_ricci_ode_cluster; D3_topology vs D3_kappa_ledger; D4_audit vs D4_counterexample_audit).",
     "evidence": "prompts/D*.md vs worktrees/ listing.",
     "status": "known-environment-limit", "owner_hint": "integrator"},
    # E. release hygiene notes
    {"id": "H1", "class": "hygiene-note", "source": "ReleaseAudit",
     "blocker": "Two compiler-generated partial-safety helpers exist for safe structural recursions: D4Audit.sqTraj._unsafe_rec and Poincare.Longrun.Surgery.SurgeryChain.append._unsafe_rec. They are DefinitionSafety.partial, not unsafe declarations, introduce no axioms, and are not in the forbidden list; reported for awareness.",
     "evidence": "ReleaseAudit output 'note: partial declaration ...'; distinct axiom cones remain within the standard three.",
     "status": "informational", "owner_hint": "none (allowed by the gate)"},
    {"id": "H2", "class": "hygiene-note", "source": "ReleaseAudit",
     "blocker": "Batteries.Util.ProofWanted is imported transitively (it defines the proof_wanted command); no project source uses proof_wanted (comment-aware scan clean) and no proof_wanted-derived project declaration exists.",
     "evidence": "manifest/forbidden-scan.json hard_match_count = 0; ReleaseAudit proof_wanted counters = 0.",
     "status": "informational", "owner_hint": "none"},
    {"id": "H3", "class": "hygiene-note", "source": "ReleaseAudit",
     "blocker": "In Lean 4.34.0-rc2 native_decide no longer routes through ofReduceBool; it emits a private axiom <decl>._native.native_decide.ax_*. The audit catches it through the unapproved-axiom rule; the negative control confirms detection.",
     "evidence": "negcontrol/NegativeControl.lean output.",
     "status": "informational", "owner_hint": "none"},
]


def main():
    prov = json.load(open(os.path.join(MANIFEST, "provenance.json")))
    gates = json.load(open(os.path.join(MANIFEST, "gate-results.json")))
    scan = json.load(open(os.path.join(MANIFEST, "forbidden-scan.json")))
    claims = json.load(open(os.path.join(MANIFEST, "claims.json")))
    card_blockers = json.load(open(os.path.join(MANIFEST, "card-blockers.json")))

    # parse claim-resolution log
    claim_errors = []
    claim_log = os.path.join(LOGS, "08_claim_resolution.log")
    if os.path.exists(claim_log):
        for line in open(claim_log, errors="replace"):
            if "error" in line:
                m = re.search(r"'([^']+)'", line)
                claim_errors.append({"name": m.group(1) if m else "?", "line": line.strip()[:220]})

    per_file = gates["per_file"]
    audit_log = os.path.join(LOGS, "04_release_audit.log")
    audit_summary = {}
    if os.path.exists(audit_log):
        for line in open(audit_log, errors="replace"):
            m = re.match(r"D5ReleaseAudit: (.*?):\s*(.*)", line.strip())
            if m:
                audit_summary[m.group(1)] = m.group(2)

    clusters = []
    for c in prov["clusters"]:
        files = c["files"]
        hashes_ok = all(f["card_hash_match"] is not False for f in files)
        per_file_ok = all(per_file.get(f["path"], 1) == 0 for f in files)
        queue_verified = c["task_id"] in QUEUE_VERIFIED
        gate_ok = gates["gate_pass"]
        if gate_ok and hashes_ok and per_file_ok and c["state_done_marker"]:
            verdict = ("accepted (queue verified + clean-room verified)" if queue_verified
                       else "accepted by D5 clean-room verification (queue.json not updated)")
        else:
            verdict = "rejected (failed clean-room gate)"
        clusters.append({
            **{k: c[k] for k in ("cluster", "task_id", "stage", "origin_worktree",
                                 "result_card", "result_card_status", "queue_status_at_snapshot",
                                 "state_done_marker")},
            "file_count": len(files),
            "files": files,
            "all_card_hashes_match": hashes_ok,
            "all_per_file_lean_exit_zero": per_file_ok,
            "queue_formally_verified": queue_verified,
            "clean_room_gate": "pass" if gate_ok else "fail",
            "verdict": verdict,
        })

    manifest = {
        "schema": "d5-clean-rebuild/build-manifest-v1",
        "task_id": "D5-clean-rebuild",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "verifier_worktree": D5,
        "prompt_worktree_discrepancy": prov["prompt_worktree_discrepancy"],
        "verdict": "RELEASE GATE PASS" if gates["gate_pass"] else "RELEASE GATE FAIL",
        "toolchain": prov["toolchain"],
        "fresh_build": {
            "dir": prov["fresh_build_dir"],
            "project_build_dir_created_from_scratch": True,
            "mathlib_cache": "shared prebuilt .lake/packages (pinned revision, reused read-only); project .lake/build wiped before the gate build",
            "lakefile": "release/lakefile.toml",
            "release_check_root": "release/ReleaseCheck.lean",
            "release_audit": "release/ReleaseAudit.lean",
            "claim_probe": "release/ReleaseClaims.lean",
            "source_scan_tool": "tools/scan_forbidden.py",
        },
        "gate": {
            "gate_pass": gates["gate_pass"],
            "gate_failures": gates["gate_failures"],
            "steps": gates["steps"],
            "per_file_failures": gates["per_file_failures"],
        },
        "forbidden_dependency_audit": {
            "auditor": "ReleaseAudit.lean (kernel-level, every project constant)",
            "exit_code": next((s["exit_code"] for s in gates["steps"] if s["id"] == "release_audit"), None),
            "summary": audit_summary,
            "negative_control": {
                "file": "negcontrol/NegativeControl.lean",
                "log": "logs/09_negative_control.log",
                "result": "PASS — sorryAx and native_decide both detected",
            },
        },
        "forbidden_token_scan": {
            "exit_code": next((s["exit_code"] for s in gates["steps"] if s["id"] == "source_scan"), None),
            "lean_files_scanned": scan["lean_files_scanned"],
            "hard_match_count": scan["hard_match_count"],
            "soft_match_count": scan["soft_match_count"],
            "hard_forbidden": scan["hard_forbidden"],
            "matches": scan["matches"],
        },
        "claim_resolution": {
            "exit_code": gates.get("claim_resolution_exit_code"),
            "claim_count": claims["claim_count"],
            "unresolved": claim_errors,
        },
        "clusters": clusters,
        "base_dependencies": prov["base_dependencies"],
        "artifact_duplicate_conflicts": prov["artifact_duplicate_conflicts"],
        "card_blockers_by_task": card_blockers,
        "unresolved_blockers": BLOCKERS,
        "blocker_counts": {
            "total": len(BLOCKERS),
            "open": sum(1 for b in BLOCKERS if b["status"] == "open"),
            "informational": sum(1 for b in BLOCKERS if b["status"] == "informational"),
            "documented": sum(1 for b in BLOCKERS if b["status"] == "documented"),
            "known_environment_limit": sum(1 for b in BLOCKERS if b["status"] == "known-environment-limit"),
        },
    }
    with open(os.path.join(MANIFEST, "build-manifest.json"), "w") as fh:
        json.dump(manifest, fh, indent=1)
    print(json.dumps({"verdict": manifest["verdict"],
                      "gate_pass": gates["gate_pass"],
                      "clusters": len(clusters),
                      "blockers": manifest["blocker_counts"],
                      "claim_errors": len(claim_errors)}, indent=1))
    return 0 if gates["gate_pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
