#!/usr/bin/env python3
"""Assemble longrun/results/D13-critical-path-review.json from the audit evidence."""
import hashlib
import json
import os
import subprocess
from datetime import datetime, timezone

WT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
REL = os.path.join(WT, "release")


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def read(path):
    return open(os.path.join(WT, path)).read()


audit = json.load(open(os.path.join(WT, "audit-evidence", "audit-summary.json")))
step_by = {s["step"]: s for s in audit["steps"]}

authored = [ln.split() for ln in read("audit-evidence/authored-hashes.txt").strip().splitlines()]
source_hashes = {
    "authored_sha256": {p: h for h, p in authored},
    "release_file_count_excluding_lake": len(read("audit-evidence/final-release-hashes.txt").strip().splitlines()),
    "release_hash_manifest": "audit-evidence/final-release-hashes.txt",
    "copied_snapshot_hash_manifest": "audit-evidence/copied-snapshot-hashes.txt",
    "base_package_unchanged_vs_integrated_snapshot": True,
}

gate_replay = json.load(open(os.path.join(WT, "audit-evidence", "gate-replay.json")))

compile_evidence = {
    "release_dir": REL,
    "fresh_build": {
        "command": "cd release && rm -rf .lake/build && lake build",
        "cwd": REL,
        "exit": 0,
        "jobs": 9329,
        "wall": "1m28.6s",
        "log": "audit-evidence/build-first.log",
    },
    "driver_steps": {k: {"cmd": v.get("cmd"), "cwd": v.get("cwd"), "exit": v.get("exit"),
                         "expected_exit": v.get("expected_exit"), "ok": v.get("ok"),
                         "log": v.get("log")}
                     for k, v in step_by.items()},
    "declaration_types": "audit-evidence/declaration-types.txt",
    "transcript": "audit-evidence/transcript.txt",
    "gate_replay": {
        "tool": "audit-evidence/tools/d13_gate_replay.py",
        "replay_of": gate_replay["replay_of"],
        "package": gate_replay["package"],
        "source_sha256": gate_replay["source_sha256"],
        "lean_files": gate_replay["lean_files"],
        "build_exit": gate_replay["build_exit"],
        "nonzero_exits": gate_replay["nonzero_exits"],
        "ok": gate_replay["ok"],
        "elapsed_seconds": gate_replay["elapsed_seconds"],
        "log": "audit-evidence/gate-replay.log",
        "json": "audit-evidence/gate-replay.json",
    },
}

axiom_evidence = {
    "programmatic_fail_closed": {
        "command": "lake env lean Poincare/D13/CriticalPathReview/AxiomAudit.lean",
        "exit": 0,
        "audited_declarations": 71,
        "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "project_axioms": 0, "unsafe": 0, "sorryAx": 0, "native_decide": 0,
        "unapproved_axioms": 0, "collect_failures": 0,
        "log": "audit-evidence/logs/03-axiom-audit.log",
    },
    "literal_print_axioms": {
        "command": "lake env lean Poincare/D13/CriticalPathReview/PrintAxiomsAll.lean",
        "exit": 0,
        "declarations_covered": 63,
        "unapproved_cones": {},
        "empty_cones": 28,
        "log": "audit-evidence/logs/06-print-axioms-all.log",
        "secondary_probe": {"command": "lake env lean Poincare/D13/CriticalPathReview/PrintAxioms.lean",
                            "exit": 0, "declarations_covered": 20,
                            "log": "audit-evidence/logs/05-print-axioms.log"},
    },
    "negative_control": {
        "command": "cd release && lake env lean ../audit-evidence/negcontrol/CriticalPathNegControlIncluded.lean",
        "cwd": REL,
        "exit": 1,
        "expected": "FAIL naming Poincare.D13.CriticalPathReview.NegControl.negControlBadAxiom",
        "log": "audit-evidence/logs/04-negcontrol-included.log",
        "root_sha256": sha("audit-evidence/negcontrol/CriticalPathNegControlIncluded.lean"),
        "placement": "OUTSIDE the release package: the dispatcher compile gate runs `lake env lean` on every .lean file under release/ and requires exit 0, so a deliberately failing control root may not live there (same convention as D13-integrated-kernel-audit).",
    },
}

# Repair attempt 1: the only cause of the dispatcher gate failure was the control root above
# sitting inside release/ (file audit-evidence/negcontrol/CriticalPathNegControlIncluded.lean);
# every other one of the 455 checked files exited 0.  The file bytes are unchanged (sha256
# ef3f7ecec38bf58ff47989aed477e95e8ae00129250bb891077f667d97a042eb) — it was relocated, not
# edited — and the driver assertion (exit 1 + named axiom) is re-run from the new path.
repair_record = {
    "attempt": 1,
    "trigger": "dispatcher compile gate ok=false: audit-evidence/negcontrol/CriticalPathNegControlIncluded.lean exit=1",
    "root_cause": "deliberately failing negative-control root placed inside the release package; compile_gate requires exit 0 for every .lean file under release/",
    "fix": "relocated the control root to <worktree>/audit-evidence/negcontrol/CriticalPathNegControlIncluded.lean (byte-identical), updated tools/d13_cp_audit.py and tools/assemble_result.py to invoke ../audit-evidence/negcontrol/... from cwd=release/",
    "not_edited": "the control file content, all 8 authored Lean files, the release package sources (all authored Lean hashes unchanged; see source_hashes.authored_sha256)",
    "verification": "audit-evidence/tools/d13_gate_replay.py re-runs the dispatcher gate algorithm over release/; see compile_evidence.gate_replay",
}

proved_declarations = [
    {"name": "Poincare.D13.CriticalPathReview.exists_last_zero",
     "class": "general",
     "statement": "0 ≤ t₀ → ContinuousOn g (Icc 0 t₀) → 0 ≤ g 0 → g t₀ < 0 → ∃ s ∈ Icc 0 t₀, g s = 0 ∧ ∀ u ∈ Ioc s t₀, g u < 0",
     "role": "last-exit order-topology step (dual to D12 exists_first_zero)"},
    {"name": "Poincare.D13.CriticalPathReview.scalar_forward_invariance",
     "class": "general",
     "statement": "expanded Lipschitz bound on [-M,M], f 0 ≥ 0 (the exact dim-1 kernel condition), x' = f(x) on (0,T), ContinuousOn x [0,T], x 0 ≥ 0, |x t| ≤ M ⟹ 0 ≤ x t on [0,T]",
     "role": "scalar case of blocker B1 with the correct kernel condition (the D12 module proves only the strictly stronger quadratic-form condition)"},
    {"name": "Poincare.D13.CriticalPathReview.scalar_forward_invariance_of_locallyLipschitz",
     "class": "general",
     "statement": "same conclusion from mathlib LocallyLipschitzOn (Icc (-M) M) f (compactness supplies the constant)",
     "role": "shows the expanded Lipschitz hypothesis is the standard local-Lipschitz regularity, not an ad-hoc strengthening"},
    {"name": "Poincare.D13.CriticalPathReview.scalar_forward_invariance_witness",
     "class": "general (non-vacuity instance)",
     "statement": "∀ c T, 0 ≤ c → 0 ≤ T → ∀ t ∈ Icc 0 T, 0 ≤ c * Real.exp t",
     "role": "nondegenerate solution x' = x starting nonnegative; all hypotheses of the main theorem are checked for it"},
    {"name": "Poincare.D13.CriticalPathReview.scalarMat_posSemidef_iff",
     "class": "general",
     "statement": "(scalarMat a).PosSemidef ↔ 0 ≤ a for Matrix (Fin 1) (Fin 1) ℝ",
     "role": "1×1 PSD reduction"},
    {"name": "Poincare.D13.CriticalPathReview.kernelTangent_scalarField_iff",
     "class": "general",
     "statement": "(∀ A, A.PosSemidef → KernelTangent A (scalarField f A)) ↔ 0 ≤ f 0",
     "role": "exact characterization of B1's kernel condition in dimension 1"},
    {"name": "Poincare.D13.CriticalPathReview.b1_dimension_one",
     "class": "general (partial closure of a named blocker: dimension 1 only)",
     "statement": "kernel condition characterization ∧ every 1×1 path with (0,0)-component solving x' = f x, starting PSD, staying in [-M,M], stays PSD on [0,T]",
     "role": "blocker B1 in dimension 1 with the correct kernel condition; n ≥ 2 remains open"},
    {"name": "Poincare.D13.CriticalPathReview.kernelTangent_scalarField_id",
     "class": "general (non-vacuity)",
     "statement": "the field f x = x satisfies B1's kernel condition in dimension 1",
     "role": "non-vacuity of the dimension-1 kernel condition"},
]

expanded_hypotheses = [
    {"declaration": "Poincare.D12.SurgeryRecognition.stage6Target_of_v3hypotheses",
     "residual_inputs": ["CompactSpace X.Carrier", "T2Space X.Carrier",
                         "ChartedSpace EuclideanThree X.Carrier", "SimplyConnectedSpace X.Carrier",
                         "ExtinctionCertificate X", "ConnectedSumDecompositionV2 X E.pieces",
                         "RemainingRecognitionHypothesesV3 X E.pieces {vanKampen, spaceForm}",
                         "CanonicalNeighborhoodInput X E"],
     "eliminated_from_type": ["SphericalPieceRecognition",
                              "RemainingRecognitionHypothesesV2 (coveringTrivial proved)",
                              "RemainingRecognitionHypotheses (pieceRecognition constructed)"],
     "checked_by": "D13CP_ELIMINATED_OK / D13CP_REQ_OK lines in audit-evidence/logs/01-statement-audit.log"},
    {"declaration": "Poincare.D12.TensorMaximumBochner.KernelTangent (blocker B1 hypothesis)",
     "kernel_condition_dim1": "0 ≤ f 0, exactly characterized by kernelTangent_scalarField_iff",
     "missing_dim_ge_2": "for n ≥ 2 and P locally Lipschitz with ∀ A ⪰ 0, KernelTangent A (P A): every differentiable M with M' = P(M), M 0 ⪰ 0 satisfies M t ⪰ 0; the D12 TangentCone.lean exhibits A ⪰ 0, KernelTangent A N, ¬ FeasibleDirection A N, so the passage is not a perturbation argument",
     "checked_by": "Poincare/D13/CriticalPathReview/B1DimensionOne.lean"},
    {"declaration": "Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV3",
     "fields": ["vanKampen : SimplyConnectedSpace X → ∀ P ∈ pieces, SimplyConnectedSpace P",
                "spaceForm : ∀ {Y}, SphericalPiece Y → { M : SphericalSpaceFormModel // IsSpaceFormModelOf Y M }"],
     "checked_by": "D13CP_REQ_OK for SphericalSpaceFormModel and SphericalPiece (constructor telescope)"},
]

semantic_class = {
    "general": ["exists_last_zero", "scalar_forward_invariance",
                "scalar_forward_invariance_of_locallyLipschitz", "scalarMat_posSemidef_iff",
                "kernelTangent_scalarField_iff", "b1_dimension_one",
                "D12 Sturm/Riccati ODE core (comparison-geodesics)",
                "D12 Milnor Levi-Civita (left-invariant model, not manifold chart)",
                "D12 diskGlueQuotHomeoSphere, finiteFreeOrbit_isQuotientCoveringMap, deckTrivial_of_simplyConnected_quotient",
                "D12 heat-domain counterexample not_fullInitialCondition_flat_of_pos",
                "D10/D12 pure ODE and finite-dimensional facts"],
    "conditional": ["stage6Target_of_certificates", "stage6Target_of_v2decomposition",
                    "stage6Target_of_v2hypotheses", "stage6Target_of_v3hypotheses",
                    "D12 parabolic mild solution (BUC, L*T < 1)", "D12 bishopGromovVolumeRatio",
                    "D12 entropy fDerivativeCorrected family", "D12 chart Levi-Civita/torsion forms"],
    "model": ["D12 so(3) curvature models", "D12 flat Gaussian entropy/shrinker models",
              "D12 1-torus spectral Poincare/heat layer", "D12 Euclidean Jacobi/Riccati model instances",
              "D12 matrix ODE positivity preservation (strengthened condition)"],
    "statement_only": ["Poincare.Stage6.poincareConjectureTopologicalThree",
                       "ExtinctionCertificate (Ricci flow with surgery/extinction)",
                       "CanonicalNeighborhoodInput", "SphericalPieceRecognition",
                       "Moise triangulation, PL->smooth, spaceForm classification",
                       "U1-U12 / I1-I8 interfaces (manifold Riemannian framework, heat kernel, F/W/mu, reduced volume, GH compactness, surgery)"],
}

exact_blockers_closed = [
    {"blocker": "B1-dimension-1 (scalar component case of the tensor-maximum-bochner blocker)",
     "constructor": "Poincare.D13.CriticalPathReview.b1_dimension_one",
     "supporting": ["Poincare.D13.CriticalPathReview.kernelTangent_scalarField_iff",
                    "Poincare.D13.CriticalPathReview.scalar_forward_invariance"],
     "downstream_checked_use": ["b1_dimension_one consumes kernelTangent_scalarField_iff (D13CP_PAIR in_proof=true)",
                                "scalar_forward_invariance_witness consumes scalar_forward_invariance (D13CP_PAIR in_proof=true)"],
     "scope": "PARTIAL: the n ≥ 2 statement of B1 remains open; this does not close B1 as recorded by the D12 card",
     "evidence": "audit-evidence/logs/01-statement-audit.log, 05-print-axioms.log, declaration-types.txt"},
    {"blocker": "D7 ConnectedSumDecomposition.sphere_of_spheres (SR-5 sphere-of-spheres step)",
     "constructor": "Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2",
     "downstream_checked_use": ["stage6Target_of_v2decomposition (D13CP_PAIR in_proof=true)",
                                "retained consumers: mkV2 3, iteratedSphereSum 38, sphereConnectSum_homeo_sphere 42"],
     "scope": "input removed from the *hypothesis list* of the end-game assembly; re-verified on this fresh build",
     "caveat": "the literal restatement iteratedSphereSum_homeo_sphere has 0 retained consumers; the consumed object is the definition iteratedSphereSum (new finding, §findings)"},
    {"blocker": "D7 SphericalPieceRecognition (opaque recognition bridge)",
     "constructor": "Poincare.D12.SurgeryRecognition.sphericalPieceRecognition_of (+ sphericalPieceRecognition_of_spaceForm, deckTrivial_of_simplyConnected_quotient)",
     "downstream_checked_use": ["RemainingRecognitionHypothesesV2.toRemaining (in_proof=true)",
                                "RemainingRecognitionHypothesesV3.toRemainingV2 (in_proof=true)",
                                "RemainingRecognitionHypothesesV3.toRemaining (in_proof=true)",
                                "type-level absence in stage6Target_of_v2hypotheses and stage6Target_of_v3hypotheses"],
     "scope": "the opaque bridge is replaced by the two explicit inputs vanKampen and spaceForm; covering recognition and deck triviality are constructed",
     "evidence": "D13CP_ELIMINATED_OK / D13CP_PAIR lines"},
]

findings = [
    "iteratedSphereSum_homeo_sphere (D12-surgery-recognition, SR-5) has 0 retained consumers on the fresh build; the actual consumer chain (endGame_finalTopology, mkV2) goes through the definition iteratedSphereSum. The sphere-of-spheres content is still constructed (in the structure field), but the relayed card's named theorem is only an anonymous-example-level restatement.",
    "The D12-heat-semigroup-analysis over-claim reported by the D13-integrated audit (heatOperatorBCF_comp -> heatOperator_gaussianKernel_L1_tendsto_seq) is a card/consumer mismatch, not a mathematical error; this review did not re-audit it.",
    "Two negative-control modules (axiom : False) remain inside the Poincare.+ library glob; the package therefore contains an inconsistent environment reachable by importing those two leaf modules. Pre-existing; not edited; excluded from this task's clean root.",
    "The relayed terminal input for this task contained only the D12 and D13/IntegratedAudit deltas; D11 and VKPort had to be copied from the verified D13-integrated worktree. Recorded as a dependency request.",
]

remaining_blockers = {
    "critical_path_end_game": [
        {"input": "ExtinctionCertificate (SR-6): Ricci flow with surgery existence, finite extinction, complexity decrease",
         "status": "hypothesis; no constructor", "evidenced_plan": False},
        {"input": "CanonicalNeighborhoodInput: canonical neighbourhood theorem interface",
         "status": "hypothesis; no constructor", "evidenced_plan": False},
        {"input": "ConnectedSumDecompositionV2 data for the terminal pieces",
         "status": "data parameter; inhabitation follows from a surgery decomposition certificate", "evidenced_plan": "partial"},
        {"input": "vanKampen (SR-4): free-product/connected-sum simple connectivity",
         "status": "hypothesis; VKPort (757 decls) compiles but is not wired",
         "evidenced_plan": True,
         "plan": "D12 card: PathConnectedOpenCover of the iterated connected sum; VanKampenFactorizationsConnected via the subdivision/sweep machinery; free-product-triviality group lemma; wire into mkV2"},
        {"input": "spaceForm (spherical space form modelling of spherical pieces)",
         "status": "hypothesis; no constructor", "evidenced_plan": False},
    ],
    "analytic_core": [
        "U8 Hamilton/quasilinear Ricci-DeTurck short-time existence: only the semilinear BUC model is proved; the derivative-loss barrier is proved; no quasilinear scheme (parabolic Holder/weighted spaces) constructed.",
        "U6 manifold heat kernel / parametrix / parabolic regularity: only Euclidean explicit kernels and the D11 bridge; D7 FullInitialCondition field refuted, admissible-test-function interface provided.",
        "U7 manifold volume form, divergence theorem, weighted IBP and Bochner identity: chart-level only (D12-volume-ibp); atlas/partition-of-unity gluing state-only.",
        "U12 F/W/mu monotonicity: model/conditional only; the general pointwise evolution identity and weighted IBP with domination are missing.",
        "U9 reduced length/volume, Cheeger-Gromov compactness, canonical neighbourhoods, ancient kappa-solutions: statement-only; D12 supplies a Gaussian model and dependency DAGs.",
        "U1-U5 Levi-Civita/curvature manifold framework (exponential map, Jacobi fields, sphere measures): only abstract interfaces and left-invariant/chart models.",
        "B1 for n >= 2 (PSD-cone invariance under the kernel condition): exact statement recorded; dimension 1 closed by this task.",
        "B3 frenzymath port toolchain mismatch (Lean v4.32.1 vs pinned v4.34.0-rc2) remains a porting blocker.",
    ],
    "introduced_or_confirmed_by_this_task": [
        "iteratedSphereSum_homeo_sphere zero retained consumers (finding 1).",
        "Relay gap: D11 + VKPort absent from the relayed input (finding 4).",
    ],
}

critical_path_eta = {
    "full_perelman_completion": {
        "estimate": "UNESTIMATED",
        "reason": "not every remaining dependency has an evidenced plan; the analytic core U1-U12/I1-I8 has no lemma-level plan for manifold Riemannian framework, manifold heat/Bochner, mu-monotonicity, reduced volume/Cheeger-Gromov, canonical neighbourhoods/ancient solutions, quasilinear short-time existence, or surgery/extinction",
        "minimum_gates_without_plan": 6,
    },
    "end_game_topological_chain": {
        "estimate": "3-8 bounded task units (~10-40 agent-hours)",
        "basis": "explicit remaining steps enumerated by D12-surgery-recognition; 757-declaration VKPort compiles and is kernel-clean; covering recognition and deck triviality already proved and consumed; risk concentrated in the free-product group lemma and in spaceForm",
        "caveat": "spaceForm has no evidenced plan and may not be derivable from the current snapshot ingredients",
    },
    "b1_dimension_ge_2": {
        "estimate": "1-3 bounded task units (~4-15 agent-hours)",
        "basis": "D12 card names the ingredients (min-eigenvalue/Danskin comparison + first-exit argument) and the pinned mathlib has the spectral theorem, eigenvalues and eigenvectorBasis; dimension 1 is now closed with the correct kernel condition",
        "caveat": "the Danskin comparison for the min eigenvalue is not in mathlib and must be formalised",
    },
    "observed_rate": {
        "this_invocation": "one agent invocation (0.3 h wall clock, 5 Lean build/audit cycles) produced 2 new mathematical lemmas with full proofs (scalar invariance + B1 dimension 1) plus 3 fail-closed audit modules",
        "snapshot_wave": "D11+D12 (20 tasks, 163 Lean files, 4343 declarations) removed 3 load-bearing inputs from the end-game hypothesis list and left the manifold analytic core unconstructed",
    },
}

next_dependency_requests = [
    "Relay D11 (6 packages) and VKPort in the terminal input for D13 successor tasks; D12 modules import Poincare.D11.HeatKernelBridge.InitialCondition and the SR-4 card depends on VKPort.",
    "Relay the D12 per-task result cards to D13 review tasks; only the D13-integrated card was relayed.",
    "D12 owners: provide a consumer for iteratedSphereSum_homeo_sphere or drop the restatement from the SR-5 claim.",
    "D12 owners: move the two negative-control modules outside the Poincare.+ library glob.",
    "D14: an evidenced plan for U8 (quasilinear Ricci-DeTurck short-time existence) is the single highest-value unblocking item; without it no analytic gate on the critical path can be estimated.",
    "D14: an evidenced plan for the manifold Riemannian framework (U1-U5, U7) is a prerequisite for every geometric input on the critical path.",
]

result = {
    "schema": "d13-critical-path-review-v1",
    "task_id": "D13-critical-path-review",
    "generated_utc": datetime.now(timezone.utc).isoformat(),
    "worktree": WT,
    "toolchain": read("release/lean-toolchain").strip(),
    "mathlib_rev": json.load(open(os.path.join(REL, "lake-manifest.json")))["packages"][0]["rev"],
    "verdict": "TASK_DONE (review deliverable + partial mathematical result; no Perelman claim)",
    "summary": "Reviewed the expanded statements of the load-bearing end-game chain, re-derived the exact residual hypothesis inventory from the compiled environment, re-ran the downstream-use probe for the claimed closures, and reconstructed the blocker ledger. Full Perelman completion remains unestimated; the end-game topological chain and B1 dimension >= 2 have bounded estimates with evidenced plans. A new partial closure of blocker B1 in dimension 1 (correct kernel condition) is proved and audited. Repair attempt 1: the dispatcher gate failure (the deliberately failing negative-control root sitting inside release/) was fixed by relocating that root outside the package byte-identically; the replay of dispatch_loop.compile_gate now reports ok=true over 454/454 .lean files and no authored Lean source changed.",
    "proved_declarations": proved_declarations,
    "expanded_hypotheses": expanded_hypotheses,
    "semantic_class": semantic_class,
    "exact_blockers_closed": exact_blockers_closed,
    "findings": findings,
    "remaining_blockers": remaining_blockers,
    "critical_path_eta": critical_path_eta,
    "source_hashes": source_hashes,
    "repair_record": repair_record,
    "compile_evidence": compile_evidence,
    "axiom_evidence": axiom_evidence,
    "next_dependency_requests": next_dependency_requests,
    "actual_elapsed_time": (
        "invocation 1: 0.3 h wall clock (~17 min, ~60 tool calls, 5 Lean build/audit cycles); "
        "invocation 2 (repair attempt 1): {:.2f} h wall clock measured from the dispatcher "
        "start 2026-09-11T18:44:30+08:00 (driver 40 s, gate replay 408 s); cap 4 h per "
        "invocation, 72 h / 24 invocations total".format(
            (datetime.now(timezone.utc) - datetime(2026, 9, 11, 10, 44, 30, tzinfo=timezone.utc)
             ).total_seconds() / 3600)),
}

out = os.path.join(WT, "longrun", "results", "D13-critical-path-review.json")
os.makedirs(os.path.dirname(out), exist_ok=True)
with open(out, "w") as f:
    json.dump(result, f, indent=1)
print("wrote", out)
