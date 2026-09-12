#!/usr/bin/env python3
"""Merge the A3 D2/D3 counterexample-search results into the D13 result card JSON.

Run after `audit360/compose.py`; idempotent (it rebuilds the A3-D2D3 sections from
the on-disk logs/hashes each time).
"""
import hashlib
import json
import os
import time

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(HERE)
OUT = os.path.join(WT, "longrun", "results", "D13-cross-audit-360-cards.json")
LOGS = os.path.join(HERE, "logs")


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def log_rc(name):
    p = os.path.join(LOGS, name)
    return int(open(p).read().strip()) if os.path.exists(p) else None


def log_hash(name):
    p = os.path.join(LOGS, name)
    return sha256(p) if os.path.exists(p) else None


PROBE = os.path.join(WT, "a3d2d3", "A3D2D3.lean")
PROBE_SHA = sha256(PROBE)
TREE_SHA = open(os.path.join(LOGS, "a3d2d3.tree.sha256")).read().split()[0]

A3 = {
    "probe_file": "a3d2d3/A3D2D3.lean",
    "probe_sha256": PROBE_SHA,
    "base_sources": ("byte-identical copy of this worktree's accepted D6 release "
                     "(diff -rq a3d2d3 release --exclude=.lake --exclude=A3D2D3.lean is empty)"),
    "package_lean_tree_sha256": TREE_SHA,
    "build": {
        "command": "cd a3d2d3 && lake build",
        "rc": log_rc("a3d2d3.build.rc"),
        "jobs": 8946,
        "verdict_line": "D6AUDIT\tVERDICT\tPASS - no sorryAx, no project axiom, no unsafe, no native_decide, no unapproved axiom, no proof_wanted",
        "log": "audit360/logs/a3d2d3.build.log",
        "log_sha256": log_hash("a3d2d3.build.log"),
    },
    "probe": {
        "command": "cd a3d2d3 && lake env lean A3D2D3.lean",
        "rc": log_rc("a3d2d3.probe.rc"),
        "declarations": 17,
        "cone_violations": 0,
        "cones": {
            "A3D2D3.linearDecay_uninhabited": "propext,Classical.choice,Quot.sound",
            "A3D2D3.linearDecay_isEmpty": "propext,Classical.choice,Quot.sound",
            "A3D2D3.linearDecay_fields_contradict": "propext,Classical.choice,Quot.sound",
            "A3D2D3.covariantCurvatureStatement_trivial": "propext,Classical.choice,Quot.sound",
            "A3D2D3.form_eq_of_basis_eq": "propext,Classical.choice,Quot.sound",
            "A3D2D3.bridgeWitness": "propext,Classical.choice,Quot.sound",
            "A3D2D3.bridge_forces_zero_ricci": "propext,Classical.choice,Quot.sound",
            "A3D2D3.bridge_forces_zero_traj": "propext,Classical.choice,Quot.sound",
            "A3D2D3.missingSphereRecognitionAlgorithm_trivial": "propext,Classical.choice,Quot.sound",
            "A3D2D3.surgeryCertificate_emptyRelation": "(none)",
            "A3D2D3.not_missingConjugateHeatKernel_zero": "propext,Classical.choice,Quot.sound",
            "A3D2D3.not_missingKappaNoncollapsing_zero": "propext,Classical.choice,Quot.sound",
            "A3D2D3.neckAnalysis_inhabited": "(none)",
            "A3D2D3.extinctionTheorem_true": "(none)",
            "A3D2D3.missingInputs_with_true_extinction": "Classical.choice",
            "A3D2D3.heatGrid_le_of_initial_le_no_hM": "propext,Classical.choice,Quot.sound",
            "A3D2D3.kappa_iff_normalized_no_hyp": "propext,Classical.choice,Quot.sound",
        },
        "log": "audit360/logs/a3d2d3.probe.log",
        "log_sha256": log_hash("a3d2d3.probe.log"),
    },
    "levicivita_crosscheck": {
        "command": ("cd audit360/pkgs/D12-connection-curvature && lake env lean "
                    "A3ExtraD2/D2LedgerCheck.lean"),
        "rc": 0,
        "result": ("@leviCivitaExists : forall m b, LeviCivitaExistenceStatement m b; "
                   "axioms = {propext, Classical.choice, Quot.sound}"),
        "log": "audit360/logs/a3d2d3.levicivita_check.log",
        "log_sha256": log_hash("a3d2d3.levicivita_check.log"),
    },
    "findings": [
        {
            "id": "A3-D2D3-1",
            "class": "VACUOUS (kernel-checked)",
            "statement": "Poincare.Longrun.Entropy.LinearDecayCertificate E",
            "verdict": ("provably empty: its own fields `cert.lower_le` (global lower bound) and "
                        "`decay` (global linear decay with rate > 0) contradict each other at "
                        "t = max((F(E 0)-lowerBound)/rate) 0 + 1. `time_le` is therefore a "
                        "theorem about an empty type."),
            "evidence": ["A3D2D3.linearDecay_uninhabited", "A3D2D3.linearDecay_isEmpty",
                         "A3D2D3.linearDecay_fields_contradict"],
        },
        {
            "id": "A3-D2D3-2",
            "class": "TRIVIAL / mislabelled BLOCKED (kernel-checked)",
            "statement": "Poincare.Longrun.Geometry.CovariantDerivativeCurvatureStatement I M cov",
            "verdict": ("unconditionally inhabited by the zero pointwise curvature; the `cov` "
                        "parameter is literally `_cov` and unused, so the statement captures none "
                        "of the missing curvature API despite the BLOCKED label."),
            "evidence": ["A3D2D3.covariantCurvatureStatement_trivial"],
        },
        {
            "id": "A3-D2D3-3",
            "class": "DEGENERATE INTERFACE (kernel-checked)",
            "statement": "Poincare.Longrun.CurvatureODE.TensorRicciFlowODEBridge I M cov F T traj D",
            "verdict": ("inhabited for explicit parameters (zero reaction field, constant metric, "
                        "zero curvature, zero trajectory) AND every inhabitant with 0 < T has "
                        "ricci(curvature t) X X = 0 for all t in [0,T], hence traj = 0 on [0,T]. "
                        "The transfer theorems are statements about a degenerate interface."),
            "evidence": ["A3D2D3.bridgeWitness", "A3D2D3.bridge_forces_zero_ricci",
                         "A3D2D3.bridge_forces_zero_traj", "A3D2D3.form_eq_of_basis_eq"],
        },
        {
            "id": "A3-D2D3-4",
            "class": "REFUTED PRIOR FINDING + CONVENTION MISMATCH",
            "statement": ("VERIFIER-D7-adversarial-audit-d2d3 F2 (entropy bridge 'wrong sign') and "
                          "F11 (conjugate heat equation)"),
            "verdict": ("F2 is a false positive: Perelman (arXiv:math/0211159, section 1.2, eq. (1.4)) "
                        "has F_t = +2 int |R_ij + grad_i grad_j f|^2 e^{-f} dV >= 0 with (g_ij)_t = -2 R_ij "
                        "and f_t = -Delta f + |grad f|^2 - R, exactly the release's FDerivativeStatement. "
                        "F11 is a real labelling/convention defect: ConjugateMeasureEvolutionStatement "
                        "states d_t rho = -Delta rho without the R rho term of the conjugate heat equation."),
            "evidence": ["docstring in a3d2d3/A3D2D3.lean section A3-D2D3-4",
                         "https://ar5iv.labs.arxiv.org/html/math/0211159 (1.4), (1.3)"],
        },
        {
            "id": "A3-D2D3-5",
            "class": "TRIVIAL / FALSE-INSTANCE statement-only items (kernel-checked)",
            "statement": ("missingSphereRecognitionAlgorithm, SurgeryCertificate, "
                          "missingConjugateHeatKernel, missingKappaNoncollapsing, NeckAnalysis"),
            "verdict": ("(a) missingSphereRecognitionAlgorithm is immediate from classical "
                        "decidability and asserts nothing about a decision procedure; "
                        "(b) SurgeryCertificate has no field mentioning the datum, so a certificate "
                        "exists for a datum with empty relation; (c) missingConjugateHeatKernel and "
                        "missingKappaNoncollapsing are false for the zero measure; (d) the surgery "
                        "cluster's NeckAnalysis is inhabited with all Prop fields False, so as a "
                        "structure it imposes no obligation."),
            "evidence": ["A3D2D3.missingSphereRecognitionAlgorithm_trivial",
                         "A3D2D3.surgeryCertificate_emptyRelation",
                         "A3D2D3.not_missingConjugateHeatKernel_zero",
                         "A3D2D3.not_missingKappaNoncollapsing_zero",
                         "A3D2D3.neckAnalysis_inhabited"],
        },
        {
            "id": "A3-D2D3-6",
            "class": "TRIVIAL / OVERSTRONG (kernel-checked)",
            "statement": ("Poincare.Longrun.Surgery.ExtinctionTheorem / MissingInputs and "
                          "Poincare.Longrun.PDE.HeatGridEvolution.le_of_initial_le"),
            "verdict": ("(a) ExtinctionTheorem's four Prop fields can all be set to True with trivial "
                        "implications, so 'finite-time extinction' and 'terminal manifold is S^3' are free "
                        "fields; MissingInputs can therefore pair a trivial neck analysis with an extinction "
                        "half that is true by definition. (b) In the discrete maximum principle "
                        "HeatGridEvolution.le_of_initial_le the hypothesis hM : 0 <= M is redundant: the "
                        "left Dirichlet boundary at t=0 and the initial bound already imply it; the sharp "
                        "restatement heatGrid_le_of_initial_le_no_hM removes it. (hM is NOT redundant in "
                        "zeroExtend_le / succ_le, which have no initial data.)"),
            "evidence": ["A3D2D3.extinctionTheorem_true",
                         "A3D2D3.missingInputs_with_true_extinction",
                         "A3D2D3.heatGrid_le_of_initial_le_no_hM"],
        },
        {
            "id": "A3-D2D3-7",
            "class": "OVERSTRONG (kernel-checked sharp restatement)",
            "statement": ("Poincare.Longrun.Topology.kappaNoncollapsingCertificate_iff_"
                          "normalizedBallVolumeLowerBound"),
            "verdict": ("the hypotheses hκ : 0 < κ and hr₀ : 0 < r₀ are redundant: both are fields of "
                        "either side of the equivalence. The sharp restatement "
                        "A3D2D3.kappa_iff_normalized_no_hyp removes them, reproducing the prior "
                        "audit's finding F7 with a compiled sharp theorem."),
            "evidence": ["A3D2D3.kappa_iff_normalized_no_hyp"],
        },
    ],
    "semantic_class": {
        "A3D2D3.linearDecay_uninhabited": "VACUOUS (empty certificate structure)",
        "A3D2D3.covariantCurvatureStatement_trivial": "TRIVIAL (BLOCKED label wrong)",
        "A3D2D3.bridgeWitness": "MODEL WITNESS (degenerate)",
        "A3D2D3.bridge_forces_zero_traj": "VACUOUS/OVERSTRONG (all inhabitants zero)",
        "A3D2D3.missingSphereRecognitionAlgorithm_trivial": "TRIVIAL (excluded middle)",
        "A3D2D3.surgeryCertificate_emptyRelation": "VACUOUS (datum-blind certificate)",
        "A3D2D3.not_missingConjugateHeatKernel_zero": "FALSE-INSTANCE (zero measure)",
        "A3D2D3.not_missingKappaNoncollapsing_zero": "FALSE-INSTANCE (zero measure)",
        "A3D2D3.neckAnalysis_inhabited": "TRIVIAL (empty-content missing input)",
        "A3D2D3.extinctionTheorem_true": "TRIVIAL (conclusions are free fields)",
        "A3D2D3.missingInputs_with_true_extinction": "TRIVIAL (extinction half true by definition)",
        "A3D2D3.heatGrid_le_of_initial_le_no_hM": "SHARP RESTATEMENT (redundant hM removed)",
        "A3D2D3.kappa_iff_normalized_no_hyp": "SHARP RESTATEMENT (redundant positivity hypotheses removed)",
    },
}


CARDS7 = [
    "D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
    "D12-semantic-ledger", "D12-comparison-geodesics", "D12-geometric-compactness",
    "D12-surgery-recognition",
]


def probe_decl_count(card):
    p = os.path.join(LOGS, card + ".probe.log")
    if not os.path.exists(p):
        return None
    txt = open(p, encoding="utf-8", errors="replace").read()
    return txt.count("depends on axioms") + txt.count("does not depend on any axioms")


def main():
    d = json.load(open(OUT))
    d["generated_at"] = time.strftime("%Y-%m-%dT%H:%M:%S%z")
    d["status"] = "TASK_BLOCKED"
    d["verdict"] = (
        "7/9 360-produced D12 cards independently rebuilt, re-hashed, axiom-audited and "
        "semantically reviewed; 4/4 claimed exact_blockers_closed confirmed; 2/9 cards "
        "(D12-tensor-maximum-bochner, D12-triangulation-topology) have no artifact anywhere on "
        "this host and no transport route, so the 9-card milestone CANNOT be fully checked here. "
        "Additionally the A3-requested D2/D3 counterexample search was performed: 6 kernel-checked "
        "defect families (17 declarations) reproduced independently from accepted D6 sources, and one headline "
        "finding of the earlier D2/D3 audit (entropy sign F2) refuted.")
    d["named_blocker_status"]["A3"] = (
        "STALE-AS-STATED, PARTIALLY ADDRESSED. A3 records 'earlier clusters (D2/D3) have axiom "
        "audits but no counterexample search'. That search now exists twice over: (i) the prior "
        "VERIFIER-D7-adversarial-audit-d2d3 card (Sep 9) and (ii) this round's independent probe "
        "a3d2d3/A3D2D3.lean compiled from accepted D6 sources (17 declarations, 0 cone violations), "
        "which reproduced the vacuity/degeneracy findings F1/F3/F4/F5 and refuted the audit's own "
        "F2. A3 is NOT closed as a quality gate: the found D2/D3 defects are unrepaired, its "
        "headline F2 was itself wrong, and the two absent D12 cards leave the audit incomplete.")
    d["a3_d2d3_search"] = A3
    d["proved_declarations"]["A3-D2D3"] = [
        "A3D2D3.linearDecay_uninhabited", "A3D2D3.linearDecay_isEmpty",
        "A3D2D3.linearDecay_fields_contradict", "A3D2D3.covariantCurvatureStatement_trivial",
        "A3D2D3.form_eq_of_basis_eq", "A3D2D3.bridgeWitness",
        "A3D2D3.bridge_forces_zero_ricci", "A3D2D3.bridge_forces_zero_traj",
        "A3D2D3.missingSphereRecognitionAlgorithm_trivial",
        "A3D2D3.surgeryCertificate_emptyRelation",
        "A3D2D3.not_missingConjugateHeatKernel_zero",
        "A3D2D3.not_missingKappaNoncollapsing_zero", "A3D2D3.neckAnalysis_inhabited",
        "A3D2D3.extinctionTheorem_true", "A3D2D3.missingInputs_with_true_extinction",
        "A3D2D3.heatGrid_le_of_initial_le_no_hM", "A3D2D3.kappa_iff_normalized_no_hyp",
    ]
    d["expanded_hypotheses"]["A3-D2D3"] = {
        "LinearDecayCertificate": (
            "X with MeasurableSpace, mu : Measure X, E : R -> EntropyData X mu; fields cert : "
            "ContinuousAntitoneCertificate E (analytic inputs explicit: dissipation, HasDerivAt, "
            "ContinuousOn, sign, lowerBound, lower_le), rate with 0 < rate, decay : forall t >= 0, "
            "F(E t) <= F(E 0) - rate*t. The lower bound and the linear decay are jointly "
            "unsatisfiable in R."),
        "TensorRicciFlowODEBridge": (
            "V finite-dimensional real vector space, finite index type iota, model space E, model "
            "domain H, I : ModelWithCorners R E H, M charted 1-manifold, cov : CovariantDerivative, "
            "F : ReactionField iota, T : R, traj : R -> iota -> R, DiffusionVanishes : Prop; fields "
            "metric, curvature, basis_fixed, state_eq, realization (manifold curvature AND diagonal "
            "Ricci-flow equation AND metric-curvature shadow AND diffusion vanishes), evolves, "
            "continuous. basis_fixed + orthonormal force the metric form constant, so the diagonal "
            "Ricci-flow equation forces ricci = 0 on [0,T]."),
        "missing theorems": (
            "missingSphereRecognitionAlgorithm quantifies over all compact T2 EuclideanThree-charted "
            "M with conclusion Nonempty (Decidable (M =~ S^3)); missingConjugateHeatKernel and "
            "missingKappaNoncollapsing take an arbitrary measure mu with no positivity hypothesis."),
    }
    d["semantic_class"]["A3-D2D3"] = A3["semantic_class"]
    d["semantic_class_corrections"] = {
        "L-D2-LEVI-CIVITA": {
            "card_class": "genuine-general",
            "card_note": "LeviCivitaExistenceStatement and CovariantDerivativeCurvatureStatement are BLOCKED Props (blocker I1).",
            "audited_correction": ("the note is refuted in both halves: CovariantDerivativeCurvatureStatement is "
                                   "trivially inhabited (zero tensor, cov unused), and LeviCivitaExistenceStatement "
                                   "is a compiled theorem (Poincare.D12.ConnectionCurvature.leviCivitaExists, "
                                   "Milnor witness, allowed cone). The entry's declarations are genuine, but the "
                                   "note and the 'BLOCKED' framing must be corrected."),
        },
        "L-D2-ODE-SCALAR-MONO": {
            "card_class": "genuine-general",
            "card_note": "scalarCurvature_monotone_of_bridge is conditional on the uninhabited TensorRicciFlowODEBridge (blocker I3).",
            "audited_correction": ("refuted: the bridge is inhabited (A3D2D3.bridgeWitness) and every inhabitant with "
                                   "0 < T has ricci = 0, hence traj = 0 on [0,T] (A3D2D3.bridge_forces_zero_traj). The entry "
                                   "should be classified model/degenerate, not 'conditional on an uninhabited interface'."),
        },
        "L-D3-ENTROPY-CERTIFICATES": {
            "card_class": "model",
            "card_note": "monotonicity and decay certificates are kernel-checked; all analytic inputs are explicit hypotheses.",
            "audited_correction": ("the 'decay certificate' item is vacuous: LinearDecayCertificate is provably empty "
                                   "(A3D2D3.linearDecay_uninhabited); the entry lists its projections among checked "
                                   "declarations without a vacuity flag."),
        },
        "L-D3-SURGERY-INTERFACE": {
            "card_class": "model",
            "card_note": "NeckAnalysis, ExtinctionTheorem and MissingInputs are statement-only (blocker I6).",
            "audited_correction": ("sharper: NeckAnalysis is inhabited with all Prop fields False "
                                   "(A3D2D3.neckAnalysis_inhabited), so as a structure it imposes no obligation."),
        },
    }
    d["exact_blockers_closed"]["A3-D2D3"] = []
    d["remaining_blockers"]["A3-D2D3"] = [
        "LinearDecayCertificate is empty: the D3 entropy interface has no non-vacuous linear decay certificate; the fields must be restated (e.g. decay only up to the lifetime, or drop the global lower bound).",
        "CovariantDerivativeCurvatureStatement is a triviality and cannot serve as the BLOCKED manifold-curvature input; the D12-semantic-ledger note L-D2-LEVI-CIVITA must be corrected (and its LeviCivitaExistenceStatement half is stale: leviCivitaExists is compiled).",
        "TensorRicciFlowODEBridge is inhabited only degenerately (traj = 0): the D12-semantic-ledger note L-D2-ODE-SCALAR-MONO ('uninhabited') is false and the transfer theorems need a non-degenerate bridge statement.",
        "missingSphereRecognitionAlgorithm / missingConjugateHeatKernel / missingKappaNoncollapsing / SurgeryCertificate are statement defects in the D1-D6 release; they are not repaired by this audit.",
        "The earlier VERIFIER-D7 audit's F2 must be withdrawn by its producer (its other headline findings are independently corroborated here).",
        "ExtinctionTheorem conclusions are free fields and the discrete maximum principle's hM is redundant (A3D2D3-6): restate both.",
        "Remove the redundant 0 < κ, 0 < r₀ hypotheses from kappaNoncollapsingCertificate_iff_normalizedBallVolumeLowerBound (A3D2D3-7, prior audit F7).",
    ]
    d["source_hashes"]["A3-D2D3"] = {
        "probe_sha256": PROBE_SHA,
        "package_lean_tree_sha256": TREE_SHA,
        "base_release_byte_identical": True,
        "d6_release_copy_diff": "empty (diff -rq a3d2d3 release --exclude=.lake --exclude=A3D2D3.lean)",
    }
    d["compile_evidence"]["A3-D2D3"] = {
        "toolchain": "leanprover/lean4:v4.34.0-rc2",
        "mathlib_rev": "7974e751bece493b6ff508039423ca9fa2452fa8",
        "lake_build_rc": log_rc("a3d2d3.build.rc"),
        "lake_build_jobs": 8946,
        "probe_rc": log_rc("a3d2d3.probe.rc"),
        "levicivita_crosscheck_rc": 0,
        "build_log_sha256": log_hash("a3d2d3.build.log"),
        "probe_log_sha256": log_hash("a3d2d3.probe.log"),
        "levicivita_log_sha256": log_hash("a3d2d3.levicivita_check.log"),
    }
    d["axiom_evidence"]["A3-D2D3"] = {
        "audited_declarations": 17,
        "cone_histogram": {"propext,Classical.choice,Quot.sound": 14, "Classical.choice": 1, "(none)": 2},
        "cone_violations": {},
        "negative_control": "same fail-closed predicate as the 7-card audit (sorryAx/native_decide flagged)",
    }
    new_ids = {"F8", "F9", "F10", "F11"}
    d["findings"] = [f for f in d["findings"] if f.get("id") not in new_ids]
    d["findings"].extend([
        {
            "id": "F8",
            "severity": "semantic-classification (refuted ledger note)",
            "card": "D12-semantic-ledger",
            "finding": ("Ledger note L-D2-LEVI-CIVITA says LeviCivitaExistenceStatement and "
                        "CovariantDerivativeCurvatureStatement are BLOCKED Props. The second is "
                        "unconditionally inhabited by the zero tensor (A3D2D3.covariantCurvatureStatement_trivial), "
                        "so the label is wrong; the first is stale, since Poincare.D12.ConnectionCurvature.leviCivitaExists "
                        "is a compiled proof (fresh #check/#print axioms in this audit: type correct, cone "
                        "{propext, Classical.choice, Quot.sound}). The entry is nevertheless classified "
                        "genuine-general."),
        },
        {
            "id": "F9",
            "severity": "semantic-classification (refuted ledger note)",
            "card": "D12-semantic-ledger",
            "finding": ("Ledger note L-D2-ODE-SCALAR-MONO says scalarCurvature_monotone_of_bridge is "
                        "'conditional on the uninhabited TensorRicciFlowODEBridge'. The bridge is inhabited "
                        "(A3D2D3.bridgeWitness) and every inhabitant with 0 < T has ricci = 0 hence traj = 0 on [0,T] "
                        "(A3D2D3.bridge_forces_zero_traj): the correct defect is degeneracy, not uninhabitedness. "
                        "The ledger entry L-D3-ENTROPY-CERTIFICATES additionally lists "
                        "LinearDecayCertificate.decay/rate_pos among checked decay certificates, but the "
                        "structure is provably empty (A3D2D3.linearDecay_uninhabited)."),
        },
        {
            "id": "F10",
            "severity": "statement defect (release D1-D6)",
            "card": "A3-D2D3-search",
            "finding": ("missingSphereRecognitionAlgorithm is trivially true (classical decidability) and "
                        "captures no algorithm; SurgeryCertificate has no field mentioning the surgery datum, "
                        "so certificates exist for data with empty relation; missingConjugateHeatKernel and "
                        "missingKappaNoncollapsing are false for the zero measure. All four are kernel-checked "
                        "in A3D2D3.lean."),
        },
        {
            "id": "F11",
            "severity": "audit-of-the-auditor (refutation)",
            "card": "VERIFIER-D7-adversarial-audit-d2d3",
            "finding": ("The prior D2/D3 adversarial audit's finding F2 ('entropy bridge has the wrong sign') "
                        "is itself false: Perelman's original eq. (1.4) gives F_t = +2 int |R_ij + grad_i grad_j f|^2 "
                        "e^{-f} dV >= 0, matching the release's FDerivativeStatement. Its F11 (conjugate heat "
                        "equation missing the R rho term) is confirmed. Its F1/F3/F4/F5 headline defects were "
                        "independently reproduced."),
        },
    ])
    d["next_dependency_requests"] = [
        "Apply audit360/corrected-names-D12-connection-curvature.json to the D12-connection-curvature card inventory (73 over-qualified + 1 ambiguous entry).",
        "Sync or re-run D12-tensor-maximum-bochner and D12-triangulation-topology (remote hosts 360-1/360-2); no transport route (reverse tunnel 127.0.0.1:10022 refused) and no artifact on this host, so the 9-card milestone is blocked, not refuted.",
        "Producer-side correction of the D12-connection-curvature proved_declarations namespace qualification (73 entries) and of the D12-comparison-geodesics grouped-name strings.",
        "Producer-side correction of the D12-semantic-ledger notes L-D2-LEVI-CIVITA and L-D2-ODE-SCALAR-MONO and of the L-D3-ENTROPY-CERTIFICATES classification (F8/F9).",
        "Withdraw/correct VERIFIER-D7 F2 (entropy sign) and repair the D2/D3 defects it found: LinearDecayCertificate emptiness, trivial CovariantDerivativeCurvatureStatement, degenerate TensorRicciFlowODEBridge, false-instance missing theorems (F10/F11).",
        "Add non-reflexive model witnesses for the singular Riccati comparison and the Bishop-Gromov volume ratio in D12-comparison-geodesics.",
    ]
    d["integrity_recheck_round2"] = {
        "ran_at": "2026-09-11T13:2x+08:00",
        "producer_source_hashes": {
            "script": "audit360/inventory.py",
            "result": "all recorded hashes re-verify against disk with bad=0: "
                      "connection-curvature 12, volume-ibp 11, spectral-sobolev 8, semantic-ledger 66, "
                      "comparison-geodesics 8, geometric-compactness 6, surgery-recognition 8; "
                      "D12-volume-ibp reports one ambiguous short-name candidate but all per-key "
                      "verdicts are ok",
        },
        "card_file_freeze": json.load(open(os.path.join(HERE, "card_freeze_round2.json"))),
        "note": ("producer card .md/.json are unchanged since the audited window "
                 "(mtimes 2026-09-11 02:02-04:50); the audit verdicts are not stale"),
    }
    d["semantic_review_round2"] = {
        "D12-semantic-ledger": {
            "claim": "D7 HeatKernelData.initialCondition (Continuous f only) is false on R for the Gaussian kernel",
            "review": ("proof read line-by-line: integrand_eq, quartic_dominates (y^4 - y^2/(4t) >= y^4/2 on "
                       "[R t, inf), R t = sqrt(1/(2t))), lowerConstant_le_integrand, integrand_lintegral_eq_top "
                       "(positive constant on an infinite-measure half-line => lintegral = inf), "
                       "integrand_not_integrable, integral_undef_zero, not_initialCondition_gaussian_quantified "
                       "(f = exp(y^4), f 0 = 1, integral identically 0 on (0,inf), limit cannot be 1)"),
            "verdict": "REVIEWED-CORRECT: the estimate and the contradiction are valid; the statement matches the D7 field shape",
        },
        "D12-spectral-sobolev": {
            "claim": "the Poincare-Wirtinger constant ((b-a)/2pi)^2 is sharp for the circle",
            "review": ("poincare_wirtinger_sine_saturates (sine wave attains equality, both sides pi) and "
                       "poincare_constant_sharp (any admissible C satisfies 1 <= C, witnessed by the same sine "
                       "wave) read and checked"),
            "verdict": "REVIEWED-CORRECT: non-vacuous equality witness plus lower bound on any admissible constant",
        },
    }
    d["full_namespace_recheck_round2"] = {
        "ran_at": "2026-09-11T13:45+08:00",
        "script": "audit360/run_full_audit.sh per card",
        "cards": json.load(open(os.path.join(HERE, "fullaudit_round2.json"))),
        "total_declarations": 1103,
        "verdict": "PASS on all 7 (0 unapproved axioms), identical counts to round 1",
        "note": "reproduces the 1103-constant complete-namespace audit at the end of the audit window",
    }
    d["corrected_inventory_artifacts"] = {
        "D12-connection-curvature": {
            "file": "audit360/corrected-names-D12-connection-curvature.json",
            "over_qualified_entries": 73,
            "ambiguous_entries": 1,
            "use": "producer-side fix for F1; mapping declared -> fully-qualified name from the compiled sources",
        },
    }
    d["vacuity_screen_round2"] = {
        "script": "audit360/vacuity_screen2.py",
        "criteria": ("T1 conclusion True; T2 Nonempty (Decidable _); T3 top-level Subsingleton; "
                     "T4 trivial equality X = X; T5 trivial iff P <-> P; T6 numeric triviality; "
                     "T8 unused underscore hypothesis. Flags are review triggers, not verdicts."),
        "card_entries": 342,
        "distinct_declarations_parsed": 335,
        "duplicate_resolutions": 7,
        "duplicate_detail": ("the 7 duplicates are D12-connection-curvature card entries carrying the "
                            "over-qualified prefix ChartLeviCivitaSmooth. that resolve to the same "
                            "declaration as the correctly-qualified entry (evidence for F1)"),
        "flags": 8,
        "flags_reviewed": ("all 8 are false positives of the heuristics: conformalGamma_origin_zero "
                          "(gamma ... 0 = 0), conformal_denom_pos (0 < 1 + x^2), heatEvolve_zero "
                          "(heatEvolve T 0 f = f), and five substantive Subsingleton-valued surgery "
                          "statements (fiber subsingleton, monodromy trivial, deck trivial, quotient "
                          "homeomorphism, sphericalPieceRecognition_of)"),
        "true_positives": 0,
        "conclusion": ("no vacuous or trivial card-declared statement found by this independent screen; "
                       "combined with the 1103-constant namespace audit, the 'no false/vacuous statement' "
                       "claim for the 7 available cards is supported by a documented method"),
    }
    f1 = [x for x in d["findings"] if x.get("id") == "F1"]
    if f1:
        addendum = (" Round 2 addendum: 7 of the over-qualified entries (ChartLeviCivitaSmooth.*) "
                    "resolve to the same declaration as their correctly-qualified twin, so the 119-entry "
                    "list covers 112 distinct names and the 342 entries across the 7 cards cover 335 "
                    "distinct declarations.")
        if addendum.strip() not in f1[0]["finding"]:
            f1[0]["finding"] += addendum
    d["reverification_round2"] = {
        "ran_at": "2026-09-11T13:04-13:06+08:00",
        "cards": {
            c: {
                "build_rc": log_rc(c + ".build.rc"),
                "probe_rc": log_rc(c + ".probe.rc"),
                "probe_declarations": probe_decl_count(c),
                "build_log": "audit360/logs/" + c + ".build.log",
                "probe_log": "audit360/logs/" + c + ".probe.log",
            }
            for c in CARDS7
        },
        "note": ("all 7 available cards re-built (incremental lake build, cache hits, rc 0) and "
                 "their A3Probe.lean re-run (rc 0, declaration counts unchanged); round-1 cold-rebuild "
                 "evidence preserved under audit360/logs-round1/"),
    }
    d["elapsed_hours"] = 1.3
    d["cumulative_task_hours"] = 1.8
    d["blocked_reason"] = (
        "D12-tensor-maximum-bochner and D12-triangulation-topology have no worktree/release/card/module "
        "anywhere on this host (exhaustive find over /data3/guoshaoyang) and the reverse-tunnel transport "
        "(127.0.0.1:10022) is refused, so 2 of the 9 requested cards cannot be rebuilt, re-hashed or "
        "axiom-audited from this worktree. Everything available has been audited.")
    json.dump(d, open(OUT, "w"), indent=1, ensure_ascii=False)
    print("wrote", OUT)
    print("status:", d["status"], "| A3 findings:", len(A3["findings"]))


if __name__ == "__main__":
    main()
