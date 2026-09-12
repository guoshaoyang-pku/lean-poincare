#!/usr/bin/env python3
"""Build audit-evidence/expanded-hypotheses.json and blocker-verdicts.json.

Types are extracted verbatim from the fresh kernel-audit inventory; the hypothesis
classification and the closure verdicts are the D13 auditor's judgement, recorded here so
the result JSON is self-contained.
"""
import json
from collections import defaultdict
from pathlib import Path

WT = Path("/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-integrated-kernel-audit")
EVID = WT / "audit-evidence"
LOG = EVID / "logs" / "11-kernel-audit.log"

types = {}
if LOG.exists():
    for line in LOG.read_text(errors="replace").splitlines():
        p = line.split("\t")
        if p[0] == "D13TYPE":
            types[p[1]] = "\t".join(p[4:])

CURATED = [
    ("Poincare.D12.HeatDomain.not_fullInitialCondition_flat_of_pos",
     "general (negative result)", "n : ℕ; 0 < n (dimension/positivity, standard)",
     "Refutes the unchanged legacy D7 `FullInitialCondition` for the explicit flat kernel in every positive dimension; no unproved input."),
    ("Poincare.D12.HeatDomain.flatHeatKernelCore_weakInitialConditionFor_integrableClass",
     "Euclidean model (v1 interface)", "n : ℕ only",
     "Constructs the repaired interface inhabitant in every dimension; no `FullInitialCondition` hypothesis."),
    ("Poincare.D12.SemanticLedger.not_initialCondition_gaussian",
     "general (negative result)", "none (closed negation)",
     "Kernel-checked refutation of the literal D7 initial-condition field against the real D7 structure with the Gaussian kernel; validates the D11 defect claim."),
    ("Poincare.D12.HeatSemigroup.heatOperatorBCF_comp",
     "Euclidean model", "n : ℕ; s > 0; t > 0",
     "Operator semigroup law on the sup-norm Banach space of bounded continuous functions; consumes the bounded `heatOperator_comp_heatOperator_of_bounded` constructor."),
    ("Poincare.D12.ConnectionCurvature.milnorConnection_isLeviCivita",
     "general (abstract left-invariant model)",
     "finite-dimensional real V, finite index ι; MetricData V ι; LieBracketData (skew + Jacobi)",
     "Milnor/Koszul construction: for arbitrary metric data and Lie bracket data the explicit formula is torsion-free and metric-compatible. Abstract (not a manifold-chart theorem)."),
    ("Poincare.D12.ConnectionCurvature.leviCivitaExists",
     "general (abstract left-invariant model)", "as above",
     "Existential corollary `∃ nabla, IsLeviCivita m b nabla`. Had no retained downstream consumer; D13 supplies `Nonvacuity.d13_consumer_leviCivitaExists`."),
    ("Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere",
     "general topology", "n : ℕ; arbitrary h : Sphere n ≃ₜ Sphere n",
     "The quotient of two closed (n+1)-balls glued along their boundary spheres by an arbitrary homeomorphism is homeomorphic to S^{n+1}."),
    ("Poincare.D12.TriangulationTopology.coveringOfSimplyConnectedIsHomeo",
     "general topology",
     "compact T2 E, path-connected E, simply-connected X, p : E → X a covering, p surjective",
     "A surjective covering from a compact path-connected space onto a simply connected space is a homeomorphism."),
    ("Poincare.D12.SpectralSobolev.poincare_wirtinger",
     "general within the 1-torus model",
     "a < b; C¹ f with f b = f a; zero mean (fourierCoeffOn hab f 0 = 0); IntervalIntegrable f'; MemLp 2 of f and f'",
     "Poincaré–Wirtinger inequality with the optimal constant ((b-a)/2π)² on the interval/1-torus model; genuine infinite-dimensional statement."),
    ("Poincare.D12.ParabolicLocal.existsUnique_heatMildSolution",
     "general semilinear parabolic model",
     "n : ℕ; F LipschitzWith L on BUCn; u₀; 0 ≤ T; L*T < 1",
     "Banach fixed point for the Duhamel map of a semilinear heat equation with a fully discharged Gaussian heat semigroup instance. Not quasilinear Ricci–DeTurck."),
    ("Poincare.D12.ComparisonGeodesics.bishopGromovVolumeRatio",
     "conditional analytic (ODE densities)",
     "0<d, 0<T, 0≤C, 0<t₀≤T; Riccati differential inequalities for m, m̄; derivative/continuity regularity",
     "Bishop–Gromov-type volume ratio comparison for density functions satisfying the Riccati inequalities; becomes geometric only when A is identified with geodesic-sphere (n-1)-volume, which is not constructed."),
    ("Poincare.D12.KappaVariational.gaussianReducedVolume_eq_one",
     "model calculation", "n : ℕ; 0 < τ",
     "Gaussian reduced-volume normalisation equals 1; a continuum Gaussian integral computation, not a general reduced-volume theorem."),
    ("Poincare.D12.TensorMaximumBochner.kernelTangent_of_feasibleDirection",
     "general (finite-dimensional matrix)",
     "finite n; A N : Matrix n n ℝ; FeasibleDirection A N",
     "Necessity of Hamilton's null-eigenvector tangent-cone condition; the *sufficient* direction (PSD-cone invariance) remains the D12 blocked input B1."),
    ("Poincare.D12.VolumeIBP.ChartMetric.integral_riemannianMeasure_eq",
     "model (Euclidean chart)", "chart metric G; f : Vec d → ℝ",
     "Chart-level Riemannian measure equals the density-weighted Lebesgue integral; global manifold gluing remains a named blocker."),
    ("Poincare.D12.SurgeryRecognition.stage6Target_of_v3hypotheses",
     "conditional assembly",
     "compact, T2, ℝ³-charted, simply connected X; ExtinctionCertificate; ConnectedSumDecompositionV2; RemainingRecognitionHypothesesV3; CanonicalNeighborhoodInput",
     "Kernel-checked implication to the Stage6 statement-only target. The geometric antecedents (extinction, canonical neighbourhoods, space-form recognition) are explicit unproved inputs."),
]

expanded = []
for name, cls, hyps, note in CURATED:
    expanded.append({
        "declaration": name,
        "semantic_class": cls,
        "full_type": types.get(name, "<not found in fresh inventory>"),
        "hypotheses_expanded": hyps,
        "audit_note": note,
    })
(EVID / "expanded-hypotheses.json").write_text(json.dumps(expanded, indent=1, ensure_ascii=False) + "\n")

# pair-level evidence from the dependency probe (downstream, constructor, in_type, in_proof)
pair_evidence = defaultdict(list)
for line in (EVID / "logs" / "14-dependency-probe.log").read_text(errors="replace").splitlines():
    p = line.split("\t")
    if p[0] == "D13DEP":
        pair_evidence[p[1]].append({"downstream": p[2], "constructor": p[3],
                                    "in_type": p[4] == "true", "in_proof": p[5] == "true"})

# ---- closure verdicts -----------------------------------------------------------------
uses = {}
for line in (EVID / "logs" / "13-usage-probe.log").read_text(errors="replace").splitlines():
    p = line.split("\t")
    if p[0] == "D13USE" and len(p) >= 5:
        uses[p[1]] = int(p[2])

VERDICTS = [
    {"task": "D12-connection-curvature",
     "claimed_blocker": "LeviCivitaExistenceStatement blocked",
     "constructors": ["Poincare.D12.ConnectionCurvature.milnorConnection",
                      "Poincare.D12.ConnectionCurvature.leviCivitaExists"],
     "claimed_downstream": "so3MeanLeviCivita -> ricci_symm / so3_ricci_e00",
     "retained_users": {c: uses.get(c) for c in
                        ["Poincare.D12.ConnectionCurvature.milnorConnection",
                         "Poincare.D12.ConnectionCurvature.leviCivitaExists"]},
     "verdict": "verified_with_caveat",
     "d13_assessment": ("The construction and its Levi-Civita property are genuine and the witness "
                        "`milnorConnection` has 10 retained consumers; the *existential* corollary "
                        "`leviCivitaExists` itself has 0 retained consumers (D13 supplies one). The "
                        "card's arrow chain routes through `milnorConnection`, not through "
                        "`leviCivitaExists`.")},
    {"task": "D12-entropy-variation",
     "claimed_blocker": "B-D7-F-DERIVATIVE",
     "constructors": ["Poincare.D12.EntropyVariation.hasDerivAt_F_of_pointwise",
                      "Poincare.D12.EntropyVariation.fflow_F_hasDerivAt",
                      "Poincare.D12.EntropyVariation.fDerivativeStatement_of_corrected_of_idempotent"],
     "claimed_downstream": "fflow_F_hasDerivAt_closedForm -> fflow_F_deriv_pos -> fflow_F_strictMonoOn -> derivative_sign_distinction",
     "retained_users": {c: uses.get(c) for c in
                        ["Poincare.D12.EntropyVariation.hasDerivAt_F_of_pointwise",
                         "Poincare.D12.EntropyVariation.fflow_F_hasDerivAt",
                         "Poincare.D12.EntropyVariation.fDerivativeStatement_of_corrected_of_idempotent"]},
     "verdict": "verified_with_caveat",
     "d13_assessment": ("The chain hasDerivAt_F_of_pointwise (8 users) -> fflow_F_hasDerivAt (5) -> "
                        "closedForm (2) -> deriv_pos (1) -> strictMonoOn (2) -> "
                        "derivative_sign_distinction is retained and kernel-clean. The literal-D7 "
                        "bridge `fDerivativeStatement_of_corrected_of_idempotent` has 0 retained "
                        "consumers; D13 supplies one. Closure is conditional at the pointwise level, "
                        "as the card itself states.")},
    {"task": "D12-heat-domain-repair",
     "claimed_blocker": "D11 initial-condition domain defect",
     "constructors": ["Poincare.D12.HeatDomain.notIntegrable_fast_times_kernel",
                      "Poincare.D12.HeatDomain.not_fullInitialCondition_flat_of_pos",
                      "Poincare.D12.HeatDomain.flatHeatKernelCore_weakInitialConditionFor_integrableClass"],
     "claimed_downstream": "flat_positive_dimension_weak_not_full; compact finite-measure upgrade",
     "retained_users": {c: uses.get(c) for c in
                        ["Poincare.D12.HeatDomain.notIntegrable_fast_times_kernel",
                         "Poincare.D12.HeatDomain.not_fullInitialCondition_flat_of_pos",
                         "Poincare.D12.HeatDomain.flatHeatKernelCore_weakInitialConditionFor_integrableClass"]},
     "verdict": "verified",
     "d13_assessment": ("The counterexample, the refutation of the legacy field, and the repaired "
                        "interface inhabitant are all present, consumed downstream, and kernel-clean. "
                        "D13 independently re-elaborates the negated statement at n = 1.")},
    {"task": "D12-heat-semigroup-analysis",
     "claimed_blocker": "operator semigroup law",
     "constructors": ["Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator",
                      "Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator_of_bounded",
                      "Poincare.D12.HeatSemigroup.heatOperatorBCF_comp"],
     "claimed_downstream": "heatOperator_gaussianKernel_L1_tendsto_seq",
     "retained_users": {c: uses.get(c) for c in
                        ["Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator",
                         "Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator_of_bounded",
                         "Poincare.D12.HeatSemigroup.heatOperatorBCF_comp",
                         "Poincare.D12.HeatSemigroup.heatOperator_gaussianKernel_L1_tendsto_seq"]},
     "verdict": "partially_over_claimed",
     "d13_assessment": ("The semigroup law itself is genuine and consumed (7 users for the general "
                        "form, 3 for the bounded form). The card's stated downstream for "
                        "`heatOperatorBCF_comp` is wrong: its only transitive consumer is "
                        "`heatOperatorBCF_comp_swap`; `heatOperator_gaussianKernel_L1_tendsto_seq` "
                        "does not reference it.")},
    {"task": "D12-kappa-variational",
     "claimed_blocker": "RLV-10 / NCF-12 / RLV-1 Gaussian-model closures",
     "constructors": ["Poincare.D12.KappaVariational.gaussianReducedVolume_eq_one",
                      "Poincare.D12.KappaVariational.gaussianReducedVolumeViaL_eq_one",
                      "Poincare.D12.KappaVariational.constantCurvatureLMinimizerExistence"],
     "claimed_downstream": "gaussianReducedVolumeCertificate_volume; gaussianUniformReducedVolumeLowerBound; constantCurvature_reducedLength_le",
     "retained_users": {c: uses.get(c) for c in
                        ["Poincare.D12.KappaVariational.gaussianReducedVolume_eq_one",
                         "Poincare.D12.KappaVariational.gaussianReducedVolumeViaL_eq_one",
                         "Poincare.D12.KappaVariational.constantCurvatureLMinimizerExistence"]},
     "verdict": "verified (model level)",
     "d13_assessment": ("All three model-space constructors have retained consumers (8/3/3 named) "
                        "and are consumed by the task's own closure records "
                        "(`kappaVariationalClosures`, `rlv10Closure`, `ncf12ModelClosure`). "
                        "Model-level only, not the general RLV/NCF statements.")},
    {"task": "D12-parabolic-local-existence",
     "claimed_blocker": "Gaussian smap continuity; semigroup law; BUC strong continuity; derivative-loss barrier",
     "constructors": ["Poincare.D12.ParabolicLocal.gaussianSmap_continuous",
                      "Poincare.D12.ParabolicLocal.heatConv_semigroup",
                      "Poincare.D12.ParabolicLocal.heatConv_tendsto_self_BUC",
                      "Poincare.D12.ParabolicLocal.derivativeLossBarrier_holds"],
     "claimed_downstream": "linearCandidate_isFixedPt; gaussianS_tendsto_self; derivativeLossBarrier_discharged",
     "retained_users": {c: uses.get(c) for c in
                        ["Poincare.D12.ParabolicLocal.gaussianSmap_continuous",
                         "Poincare.D12.ParabolicLocal.heatConv_semigroup",
                         "Poincare.D12.ParabolicLocal.heatConv_tendsto_self_BUC",
                         "Poincare.D12.ParabolicLocal.derivativeLossBarrier_holds"]},
     "verdict": "verified",
     "d13_assessment": ("Each constructor has 13-17 named retained consumers and the chain reaches "
                        "`existsUnique_heatMildSolution`. The derivative-loss barrier is proved as a "
                        "negation and consumed by `derivativeLossBarrier_discharged`.")},
    {"task": "D12-surgery-recognition",
     "claimed_blocker": "SR-5 sphere_of_spheres; covering recognition; coveringTrivial",
     "constructors": ["Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2",
                      "Poincare.D12.SurgeryRecognition.finiteFreeOrbit_isQuotientCoveringMap",
                      "Poincare.D12.SurgeryRecognition.deckTrivial_of_simplyConnected_quotient"],
     "claimed_downstream": "stage6Target_of_v2/v3hypotheses; RemainingRecognitionHypothesesV2/V3.toRemaining; sphericalPieceRecognition_of_spaceForm",
     "retained_users": {c: uses.get(c) for c in
                        ["Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2",
                         "Poincare.D12.SurgeryRecognition.finiteFreeOrbit_isQuotientCoveringMap",
                         "Poincare.D12.SurgeryRecognition.deckTrivial_of_simplyConnected_quotient"]},
     "verdict": "verified",
     "d13_assessment": ("Constructors are retained and consumed by the V3 hypothesis records that feed "
                        "`stage6Target_of_v3hypotheses`; the latter remains a conditional assembly "
                        "(extinction, canonical neighbourhoods and space-form recognition are still "
                        "hypotheses). The van Kampen asset (SR-4) is absent from the relay; D13 "
                        "recovered and audited `release/Poincare/VKPort`.")},
    {"task": "D12-triangulation-topology",
     "claimed_blocker": "DAG nodes 4/5/7/8/9/10/13",
     "constructors": ["Poincare.D12.TriangulationTopology.coveringOfSimplyConnectedIsHomeo",
                      "Poincare.D12.TriangulationTopology.antipodalQuotientCovering",
                      "Poincare.D12.TriangulationTopology.alexanderHomeo",
                      "Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere",
                      "Poincare.D12.TriangulationTopology.simplexHomeoDisk",
                      "Poincare.D12.TriangulationTopology.sphereOfTwoDisks"],
     "claimed_downstream": "sphericalSpaceFormRecognition; diskGlueQuotHomeoSphere_refl_apply; sphereOfTwoDisks_hemisphere_instance; MoiseBranch examples",
     "retained_users": {c: uses.get(c) for c in
                        ["Poincare.D12.TriangulationTopology.coveringOfSimplyConnectedIsHomeo",
                         "Poincare.D12.TriangulationTopology.antipodalQuotientCovering",
                         "Poincare.D12.TriangulationTopology.alexanderHomeo",
                         "Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere",
                         "Poincare.D12.TriangulationTopology.simplexHomeoDisk",
                         "Poincare.D12.TriangulationTopology.sphereOfTwoDisks"]},
     "verdict": "verified_with_caveat",
     "d13_assessment": ("Most constructors are retained and consumed (8/11/4/1 users). Two "
                        "(`antipodalQuotientCovering`, `simplexHomeoDisk`) had no retained consumer: "
                        "their uses are anonymous `example`s that Lean does not store in oleans. D13 "
                        "independently consumes both in `NonvacuityProbe.lean`.")},
    {"task": "D12-tensor-maximum-bochner",
     "claimed_blocker": "C1/C2/C3 partial closures (task blocked)",
     "constructors": ["Poincare.D12.TensorMaximumBochner.kernelTangent_of_feasibleDirection",
                      "Poincare.D12.TensorMaximumBochner.hamiltonField_kernelTangent",
                      "Poincare.D12.TensorMaximumBochner.adjugate_posSemidef"],
     "claimed_downstream": "C3 axiom-audit coverage",
     "retained_users": {c: uses.get(c) for c in
                        ["Poincare.D12.TensorMaximumBochner.kernelTangent_of_feasibleDirection",
                         "Poincare.D12.TensorMaximumBochner.hamiltonField_kernelTangent",
                         "Poincare.D12.TensorMaximumBochner.adjugate_posSemidef"]},
     "verdict": "partial_only",
     "d13_assessment": ("These are genuine finite-dimensional matrix theorems but the task's own "
                        "stated mathematical blocker B1 (PSD-cone invariance under the correct "
                        "tangent-cone condition) remains open. No D13 evidence closes B1.")},
]
for v in VERDICTS:
    v["pair_evidence"] = pair_evidence.get(v["task"], [])
(EVID / "blocker-verdicts.json").write_text(json.dumps(VERDICTS, indent=1, ensure_ascii=False) + "\n")
print("wrote expanded-hypotheses.json (%d) and blocker-verdicts.json (%d)" % (len(expanded), len(VERDICTS)))
