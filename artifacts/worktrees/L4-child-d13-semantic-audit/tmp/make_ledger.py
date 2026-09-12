#!/usr/bin/env python3
"""Build the L4 D13 semantic-audit ledger JSON (run from the worktree root).

Reads the compile log produced by the audit probe and writes
longrun/results/L4-child-d13-semantic-audit.json.
"""
import hashlib
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone

WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-child-d13-semantic-audit"
LEADER = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L4-geometric-critical-path"
LOG = os.path.join(WT, "release/audit_build/compile_final.log")
PROBE = os.path.join(WT, "release/audit_src/Poincare/L4/D13SemanticAudit.lean")

SRC = {
    "release/Poincare/D13/ManifoldIBP/POUConstruction.lean": 60,
    "release/Poincare/D13/ManifoldIBP/PartialChartModelPOU.lean": 192,
    "release/Poincare/D13/ManifoldIBP/SmoothAtlasModel.lean": 129,
    "release/Poincare/D13/ManifoldIBP/Transfer.lean": 131,
    "release/Poincare/D13/HeatKernelBridge.lean": 412,
    "release/Poincare/D13/ManifoldIBP/SmoothAtlas.lean": None,
    "release/Poincare/D13/ManifoldIBP/GlobalMeasure.lean": None,
    "release/Poincare/D13/ManifoldIBP/OverlapIBPData.lean": None,
    "release/Poincare/D13/ManifoldIBP/DisjointModel.lean": None,
    "release/Poincare/D13/ManifoldIBP/IntegrableTransfer.lean": None,
    "release/Poincare/D13/CertificateOn.lean": 137,
    "release/Poincare/D13/ManifoldIBP/Blocked.lean": 46,
    "release/Poincare/D13/ManifoldIBP/SmoothAtlasPartialAE.lean": 58,
    "release/Poincare/D13/ManifoldIBP/SmoothAtlasIBP.lean": 62,
    "release/Poincare/D12/VolumeIBP/Basic.lean": 63,
}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def read_log():
    with open(LOG, "r", errors="replace") as f:
        return f.read()


def axioms_from_log(log, name):
    m = re.search(re.escape("'" + name + "'") + r" depends on axioms: \[(.*?)\]", log, re.S)
    if not m:
        return None
    return [a.strip() for a in m.group(1).split(",") if a.strip()]


AX = ["propext", "Classical.choice", "Quot.sound"]

D = {}

# ---------------------------------------------------------------- declarations
D["declarations"] = [
    {
        "id": "H1",
        "name": "Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae",
        "file": "release/Poincare/D13/ManifoldIBP/POUConstruction.lean",
        "line": 60,
        "classification": "proved theorem (general; conditional on explicit atlas-structure and operator-identification hypotheses)",
        "statement": (
            "For A : SmoothOverlapAtlas M (n+1): given coherence htrans, base chart b, a finite type iota "
            "with chartOf : iota -> Nat, functions f u v Du Guv : M -> R, measurability of f, v, Du, Guv, "
            "support of v and Guv inside chart b image, C^2 chart expressions of f, u, v, compact support of "
            "v o chart b, tsupport (v o chart b) inside source b, a finite chart cover of chart b '' source b, "
            "the pointwise operator identifications hD (Du = Delta_F u in every chart) and hG "
            "(Guv = <grad u, grad v> in every chart), proper transitions and null source frontiers: "
            "integral Du*v d((globalMeasure volume).withDensity (weight f)) = - integral Guv d(same)."
        ),
        "hypotheses": [
            {"name": "htrans", "lean": "∀ i j y, A.chart j y ∈ A.chart i '' A.source i → A.transition i j y ∈ A.source i",
             "domain": "all i j : Nat, all y : Vec (n+1)", "note": "atlas coherence; REDUNDANT — KERNEL-CHECKED as derivable from SmoothOverlapAtlas.inj_chart + transition_chart_global (probe theorem Poincare.L4.D13Audit.htrans_derivable, axiom-clean)"},
            {"name": "b", "lean": "b : Nat", "domain": "base chart index", "note": "no constraint"},
            {"name": "iota / chartOf / hcover", "lean": "[Fintype ι], chartOf : ι → Nat, A.chart b '' A.source b ⊆ ⋃ j, A.chart (chartOf j) '' A.source (chartOf j)",
             "domain": "finite index type", "note": "finiteness of the cover is a genuine hypothesis; the ambient atlas is countably indexed"},
            {"name": "hf hv hDu hGuv", "lean": "Measurable f, v, Du, Guv", "domain": "global on M", "note": "used for the integrability transfer"},
            {"name": "hvsupp", "lean": "∀ m, v m ≠ 0 → m ∈ A.chart b '' A.source b", "domain": "all m : M", "note": "test function supported in the base chart image"},
            {"name": "hfc huc hvc", "lean": "∀ i, ContDiff R 2 (fun y => f/u/v (A.chart i y))", "domain": "ALL i : Nat (vacuous on empty sources)", "note": "only the charts in range chartOf and b are needed; harmless strengthening"},
            {"name": "hvcc", "lean": "HasCompactSupport (fun y => v (A.chart b y))", "domain": "coordinate space", "note": "compact support of the base-chart expression"},
            {"name": "htsupp_b", "lean": "tsupport (fun y => v (A.chart b y)) ⊆ A.source b", "domain": "topological support", "note": "strict support inside the open source; no boundary term"},
            {"name": "hD", "lean": "∀ i y, y ∈ A.source i → Du (A.chart i y) = (A.metric i).driftLaplacian (f ∘ chart i) (u ∘ chart i) y",
             "domain": "all i : Nat, y ∈ source i", "note": "integrand identification; NOT conclusion-equivalent"},
            {"name": "hG", "lean": "∀ i y, y ∈ A.source i → Guv (A.chart i y) = (A.metric i).gradInnerInverse (u ∘ chart i) (v ∘ chart i) y",
             "domain": "all i : Nat, y ∈ source i", "note": "integrand identification"},
            {"name": "hGuvsupp", "lean": "∀ m, Guv m ≠ 0 → m ∈ A.chart b '' A.source b", "domain": "all m : M", "note": "second integrand supported in the base chart image"},
            {"name": "hproper", "lean": "∀ i j K, IsCompact K → IsCompact (A.transition i j ⁻¹' K)", "domain": "all i j : Nat", "note": "needed for compact support of the transition pullbacks of the POU pieces"},
            {"name": "hbd", "lean": "∀ i, volume (frontier (A.source i)) = 0", "domain": "all i : Nat", "note": "null chart frontiers; replaces a boundary term"},
        ],
        "hidden_interface_fields": [
            "SmoothOverlapAtlas (extends OverlapAtlas): chart, source, isOpen_source, measurable_chart, injOn_chart, cover, measurableSet_image, metric, transition, transition_mem, transition_chart, transition_diff, metric_transform; plus isOpen_overlap, inj_chart, measurable_readback, contDiff_transition, transition_chart_global",
            "ChartMetric: g, smooth (ContDiff R top = analytic), posDef (positive definite Gram matrix)",
            "None of the structure fields encodes the IBP conclusion; the IBP is the D12 chart theorem ChartMetric.chart_weighted_ibp assembled through a constructed POU.",
        ],
        "conclusion_equivalent_hypothesis": "no — hD/hG identify the two integrands with the chart operators; the equality itself is derived from the proved chart-level IBP; the POU and both integrability statements are constructed in the proof (POUConstruction.lean:87-236)",
        "contradictory_or_vacuous": "no — probe h1_nonvacuous instantiates the theorem on the half-space atlas with a bump chi (chi 0 = 1) and chi as both test functions",
        "domain_checks": "support hypotheses are topological (insides of open sources), so no (0,T) vs (0,T] issue; the integral is over the global glued measure, not over a chart",
        "model_vs_manifold": "general theorem over an abstract measurable space with an atlas structure (not mathlib's IsManifold); honest, as the card's limitations section states",
        "non_vacuity_witness": "Poincare.L4.D13Audit.h1_nonvacuous / h1_cover_partial_ae_instantiated (half-space atlas hsAtlas G1, G1 = euclideanChartMetric 1, f = 0, u = v = bump, Du = laplacian, Guv = gradInnerInverse)",
        "axioms": AX,
        "defects": [],
    },
    {
        "id": "H2",
        "name": "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional",
        "file": "release/Poincare/D13/ManifoldIBP/PartialChartModelPOU.lean",
        "line": 192,
        "classification": "proved theorem (model: partial half-space atlas, unconditional relative to an arbitrary ChartMetric)",
        "statement": (
            "For G : ChartMetric (n+1), f u v : Vec (n+1) -> R with f, u, v C^2, v compactly supported and "
            "tsupport v ⊆ {y | y 0 < 1}: integral (G.driftLaplacian f u) * v d((hsAtlas G).globalMeasure volume "
            "with density (hsAtlas G).weight f) = - integral (G.gradInnerInverse u v) d(same)."
        ),
        "hypotheses": [
            {"name": "G", "lean": "G : ChartMetric (n+1)", "domain": "arbitrary chart metric; inhabited by euclideanChartMetric", "note": "the atlas is built from G (identity on {y0<1}, dilation by 2 on {0<y0})"},
            {"name": "hf hu hv", "lean": "ContDiff R 2 f, ContDiff R 2 u, ContDiff R 2 v", "domain": "global on Vec (n+1)", "note": "C^2 chart data"},
            {"name": "hvc", "lean": "HasCompactSupport v", "domain": "global", "note": "test function compactly supported"},
            {"name": "hvsupp", "lean": "tsupport v ⊆ {y | y 0 < 1}", "domain": "topological support inside base chart source", "note": "strict; excludes the boundary {y0=1}"},
        ],
        "hidden_interface_fields": [
            "ChartMetric (g, smooth, posDef) only; the atlas hsAtlas, its POU (hsPsi), the chart identifications (dilateMetric_driftLaplacian / _gradInnerInverse), the compact support of the pieces and the integrability are all constructed inside the proof",
        ],
        "conclusion_equivalent_hypothesis": "no",
        "contradictory_or_vacuous": "no — probe h2_nonvacuous (bump, chi 0 = 1); the conclusion is the genuine Dirichlet-type identity integral (Delta chi) chi = - integral |grad chi|^2",
        "domain_checks": "the support condition is on tsupport (strictly inside the open half-space); the C^2 requirement is on all of Vec (n+1); the measure is the glued global measure of the overlapping atlas (chart-independence proved in GlobalMeasure.lean:300-321)",
        "model_vs_manifold": "model atlas (two overlapping half-space charts), explicitly labelled model by the card; not a general manifold theorem",
        "non_vacuity_witness": "Poincare.L4.D13Audit.h2_nonvacuous / h2_weightedIBP_unconditional_instantiated; also h2_dirichlet_two_bumps with two distinct bumps",
        "axioms": AX,
        "defects": [],
    },
    {
        "id": "H3",
        "name": "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_greenIdentity",
        "file": "release/Poincare/D13/ManifoldIBP/PartialChartModelPOU.lean",
        "line": 484,
        "classification": "proved theorem (model; consumed consequence of H2 applied twice)",
        "statement": (
            "For G : ChartMetric (n+1), F U V C^2, U and V compactly supported with tsupport inside {y0<1}: "
            "integral (Delta_F U) * V dmu = integral U * (Delta_F V) dmu on the weighted global measure."
        ),
        "hypotheses": [
            {"name": "hF hU hV", "lean": "ContDiff R 2 F/U/V", "domain": "global", "note": "C^2"},
            {"name": "hUc hVc", "lean": "HasCompactSupport U, HasCompactSupport V", "domain": "global", "note": "both test functions"},
            {"name": "hUsupp hVsupp", "lean": "tsupport U ⊆ {y0<1}, tsupport V ⊆ {y0<1}", "domain": "topological support in base chart source", "note": "both"},
        ],
        "hidden_interface_fields": ["ChartMetric only"],
        "conclusion_equivalent_hypothesis": "no — derived by applying H2 to (F,U,V) and (F,V,U) and using ChartMetric.gradInnerInverse_comm",
        "contradictory_or_vacuous": "no — probe h3_nonvacuous uses two distinct bumps; the two sides are integrals of a non-zero product",
        "domain_checks": "same support discipline as H2; no boundary term",
        "model_vs_manifold": "model atlas; card labels it a consumed consequence of the model theorem",
        "non_vacuity_witness": "Poincare.L4.D13Audit.h3_nonvacuous / h3_greenIdentity_instantiated",
        "axioms": AX,
        "defects": [
            "Documentation only: the cited non-vacuity companion halfSpaceAtlas_integrable_dirichlet covers the Dirichlet case U = V, not the general U != V Green case. Integrability of the general Green integrands holds by the same transfer argument; the probe instantiates the identity for two distinct bumps but does not separately prove Integrable for both sides (no mathematical defect found)."
        ],
    },
    {
        "id": "H4",
        "name": "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_laplacianIntegralZero",
        "file": "release/Poincare/D13/ManifoldIBP/PartialChartModelPOU.lean",
        "line": 629,
        "classification": "proved theorem (model; divergence theorem on the partial atlas, unweighted measure)",
        "statement": (
            "For G : ChartMetric (n+1) and V C^2 compactly supported with tsupport V ⊆ {y0<1}: "
            "integral G.laplacian V d((hsAtlas G).globalMeasure volume) = 0."
        ),
        "hypotheses": [
            {"name": "hV", "lean": "ContDiff R 2 V", "domain": "global", "note": "C^2"},
            {"name": "hVc", "lean": "HasCompactSupport V", "domain": "global", "note": ""},
            {"name": "hVsupp", "lean": "tsupport V ⊆ {y0<1}", "domain": "topological support inside base chart source", "note": "keeps the boundary term zero"},
        ],
        "hidden_interface_fields": ["ChartMetric only"],
        "conclusion_equivalent_hypothesis": "no — proof transfers to chart 0 and applies the D12 chart identity laplacian_integral_eq_zero",
        "contradictory_or_vacuous": "no — probe h4_nonvacuous with a bump; the integrand is supported where V is and is non-zero on a set of positive measure (transfer argument closes it)",
        "domain_checks": "the atlas is genuinely partial (source 0 = {y0<1}); the strict tsupport condition is what removes the boundary term; no (0,T) issue",
        "model_vs_manifold": "model atlas; the card labels it the partial-atlas divergence theorem",
        "non_vacuity_witness": "Poincare.L4.D13Audit.h4_nonvacuous / h4_laplacianIntegralZero_instantiated",
        "axioms": AX,
        "defects": [],
    },
    {
        "id": "H5",
        "name": "Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_weightedIBP_via_pou",
        "file": "release/Poincare/D13/ManifoldIBP/SmoothAtlasModel.lean",
        "line": 129,
        "classification": "conditional interface (explicit POU data + explicit integrability of the lifted pieces) — NOT an unconditional theorem",
        "statement": (
            "For G : ChartMetric (n+1), F U V C^2 with V compactly supported, R : R and a two-chart family "
            "psi : Fin 2 -> Vec (n+1) -> R with each psi i smooth and tsupport (psi i) inside ball 0 (R+1), "
            "sum psi i = 1 on tsupport V, and integrability of the lifted pieces (hintL) and pairings (hintR) "
            "for the entropy-weighted global measure of the total dilation atlas: the weighted IBP identity holds."
        ),
        "hypotheses": [
            {"name": "hF hU hV", "lean": "ContDiff R 2 F/U/V", "domain": "global", "note": "C^2"},
            {"name": "hVc", "lean": "HasCompactSupport V", "domain": "global", "note": ""},
            {"name": "psi / hψ_sm", "lean": "psi : Fin 2 → Vec → R, ∀ i, ContDiff R ∞ (psi i)", "domain": "2 charts", "note": "supplied, not constructed"},
            {"name": "hψ_supp", "lean": "∀ i, tsupport (psi i) ⊆ ball 0 (R+1)", "domain": "each piece compactly supported in a ball", "note": "supplied"},
            {"name": "hψ_sum", "lean": "∀ x ∈ tsupport V, ∑ i, psi i x = 1", "domain": "only on tsupport V", "note": "supplied POU property"},
            {"name": "hintL", "lean": "∀ j, Integrable (fun m => Δ_F U m * pouPiece 0 V (psi j) m) (weighted global measure)", "domain": "each of the two pieces", "note": "integrability ASSUMED"},
            {"name": "hintR", "lean": "∀ j, Integrable (fun m => pouPairing 0 j U V (psi j) m) (weighted global measure)", "domain": "each of the two pieces", "note": "integrability ASSUMED"},
        ],
        "hidden_interface_fields": [
            "none beyond the hypotheses; the atlas dilationAtlasTwoSmooth is total with chart 0 = id and its measure is the honest chart measure",
        ],
        "conclusion_equivalent_hypothesis": "no — hintL/hintR are the integrability that makes the two sides meaningful, not the equality; the equality is assembled from the D12 chart IBP by globalWeightedIBP_of_pou",
        "contradictory_or_vacuous": "no — the probe constructs a genuine compactly supported POU (psi 0 = a bump equal to 1 on tsupport chi, psi 1 = 0) and discharges all four integrability obligations, instantiating the identity for a non-zero chi",
        "domain_checks": "POU sum required only on tsupport V; supports in a ball; no (0,T) issue",
        "model_vs_manifold": "total dilation-chart model, not a general manifold; conditional on the supplied POU and integrability",
        "non_vacuity_witness": "Poincare.L4.D13Audit.h5_nonvacuous / h5_dilationAtlasTwo_via_pou_instantiated",
        "axioms": AX,
        "defects": [
            "The card's expanded_hypotheses section has no explicit item for this declaration; the POU and integrability hypotheses are visible only through the pre-existing globalWeightedIBP_of_pou family entry. The card's semantic_class does classify that family as conditional interface, and the theorem docstring is honest, so this is a documentation omission rather than an overclaim."
        ],
    },
    {
        "id": "H6",
        "name": "Poincare.D13.ManifoldIBP.manifoldWeightedIBP_of_atlasData",
        "file": "release/Poincare/D13/ManifoldIBP/Transfer.lean",
        "line": 131,
        "classification": "conditional interface (transfer through the ManifoldAtlasData fields); the conclusion is a rewriting of ChartSumData.globalWeightedIBP",
        "statement": (
            "For A : ManifoldAtlasData M n iota and u v : M -> R: given C^2 chart drifts, chartwise C^2 u and v, "
            "chartwise compact support of v, and integrability of (driftLaplacianM u * v) and (gradInnerM u v) "
            "against A.mu: integral (driftLaplacianM u * v) dA.mu = - integral (gradInnerM u v) dA.mu."
        ),
        "hypotheses": [
            {"name": "hd", "lean": "∀ i, ContDiff R 2 (A.drift i)", "domain": "all charts", "note": "chart drift regularity"},
            {"name": "hu hv", "lean": "∀ i, ContDiff R 2 (u ∘ A.chart i), ∀ i, ContDiff R 2 (v ∘ A.chart i)", "domain": "all charts", "note": "chartwise C^2; a manifold-level function must be C^2 in every chart"},
            {"name": "hvc", "lean": "∀ i, HasCompactSupport (v ∘ A.chart i)", "domain": "all charts", "note": "STRONGER than compact support of v on M for an overlapping atlas"},
            {"name": "hg", "lean": "Integrable (fun m => A.driftLaplacianM u m * v m) A.mu", "domain": "manifold", "note": "integrability ASSUMED; needed to apply integral_decomp"},
            {"name": "hg'", "lean": "Integrable (fun m => A.gradInnerM u v m) A.mu", "domain": "manifold", "note": "integrability ASSUMED"},
        ],
        "hidden_interface_fields": [
            "ManifoldAtlasData.mu : Measure M (the measure itself is a field)",
            "ManifoldAtlasData.chart : Fin iota -> Vec (n+1) -> M",
            "ManifoldAtlasData.metric : Fin iota -> ChartMetric (n+1)",
            "ManifoldAtlasData.drift : Fin iota -> Vec (n+1) -> R",
            "ManifoldAtlasData.integral_decomp (B-D13-MANIFOLD-GLUING): ∀ g, Integrable g mu -> ∫ g dmu = Σ_i ∫ g(chart i x) e^{-drift i x} ρ_i(x) dx — assumed",
            "ManifoldAtlasData.driftLaplacianM and gradInnerM: the manifold operators are fields, not constructed",
            "ManifoldAtlasData.weighted_laplacian_compat (B-D13-OPERATOR-COMPAT): Δ^M u (chart i x) = chart driftLaplacian (u ∘ chart i) x — assumed",
            "ManifoldAtlasData.grad_inner_compat (B-D13-OPERATOR-COMPAT): gradInnerM u v (chart i x) = chart gradInnerInverse (u∘chart i) (v∘chart i) x — assumed",
        ],
        "conclusion_equivalent_hypothesis": "no in the strict sense (the fields are structural and quantified over all integrable g / all u v i x), but the theorem is a rewriting: after the interface fields the goal is exactly the proved chartwise ChartSumData.globalWeightedIBP. The mathematical content therefore lies in the interface, which is honestly labelled conditional by the card and by Blocked.lean.",
        "contradictory_or_vacuous": "no — ManifoldAtlasData is inhabited: dilationAtlasTwoData (OverlapIBPData.lean:79) and disjointAtlasData (DisjointModel.lean:105); the probe instantiates the disjoint model with a non-zero bump through disjointAtlas_weightedIBP, which discharges hg/hg'",
        "domain_checks": "no time-domain issue; the integral is over the abstract measure A.mu, whose gluing is an assumed field",
        "model_vs_manifold": "the abstract interface can be instantiated for the single-chart dilation model and the disjoint model; no instantiation from mathlib's manifold API is built (card's remaining blocker B-D13-RIEMANNIAN-METRIC-BRIDGE-PACKAGING)",
        "non_vacuity_witness": "Poincare.L4.D13Audit.h6_nonvacuous / h6_atlasData_instantiated via Poincare.D13.ManifoldIBP.disjointAtlas_weightedIBP",
        "axioms": AX,
        "defects": [],
    },
    {
        "id": "H7",
        "name": "Poincare.D13.HeatKernelBridge.finiteLifetimeEntropyBridge_gaussian",
        "file": "release/Poincare/D13/HeatKernelBridge.lean",
        "line": 412,
        "classification": "proved theorem (model: explicit backward Gaussian on the Euclidean chart Vec 2, clamped lifetime)",
        "statement": (
            "For all tau0 t1 : R with t1 < tau0: FiniteLifetimeEntropyBridge (gaussCalculus tau0 t1 ht1) "
            "(gaussEntropyData tau0 t1 ht1) 0 t1 — the six bridge fields (f_derivative, weighted_ibp, "
            "weighted_laplacian_compatibility, bochner, conjugate_measure_evolution, regularity)."
        ),
        "hypotheses": [
            {"name": "tau0 t1", "lean": "tau0 t1 : R", "domain": "reals", "note": "no positivity is assumed; the substantive case is 0 < t1 < tau0, where the interior (0,t1) is non-empty"},
            {"name": "ht1", "lean": "t1 < tau0", "domain": "real inequality", "note": "keeps tau(t) = tau0 - t > 0 on the lifetime"},
        ],
        "hidden_interface_fields": [
            "FiniteLifetimeEntropyBridge (CertificateOn.lean:137): a Prop structure whose six fields are all proved here; it is NOT an axiom and the module does not inhabit it otherwise",
            "EntropyData (Longrun/Entropy/Functional.lean:41): R, gradSq, f, rho, tau, tau_pos, n, riccHess, rho_nonneg, integrable_F, integrable_W — all instantiated explicitly for the Gaussian",
            "WeightedCalculus (gaussCalculus = euclideanChartCalculus 1 (gaussPotential ...))",
        ],
        "conclusion_equivalent_hypothesis": "no — every field is proved from explicit lemmas: F(t) = 1/(tau0-t), FDissipation = 1/(tau0-t)^2, restricted IBP (D12), Euclidean Laplacian compatibility, flat Bochner identity, gaussian_conjugate_heat, C^1 regularity",
        "contradictory_or_vacuous": "no — probe h7_bridge_instantiated at tau0 = 1, t1 = 1/2 computes F(1/4) = 4/3; h7_fderivative_at_interior instantiates the interior derivative field at t = 1/4",
        "domain_checks": "derivative-type fields are required on Ioo 0 t1 (open interior), regularity on Icc 0 t1 (closed interval) — the correct combination for monotoneOn_of_deriv_nonneg; the clamped tau keeps tau > 0 for all real t while the fields on the lifetime see the true backward time tau0 - t",
        "model_vs_manifold": "explicit Euclidean chart Vec 2 model; the card lists the Gaussian family under model and records the absence of a manifold WeightedCalculus instance as a remaining blocker",
        "non_vacuity_witness": "Poincare.L4.D13Audit.h7_bridge_instantiated, h7_fderivative_at_interior",
        "axioms": AX,
        "defects": [],
    },
    {
        "id": "H8",
        "name": "Poincare.D13.HeatKernelBridge.monotoneOn_F_gaussian",
        "file": "release/Poincare/D13/HeatKernelBridge.lean",
        "line": 465,
        "classification": "proved theorem (model; D4 certificate consumption)",
        "statement": (
            "For all tau0 t1 : R with t1 < tau0: MonotoneOn (fun s => (gaussEntropyData tau0 t1 ht1 s).F) (Icc 0 t1)."
        ),
        "hypotheses": [
            {"name": "tau0 t1", "lean": "tau0 t1 : R", "domain": "reals", "note": ""},
            {"name": "ht1", "lean": "t1 < tau0", "domain": "real", "note": "same lifetime condition as H7"},
        ],
        "hidden_interface_fields": [
            "consumes FiniteLifetimeEntropyBridge through Poincare.D13.CertificateOn.monotoneOn_of_bridge; the additional upper-bound hypothesis hbound of that reduction is DISCHARGED (1/(tau0-t) <= 1/(tau0-t1)), not assumed",
        ],
        "conclusion_equivalent_hypothesis": "no — the monotonicity follows from the bridge plus the explicit F(s) = 1/(tau0-s) computation; FDissipation_nonneg is a proved algebraic lemma",
        "contradictory_or_vacuous": "no — probe h8_monotoneOn_instantiated at tau0 = 1, t1 = 1/2 gives F(0) = 1 and F(1/2) = 2, a genuine ordering of distinct values",
        "domain_checks": "MonotoneOn on the closed interval Icc 0 t1; the derivative is supplied on the open interior by the bridge. If t1 <= 0 the interval is empty/trivial; the substantive case 0 < t1 < tau0 is non-vacuous",
        "model_vs_manifold": "Euclidean Vec 2 model functional computed from an explicit Gaussian; no Perelman monotonicity or manifold claim (card explicitly not-claimed)",
        "non_vacuity_witness": "Poincare.L4.D13Audit.h8_monotoneOn_instantiated",
        "axioms": AX,
        "defects": [],
    },
]

# ------------------------------------------------------------------ card audit
D["card_claim_audit"] = {
    "card": "worktrees/D13-manifold-ibp-volume-form/longrun/results/D13-manifold-ibp-volume-form.{md,json}",
    "expanded_hypotheses": [
        {"claim": "H1 assumes htrans, hproper, hbd, hcover, C^2 chart expressions, compact support, tsupport in source b, v supported in chart b image, hD/hG, measurability; NO POU and NO integrability hypotheses",
         "verdict": "SUPPORTED (kernel-checked statements; integrability and POU constructed at POUConstruction.lean:87-236); htrans is in fact derivable from the atlas structure and hence redundant (kernel-checked: Poincare.L4.D13Audit.htrans_derivable)"},
        {"claim": "H2 assumes only C^2 f,u,v and compact support with tsupport v inside {y0<1}",
         "verdict": "SUPPORTED"},
        {"claim": "halfSpaceAtlas_weightedIBP_of_cover / _chartOne: same data with base chart 0 / 1",
         "verdict": "SUPPORTED (existence of both declarations and their headline-consuming proofs verified)"},
        {"claim": "greenIdentity / dirichletEnergy: two C^2 compactly supported functions with topological support in the base chart source",
         "verdict": "SUPPORTED for greenIdentity (U,V) and dirichletEnergy (single V used twice); minor gap: the cited integrability companion covers only U = V"},
        {"claim": "integrable_globalMeasure_withDensity_of_supported assumes measurability of f and g, support of g in one chart image, integrability of the weighted chart expression",
         "verdict": "SUPPORTED (IntegrableTransfer.lean:99-104)"},
        {"claim": "pre-existing interfaces unchanged: globalWeightedIBP_of_pou_partial_ae takes explicit POU data; ManifoldAtlasData takes integral_decomp + operator compatibility (inhabited with proofs for the models); ChartMetric.smooth asks ContDiff R top (= analytic) with SmoothChartMetric the C^inf variant",
         "verdict": "SUPPORTED — ManifoldAtlasData fields confirmed; inhabited by dilationAtlasTwoData and disjointAtlasData; ContDiff R top = omega verified (probe top_eq_omega); SmoothChartMetric uses ContDiff R infinity (ChartMetricBridge.lean:134)"},
        {"claim": "No hypothesis is equivalent to a conclusion",
         "verdict": "SUPPORTED for all eight headlines: the operator identifications/nterface fields are structural, and every conclusion is derived from proved chart-level theorems; H6 is the weakest case and is honestly classified conditional"},
        {"claim": "The dilation-atlas IBP via POU is covered by the expanded-hypotheses section",
         "verdict": "NOT SUPPORTED AS WRITTEN (documentation omission): dilationAtlasTwo_weightedIBP_via_pou keeps explicit POU and integrability hypotheses and has no dedicated entry. It is nevertheless classified as a conditional interface by the card's semantic_class and by its own docstring, so no mathematical overclaim results"},
        {"claim": "ChartMetric.smooth asking for analytic coefficients is a defect",
         "verdict": "SUPPORTED (ContDiff R top = omega is analytic at this pin; D12 only uses C^2, so it is a regularity over-requirement of the interface, not of the theorems)"},
    ],
    "exact_blockers_closed": [
        {"claim": "U7-GLOBAL-INTEGRABILITY closed by integrable_chartMeasure_iff, integrable_globalMeasure_iff, integrable_globalMeasure_withDensity_of_supported",
         "verdict": "SUPPORTED as proved transfer lemmas; the wording 'consumed by hintL/hintR of halfSpaceAtlas_weightedIBP_unconditional and of globalWeightedIBP_of_cover_partial_ae' is loose: those theorems have no hintL/hintR hypotheses, the integrability is constructed internally (local hintL/hintR in the proofs)"},
        {"claim": "U7-GLOBAL-POU closed by exists_smooth_partitionOfUnity_subordinate applied inside globalWeightedIBP_of_cover_partial_ae",
         "verdict": "SUPPORTED (POUConstruction.lean:89-101; the POU existence theorem takes a finite open cover of a compact set, exactly the hypotheses available)"},
        {"claim": "U7-GLOBAL-BOUNDARY closed by hsStep/hsPsi/hsPsi_sum/hasCompactSupport_hsPsi/halfSpaceAtlas_weightedIBP_unconditional",
         "verdict": "SUPPORTED for the model atlas; the general fat-boundary case remains a named remaining blocker"},
        {"claim": "U7-DIVERGENCE closed by support_laplacian_subset + halfSpaceAtlas_laplacianIntegralZero",
         "verdict": "SUPPORTED (H4 probe)"},
        {"claim": "U7-GLOBAL-LIFT closed by globalWeightedIBP_of_pou_partial(_ae) and the two new theorems apply it with all hypotheses discharged",
         "verdict": "SUPPORTED (H1 proof term applies globalWeightedIBP_of_cover_partial_ae; H2 applies the partial-AE route)"},
        {"claim": "U7-GLOBAL-POU (invocation 6): dilationAtlasTwo_weightedIBP_via_pou consumes globalWeightedIBP_of_pou",
         "verdict": "SUPPORTED (SmoothAtlasModel.lean:170 applies it)"},
        {"claim": "U7-GLOBAL-MEASURE / VOLUME-FORM closed: globalMeasure, chartMeasure_apply_eq, globalMeasure_apply_chart, globalMeasure_restrict_eq_chartMeasure, globalMeasure_apply_chart_volumeForm, dilationAtlasTwoData; consumed by dilationAtlasTwoData_weightedIBP through manifoldWeightedIBP_of_atlasData",
         "verdict": "SUPPORTED for the OverlapAtlas.globalMeasure construction and its chart-independence; note that the *abstract* ManifoldAtlasData.integral_decomp remains an interface field (B-D13-MANIFOLD-GLUING in Blocked.lean), which the card discloses under semantic_class but does not list in remaining_blockers"},
        {"claim": "U7 chart-level (D12/D13) closed",
         "verdict": "SUPPORTED (chart_weighted_ibp, laplacian_integral_eq_zero, BochnerFlat.bochnerIdentityOn_euclidean all exist and are used)"},
        {"claim": "I4 (all five components) closed for the Gaussian family, consumed by monotoneOn_F_gaussian etc.",
         "verdict": "SUPPORTED (H7/H8 probes; numeric values 1, 4/3, 2); scoped to the explicit Gaussian model, as the card states"},
        {"claim": "I4-residual defects proved: unrestricted WeightedIBPStatement false; forall-t>0 forms unsatisfiable",
         "verdict": "SUPPORTED as declarations (Bridge.lean:274 unrestrictedWeightedIBPStatement_false exists); not independently re-proved in this audit"},
    ],
    "overall": "The card's expanded-hypotheses and blockers-closed claims are substantially supported by the kernel: every cited declaration exists and every headline has a kernel-checked model instantiation. Three documentation-level findings: (1) htrans is redundant (derivable from the structure); (2) H5 has no dedicated expanded-hypotheses entry though it is conditional; (3) the U7-GLOBAL-INTEGRABILITY row's 'hintL/hintR of H1/H2' wording is imprecise. No conclusion-equivalent hypothesis, contradictory hypothesis, vacuous hypothesis or model-vs-manifold overclaim was found in the eight headlines.",
}

# ---------------------------------------------------------------- environment
D["environment"] = {
    "worktree": WT,
    "toolchain": "leanprover/lean4:v4.34.0-rc2",
    "mathlib_rev": "7974e751bece493b6ff508039423ca9fa2452fa8",
    "audited_tree": "worktrees/leaders/L4-geometric-critical-path/release/Poincare/D13 (byte-identical to worktrees/D13-manifold-ibp-volume-form/release/Poincare/D13 except CriticalPathReview/)",
    "build_note": "audit probes compiled from release/audit_src with LEAN_PATH prepended by the leader worktree's compiled oleans; all writes go to worktree-local release/audit_build",
    "forbidden_token_scan": "grep -rn 'sorry|admit|^axiom|unsafe|native_decide|proof_wanted' over Poincare/D13 returns only docstring occurrences",
}

D["source_hashes"] = {}
for rel in SRC:
    p = os.path.join(LEADER, rel)
    D["source_hashes"][rel] = {"sha256": sha256(p)}

D["audit_probe"] = {
    "file": "release/audit_src/Poincare/L4/D13SemanticAudit.lean",
    "sha256": sha256(PROBE),
    "module": "Poincare.L4.D13SemanticAudit",
    "compile_command": "cd release && LEAN_PATH=<leader .lake/build/lib/lean> lake env lean -R audit_src -o audit_build/lib/lean/Poincare/L4/D13SemanticAudit.olean audit_src/Poincare/L4/D13SemanticAudit.lean",
    "cwd": "release/",
    "exit": 0,
    "oleans_written": "release/audit_build/lib/lean/Poincare/L4/D13SemanticAudit.olean",
    "forbidden_tokens": "none (no sorry/axiom/admit/unsafe/native_decide/proof_wanted in the probe)",
}

D["axiom_evidence"] = {
    "method": "#print axioms on the eight headlines plus the probe's non-vacuity theorems, fresh elaboration from source",
    "headline_cones": {("H" + str(i + 1)): axioms_from_log(read_log(), n) for i, n in enumerate([
        "Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae",
        "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional",
        "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_greenIdentity",
        "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_laplacianIntegralZero",
        "Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_weightedIBP_via_pou",
        "Poincare.D13.ManifoldIBP.manifoldWeightedIBP_of_atlasData",
        "Poincare.D13.HeatKernelBridge.finiteLifetimeEntropyBridge_gaussian",
        "Poincare.D13.HeatKernelBridge.monotoneOn_F_gaussian",
    ])},
    "expected": AX,
    "sorryAx": False,
}

D["classification_summary"] = {
    "proved_general_conditional": ["H1 (constructed POU + constructed integrability, conditional on atlas structure and operator identifications)"],
    "proved_model_unconditional": ["H2", "H3", "H4", "H7", "H8"],
    "conditional_interface": ["H5 (supplied POU + supplied integrability)", "H6 (ManifoldAtlasData interface fields)"],
    "statement_only": [],
    "upstream_source_claim": ["Frenzymath snapshot bb91a091 (not built here)"],
}

D["audit_probe"]["probe_axiom_cones"] = {
    name: axioms_from_log(read_log(), "Poincare.L4.D13Audit." + name) for name in [
        "top_eq_omega", "smooth_lt_analytic", "exists_bump_in_halfSpace", "exists_bump_zero",
        "htrans_derivable", "h1_nonvacuous", "h2_nonvacuous", "h3_nonvacuous", "h4_nonvacuous",
        "h5_nonvacuous", "h6_nonvacuous", "h7_bridge_instantiated", "h7_fderivative_at_interior",
        "h8_monotoneOn_instantiated"]}
D["audit_probe"]["compile_exit"] = 0
D["audit_probe"]["error_count"] = 0
D["audit_probe"]["evidence_files"] = {
    "statements": "release/audit_build/evidence/statements.txt (first 140 lines of the final log: the eight #check outputs and the interface #print outputs)",
    "axioms": "release/audit_build/evidence/axioms_summary.txt (all 21 axiom cones printed by the probe)"}
D["defects_found"] = [
    {"id": "F1", "severity": "informational-positive", "declaration": "H1",
     "finding": "htrans is a redundant hypothesis: derivable from the SmoothOverlapAtlas fields inj_chart and transition_chart_global. Kernel-checked in the probe (htrans_derivable). The theorem is therefore slightly stronger than its hypothesis list suggests; no unsoundness.",
     "evidence": "release/audit_src/Poincare/L4/D13SemanticAudit.lean, theorem htrans_derivable"},
    {"id": "F2", "severity": "documentation", "declaration": "H5 (card claim)",
     "finding": "The card's expanded_hypotheses section has no dedicated entry for dilationAtlasTwo_weightedIBP_via_pou, which is a conditional interface with supplied POU and supplied integrability. The card's semantic_class and the theorem docstring do say so, so no mathematical overclaim results.",
     "evidence": "D13-manifold-ibp-volume-form.json expanded_hypotheses; SmoothAtlasModel.lean:129-148"},
    {"id": "F3", "severity": "documentation", "declaration": "card row U7-GLOBAL-INTEGRABILITY",
     "finding": "The row says the integrability transfer is 'consumed by hintL/hintR of halfSpaceAtlas_weightedIBP_unconditional and of globalWeightedIBP_of_cover_partial_ae'. Those theorems have no hintL/hintR hypotheses: the integrability is constructed internally (local hintL/hintR in the proofs). Loose wording, not a false mathematical claim.",
     "evidence": "POUConstruction.lean:115-236; PartialChartModelPOU.lean proof of halfSpaceAtlas_weightedIBP_unconditional"},
    {"id": "F4", "severity": "documentation", "declaration": "H3",
     "finding": "The non-vacuity companion cited for the Green identity, halfSpaceAtlas_integrable_dirichlet, is stated for U = V (Dirichlet case) only. Integrability of the general Green integrands holds by the same transfer argument; the probe instantiates the identity with two distinct bumps but does not separately kernel-check both integrability statements.",
     "evidence": "PartialChartModelPOU.lean:511-577; probe h3_nonvacuous"},
    {"id": "F5", "severity": "documentation", "declaration": "card remaining_blockers",
     "finding": "B-D13-MANIFOLD-GLUING (the abstract ManifoldAtlasData.integral_decomp field) is named in Blocked.lean but does not appear in the card's remaining_blockers list; it is disclosed indirectly under semantic_class (ManifoldAtlasData under conditional_interface).",
     "evidence": "Blocked.lean:11-14,40-48; card semantic_class.conditional_interface"},
]
D["no_defect_found"] = [
    "No conclusion-equivalent hypothesis in any of the eight headlines.",
    "No contradictory hypothesis bundle: every headline has a kernel-checked model instantiation (probe h1..h8_nonvacuous, all axiom-clean).",
    "No vacuous headline: each instantiation uses a non-zero C^2 bump or the explicit Gaussian with concrete values F(0)=1, F(1/4)=4/3, F(1/2)=2.",
    "No wrong-domain defect: (0,T) vs (0,T] usage is correct (bridge derivative fields on Ioo 0 t1, regularity/monotonicity on Icc 0 t1), and the atlas support hypotheses are strict topological supports inside open sources.",
    "No model-vs-manifold overclaim in the eight statements: the model statements (H2-H5, H7, H8) are labelled model; H1 is general but conditional on an abstract atlas structure; H6 is a conditional interface.",
]
D["generated_utc"] = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")

os.makedirs(os.path.join(WT, "longrun/results"), exist_ok=True)
with open(os.path.join(WT, "longrun/results/L4-child-d13-semantic-audit.json"), "w") as f:
    json.dump(D, f, indent=2)
print("wrote ledger; declarations:", len(D["declarations"]))
print("probe axioms:", D["axiom_evidence"]["headline_cones"])
