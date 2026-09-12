#!/usr/bin/env python3
"""Build the semantic classification of the imported upstream claims.

Vocabulary (per the M2 acceptance):
  proved          - compiled; axiom cone within {propext, Classical.choice, Quot.sound};
                    hypotheses are genuine mathematical data, not an unproved interface
  conditional     - compiled implication whose antecedent is an unproved interface
                    (e.g. `IsRicciFlowOn`, `SmoothCompleteRicciFlowOn`)
  model           - proved but only for a toy/finite/Euclidean model of the intended geometry
  statement-only  - declaration whose proof is admitted (`sorry`), so no claim may rest on it
  upstream source claim - asserted in the upstream blueprint/prose but not a kernel-checked
                    theorem of the snapshot
  definition      - a definition/predicate/structure: not itself a claim

The curated table below names one entry per declaration used in the compile-time
probes; file/line are filled in from `evidence/upstream-qualified-names.json`.

Usage: classify-claims.py <worktree-root>
"""
import json
import re
import sys
from pathlib import Path

ROOT = Path(sys.argv[1]).resolve()

# (fully qualified name, class, note)
TABLE = [
    # ---- U1 curvature tensor ----
    ("Riemannian.AffineConnection.curvature_zero_left", "proved", "curvature operator vanishes on a zero slot"),
    ("Riemannian.AffineConnection.curvature_zero_right", "proved", "curvature operator vanishes on a zero slot"),
    ("Riemannian.AffineConnection.curvature_apply_congr", "proved", "congruence for curvature application"),
    ("Riemannian.AffineConnection.curvatureOperatorAt_add_left", "proved", "additivity of curvature operator"),
    ("Riemannian.AffineConnection.curvatureOperatorAt_smul_left", "proved", "homogeneity of curvature operator"),
    ("Riemannian.leviCivita_curvature_frame_expansion", "proved", "curvature in a moving frame"),
    ("Riemannian.leviCivita_curvature_chartFrame_expansion", "proved", "curvature in a chart frame"),
    ("PetersenLib.curvatureTensorTypes", "definition", "(0,4)-curvature tensor type alias"),
    ("PetersenLib.curvatureTensor_coordinates", "proved", "coordinate formula for the curvature tensor"),
    ("PetersenLib.curvatureTensor_indexLowering", "proved", "index lowering with the metric"),
    ("PetersenLib.contMDiff_curvatureTensorFour", "proved", "smoothness of the curvature tensor"),
    ("PetersenLib.curvatureTensor_zero_first", "proved", "curvature vanishes on a zero slot"),
    ("MorganTianLib.curvatureFormAt_antisymm_left", "proved", "pointwise (0,4) curvature is antisymmetric in its first pair (adapter-aliased: UpstreamAdapters.Adapters.MorganTian.curvatureFormAt_antisymm_left)"),
    ("MorganTianLib.curvatureFormAt_antisymm_right", "proved", "pointwise (0,4) curvature is antisymmetric in its last pair for a metric-compatible connection (adapter-aliased)"),
    ("MorganTianLib.curvatureFormAt_bianchi", "proved", "pointwise first Bianchi identity for a symmetric connection (adapter-aliased)"),
    ("MorganTianLib.isAlgCurvatureForm_curvatureFormAt", "proved", "pointwise (0,4) form of a Levi-Civita connection is an algebraic curvature form (adapter-aliased)"),

    # ---- U2 Ricci / scalar curvature ----
    ("Riemannian.sectionalCurvature", "definition", "sectional curvature"),
    ("Riemannian.sectionalCurvature_eq_of_orthonormal", "proved", "orthonormal-frame formula"),
    ("Riemannian.ricciForm_self_eq_sum_sectionalCurvature", "proved", "Ricci as a sum of sectional curvatures"),
    ("Riemannian.ricciForm_self_ge_of_sectionalCurvature_ge", "proved", "Ricci lower bound from sectional bound"),
    ("Riemannian.Variation.hasRicciLowerBound_of_sectionalCurvatureLowerBound", "proved", "variational Ricci bound"),
    ("Riemannian.sphere_sectionalCurvature_one", "model", "round sphere model has sectional curvature 1"),
    ("Riemannian.Hyperbolic.hyperbolicMetric_sectionalCurvature_eq_neg_one", "model", "hyperbolic model has sectional curvature -1"),
    ("MorganTianLib.ricciAt", "definition", "pointwise Ricci tensor"),
    ("MorganTianLib.scalarCurvatureAt", "definition", "pointwise scalar curvature"),
    ("MorganTianLib.sum_metricInner_riemannCurvature_frame_eq_ricciAt", "proved", "Ricci as a frame trace of curvature"),
    ("MorganTianLib.trace_frameCurvOp_eq_ricciAt", "proved", "Ricci as a trace of the curvature operator"),
    ("MorganTianLib.ricci_curvature_comparison", "proved", "Ricci comparison with explicit curvature-bound hypotheses"),

    # ---- U3 geodesics / exponential / parallel transport ----
    ("Riemannian.Geodesic.hasGeodesicEquationAt_iff_covDerivAlong_velocity_eq_zero", "proved", "geodesic equation iff covariant derivative of velocity vanishes"),
    ("Riemannian.Geodesic.isGeodesic_iff_covDerivAlong_velocity_eq_zero", "proved", "geodesic characterization"),
    ("Riemannian.Geodesic.continuous_and_isGeodesic_iff_leviCivita_covDerivAlong_velocity_eq_zero", "proved", "Levi-Civita geodesic characterization"),
    ("Riemannian.parallelTransportTangentEquiv", "definition", "parallel transport as a linear equivalence"),
    ("Riemannian.metricInner_parallelTransportTangentEquiv", "proved", "parallel transport preserves the metric"),
    ("PetersenLib.expMap", "definition", "exponential map"),
    ("PetersenLib.expMap_zero", "proved", "exp(0) = identity point"),
    ("PetersenLib.expMap_smul", "proved", "homogeneity of the exponential map"),
    ("PetersenLib.expMap_localDiffeomorphism", "proved", "exp is a local diffeomorphism"),
    ("PetersenLib.isGeodesicOn_of_isChartGeodesicOn", "proved", "chart geodesics are geodesics"),
    ("PetersenLib.segment_isGeodesic", "proved", "minimizing segments are geodesics"),
    ("PetersenLib.energyLocalMinimum_isGeodesic", "proved", "energy minimizers are geodesics"),

    # ---- U4 Levi-Civita connection ----
    ("Riemannian.RiemannianMetric.leviCivita_chartContraction_eq", "proved", "chart formula for Levi-Civita"),
    ("Riemannian.RiemannianMetric.leviCivita_covDerivAlong_eq", "proved", "covariant derivative along a curve"),
    ("Riemannian.AffineConnection.preservesMetricUnderParallelTransport_iff_isMetricCompatible", "proved", "metric compatibility iff parallel transport is an isometry"),
    ("Riemannian.AffineConnection.PreservesMetricUnderParallelTransport", "definition", "metric-compatibility predicate"),

    # ---- U6 parabolic / maximum principle ----
    ("MorganTianLib.hamilton_tensor_maximum_principle_compact", "proved", "Hamilton tensor maximum principle, compact carrier, explicit PDE hypotheses"),
    ("MorganTianLib.hamilton_tensor_maximum_principle_bounded", "proved", "bounded-carrier variant"),
    ("Topping.weak_maximum_principle", "proved", "weak parabolic maximum principle"),
    ("Topping.weak_maximum_principle_of_pos", "proved", "positivity form of the weak maximum principle"),

    # ---- U7 / U10 divergence, Laplacian, Bochner ----
    ("MorganTianLib.laplacianAt_eq_chart_divergence", "proved", "Laplacian equals chart divergence"),
    ("MorganTianLib.chartVolumeDensity_mul_laplacianAt_eq_divergence", "proved", "weighted divergence identity"),
    ("MorganTianLib.function_bochner_formula", "proved", "Bochner formula for functions on a Riemannian manifold"),
    ("Topping.divergence_ricciTensorField", "proved", "divergence of the Ricci tensor (contracted Bianchi)"),
    ("Topping.ParabolicPDE.metricLaplacianAt_eq_laplaceBeltramiChart_divergence", "proved", "metric Laplacian as Beltrami divergence"),

    # ---- U8 Ricci flow ----
    ("MorganTianLib.IsRicciFlowEquationOn", "definition", "pointwise Ricci-flow equation predicate"),
    ("MorganTianLib.IsRicciFlowOn", "conditional", "structure packaging a solution of the Ricci-flow equation on an interval; consumers must supply it, existence is not proved here"),
    ("MorganTianLib.IsRicciFlowOn.metricInner_hasDerivAt", "conditional", "derivative of the metric under the flow hypothesis"),
    ("MorganTianLib.IsRicciFlowOn.inner_hasDerivWithinAt", "conditional", "one-sided derivative under the flow hypothesis"),
    ("MorganTianLib.ricciFlowRiemannVariationIntrinsic_eq_curvature_evolution_explicit", "conditional", "curvature evolution under the flow hypothesis"),
    ("MorganTianLib.hasDerivAt_chartRiemannEnergyOnE_of_isRicciFlowOn", "conditional", "energy derivative under the flow hypothesis"),
    ("Topping.hasVolumeDerivativeOn_riemannianMeasure_of_isRicciFlowOn", "conditional", "volume derivative under the flow hypothesis"),
    ("Topping.riemannianVolume_antitoneOn_of_isRicciFlowOn", "conditional", "volume monotonicity under the flow hypothesis (nonnegative Ricci)"),

    # ---- U9 Perelman machinery ----
    ("KleinerLott.IsKappaNoncollapsedOnScale", "definition", "kappa-noncollapsing predicate"),
    ("KleinerLott.SmoothCompleteRicciFlowOn", "conditional", "structure packaging a smooth complete Ricci flow; existence is not proved here"),
    ("KleinerLott.RiemannCurvatureFamily.ricciAt", "definition", "Ricci curvature of a curvature family"),
    ("KleinerLott.IsHamiltonIveyPinched", "definition", "Hamilton-Ivey pinching predicate"),
    ("KleinerLott.exists_point_selection_of_bounded_moving_curvature", "proved", "point selection from bounded moving curvature (explicit hypotheses)"),

    # ---- M4 topology ----
    ("HatcherLib.simplyConnected_iff_unique_path_class", "proved", "simple connectivity via unique path classes"),
    ("HatcherLib.IsUniversalCoveringMap.simplyConnectedSpace", "proved", "universal cover is simply connected"),
    ("HatcherLib.UniversalCoverConstruction.universalCover_simplyConnectedSpace", "proved", "construction of the universal cover"),
    ("HatcherLib.attachingSpace_homotopyEquiv", "proved", "homotopy equivalence for attaching spaces"),
    ("HatcherLib.homotopyEquivPiOneMulEquiv", "proved", "pi_1 is invariant under homotopy equivalence"),
    ("HatcherLib.collapseMk_homotopyEquiv", "proved", "collapse map is a homotopy equivalence"),
    ("HatcherLib.simplyConnectedSpace_of_pathConnectedOpenCover", "proved", "simple connectivity from an open cover (van Kampen form)"),
]

# Adapter-authored constructed-input consumers (this task's own theorems; not
# upstream declarations).  File/line are resolved from the authored sources at
# run time, so the table cannot silently point at stale locations.
# (fully qualified name, class, note)
ADAPTER_CONSUMERS = [
    ("UpstreamAdapters.DownstreamGeometry.euclidean_curvatureOperatorAt_eq_zero", "model",
     "U1 consumer: pointwise curvature operator of the constructed flat Euclidean plane vanishes; new pointwise form (upstream has only the field-level euclideanConnection_curvature)"),
    ("UpstreamAdapters.DownstreamGeometry.euclidean_curvatureFormAt_eq_zero", "model",
     "U1 consumer: pointwise curvature (0,4) form of the constructed flat Euclidean plane vanishes; public re-derivation of an upstream PRIVATE lemma of the same name (MorganTianLib Ch03/RicciFlow/EuclideanExample.lean:34), which is not consumable downstream"),
    ("UpstreamAdapters.DownstreamGeometry.euclidean_alias_curvature_zero_third", "model",
     "U1 consumer routed through the adapter alias curvature_zero_right (renamed upstream proof)"),
    ("UpstreamAdapters.DownstreamGeometry.euclideanLine_zero", "proved",
     "constructed affine line starts at its base point"),
    ("UpstreamAdapters.DownstreamGeometry.euclideanLine_contMDiff", "proved",
     "constructed affine line is C^1 (regularity input of parallel transport)"),
    ("UpstreamAdapters.DownstreamGeometry.euclideanLine_isGeodesic", "model",
     "U3 consumer: the constructed affine line is a geodesic of the Euclidean plane; upstream instantiation of the public isGeodesic_euclideanGeodesic (not new mathematics)"),
    ("UpstreamAdapters.DownstreamGeometry.euclideanLine_hasGeodesicEquationAt", "model",
     "U3 consumer: projection of the public IsGeodesic predicate to the moving-foot geodesic equation"),
    ("UpstreamAdapters.DownstreamGeometry.euclideanLine_expMapIntrinsic", "model",
     "U3 consumer: immediate consequence of the public expMapIntrinsic_euclidean"),
    ("UpstreamAdapters.DownstreamGeometry.euclideanLine_expMapIntrinsic_smul", "model",
     "U3 consumer: scaling form of the public expMapIntrinsic_euclidean"),
    ("UpstreamAdapters.DownstreamGeometry.euclideanLine_expMapIntrinsic_add", "model",
     "U3 consumer: derived exponential flow identity (not stated upstream)"),
    ("UpstreamAdapters.DownstreamGeometry.euclideanLine_parallelTransport_preserves", "model",
     "U3 consumer: upstream instantiation of the public metricInner_parallelTransportTangentEquiv"),
    ("UpstreamAdaptersPetersen.DownstreamUse.euclidean_curvatureTensorAt_eq_zero", "model",
     "U1 consumer (Petersen family): pointwise curvature tensor of the constructed flat Euclidean plane vanishes; new pointwise form of the public field-level euclideanSpace_curvature_eq_zero"),
    ("UpstreamAdaptersPetersen.DownstreamUse.euclidean_expMap_zero", "model",
     "U3 consumer (Petersen family): upstream instantiation of the public expMap_zero at the concrete Euclidean metric"),
    ("UpstreamAdaptersPetersen.DownstreamUse.euclidean_expMap_zero_smul", "model",
     "U3 consumer (Petersen family): trivial scaled form of expMap_zero at the concrete Euclidean metric"),
    ("UpstreamAdapters.DownstreamGeometry.curvatureOperatorAt_antisymm_left", "proved",
     "U1 general consumer: pointwise curvature operator of any affine connection is antisymmetric in its first two arguments; no upstream pointwise form exists (upstream has field-level curvature_antisymm_left only)"),
    ("UpstreamAdapters.DownstreamGeometry.curvatureOperatorAt_bianchi", "proved",
     "U1 general consumer: pointwise first Bianchi identity for any symmetric affine connection; no upstream pointwise form exists (upstream has field-level curvature_bianchi only)"),
    ("UpstreamAdapters.DownstreamGeometry.curvatureOperatorAt_zero_first", "proved",
     "U1 general consumer: pointwise zero first slot for any affine connection; proof routed through the adapter alias curvature_zero_left"),
    ("UpstreamAdapters.DownstreamGeometry.curvatureOperatorAt_zero_third", "proved",
     "U1 general consumer: pointwise zero third slot for any affine connection; proof routed through the adapter alias curvature_zero_right"),
    ("UpstreamAdapters.PointwiseSymmetries.curvatureFormAt_skew_fst", "proved",
     "U1 DERIVED pointwise form consumer: the (0,4)-form of ANY affine connection is antisymmetric in its first pair; upstream states this pointwise only bundled for a Levi-Civita connection (isAlgCurvatureForm_curvatureFormAt). Derived from the field-level curvatureForm_antisymm_left through the curvatureFormAt_eq tensoriality bridge; not new mathematics, weaker hypothesis than the upstream pointwise route"),
    ("UpstreamAdapters.PointwiseSymmetries.curvatureFormAt_skew_snd_of_isMetricCompatible", "proved",
     "U1 DERIVED pointwise form consumer: the (0,4)-form is antisymmetric in its last pair for any metric-compatible connection; the upstream pointwise route requires IsLeviCivita (symmetric AND compatible), this needs compatibility alone. Derived from curvatureForm_antisymm_right through curvatureFormAt_eq"),
    ("UpstreamAdapters.PointwiseSymmetries.curvatureFormAt_bianchi_of_isSymmetric", "proved",
     "U1 DERIVED pointwise form consumer: pointwise first Bianchi identity for the (0,4)-form of any symmetric connection (no metric compatibility needed); the upstream pointwise route bundles IsLeviCivita. Derived from curvatureForm_bianchi through curvatureFormAt_eq"),
    ("UpstreamAdapters.PointwiseSymmetries.curvatureFormAt_pairSwap_of_isSymmetric_of_isMetricCompatible", "proved",
     "U1 DERIVED pointwise form consumer: pointwise pair-swap R(x,y,z,t) = R(z,t,x,y) for a symmetric metric-compatible connection; the pointwise form of the upstream field-level curvatureForm_pairSwap. Derived consumer, not new mathematics"),

    # ---- round 5 completeness: the remaining non-alias authored declarations ----
    # Until round 5 the DownstreamUse.lean consumers and the small constructions
    # were audited (all 94 cones) but not listed here, so "adapter-authored" meant
    # 22 of the 35 non-alias authored declarations.  They are listed now so that
    # every non-alias authored declaration carries an explicit class.
    ("UpstreamAdapters.DownstreamUse.stdFormR", "definition",
     "constructed input: the standard positive-definite bilinear form (x,y) -> x*y on R, assembled from mathlib's linMulLin"),
    ("UpstreamAdapters.DownstreamUse.stdFormR_apply", "proved",
     "computation rule for the constructed input form (simp lemma, mathlib only)"),
    ("UpstreamAdapters.DownstreamUse.stdFormR_isPosDef", "proved",
     "the constructed input form is positive definite (mathlib mul_self_pos); constructed-input property, not an upstream-snapshot consumer"),
    ("UpstreamAdapters.DownstreamUse.riesz_inner_stdFormR", "proved",
     "consumer of Shared.BilinearForm.riesz_inner at the constructed form: the Riesz representative represents its functional"),
    ("UpstreamAdapters.DownstreamUse.riesz_id_stdFormR", "proved",
     "consumer of Shared.BilinearForm.riesz_unique at the constructed form: the representative of the identity functional is 1"),
    ("UpstreamAdapters.DownstreamUse.riesz_two_smul_id_stdFormR", "proved",
     "consumer of Shared.BilinearForm.riesz_unique at the constructed form: the representative of 2*id is 2"),
    ("UpstreamAdapters.DownstreamUse.eq_one_of_inner_stdFormR_eq", "proved",
     "consumer of Shared.BilinearForm.inner_eq_iff_eq + riesz_unique at the constructed form: a vector testing as 1 against everything is 1"),
    ("UpstreamAdapters.DownstreamUse.edist_le_pathLength_refl", "proved",
     "consumer of Shared.LengthSpace.edist_le_pathLength at the constructed constant path in R"),
    ("UpstreamAdapters.DownstreamUse.tangentBundle_real_t2", "proved",
     "consumer of Shared.TangentBundle.t2Space at the constructed manifold R: its tangent bundle is Hausdorff"),
    ("UpstreamAdapters.DownstreamUse.t2Space_prod_real", "proved",
     "consumer of Shared.FiberBundle.t2Space_totalSpace at the trivial bundle R x R"),
    ("UpstreamAdapters.DownstreamGeometry.Plane", "definition",
     "constructed input manifold: the Euclidean plane EuclideanSpace R (Fin 2)"),
    ("UpstreamAdapters.DownstreamGeometry.euclideanLine", "definition",
     "constructed input curve t -> p + t*v used by the U3 consumers"),
    ("UpstreamAdaptersPetersen.DownstreamUse.Plane", "definition",
     "constructed input manifold for the Petersen-family consumers: EuclideanSpace R (Fin 2) as a manifold over EuclideanSpace R (Fin 2)"),
]


def adapter_provenance(root, name):
    """Resolve an adapter-authored declaration to file:line by scanning sources.

    Two failure modes found in round 5 are fixed here: (a) declaration
    modifiers (`noncomputable def`, `private theorem`, ...) are matched, and
    (b) the search prefers the file whose module path is the declaration's
    namespace prefix, so a short name that occurs in two namespaces (e.g.
    `Plane` in both DownstreamGeometry and the Petersen DownstreamUse) resolves
    to the declaring file instead of the first file in sorted order.
    """
    short = name.rsplit(".", 1)[1]
    prefix = name.rsplit(".", 1)[0] if "." in name else ""
    rx = re.compile(
        r"^[ \t]*(?:@\[[^\]]*\][ \t]*)?"
        r"(?:private[ \t]+|protected[ \t]+|noncomputable[ \t]+|partial[ \t]+|scoped[ \t]+|unsafe[ \t]+)*"
        r"(?:theorem|lemma|def|abbrev|opaque|alias)[ \t]+" + re.escape(short) + r"\b",
        re.M,
    )
    files = [p for p in sorted((root / "adapters").rglob("*.lean")) if ".lake" not in p.parts]

    def module_of(p):
        return ".".join(p.relative_to(root / "adapters").with_suffix("").parts)

    preferred = [p for p in files if module_of(p) == prefix]
    ordered = preferred + [p for p in files if p not in preferred]
    for p in ordered:
        text = p.read_text(errors="replace")
        m = rx.search(text)
        if m:
            return {"package": "adapters", "file": str(p.relative_to(root)),
                    "line": text[: m.start()].count("\n") + 1,
                    "kind": "adapter-authored"}
    return {"package": "adapters", "file": "?", "line": 0, "kind": "adapter-authored"}


PACKAGE_SUMMARY = {
    "shared": {"build": "lake build exit 0 (2476 jobs)", "class": "proved/definition", "note": "book-agnostic infrastructure; Riesz extraction, length spaces, fibre-bundle T2"},
    "formalized-sources/DoCarmo": {"build": "lake build DoCarmoLib exit 0", "class": "proved (geometry core) + model examples", "note": "Riemannian geometry: Levi-Civita, curvature, geodesics, parallel transport, sectional/Ricci"},
    "formalized-sources/Petersen": {"build": "lake build PetersenLib (see exit code)", "class": "proved (geometry core)", "note": "curvature tensor, exponential map, geodesics, comparison"},
    "formalized-sources/MorganTian": {"build": "lake build MorganTianLib exit 0", "class": "proved + conditional (IsRicciFlowOn)", "note": "Ricci flow: pointwise Ricci/scalar, Hamilton maximum principles, curvature evolution, Bochner, divergence; 0 sorry; 426 self-audited cones all in {propext, Classical.choice, Quot.sound}"},
    "formalized-sources/Topping": {"build": "lake build Topping exit 0", "class": "proved + conditional (isRicciFlowOn hypotheses)", "note": "weak maximum principles, divergence, volume evolution under Ricci flow; 213 self-audited cones"},
    "formalized-sources/Hatcher": {"build": "lake build HatcherLib (see exit code)", "class": "proved (algebraic topology)", "note": "fundamental group, covering spaces, homotopy equivalences"},
    "formalized-sources/KleinerLott": {"build": "lake build KleinerLott (see exit code)", "class": "conditional interfaces + proved point selection", "note": "kappa-noncollapsing, point selection, smooth complete Ricci flow interface"},
    "formalized-sources/ChowKnopf": {"build": "lake build ChowKnopf (see exit code)", "class": "small Ricci-flow development", "note": "8 files"},
    "formalized-sources/LeeSmooth": {"build": "not built by this task", "class": "statement-only", "note": "274 real sorry occurrences (comment-stripped); no claim may rest on these"},
    "formalized-sources/LeeRiemannian": {"build": "lake build LeeLib exit 0 (3685 jobs, round 4)", "class": "proved (Riemannian geometry; 0 real sorry)", "note": "116 files; not imported into the adapter's own modules, but compile-checked in this workspace since round 4"},
    "formalized-sources/Evans": {"build": "lake build EvansLib exit 0 (3754 jobs, round 4)", "class": "proved (PDE; 0 real sorry)", "note": "65 files; compile-checked in this workspace since round 4"},
    "formalized-sources/HanLinLectureNotes": {"build": "lake build HanLinLectureNotes exit 0 (8691 jobs, round 4)", "class": "proved (elliptic PDE; 0 real sorry)", "note": "37 files; compile-checked in this workspace since round 4"},
    "formalized-sources/GilbargTrudinger": {"build": "lake build GilbargTrudinger exit 0 (8663 jobs, round 4)", "class": "proved (elliptic PDE; 0 real sorry)", "note": "9 files; compile-checked in this workspace since round 4"},
    "formalized-sources/CaoZhu": {"build": "n/a", "class": "stub", "note": "3 files, 0 declarations"},
    "formalized-sources/CheegerGromovTaylor": {"build": "n/a", "class": "stub", "note": "3 files, 0 declarations"},
    "formalized-sources/ChowEtAl": {"build": "n/a", "class": "stub", "note": "3 files, 0 declarations"},
    "formalized-sources/Thurston": {"build": "n/a", "class": "stub", "note": "3 files, 0 declarations"},
    "PoincareConjecture": {"build": "n/a", "class": "stub", "note": "root project has 0 declarations; no Poincare theorem is present"},
}


def main():
    qn = json.loads((ROOT / "evidence" / "upstream-qualified-names.json").read_text())
    index = {}
    for kw, pkgs in qn.items():
        for pkg, hits in pkgs.items():
            for h in hits:
                index.setdefault(h["name"], {"package": pkg, "file": h["file"], "line": h["line"], "kind": h["kind"]})
    entries, missing = [], []
    for name, cls, note in ADAPTER_CONSUMERS:
        entries.append({"name": name, "class": cls, "note": note,
                        **adapter_provenance(ROOT, name)})
    for name, cls, note in TABLE:
        meta = index.get(name)
        if meta is None:
            missing.append(name)
            meta = {"package": "?", "file": "?", "line": 0, "kind": "?"}
        entries.append({"name": name, "class": cls, "note": note, **meta})
    out = {
        "vocabulary": {
            "proved": "compiled; axiom cone within {propext, Classical.choice, Quot.sound}; hypotheses are genuine data",
            "conditional": "compiled implication whose antecedent is an unproved interface structure",
            "model": "proved for a toy/finite/Euclidean model of the intended geometry",
            "statement-only": "proof admitted (sorry); no claim may rest on it",
            "upstream source claim": "asserted in upstream prose/blueprint but not kernel-checked",
            "definition": "definition/predicate/structure; not itself a claim",
        },
        "entries": entries,
        "packages": PACKAGE_SUMMARY,
        "missing_from_static_index": missing,
    }
    (ROOT / "evidence" / "claim-classification.json").write_text(json.dumps(out, indent=1))
    from collections import Counter
    print("classes:", dict(Counter(e["class"] for e in entries)))
    print("missing from static index:", missing)


if __name__ == "__main__":
    main()
