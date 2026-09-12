#!/usr/bin/env python3
"""Fail-closed kernel-axiom audit for the L4 geometric-comparison development.

Run from the release/ directory (or anywhere; the script locates release/ relative to
itself):

    python3 tools/l4_axiom_audit.py

What it does
------------
1. Compiles `Poincare/L4/AxiomAudit.lean` (which contains only `#print axioms` commands)
   with the pinned toolchain via `lake env lean`, and parses every kernel axiom report.
2. Fails closed unless every expected declaration is reported AND every reported axiom is
   in the whitelist {propext, Classical.choice, Quot.sound}.  A missing report is a failure;
   an unexpected declaration is a failure; `sorryAx` or any custom axiom is a failure.
3. Runs a planted negative control (an `axiom`-based `False` theorem) through the *same*
   checker and requires that it be detected; if the negative control passes the whitelist,
   the audit itself is considered broken and the script fails.
4. Scans the authored L4 sources for forbidden tokens (`sorry`, `admit`, `axiom`,
   `unsafe`, `native_decide`, `proof_wanted`) with comments stripped, so that prose in
   docstrings cannot hide a real occurrence.
5. Prints a JSON summary including sha256 hashes of the audited sources.

Exit status 0 iff every check passed.
"""

from __future__ import annotations

import hashlib
import json
import pathlib
import re
import subprocess
import sys

RELEASE = pathlib.Path(__file__).resolve().parents[1]
DEBUG = RELEASE.parent / "debug"

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

EXPECTED = [
    "Poincare.L4.GeodesicComparison.abs_sub_le_of_deriv_bound",
    "Poincare.L4.GeodesicComparison.jacobi_linear_bounds",
    "Poincare.L4.GeodesicComparison.jacobi_pos_and_ratio_bound",
    "Poincare.L4.GeodesicComparison.euclideanNormalizedOn_of_jacobi",
    "Poincare.L4.GeodesicComparison.riccati_identity_of_jacobi",
    "Poincare.L4.GeodesicComparison.rauch_upper_of_jacobi",
    "Poincare.L4.GeodesicComparison.jacobi_areaRatio_antitone",
    "Poincare.L4.GeodesicComparison.sin_jacobiSolution",
    "Poincare.L4.GeodesicComparison.sin_rauch_witness",
    "Poincare.L4.GeodesicComparison.sin_areaRatio_witness",
    "Poincare.L4.GeodesicComparison.sin_jacobiSolution_threeHalves",
    "Poincare.L4.GeodesicComparison.sin_rauch_witness_long",
    "Poincare.L4.GeodesicComparison.sin_areaRatio_witness_long",
    "Poincare.L4.GeodesicComparison.logDeriv_continuousOn",
    "Poincare.L4.GeodesicComparison.rauch_lower_of_jacobi",
    "Poincare.L4.GeodesicComparison.jacobi_bishopGromovVolumeRatio",
    "Poincare.L4.GeodesicComparison.jacobi_radialVolume_doubling",
    "Poincare.L4.GeodesicComparison.sinh_half_le_one",
    "Poincare.L4.GeodesicComparison.sinh_jacobiSolution",
    "Poincare.L4.GeodesicComparison.sinh_rauch_lower_witness",
    "Poincare.L4.GeodesicComparison.sin_volumeRatio_witness",
    "Poincare.L4.GeodesicComparison.sin_radialVolume_doubling",
    "Poincare.L4.GeodesicComparison.sub_le_of_deriv_le",
    "Poincare.L4.GeodesicComparison.rauch_upper_of_jacobi_of_curvBound",
    "Poincare.L4.GeodesicComparison.sin_rauch_curvBound_witness",
    "Poincare.L4.GeodesicComparison.jacobiSolTwo_rauch_curvBound_witness",
    "Poincare.L4.GeodesicComparison.jacobiSol_pos_of_nonneg",
    "Poincare.L4.GeodesicComparison.jacobiSol_jacobiSolutionOn",
    "Poincare.L4.GeodesicComparison.jacobiSol_second_deriv_bound",
    "Poincare.L4.GeodesicComparison.rauch_upper_of_jacobi_constCurv",
    "Poincare.L4.GeodesicComparison.rauch_constCurv_witness",
    "Poincare.L4.GeodesicComparison.jacobi_le_constCurvModel",
    "Poincare.L4.GeodesicComparison.jacobiSolTwo_le_model_witness",
    "Poincare.L4.GeodesicComparison.JacobiSolutionOn.mono",
    "Poincare.L4.GeodesicComparison.conjugate_point_bound",
    "Poincare.L4.GeodesicComparison.conjugate_point_bound_witness",
    "Poincare.L4.GeodesicComparison.jacobiSol_pos_of_nonpos",
    "Poincare.L4.GeodesicComparison.jacobiSol_monotoneOn_of_nonpos",
    "Poincare.L4.GeodesicComparison.jacobiSol_second_deriv_bound_nonpos",
    "Poincare.L4.GeodesicComparison.rauch_lower_of_jacobi_constCurv",
    "Poincare.L4.GeodesicComparison.sinh_quarter_le_three",
    "Poincare.L4.GeodesicComparison.sinh_one_le_three",
    "Poincare.L4.GeodesicComparison.rauch_lower_constCurv_witness",
    "Poincare.L4.GeodesicComparison.constCurvModel_le_jacobi",
    "Poincare.L4.GeodesicComparison.constCurvModel_le_jacobi_witness",
    "Poincare.L4.GeodesicComparison.hasDerivAtR_sturmModel",
    "Poincare.L4.GeodesicComparison.hasDerivAtR_sturmModelDeriv",
    "Poincare.L4.GeodesicComparison.sturmModel_jacobiSolutionOn",
    "Poincare.L4.GeodesicComparison.sturmModel_pos",
    "Poincare.L4.GeodesicComparison.exists_jacobi_zero_of_curvature_gt",
    "Poincare.L4.GeodesicComparison.exists_jacobi_zero_before_pi_sqrt",
    "Poincare.L4.GeodesicComparison.eq_curvature_of_no_jacobi_zero_before_pi_sqrt",
    "Poincare.L4.GeodesicComparison.sin_sqrt_two_explicit_zero",
    "Poincare.L4.GeodesicComparison.sturm_zero_curvature_witness",
    "Poincare.L4.GeodesicComparison.sin_no_zero_in_Ioo_zero_pi",
    "Poincare.L4.GeodesicComparison.sturm_zero_strictness_necessary",
    "Poincare.L4.GeodesicComparison.jacobiSolutionOn_mono_Icc",
    "Poincare.L4.GeodesicComparison.sturmModel_pos_of_le",
    "Poincare.L4.GeodesicComparison.eq_curvature_of_first_jacobi_zero_of_curvature_le",
    "Poincare.L4.GeodesicComparison.eq_curvature_of_first_jacobi_zero_before_pi_sqrt",
    "Poincare.L4.GeodesicComparison.first_jacobi_zero_le_of_curvature_deficit",
    "Poincare.L4.GeodesicComparison.const_curvature_deficit_no_first_zero",
    "Poincare.L4.GeodesicComparison.sturmModel_first_zero_witness",
    "Poincare.L4.GeodesicComparison.sin_no_first_zero_before_pi_div_sqrt_two",
    "Poincare.L4.GeodesicComparison.sturmModel_pos_at_right",
    "Poincare.L4.GeodesicComparison.exists_smul_sturmModel_of_wronskian_eq_zero",
    "Poincare.L4.GeodesicComparison.wronskian_sturmModel_eq_zero_of_curvature_eq",
    "Poincare.L4.GeodesicComparison.exists_smul_sturmModel_of_curvature_eq",
    "Poincare.L4.GeodesicComparison.sturmModel_eq_zero_at_pi_sqrt",
    "Poincare.L4.GeodesicComparison.wronskian_sturmModel_eq_zero_of_pos",
    "Poincare.L4.GeodesicComparison.eq_zero_of_wronskian_sturmModel_eq_zero",
    "Poincare.L4.GeodesicComparison.no_first_zero_of_curvature_le_of_lt_pi",
    "Poincare.L4.GeodesicComparison.no_first_zero_before_pi_sqrt_of_curvature_le",
    "Poincare.L4.GeodesicComparison.nonvanishing_near_left_of_deriv_ne",
    "Poincare.L4.GeodesicComparison.no_zero_of_curvature_le_of_deriv_ne",
    "Poincare.L4.GeodesicComparison.no_first_zero_before_pi_sqrt_of_curvature_le",
    "Poincare.L4.GeodesicComparison.strict_span_necessary",
    "Poincare.L4.ManifoldIBP.metricInnerInverse_self_nonneg",
    "Poincare.L4.ManifoldIBP.gradInnerInverse_self_nonneg",
    "Poincare.L4.ManifoldIBP.halfSpaceAtlas_dirichletEnergy_nonneg",
    "Poincare.L4.ManifoldIBP.halfSpaceAtlas_weightedLaplacian_selfAdjoint",
    "Poincare.L4.ManifoldIBP.smoothOverlapAtlas_transition_mem_source",
    "Poincare.L4.ManifoldIBP.halfSpaceAtlas_coherence_derived",
    "Poincare.L4.ManifoldIBP.globalWeightedIBP_of_cover_partial_ae'",
    "Poincare.L4.Compactness.coveringNumber_le_of_ghDist_lt",
    "Poincare.L4.Compactness.IsCover.finset_biUnion",
    "Poincare.L4.Compactness.exists_finset_isCover_card_le",
    "Poincare.L4.Compactness.exists_finset_cover_card_le_of_doubling",
    "Poincare.L4.Compactness.coveringNumber_le_of_doubling",
    "Poincare.L4.Compactness.coveringNumber_le_of_doubling_of_le",
    "Poincare.L4.Compactness.coveringNumber_univ_le_of_ghDist_lt_of_doubling",
    "Poincare.L4.Compactness.encard_le_of_forall_finset_card_le",
    "Poincare.L4.Compactness.finset_card_mul_measure_le",
    "Poincare.L4.Compactness.encard_mul_measure_le_of_isSeparated",
    "Poincare.L4.Compactness.packingNumber_le_measure_ratio",
    "Poincare.L4.Compactness.packingNumber_mul_measure_le",
    "Poincare.L4.Compactness.coveringNumber_mul_measure_le",
    "Poincare.L4.Compactness.coveringNumber_le_measure_ratio",
    "Poincare.L4.Compactness.coveringNumber_le_of_measure_doubling",
    "Poincare.L4.Compactness.coveringNumber_le_of_dyadic_doubling",
    "Poincare.L4.Compactness.coveringNumber_le_of_unifLocDoublingMeasure",
    "Poincare.L4.Compactness.real_coveringNumber_doubling_witness",
    "Poincare.L4.Compactness.measure_closedBall_le_pow_mul",
    "Poincare.L4.Compactness.coveringNumber_le_of_measure_doubling_allScales",
    "Poincare.L4.Compactness.coveringNumber_le_floor_of_measure_doubling_allScales",
]

D13_HEADLINES = [
    "Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae",
    "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional",
    "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_greenIdentity",
    "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_laplacianIntegralZero",
    "Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_weightedIBP_via_pou",
    "Poincare.D13.ManifoldIBP.manifoldWeightedIBP_of_atlasData",
    "Poincare.D13.HeatKernelBridge.finiteLifetimeEntropyBridge_gaussian",
    "Poincare.D13.HeatKernelBridge.monotoneOn_F_gaussian",
]

AUTHORED = [
    "Poincare/L4/GeodesicComparison/RauchBridge.lean",
    "Poincare/L4/GeodesicComparison/DownstreamComparison.lean",
    "Poincare/L4/GeodesicComparison/ConstantCurvatureRauch.lean",
    "Poincare/L4/GeodesicComparison/CurvatureBoundRauch.lean",
    "Poincare/L4/GeodesicComparison/ConjugatePointBound.lean",
    "Poincare/L4/GeodesicComparison/ConstantCurvatureRauchLower.lean",
    "Poincare/L4/GeodesicComparison/SturmZeroCount.lean",
    "Poincare/L4/GeodesicComparison/TwoSidedSturm.lean",
    "Poincare/L4/GeodesicComparison/SturmUniqueness.lean",
    "Poincare/L4/ManifoldIBP/WeightedSelfAdjointness.lean",
    "Poincare/L4/ManifoldIBP/AtlasHypothesisRedundancy.lean",
    "Poincare/L4/ManifoldIBP/D13HeadlineAudit.lean",
    "Poincare/L4/Compactness/CoveringStability.lean",
    "Poincare/L4/Compactness/DoublingToCovers.lean",
    "Poincare/L4/Compactness/MeasureGrowthCovers.lean",
    "Poincare/L4/AxiomAudit.lean",
]

FORBIDDEN = ["sorry", "admit", "axiom", "unsafe", "native_decide", "proof_wanted"]

AXIOM_RE = re.compile(r"'([^']+)' depends on axioms: \[(.*?)\]", re.S)


def strip_comments(src: str) -> str:
    """Remove nested block comments and line comments (no string literals in Lean paths)."""
    out: list[str] = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
        elif src.startswith("/-", i):
            depth += 1
            i += 2
        elif depth > 0 and src.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth > 0:
            i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def parse_axioms(text: str) -> dict[str, list[str]]:
    return {
        name: [a.strip() for a in ax.split(",") if a.strip()]
        for name, ax in AXIOM_RE.findall(text)
    }


def audit_reports(text: str, expected: list[str]) -> tuple[list[str], dict[str, list[str]]]:
    """Fail-closed check of a Lean output text against `expected` declarations."""
    violations: list[str] = []
    found = parse_axioms(text)
    for name in expected:
        if name not in found:
            violations.append(f"missing axiom report for {name}")
            continue
        bad = [a for a in found[name] if a not in ALLOWED]
        if bad:
            violations.append(f"{name} depends on forbidden axioms {bad}")
    extra = sorted(set(found) - set(expected))
    if extra:
        violations.append(f"unexpected declarations in audit output: {extra}")
    return violations, found


def run_lean(path: pathlib.Path) -> tuple[int, str]:
    try:
        arg = str(path.relative_to(RELEASE))
    except ValueError:
        arg = str(path)
    proc = subprocess.run(
        ["lake", "env", "lean", arg],
        cwd=RELEASE,
        capture_output=True,
        text=True,
    )
    return proc.returncode, proc.stdout + proc.stderr


def sha256(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return h.hexdigest()


def main() -> int:
    report: dict = {"allowed": sorted(ALLOWED), "expected": len(EXPECTED), "violations": []}

    # --- 1/2. Real audit, fail-closed. -------------------------------------------------
    rc, out = run_lean(RELEASE / "Poincare/L4/AxiomAudit.lean")
    if rc != 0:
        report["violations"].append(f"AxiomAudit.lean failed to compile (exit {rc})")
        report["lean_output_tail"] = out[-2000:]
    violations, found = audit_reports(out, EXPECTED)
    report["violations"].extend(violations)
    report["audited"] = len(found)
    report["axiom_cones"] = found

    # --- 2b. Independent re-audit of the D13 headline theorems. ------------------------
    rc2, out2 = run_lean(RELEASE / "Poincare/L4/ManifoldIBP/D13HeadlineAudit.lean")
    if rc2 != 0:
        report["violations"].append(f"D13HeadlineAudit.lean failed to compile (exit {rc2})")
        report["d13_lean_output_tail"] = out2[-2000:]
    d13_violations, d13_found = audit_reports(out2, D13_HEADLINES)
    report["violations"].extend(d13_violations)
    report["d13_headlines_audited"] = len(d13_found)
    report["d13_axiom_cones"] = d13_found

    # --- 3. Planted negative control through the same checker. ------------------------
    DEBUG.mkdir(parents=True, exist_ok=True)
    neg = DEBUG / "L4NegControl.lean"
    neg.write_text(
        "axiom l4NegControlAxiom : False\n"
        "theorem l4NegControl : False := l4NegControlAxiom\n"
        "#print axioms l4NegControl\n"
    )
    nrc, nout = run_lean(neg)
    neg_violations, neg_found = audit_reports(nout, ["l4NegControl"])
    control_detected = bool(neg_violations) and any(
        "forbidden axioms" in v for v in neg_violations
    )
    report["negative_control"] = {
        "lean_exit": nrc,
        "axioms_reported": neg_found,
        "detected": control_detected,
        "violations": neg_violations,
    }
    if nrc != 0 or not control_detected:
        report["violations"].append(
            "negative control was not detected: the audit cannot be trusted (fail-closed)"
        )

    # --- 4. Forbidden-token scan over authored sources. --------------------------------
    forbidden_hits: dict[str, list[str]] = {}
    for rel in AUTHORED:
        p = RELEASE / rel
        src = strip_comments(p.read_text())
        hits = []
        for tok in FORBIDDEN:
            for m in re.finditer(rf"\b{re.escape(tok)}\b", src):
                line = src[: m.start()].count("\n") + 1
                hits.append(f"{rel}:{line}:{tok}")
        if hits:
            forbidden_hits[rel] = hits
    report["forbidden_tokens"] = forbidden_hits
    if forbidden_hits:
        report["violations"].append(f"forbidden tokens found: {forbidden_hits}")

    # --- 5. Source hashes. -------------------------------------------------------------
    report["source_sha256"] = {rel: sha256(RELEASE / rel) for rel in AUTHORED}

    report["verdict"] = "PASS" if not report["violations"] else "FAIL"
    print(json.dumps(report, indent=2))
    return 0 if report["verdict"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
