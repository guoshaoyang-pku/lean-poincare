#!/usr/bin/env python3
"""Fail-closed programmatic axiom audit for Poincare.D12.KappaVariational.

Parses the output of `lake env lean Poincare/D12/KappaVariational/Audit.lean` and checks:
  * every `'decl' depends on axioms: [...]` line lists only permitted axioms
    (propext, Classical.choice, Quot.sound);
  * the expected set of declarations is present (no missing declaration);
  * no forbidden tokens (sorryAx, Lean.ofReduceBool, trustCompiler, any project axiom)
    appear anywhere in the log.

Exit 0 only when every check passes; any failure is exit 1 (fail-closed).
"""
import json
import re
import sys

PERMITTED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_TOKENS = ["sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler", "trustCompiler",
                    "Classical.choice.__", "propext.__", "Quot.sound.__"]

EXPECTED = [
    "Poincare.D12.KappaVariational.gaussianVecTau",
    "Poincare.D12.KappaVariational.gaussianVecTauNormalized",
    "Poincare.D12.KappaVariational.gaussianVecTau_def",
    "Poincare.D12.KappaVariational.gaussianVecTauNormalized_def",
    "Poincare.D12.KappaVariational.integral_gaussianKernel_tau",
    "Poincare.D12.KappaVariational.gaussianKernel_tau_eq",
    "Poincare.D12.KappaVariational.integral_gaussianVecTau_fubini",
    "Poincare.D12.KappaVariational.integral_gaussianVecTau",
    "Poincare.D12.KappaVariational.integral_gaussianVecTau_eq_rpow",
    "Poincare.D12.KappaVariational.integral_gaussianVecTauNormalized",
    "Poincare.D12.KappaVariational.gaussianVecTau_eq_exp_neg_sum_sq",
    "Poincare.D12.KappaVariational.gaussianVecTau_eq_exp_neg_normSq_div",
    "Poincare.D12.KappaVariational.integral_exp_neg_normSq_div",
    "Poincare.D12.KappaVariational.gaussianReducedVolumeDensity",
    "Poincare.D12.KappaVariational.gaussianReducedVolume",
    "Poincare.D12.KappaVariational.gaussianReducedVolumeDensity_def",
    "Poincare.D12.KappaVariational.gaussianReducedVolume_def",
    "Poincare.D12.KappaVariational.integral_gaussianReducedVolumeDensity",
    "Poincare.D12.KappaVariational.gaussianReducedVolume_eq_one",
    "Poincare.D12.KappaVariational.gaussianReducedVolumeViaL",
    "Poincare.D12.KappaVariational.gaussianReducedVolumeViaL_eq_gaussianReducedVolume",
    "Poincare.D12.KappaVariational.gaussianReducedVolumeViaL_eq_one",
    "Poincare.D12.KappaVariational.gaussianReducedVolumeDensity_pos",
    "Poincare.D12.KappaVariational.gaussianReducedVolumeDensity_ne_zero",
    "Poincare.D12.KappaVariational.gaussianReducedVolumeDensity_two_half_zero",
    "Poincare.D12.KappaVariational.gaussianReducedVolumeDensity_two_half_zero_ne_one",
    "Poincare.D12.KappaVariational.constantCurvatureFlow",
    "Poincare.D12.KappaVariational.constantCurvatureFlow_scalarCurvature",
    "Poincare.D12.KappaVariational.constantCurvatureFlow_metric",
    "Poincare.D12.KappaVariational.intervalIntegrable_sqrt",
    "Poincare.D12.KappaVariational.integral_sqrt",
    "Poincare.D12.KappaVariational.toGaussianPath",
    "Poincare.D12.KappaVariational.constantCurvature_length_le",
    "Poincare.D12.KappaVariational.constantCurvatureLPath",
    "Poincare.D12.KappaVariational.constantCurvature_LlengthAlong",
    "Poincare.D12.KappaVariational.constantCurvature_isLMinimizer",
    "Poincare.D12.KappaVariational.rpow_three_halves_eq_mul_sqrt",
    "Poincare.D12.KappaVariational.constantCurvature_reducedLength",
    "Poincare.D12.KappaVariational.constantCurvature_reducedLength_le",
    "Poincare.D12.KappaVariational.constantCurvatureReducedLengthData",
    "Poincare.D12.KappaVariational.constantCurvatureReducedLengthData_reducedLength",
    "Poincare.D12.KappaVariational.constantCurvatureLMinimizerExistence",
    "Poincare.D12.KappaVariational.constantCurvature_reducedLength_mono_in_R0",
    "Poincare.D12.KappaVariational.gaussianReducedVolumeCertificate",
    "Poincare.D12.KappaVariational.gaussianReducedVolumeCertificate_volume",
    "Poincare.D12.KappaVariational.gaussianReducedVolumeCertificate_constant_one",
    "Poincare.D12.KappaVariational.gaussianReducedVolumeCertificate_antitoneOn",
    "Poincare.D12.KappaVariational.gaussianReducedVolume_monotoneOn_and_antitoneOn",
    "Poincare.D12.KappaVariational.gaussianUniformReducedVolumeLowerBound",
    "Poincare.D12.KappaVariational.gaussianUniformReducedVolumeLowerBound_integral",
    "Poincare.D12.KappaVariational.gaussianReducedVolumeDensity_shape",
    "Poincare.D12.KappaVariational.gaussianReducedVolumeDensity_shape_integral",
    "Poincare.D12.KappaVariational.ClosureRecord",
    "Poincare.D12.KappaVariational.rlv10Statement",
    "Poincare.D12.KappaVariational.rlv10Closure",
    "Poincare.D12.KappaVariational.ncf12ModelStatement",
    "Poincare.D12.KappaVariational.ncf12ModelClosure",
    "Poincare.D12.KappaVariational.rlv1ModelStatement",
    "Poincare.D12.KappaVariational.rlv1ModelClosure",
    "Poincare.D12.KappaVariational.kappaVariationalClosures",
    "Poincare.D12.KappaVariational.kappaVariationalClosures_nonempty",
    "Poincare.D12.KappaVariational.ballVolumeComparisonExists",
    "Poincare.D12.KappaVariational.gaussianKappaNoncollapsing_of_ballVolumeComparison",
    "Poincare.D12.KappaVariational.kappaVariationalRemainingDependencies",
    "Poincare.D12.KappaVariational.kappaVariationalRemainingDependencies_length",
    "Poincare.D12.KappaVariational.kappaVariationalRemainingDependencies_all_named",
]

LINE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
NONE_LINE = re.compile(r"'([^']+)' does not depend on any axioms")


def main() -> int:
    log_path = sys.argv[1] if len(sys.argv) > 1 else "audit.log"
    out_path = sys.argv[2] if len(sys.argv) > 2 else "axioms.json"
    with open(log_path, encoding="utf-8") as f:
        text = f.read()

    failures = []
    for tok in FORBIDDEN_TOKENS:
        if tok in text:
            failures.append(f"forbidden token in log: {tok}")

    cones = {}
    for m in NONE_LINE.finditer(text):
        cones[m.group(1)] = []
    for m in LINE.finditer(text):
        name, axs = m.group(1), m.group(2)
        axs_list = [a.strip() for a in axs.split(",") if a.strip()]
        cones[name] = axs_list
        bad = [a for a in axs_list if a not in PERMITTED]
        if bad:
            failures.append(f"declaration '{name}' has non-permitted axioms {bad}")

    for name in EXPECTED:
        if name not in cones:
            failures.append(f"declaration '{name}' missing from the audit output")

    result = {
        "permitted": sorted(PERMITTED),
        "declarations_audited": len(cones),
        "declarations_expected": len(EXPECTED),
        "failures": failures,
        "pass": not failures,
    }
    summary = {}
    for name, axs in cones.items():
        key = ",".join(sorted(axs)) if axs else "(none)"
        summary[key] = summary.get(key, 0) + 1
    result["cone_summary"] = summary
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(result, f, indent=2, sort_keys=True)

    if failures:
        print("AUDIT_FAIL")
        for fl in failures:
            print("  " + fl)
        return 1
    print(f"AUDIT_OK: {len(cones)} declarations audited, cone summary: {summary}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
