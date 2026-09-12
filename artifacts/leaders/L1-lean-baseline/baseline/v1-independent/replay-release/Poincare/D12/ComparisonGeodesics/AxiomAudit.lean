/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D12 — kernel axiom audit for the comparison-geodesics development

This file contains no mathematics: it asks the Lean kernel to print the axiom
dependencies of every declaration of the D12 comparison-geodesics development.  The
expected (and observed) answer for all of them is the standard classical trio

`[propext, Classical.choice, Quot.sound]`

with no `sorryAx`, no `native_decide`, no custom axiom and no `unsafe` declaration
anywhere in the dependency cone.  The machine-checked fail-closed gate over this output
is `tools/d12_axiom_audit.py` (run from `release/`): it fails unless every audited
declaration reports exactly a subset of the whitelist and the audit covers all expected
declarations.
-/
import Poincare.D12.ComparisonGeodesics.ModelEuclidean
import Poincare.D12.ComparisonGeodesics.VolumeRatio
import Poincare.D12.ComparisonGeodesics.SingularRiccati
import Poincare.D12.ComparisonGeodesics.RiccatiComparison
import Poincare.D12.ComparisonGeodesics.SturmComparison
import Poincare.D12.ComparisonGeodesics.Definitions

/-! ## Definitions.lean -/

#print axioms Poincare.D12.ComparisonGeodesics.JacobiSolutionOn
#print axioms Poincare.D12.ComparisonGeodesics.JacobiSolutionOn.neg
#print axioms Poincare.D12.ComparisonGeodesics.wronskian
#print axioms Poincare.D12.ComparisonGeodesics.RiccatiLeOn
#print axioms Poincare.D12.ComparisonGeodesics.RiccatiEqOn
#print axioms Poincare.D12.ComparisonGeodesics.RiccatiEqOn.toLe
#print axioms Poincare.D12.ComparisonGeodesics.EuclideanNormalizedOn
#print axioms Poincare.D12.ComparisonGeodesics.radialVolume
#print axioms Poincare.D12.ComparisonGeodesics.hasDerivAtR_id
#print axioms Poincare.D12.ComparisonGeodesics.hasDerivAtR_const
#print axioms Poincare.D12.ComparisonGeodesics.hasDerivAtR_inv
#print axioms Poincare.D12.ComparisonGeodesics.hasDerivAtR_pow

/-! ## SturmComparison.lean -/

#print axioms Poincare.D12.ComparisonGeodesics.wronskian_hasDerivAt
#print axioms Poincare.D12.ComparisonGeodesics.wronskian_deriv
#print axioms Poincare.D12.ComparisonGeodesics.wronskian_continuousOn
#print axioms Poincare.D12.ComparisonGeodesics.wronskian_differentiableOn
#print axioms Poincare.D12.ComparisonGeodesics.wronskian_antitoneOn_of_le
#print axioms Poincare.D12.ComparisonGeodesics.deriv_nonpos_of_posOn_Ioo_of_eq_at_right
#print axioms Poincare.D12.ComparisonGeodesics.nonneg_of_continuousOn_of_posOn_Ioo
#print axioms Poincare.D12.ComparisonGeodesics.sturm_zero_comparison_of_pos
#print axioms Poincare.D12.ComparisonGeodesics.sign_constant_of_no_zero
#print axioms Poincare.D12.ComparisonGeodesics.sturm_zero_comparison

/-! ## RiccatiComparison.lean -/

#print axioms Poincare.D12.ComparisonGeodesics.logDeriv
#print axioms Poincare.D12.ComparisonGeodesics.logDeriv_hasDerivAt
#print axioms Poincare.D12.ComparisonGeodesics.logDeriv_riccati
#print axioms Poincare.D12.ComparisonGeodesics.logDeriv_le_of_le
#print axioms Poincare.D12.ComparisonGeodesics.solution_le_of_initial
#print axioms Poincare.D12.ComparisonGeodesics.solution_le_of_same_initial

/-! ## SingularRiccati.lean -/

#print axioms Poincare.D12.ComparisonGeodesics.riccati_delta_le_exp
#print axioms Poincare.D12.ComparisonGeodesics.riccati_le_of_initial
#print axioms Poincare.D12.ComparisonGeodesics.riccati_delta_ge_exp
#print axioms Poincare.D12.ComparisonGeodesics.riccati_ge_of_initial
#print axioms Poincare.D12.ComparisonGeodesics.riccati_le_of_singular_normalization
#print axioms Poincare.D12.ComparisonGeodesics.riccati_ge_of_singular_normalization
#print axioms Poincare.D12.ComparisonGeodesics.euclideanNormalizedOn_not_continuousOn_zero

/-! ## VolumeRatio.lean -/

#print axioms Poincare.D12.ComparisonGeodesics.areaRatio_hasDerivAt
#print axioms Poincare.D12.ComparisonGeodesics.areaRatio_antitone_of_logDeriv_le
#print axioms Poincare.D12.ComparisonGeodesics.radialVolume_pos_of_pos
#print axioms Poincare.D12.ComparisonGeodesics.radialVolume_hasDerivAt
#print axioms Poincare.D12.ComparisonGeodesics.radialVolume_numerator_le_zero
#print axioms Poincare.D12.ComparisonGeodesics.volumeRatio_antitone
#print axioms Poincare.D12.ComparisonGeodesics.bishopGromovVolumeRatio
#print axioms Poincare.D12.ComparisonGeodesics.bishopGromov_volume_le

/-! ## ModelEuclidean.lean -/

#print axioms Poincare.D12.ComparisonGeodesics.euclidModelM
#print axioms Poincare.D12.ComparisonGeodesics.euclidModelDm
#print axioms Poincare.D12.ComparisonGeodesics.euclidModelA
#print axioms Poincare.D12.ComparisonGeodesics.euclidModelM_hasDerivAt
#print axioms Poincare.D12.ComparisonGeodesics.euclidModelM_riccati
#print axioms Poincare.D12.ComparisonGeodesics.euclidModelM_contOn
#print axioms Poincare.D12.ComparisonGeodesics.euclidModelM_normalized
#print axioms Poincare.D12.ComparisonGeodesics.euclidModelA_hasDerivAt
#print axioms Poincare.D12.ComparisonGeodesics.euclidModelA_pos
#print axioms Poincare.D12.ComparisonGeodesics.euclidModelA_zero
#print axioms Poincare.D12.ComparisonGeodesics.euclidModelA_contOn
#print axioms Poincare.D12.ComparisonGeodesics.euclidModelA_logDeriv
#print axioms Poincare.D12.ComparisonGeodesics.euclidModel_volume
#print axioms Poincare.D12.ComparisonGeodesics.euclidModel_singular_comparison
#print axioms Poincare.D12.ComparisonGeodesics.euclidModel_singular_comparison_ge
#print axioms Poincare.D12.ComparisonGeodesics.euclidModel_bishopGromov
