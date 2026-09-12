/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — kernel axiom audit for the geometric-comparison development

This file contains no mathematics: it asks the Lean kernel to print the axiom dependencies
of every declaration authored under `Poincare/L4/GeodesicComparison/`.  The expected (and
observed) answer for all of them is the standard classical trio

`[propext, Classical.choice, Quot.sound]`

with no `sorryAx`, no `native_decide`, no custom axiom and no `unsafe` declaration anywhere
in the dependency cone.  The machine-checked fail-closed gate over this output is
`tools/l4_axiom_audit.py` (run from `release/`): it fails unless every audited declaration
reports exactly a subset of the whitelist, the audit covers every expected declaration, and
a planted negative control is detected.
-/
import Poincare.L4.GeodesicComparison.RauchBridge
import Poincare.L4.GeodesicComparison.DownstreamComparison
import Poincare.L4.GeodesicComparison.ConstantCurvatureRauch
import Poincare.L4.GeodesicComparison.CurvatureBoundRauch
import Poincare.L4.GeodesicComparison.ConjugatePointBound
import Poincare.L4.GeodesicComparison.ConstantCurvatureRauchLower
import Poincare.L4.GeodesicComparison.SturmZeroCount
import Poincare.L4.GeodesicComparison.TwoSidedSturm
import Poincare.L4.GeodesicComparison.SturmUniqueness
import Poincare.L4.ManifoldIBP.WeightedSelfAdjointness
import Poincare.L4.ManifoldIBP.AtlasHypothesisRedundancy
import Poincare.L4.Compactness.CoveringStability
import Poincare.L4.Compactness.DoublingToCovers
import Poincare.L4.Compactness.MeasureGrowthCovers

/-! ## RauchBridge.lean -/

#print axioms Poincare.L4.GeodesicComparison.abs_sub_le_of_deriv_bound
#print axioms Poincare.L4.GeodesicComparison.jacobi_linear_bounds
#print axioms Poincare.L4.GeodesicComparison.jacobi_pos_and_ratio_bound
#print axioms Poincare.L4.GeodesicComparison.euclideanNormalizedOn_of_jacobi
#print axioms Poincare.L4.GeodesicComparison.riccati_identity_of_jacobi
#print axioms Poincare.L4.GeodesicComparison.rauch_upper_of_jacobi
#print axioms Poincare.L4.GeodesicComparison.jacobi_areaRatio_antitone
#print axioms Poincare.L4.GeodesicComparison.sin_jacobiSolution
#print axioms Poincare.L4.GeodesicComparison.sin_rauch_witness
#print axioms Poincare.L4.GeodesicComparison.sin_areaRatio_witness
#print axioms Poincare.L4.GeodesicComparison.sin_jacobiSolution_threeHalves
#print axioms Poincare.L4.GeodesicComparison.sin_rauch_witness_long
#print axioms Poincare.L4.GeodesicComparison.sin_areaRatio_witness_long

/-! ## DownstreamComparison.lean -/

#print axioms Poincare.L4.GeodesicComparison.logDeriv_continuousOn
#print axioms Poincare.L4.GeodesicComparison.rauch_lower_of_jacobi
#print axioms Poincare.L4.GeodesicComparison.jacobi_bishopGromovVolumeRatio
#print axioms Poincare.L4.GeodesicComparison.jacobi_radialVolume_doubling
#print axioms Poincare.L4.GeodesicComparison.sinh_half_le_one
#print axioms Poincare.L4.GeodesicComparison.sinh_jacobiSolution
#print axioms Poincare.L4.GeodesicComparison.sinh_rauch_lower_witness
#print axioms Poincare.L4.GeodesicComparison.sin_volumeRatio_witness
#print axioms Poincare.L4.GeodesicComparison.sin_radialVolume_doubling

/-! ## GeodesicComparison/ConstantCurvatureRauch.lean -/

#print axioms Poincare.L4.GeodesicComparison.jacobiSol_pos_of_nonneg
#print axioms Poincare.L4.GeodesicComparison.jacobiSol_jacobiSolutionOn
#print axioms Poincare.L4.GeodesicComparison.jacobiSol_second_deriv_bound
#print axioms Poincare.L4.GeodesicComparison.rauch_upper_of_jacobi_constCurv
#print axioms Poincare.L4.GeodesicComparison.rauch_constCurv_witness
#print axioms Poincare.L4.GeodesicComparison.jacobi_le_constCurvModel
#print axioms Poincare.L4.GeodesicComparison.jacobiSolTwo_le_model_witness

/-! ## GeodesicComparison/CurvatureBoundRauch.lean -/

#print axioms Poincare.L4.GeodesicComparison.sub_le_of_deriv_le
#print axioms Poincare.L4.GeodesicComparison.rauch_upper_of_jacobi_of_curvBound
#print axioms Poincare.L4.GeodesicComparison.sin_rauch_curvBound_witness
#print axioms Poincare.L4.GeodesicComparison.jacobiSolTwo_rauch_curvBound_witness

/-! ## GeodesicComparison/ConjugatePointBound.lean -/

#print axioms Poincare.L4.GeodesicComparison.JacobiSolutionOn.mono
#print axioms Poincare.L4.GeodesicComparison.conjugate_point_bound
#print axioms Poincare.L4.GeodesicComparison.conjugate_point_bound_witness

/-! ## GeodesicComparison/ConstantCurvatureRauchLower.lean -/

#print axioms Poincare.L4.GeodesicComparison.jacobiSol_pos_of_nonpos
#print axioms Poincare.L4.GeodesicComparison.jacobiSol_monotoneOn_of_nonpos
#print axioms Poincare.L4.GeodesicComparison.jacobiSol_second_deriv_bound_nonpos
#print axioms Poincare.L4.GeodesicComparison.rauch_lower_of_jacobi_constCurv
#print axioms Poincare.L4.GeodesicComparison.sinh_quarter_le_three
#print axioms Poincare.L4.GeodesicComparison.sinh_one_le_three
#print axioms Poincare.L4.GeodesicComparison.rauch_lower_constCurv_witness
#print axioms Poincare.L4.GeodesicComparison.constCurvModel_le_jacobi
#print axioms Poincare.L4.GeodesicComparison.constCurvModel_le_jacobi_witness

 /-! ## GeodesicComparison/SturmZeroCount.lean -/

#print axioms Poincare.L4.GeodesicComparison.hasDerivAtR_sturmModel
#print axioms Poincare.L4.GeodesicComparison.hasDerivAtR_sturmModelDeriv
#print axioms Poincare.L4.GeodesicComparison.sturmModel_jacobiSolutionOn
#print axioms Poincare.L4.GeodesicComparison.sturmModel_pos
#print axioms Poincare.L4.GeodesicComparison.exists_jacobi_zero_of_curvature_gt
#print axioms Poincare.L4.GeodesicComparison.exists_jacobi_zero_before_pi_sqrt
#print axioms Poincare.L4.GeodesicComparison.eq_curvature_of_no_jacobi_zero_before_pi_sqrt
#print axioms Poincare.L4.GeodesicComparison.sin_sqrt_two_explicit_zero
#print axioms Poincare.L4.GeodesicComparison.sturm_zero_curvature_witness
#print axioms Poincare.L4.GeodesicComparison.sin_no_zero_in_Ioo_zero_pi
#print axioms Poincare.L4.GeodesicComparison.sturm_zero_strictness_necessary

 /-! ## GeodesicComparison/TwoSidedSturm.lean -/

#print axioms Poincare.L4.GeodesicComparison.jacobiSolutionOn_mono_Icc
#print axioms Poincare.L4.GeodesicComparison.sturmModel_pos_of_le
#print axioms Poincare.L4.GeodesicComparison.eq_curvature_of_first_jacobi_zero_of_curvature_le
#print axioms Poincare.L4.GeodesicComparison.eq_curvature_of_first_jacobi_zero_before_pi_sqrt
#print axioms Poincare.L4.GeodesicComparison.first_jacobi_zero_le_of_curvature_deficit
#print axioms Poincare.L4.GeodesicComparison.const_curvature_deficit_no_first_zero
#print axioms Poincare.L4.GeodesicComparison.sturmModel_first_zero_witness
#print axioms Poincare.L4.GeodesicComparison.sin_no_first_zero_before_pi_div_sqrt_two

 /-! ## GeodesicComparison/SturmUniqueness.lean -/

#print axioms Poincare.L4.GeodesicComparison.sturmModel_pos_at_right
#print axioms Poincare.L4.GeodesicComparison.exists_smul_sturmModel_of_wronskian_eq_zero
#print axioms Poincare.L4.GeodesicComparison.wronskian_sturmModel_eq_zero_of_curvature_eq
#print axioms Poincare.L4.GeodesicComparison.exists_smul_sturmModel_of_curvature_eq
#print axioms Poincare.L4.GeodesicComparison.sturmModel_eq_zero_at_pi_sqrt
#print axioms Poincare.L4.GeodesicComparison.wronskian_sturmModel_eq_zero_of_pos
#print axioms Poincare.L4.GeodesicComparison.eq_zero_of_wronskian_sturmModel_eq_zero
#print axioms Poincare.L4.GeodesicComparison.no_first_zero_of_curvature_le_of_lt_pi
#print axioms Poincare.L4.GeodesicComparison.no_first_zero_before_pi_sqrt_of_curvature_le
#print axioms Poincare.L4.GeodesicComparison.nonvanishing_near_left_of_deriv_ne
#print axioms Poincare.L4.GeodesicComparison.no_zero_of_curvature_le_of_deriv_ne
#print axioms Poincare.L4.GeodesicComparison.no_first_zero_before_pi_sqrt_of_curvature_le
#print axioms Poincare.L4.GeodesicComparison.strict_span_necessary

 /-! ## ManifoldIBP/AtlasHypothesisRedundancy.lean -/

#print axioms Poincare.L4.ManifoldIBP.smoothOverlapAtlas_transition_mem_source
#print axioms Poincare.L4.ManifoldIBP.halfSpaceAtlas_coherence_derived
#print axioms Poincare.L4.ManifoldIBP.globalWeightedIBP_of_cover_partial_ae'

/-! ## ManifoldIBP/WeightedSelfAdjointness.lean -/

#print axioms Poincare.L4.ManifoldIBP.metricInnerInverse_self_nonneg
#print axioms Poincare.L4.ManifoldIBP.gradInnerInverse_self_nonneg
#print axioms Poincare.L4.ManifoldIBP.halfSpaceAtlas_dirichletEnergy_nonneg
#print axioms Poincare.L4.ManifoldIBP.halfSpaceAtlas_weightedLaplacian_selfAdjoint

/-! ## Compactness/CoveringStability.lean -/

#print axioms Poincare.L4.Compactness.coveringNumber_le_of_ghDist_lt

/-! ## Compactness/DoublingToCovers.lean -/

#print axioms Poincare.L4.Compactness.IsCover.finset_biUnion
#print axioms Poincare.L4.Compactness.exists_finset_isCover_card_le
#print axioms Poincare.L4.Compactness.exists_finset_cover_card_le_of_doubling
#print axioms Poincare.L4.Compactness.coveringNumber_le_of_doubling
#print axioms Poincare.L4.Compactness.coveringNumber_le_of_doubling_of_le
#print axioms Poincare.L4.Compactness.coveringNumber_univ_le_of_ghDist_lt_of_doubling

/-! ## Compactness/MeasureGrowthCovers.lean -/

#print axioms Poincare.L4.Compactness.encard_le_of_forall_finset_card_le
#print axioms Poincare.L4.Compactness.finset_card_mul_measure_le
#print axioms Poincare.L4.Compactness.encard_mul_measure_le_of_isSeparated
#print axioms Poincare.L4.Compactness.packingNumber_le_measure_ratio
#print axioms Poincare.L4.Compactness.packingNumber_mul_measure_le
#print axioms Poincare.L4.Compactness.coveringNumber_mul_measure_le
#print axioms Poincare.L4.Compactness.coveringNumber_le_measure_ratio
#print axioms Poincare.L4.Compactness.coveringNumber_le_of_measure_doubling
#print axioms Poincare.L4.Compactness.coveringNumber_le_of_dyadic_doubling
#print axioms Poincare.L4.Compactness.coveringNumber_le_of_unifLocDoublingMeasure
#print axioms Poincare.L4.Compactness.real_coveringNumber_doubling_witness
#print axioms Poincare.L4.Compactness.measure_closedBall_le_pow_mul
#print axioms Poincare.L4.Compactness.coveringNumber_le_of_measure_doubling_allScales
#print axioms Poincare.L4.Compactness.coveringNumber_le_floor_of_measure_doubling_allScales
