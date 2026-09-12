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
import Poincare.L4.GeodesicComparison.ZeroSpacing
import Poincare.L4.ManifoldIBP.WeightedSelfAdjointness
import Poincare.L4.ManifoldIBP.AtlasHypothesisRedundancy
import Poincare.L4.Compactness.CoveringStability
import Poincare.L4.Compactness.DoublingToCovers
import Poincare.L4.Compactness.MeasureGrowthCovers
import Poincare.L4.Compactness.FamilyCovers
import Poincare.L4.PointedGH.Family
import Poincare.L4.Compactness.MeasureGrowthChain
import Poincare.L4.Compactness.MeasureGrowthChainWitness
import Poincare.L4.Compactness.MeasureGrowthChainCircle
import Poincare.L4.Compactness.MeasureGrowthChainCircleFamily
import Poincare.L4.Compactness.RicciGrowthChain
import Poincare.L4.Compactness.FlatTorusGrowth
import Poincare.L4.GeodesicComparison.FlatGeodesicExpModel

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
#print axioms Poincare.L4.GeodesicComparison.eq_zero_of_wronskian_sturmModel_eq_zero
#print axioms Poincare.L4.GeodesicComparison.no_first_zero_of_curvature_le_of_lt_pi
#print axioms Poincare.L4.GeodesicComparison.no_first_zero_before_pi_sqrt_of_curvature_le
#print axioms Poincare.L4.GeodesicComparison.nonvanishing_near_left_of_deriv_ne
#print axioms Poincare.L4.GeodesicComparison.no_zero_of_curvature_le_of_deriv_ne
#print axioms Poincare.L4.GeodesicComparison.strict_span_necessary

 /-! ## GeodesicComparison/ZeroSpacing.lean -/

#print axioms Poincare.L4.GeodesicComparison.zero_spacing_lt_of_curvature_gt
#print axioms Poincare.L4.GeodesicComparison.zero_spacing_ge_of_curvature_le
#print axioms Poincare.L4.GeodesicComparison.sturmModel_zero_spacing
#print axioms Poincare.L4.GeodesicComparison.sturmModel_spacing_boundary

 /-! ## ManifoldIBP/AtlasHypothesisRedundancy.lean -/

#print axioms Poincare.L4.ManifoldIBP.smoothOverlapAtlas_transition_mem_source
#print axioms Poincare.L4.ManifoldIBP.halfSpaceAtlas_coherence_derived
#print axioms Poincare.L4.ManifoldIBP.globalWeightedIBP_of_cover_partial_ae_no_coherence

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

/-! ## Compactness/MeasureGrowthChain.lean (round 5) -/

#print axioms Poincare.L4.Compactness.UniformMeasureGrowth.coveringNumber_le
#print axioms Poincare.L4.Compactness.UniformMeasureGrowth.doublingConstant
#print axioms Poincare.L4.Compactness.UniformMeasureGrowth.coveringNumber_le_doublingConstant
#print axioms Poincare.L4.Compactness.totallyBounded_of_uniformMeasureGrowth
#print axioms Poincare.L4.Compactness.isCompact_of_uniformMeasureGrowth
#print axioms Poincare.L4.Compactness.exists_pointed_subseq_of_uniformMeasureGrowth
#print axioms Poincare.L4.Compactness.subsingletonGHSpaceRepPUnit
#print axioms Poincare.L4.Compactness.dirac_closedBall_of_subsingleton
#print axioms Poincare.L4.Compactness.punitGrowth
#print axioms Poincare.L4.Compactness.punitGrowth_measure_varies
#print axioms Poincare.L4.Compactness.totallyBounded_punit
#print axioms Poincare.L4.Compactness.isCompact_punit
#print axioms Poincare.L4.Compactness.exists_pointed_subseq_punit

/-! ## Consumed child-artifact headlines (round 5, independent re-audit) -/

#print axioms Poincare.L4.Compactness.totallyBounded_of_uniformDoubling
#print axioms Poincare.L4.Compactness.isCompact_of_uniformDoubling
#print axioms Poincare.L4.PointedGH.pointed_subseq_of_compact
#print axioms Poincare.L4.PointedGH.exists_dist_optimalGHInjl_optimalGHInjr_lt

/-! ## Compactness/MeasureGrowthChainWitness.lean (round 5, non-degenerate witness) -/

#print axioms Poincare.L4.Compactness.dZero
#print axioms Poincare.L4.Compactness.dOne
#print axioms Poincare.L4.Compactness.dZero_ne_dOne
#print axioms Poincare.L4.Compactness.twoPointZero_ne_one
#print axioms Poincare.L4.Compactness.dist_twoPointZero_twoPointOne
#print axioms Poincare.L4.Compactness.twoPoint_eq_zero_or_one
#print axioms Poincare.L4.Compactness.twoPointMeasure_apply
#print axioms Poincare.L4.Compactness.twoPointMeasure_closedBall
#print axioms Poincare.L4.Compactness.twoPointMeasureOf_apply_member
#print axioms Poincare.L4.Compactness.twoPointGrowth
#print axioms Poincare.L4.Compactness.twoPointGrowth_nondegenerate
#print axioms Poincare.L4.Compactness.twoPointGrowth_doublingConstant
#print axioms Poincare.L4.Compactness.totallyBounded_twoPoint
#print axioms Poincare.L4.Compactness.isCompact_twoPoint
#print axioms Poincare.L4.Compactness.exists_pointed_subseq_twoPoint

/-! ## Compactness/MeasureGrowthChainCircle.lean (round 5, geometric circle realization) -/

#print axioms Poincare.L4.Compactness.circleEquiv
#print axioms Poincare.L4.Compactness.circleZero
#print axioms Poincare.L4.Compactness.circleMeasure
#print axioms Poincare.L4.Compactness.circleMeasure_closedBall
#print axioms Poincare.L4.Compactness.circleMeasure_univ
#print axioms Poincare.L4.Compactness.circleMeasureOf
#print axioms Poincare.L4.Compactness.circleMeasureOf_apply_member
#print axioms Poincare.L4.Compactness.circle_norm_le_one
#print axioms Poincare.L4.Compactness.circle_dist_le_one
#print axioms Poincare.L4.Compactness.circle_m_pos
#print axioms Poincare.L4.Compactness.circle_toNNReal_eq_of_pos
#print axioms Poincare.L4.Compactness.circleGrowth
#print axioms Poincare.L4.Compactness.circleGrowth_measure_varies
#print axioms Poincare.L4.Compactness.totallyBounded_circle
#print axioms Poincare.L4.Compactness.isCompact_circle
#print axioms Poincare.L4.Compactness.exists_pointed_subseq_circle

/-! ## Round-5 completion: remaining top-level declarations of the new modules -/

#print axioms Poincare.L4.Compactness.instMeasurableSpaceGHSpaceRep
#print axioms Poincare.L4.Compactness.instBorelSpaceGHSpaceRep
#print axioms Poincare.L4.Compactness.UniformMeasureGrowth
#print axioms Poincare.L4.Compactness.twoPointEquiv
#print axioms Poincare.L4.Compactness.twoPointZero
#print axioms Poincare.L4.Compactness.twoPointOne
#print axioms Poincare.L4.Compactness.twoPointEquiv_twoPointZero
#print axioms Poincare.L4.Compactness.twoPointEquiv_twoPointOne
#print axioms Poincare.L4.Compactness.twoPointMeasure
#print axioms Poincare.L4.Compactness.twoPointMeasureOf
#print axioms Poincare.L4.Compactness.two_mul_half
#print axioms Poincare.L4.Compactness.half_le_two_mul_half
#print axioms Poincare.L4.Compactness.one_le_two_mul_half
#print axioms Poincare.L4.Compactness.one_le_two_mul_one
#print axioms Poincare.L4.Compactness.coe_half
#print axioms Poincare.L4.Compactness.half_le_two_mul_half_nn
#print axioms Poincare.L4.Compactness.one_le_two_mul_half_nn

/-! ## Compactness/MeasureGrowthChainCircleFamily.lean (round 5, circumference-parameterized) -/

#print axioms Poincare.L4.Compactness.circleEquivT
#print axioms Poincare.L4.Compactness.circleMeasureT
#print axioms Poincare.L4.Compactness.circleMeasureT_closedBall
#print axioms Poincare.L4.Compactness.circleMeasureT_univ
#print axioms Poincare.L4.Compactness.circleMeasureTOf
#print axioms Poincare.L4.Compactness.circleMeasureTOf_apply_member
#print axioms Poincare.L4.Compactness.circleT_norm_le
#print axioms Poincare.L4.Compactness.circleT_dist_le
#print axioms Poincare.L4.Compactness.circleGrowthT
#print axioms Poincare.L4.Compactness.circleGrowthT_constants
#print axioms Poincare.L4.Compactness.circleGrowthT_measure_varies
#print axioms Poincare.L4.Compactness.totallyBounded_circleT
#print axioms Poincare.L4.Compactness.isCompact_circleT
#print axioms Poincare.L4.Compactness.exists_pointed_subseq_circleT

/-! ## Round 6 (session slice 3): Compactness/RicciGrowthChain.lean -/

#print axioms Poincare.L4.Compactness.UniformRicciBallGrowth
#print axioms Poincare.L4.Compactness.UniformRicciBallGrowth.A_nonneg
#print axioms Poincare.L4.Compactness.UniformRicciBallGrowth.intervalIntegrable_A
#print axioms Poincare.L4.Compactness.UniformRicciBallGrowth.radialVolume_eq_zero_of_nonpos
#print axioms Poincare.L4.Compactness.UniformRicciBallGrowth.radialVolume_nonneg
#print axioms Poincare.L4.Compactness.UniformRicciBallGrowth.radialVolume_mono
#print axioms Poincare.L4.Compactness.UniformRicciBallGrowth.radialVolume_eq_of_ge
#print axioms Poincare.L4.Compactness.UniformRicciBallGrowth.radialVolume_pos
#print axioms Poincare.L4.Compactness.UniformRicciBallGrowth.radialVolume_halving
#print axioms Poincare.L4.Compactness.UniformRicciBallGrowth.doublingNNReal
#print axioms Poincare.L4.Compactness.UniformRicciBallGrowth.toUniformMeasureGrowth
#print axioms Poincare.L4.Compactness.totallyBounded_of_uniformRicciBallGrowth
#print axioms Poincare.L4.Compactness.isCompact_of_uniformRicciBallGrowth
#print axioms Poincare.L4.Compactness.exists_pointed_subseq_of_uniformRicciBallGrowth

/-! ## Round 6 (session slice 3): Compactness/FlatTorusGrowth.lean -/

#print axioms Poincare.L4.Compactness.FlatTorus
#print axioms Poincare.L4.Compactness.torusEquiv
#print axioms Poincare.L4.Compactness.torusZero
#print axioms Poincare.L4.Compactness.torusMeasure
#print axioms Poincare.L4.Compactness.torusMeasureOf
#print axioms Poincare.L4.Compactness.torusMeasureOf_apply_member
#print axioms Poincare.L4.Compactness.torusMeasure_closedBall
#print axioms Poincare.L4.Compactness.torusMeasure_univ
#print axioms Poincare.L4.Compactness.torusA
#print axioms Poincare.L4.Compactness.torusA_of_mem
#print axioms Poincare.L4.Compactness.torusA_of_notMem
#print axioms Poincare.L4.Compactness.torusA_of_nonpos
#print axioms Poincare.L4.Compactness.torusA_of_gt
#print axioms Poincare.L4.Compactness.torusA_half
#print axioms Poincare.L4.Compactness.torusA_eq_of_mem_Icc
#print axioms Poincare.L4.Compactness.torusA_pos
#print axioms Poincare.L4.Compactness.torusA_nonneg
#print axioms Poincare.L4.Compactness.torusA_abs_le_four
#print axioms Poincare.L4.Compactness.torusA_cont
#print axioms Poincare.L4.Compactness.torusA_hasDerivAt
#print axioms Poincare.L4.Compactness.torusA_zero
#print axioms Poincare.L4.Compactness.torusA_measurable
#print axioms Poincare.L4.Compactness.torusA_intervalIntegrable
#print axioms Poincare.L4.Compactness.torusRadialVolume_of_le_half
#print axioms Poincare.L4.Compactness.torusRadialVolume_of_ge_half
#print axioms Poincare.L4.Compactness.torusRadialVolume_of_nonpos
#print axioms Poincare.L4.Compactness.torusRadialVolume_eq
#print axioms Poincare.L4.Compactness.torusMeasure_closedBall_eq_ofReal
#print axioms Poincare.L4.Compactness.circle_norm_le_half
#print axioms Poincare.L4.Compactness.circle_dist_le_half
#print axioms Poincare.L4.Compactness.torus_dist_le_half
#print axioms Poincare.L4.Compactness.torusRicciBallGrowth
#print axioms Poincare.L4.Compactness.torusGrowth_measure_varies
#print axioms Poincare.L4.Compactness.torus_nondegenerate
#print axioms Poincare.L4.Compactness.totallyBounded_torus
#print axioms Poincare.L4.Compactness.isCompact_torus
#print axioms Poincare.L4.Compactness.exists_pointed_subseq_torus

/-! ## Round 6 (session slice 3): GeodesicComparison/FlatGeodesicExpModel.lean -/

#print axioms Poincare.L4.GeodesicComparison.geodesicLine
#print axioms Poincare.L4.GeodesicComparison.geodesicLine_zero
#print axioms Poincare.L4.GeodesicComparison.geodesicLine_flow
#print axioms Poincare.L4.GeodesicComparison.dist_geodesicLine
#print axioms Poincare.L4.GeodesicComparison.expMap
#print axioms Poincare.L4.GeodesicComparison.expMap_eq
#print axioms Poincare.L4.GeodesicComparison.expMap_injective
#print axioms Poincare.L4.GeodesicComparison.radialJacobi
#print axioms Poincare.L4.GeodesicComparison.radialJacobi_zero
#print axioms Poincare.L4.GeodesicComparison.radialJacobi_eq_zero_iff
#print axioms Poincare.L4.GeodesicComparison.radialJacobi_hasDerivAt
#print axioms Poincare.L4.GeodesicComparison.radialJacobi_hasDerivAt_deriv
#print axioms Poincare.L4.GeodesicComparison.radialJacobi_deriv
#print axioms Poincare.L4.GeodesicComparison.radialJacobi_second_deriv
#print axioms Poincare.L4.GeodesicComparison.scalarRadialJacobiSolutionOn
#print axioms Poincare.L4.GeodesicComparison.euclidModelA_one_eq
#print axioms Poincare.L4.GeodesicComparison.torusA_eq_eight_mul_radialJacobi
