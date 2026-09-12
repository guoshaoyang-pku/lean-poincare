/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — per-declaration kernel axiom report for the Sturm interlacing deliverable

This driver prints the axiom cone of every declaration added by
`Poincare/L4/GeodesicComparison/SturmInterlacing.lean` and
`Poincare/L4/GeodesicComparison/SturmInterlacingConjugateCrossCheck.lean`, together with the
consumed D12 engine declarations and the cross-checked
`Poincare.L4.GeodesicComparison.conjugate_point_bound`.

`tools/run_sturm_gates.py` parses this output fail-closed: every audited declaration must
appear, and its cone must be a subset of `{propext, Classical.choice, Quot.sound}`.
-/
import Poincare.L4.GeodesicComparison.SturmInterlacingConjugateCrossCheck

/-! ## Constructed data -/

#print axioms Poincare.L4.GeodesicComparison.modelJacobiSolutionOn
#print axioms Poincare.L4.GeodesicComparison.sinJacobiSolutionOn
#print axioms Poincare.L4.GeodesicComparison.linearJacobiSolutionOn
#print axioms Poincare.L4.GeodesicComparison.modelJacobiSol_pos
#print axioms Poincare.L4.GeodesicComparison.modelJacobiSol_firstZero
#print axioms Poincare.L4.GeodesicComparison.modelJacobiDeriv_firstZero
#print axioms Poincare.L4.GeodesicComparison.jacobiSolShift
#print axioms Poincare.L4.GeodesicComparison.jacobiDerivShift
#print axioms Poincare.L4.GeodesicComparison.hasDerivAt_jacobiSolShift
#print axioms Poincare.L4.GeodesicComparison.hasDerivAt_jacobiDerivShift
#print axioms Poincare.L4.GeodesicComparison.jacobiSolShift_jacobiSolutionOn
#print axioms Poincare.L4.GeodesicComparison.jacobiSolShift_pos

/-! ## Interlacing -/

#print axioms Poincare.L4.GeodesicComparison.exists_zero_of_curvature_lt
#print axioms Poincare.L4.GeodesicComparison.sturm_dichotomy_of_interior_bound
#print axioms Poincare.L4.GeodesicComparison.sin_zero_interlaces_half_model
#print axioms Poincare.L4.GeodesicComparison.sin_first_zero_lt_half_model_first_zero
#print axioms Poincare.L4.GeodesicComparison.sin_interlaces_half_model_all
#print axioms Poincare.L4.GeodesicComparison.sin_zero_in_half_model_interval

/-! ## Zero counting and the first-zero bound -/

#print axioms Poincare.L4.GeodesicComparison.eq_zero_at_pi_sqrt_of_curvature_eq
#print axioms Poincare.L4.GeodesicComparison.exists_jacobi_zero_on_Ioc_pi_sqrt
#print axioms Poincare.L4.GeodesicComparison.exists_jacobi_zero_on_Ioc_pi_sqrt_of_interior_bound
#print axioms Poincare.L4.GeodesicComparison.exists_jacobi_zero_on_Ioc_pi_sqrt_normalized
#print axioms Poincare.L4.GeodesicComparison.exists_jacobi_zero_of_horizon
#print axioms Poincare.L4.GeodesicComparison.firstPositiveZero
#print axioms Poincare.L4.GeodesicComparison.firstPositiveZero_le_pi_sqrt
#print axioms Poincare.L4.GeodesicComparison.firstPositiveZero_le_pi_sqrt_of_interior_bound
#print axioms Poincare.L4.GeodesicComparison.firstPositiveZero_le_pi_sqrt_of_horizon
#print axioms Poincare.L4.GeodesicComparison.pos_near_zero_of_normalized_initial
#print axioms Poincare.L4.GeodesicComparison.firstPositiveZero_mem_of_normalized
#print axioms Poincare.L4.GeodesicComparison.firstPositiveZero_jacobiSol_two

/-! ## First-positive-zero ordering (the interlacing in first-zero form) -/

#print axioms Poincare.L4.GeodesicComparison.firstPositiveZero_modelJacobiSol
#print axioms Poincare.L4.GeodesicComparison.firstPositiveZero_sin
#print axioms Poincare.L4.GeodesicComparison.firstPositiveZero_lt_of_curvature_lt
#print axioms Poincare.L4.GeodesicComparison.firstPositiveZero_sin_lt_half_model

/-! ## Wronskian consumption with explicit data -/

#print axioms Poincare.L4.GeodesicComparison.wronskian_sin_linear_antitoneOn
#print axioms Poincare.L4.GeodesicComparison.mul_cos_le_sin
#print axioms Poincare.L4.GeodesicComparison.wronskian_deriv_sin_linear
#print axioms Poincare.L4.GeodesicComparison.wronskian_deriv_sin_linear_at_pi_div_two

/-! ## Refutation of the naive instantiation -/

#print axioms Poincare.L4.GeodesicComparison.linear_model_no_second_zero
#print axioms Poincare.L4.GeodesicComparison.linear_model_no_interior_zero
#print axioms Poincare.L4.GeodesicComparison.sin_first_positive_zero_is_pi
#print axioms Poincare.L4.GeodesicComparison.sin_zero_linear_zeroFree_interlacing

/-! ## Sharpened positivity bound and the cross-check -/

#print axioms Poincare.L4.GeodesicComparison.no_positive_solution_past_pi_sqrt
#print axioms Poincare.L4.GeodesicComparison.conjugate_point_bound_via_engine
#print axioms Poincare.L4.GeodesicComparison.conjugate_point_bound_cross_check
#print axioms Poincare.L4.GeodesicComparison.sharpened_witness
#print axioms Poincare.L4.GeodesicComparison.witness_agreement

/-! ## Consumed engine and cross-checked inputs (provenance) -/

#print axioms Poincare.D12.ComparisonGeodesics.sturm_zero_comparison
#print axioms Poincare.D12.ComparisonGeodesics.sturm_zero_comparison_of_pos
#print axioms Poincare.D12.ComparisonGeodesics.wronskian_deriv
#print axioms Poincare.D12.ComparisonGeodesics.wronskian_antitoneOn_of_le
#print axioms Poincare.D12.ComparisonGeodesics.wronskian_differentiableOn
#print axioms Poincare.D12.ComparisonGeodesics.wronskian_continuousOn
#print axioms Poincare.L4.GeodesicComparison.conjugate_point_bound
#print axioms Poincare.L4.GeodesicComparison.sin_no_zero_in_Ioo_zero_pi
#print axioms Poincare.L4.GeodesicComparison.exists_jacobi_zero_before_pi_sqrt
#print axioms Poincare.D10.jacobiSol
#print axioms Poincare.D10.hasDerivAt_jacobiSol
#print axioms Poincare.D10.hasDerivAt_jacobiDeriv
#print axioms Poincare.D10.continuous_jacobiSol
#print axioms Poincare.D10.jacobiSolSphere_firstZero
#print axioms Poincare.D10.jacobiSolSphere_pos
