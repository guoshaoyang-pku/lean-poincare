/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4-C4 — per-declaration kernel axiom audit

`#print axioms` for every declaration authored in
`Poincare.L4.GeodesicComparison.ConstCurvNormalization`, plus the D12 singular Riccati engine
it consumes and the D10 constant-curvature model facts it is built on.  The expected axiom
cone for every declaration is a subset of `{propext, Classical.choice, Quot.sound}` and in
particular must not contain `sorryAx`; this is checked fail-closed by `tools/c4_verify.py`.
-/
import Poincare.L4.GeodesicComparison.ConstCurvNormalization

-- ## Authored declarations (L4-C4)
#print axioms Poincare.L4.GeodesicComparison.sin_sub_mul_cos_nonneg
#print axioms Poincare.L4.GeodesicComparison.sin_sub_mul_cos_le_cube
#print axioms Poincare.L4.GeodesicComparison.sphere_logDeriv_bound
#print axioms Poincare.L4.GeodesicComparison.jacobiSolSphere_abs_le
#print axioms Poincare.L4.GeodesicComparison.jacobiSolSphere_logDeriv_bound
#print axioms Poincare.L4.GeodesicComparison.jacobiSol_logDeriv_bound
#print axioms Poincare.L4.GeodesicComparison.jacobiSol_logDeriv_normalized
#print axioms Poincare.L4.GeodesicComparison.jacobiSol_pos_of_nonneg
#print axioms Poincare.L4.GeodesicComparison.jacobiSol_pos_of_nonneg_Ioc
#print axioms Poincare.L4.GeodesicComparison.jacobiSol_riccati_identity
#print axioms Poincare.L4.GeodesicComparison.abs_sub_le_of_deriv_bound
#print axioms Poincare.L4.GeodesicComparison.jacobi_linear_bounds
#print axioms Poincare.L4.GeodesicComparison.jacobi_pos_and_ratio_bound
#print axioms Poincare.L4.GeodesicComparison.euclideanNormalizedOn_of_jacobi
#print axioms Poincare.L4.GeodesicComparison.jacobi_riccati_identity
#print axioms Poincare.L4.GeodesicComparison.logDeriv_continuousOn
#print axioms Poincare.L4.GeodesicComparison.logDeriv_continuousOn_jacobi
#print axioms Poincare.L4.GeodesicComparison.rauch_upper_of_constCurv
#print axioms Poincare.L4.GeodesicComparison.rauch_upper_of_constCurv_jacobi
#print axioms Poincare.L4.GeodesicComparison.rauch_upper_flat_of_jacobi
#print axioms Poincare.L4.GeodesicComparison.sphere_jacobiSolutionOn_four_oneHalf
#print axioms Poincare.L4.GeodesicComparison.spherical_rauch_witness
#print axioms Poincare.L4.GeodesicComparison.spherical_rauch_witness_cot
#print axioms Poincare.L4.GeodesicComparison.jacobiSolOne_normalization_witness
#print axioms Poincare.L4.GeodesicComparison.jacobiSolOne_normalized
#print axioms Poincare.L4.GeodesicComparison.flat_model_normalized

-- ## Consumed engine (D12, imported canonical artifact)
#print axioms Poincare.D12.ComparisonGeodesics.riccati_le_of_singular_normalization
#print axioms Poincare.D12.ComparisonGeodesics.riccati_le_of_initial
#print axioms Poincare.D12.ComparisonGeodesics.riccati_delta_le_exp

-- ## Consumed model facts (D10, imported canonical artifact)
#print axioms Poincare.D10.jacobiSol_ode
#print axioms Poincare.D10.hasDerivAt_jacobiSol
#print axioms Poincare.D10.hasDerivAt_jacobiDeriv
#print axioms Poincare.D10.jacobiSolSphere_pos
#print axioms Poincare.D10.continuous_jacobiSol
