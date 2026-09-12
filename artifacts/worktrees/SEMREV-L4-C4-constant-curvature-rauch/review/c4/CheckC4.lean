/-
Independent review probe (SEMREV-L4-C4).  Prints the exact type of every declaration
claimed in the parent result card, plus the definitions and engine signatures they rest on.
This file is part of the review worktree only and is not part of the parent artifact.
-/
import Poincare.L4.GeodesicComparison.ConstCurvNormalization

open Poincare.L4.GeodesicComparison
open Poincare.D12.ComparisonGeodesics
open Poincare.D10

-- authored declarations (26)
#check @sin_sub_mul_cos_nonneg
#check @sin_sub_mul_cos_le_cube
#check @sphere_logDeriv_bound
#check @jacobiSolSphere_abs_le
#check @jacobiSolSphere_logDeriv_bound
#check @jacobiSol_logDeriv_bound
#check @jacobiSol_logDeriv_normalized
#check @jacobiSol_pos_of_nonneg
#check @jacobiSol_pos_of_nonneg_Ioc
#check @jacobiSol_riccati_identity
#check @abs_sub_le_of_deriv_bound
#check @jacobi_linear_bounds
#check @jacobi_pos_and_ratio_bound
#check @euclideanNormalizedOn_of_jacobi
#check @jacobi_riccati_identity
#check @logDeriv_continuousOn
#check @logDeriv_continuousOn_jacobi
#check @rauch_upper_of_constCurv
#check @rauch_upper_of_constCurv_jacobi
#check @rauch_upper_flat_of_jacobi
#check @sphere_jacobiSolutionOn_four_oneHalf
#check @spherical_rauch_witness
#check @spherical_rauch_witness_cot
#check @jacobiSolOne_normalization_witness
#check @jacobiSolOne_normalized
#check @flat_model_normalized

-- definitions and imported engine signatures
#check @EuclideanNormalizedOn
#check @JacobiSolutionOn
#check @RiccatiLeOn
#check @RiccatiEqOn
#check @riccati_le_of_singular_normalization
#check @riccati_le_of_initial
#check @riccati_delta_le_exp
#check @Poincare.D10.jacobiSol
#check @Poincare.D10.jacobiDeriv
#check @Poincare.D10.jacobiSolSphere
#check @Poincare.D10.jacobiSol_ode
#check @Poincare.D10.hasDerivAt_jacobiSol
#check @Poincare.D10.hasDerivAt_jacobiDeriv
#check @Poincare.D10.jacobiSolSphere_pos
#check @Poincare.D10.continuous_jacobiSol
#check @Poincare.D10.jacobiSol_zero
#check @Poincare.D10.jacobiDeriv_zero
#check @Poincare.D10.jacobiSol_of_pos
#check @Poincare.D10.jacobiSol_of_zero
#check @Poincare.D10.jacobiDeriv_of_pos
#check @Poincare.D10.jacobiSolSphere
#check @Poincare.D10.jacobiSolSphere_nonneg
#check @Poincare.D10.jacobiSolSphere_firstZero
