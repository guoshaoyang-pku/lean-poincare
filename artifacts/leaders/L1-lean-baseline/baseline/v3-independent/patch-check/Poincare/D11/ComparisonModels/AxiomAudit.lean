/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D11 — kernel axiom audit for the comparison-model declarations

Every definition and headline theorem of `Poincare.D11.ComparisonModels` is audited with
`#print axioms`.  The allowed cone is `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no `axiom`, no `unsafe`, no `native_decide`, no `proof_wanted` is used anywhere in the four
authored modules.

Run with `lake env lean` and inspect the output: every query must print exactly
`[propext, Classical.choice, Quot.sound]`.
-/
import Poincare.D11.ComparisonModels.LaplacianComparison
import Poincare.D11.ComparisonModels.ModelMetrics

-- Basic.lean
#print axioms Poincare.D11.firstZero_le_firstZero
#print axioms Poincare.D11.jacobiSol_pos
#print axioms Poincare.D11.jacobiSol_pos_of_nonpos
#print axioms Poincare.D11.jacobiSol_pos_of_le
#print axioms Poincare.D11.jacobiSol_nonneg_of_le
#print axioms Poincare.D11.continuous_jacobiDeriv
#print axioms Poincare.D11.differentiable_jacobiDeriv
#print axioms Poincare.D11.continuous_jacobiSol_pow
#print axioms Poincare.D11.differentiable_jacobiSol_pow

-- ModelMetrics.lean
#print axioms Poincare.D11.polarMetric
#print axioms Poincare.D11.polarMetric_symm
#print axioms Poincare.D11.polarMetric_add_left
#print axioms Poincare.D11.polarMetric_add_right
#print axioms Poincare.D11.polarMetric_smul_left
#print axioms Poincare.D11.polarMetric_smul_right
#print axioms Poincare.D11.polarMetric_nonneg
#print axioms Poincare.D11.polarMetric_pos_of_pos
#print axioms Poincare.D11.WarpedProductModel
#print axioms Poincare.D11.WarpedProductModel.jacobi_ode
#print axioms Poincare.D11.WarpedProductModel.normalized_initial
#print axioms Poincare.D11.warpedProductModel_jacobiSolSphere
#print axioms Poincare.D11.warpedProductModel_jacobiSolFlat
#print axioms Poincare.D11.warpedProductModel_jacobiSolHyperbolic
#print axioms Poincare.D11.warpedProductModel_jacobiSol
#print axioms Poincare.D11.modelSphereMetric
#print axioms Poincare.D11.modelFlatMetric
#print axioms Poincare.D11.modelHyperbolicMetric
#print axioms Poincare.D11.modelSphereMetric_symm
#print axioms Poincare.D11.modelFlatMetric_symm
#print axioms Poincare.D11.modelHyperbolicMetric_symm
#print axioms Poincare.D11.modelSphereMetric_posDef
#print axioms Poincare.D11.modelFlatMetric_posDef
#print axioms Poincare.D11.modelHyperbolicMetric_posDef
#print axioms Poincare.D11.polarMetric_jacobiSol_posDef

-- BishopGromov.lean
#print axioms Poincare.D11.ballVolume
#print axioms Poincare.D11.wronskian
#print axioms Poincare.D11.continuous_wronskian
#print axioms Poincare.D11.differentiable_wronskian
#print axioms Poincare.D11.wronskian_deriv
#print axioms Poincare.D11.wronskian_le_zero
#print axioms Poincare.D11.jacobiSol_div_antitoneOn
#print axioms Poincare.D11.jacobiSol_mul_le_mul_of_le
#print axioms Poincare.D11.ballVolume_ge_jacobiSol_pow
#print axioms Poincare.D11.ballVolume_pos
#print axioms Poincare.D11.continuousOn_ballVolume
#print axioms Poincare.D11.differentiableOn_ballVolume
#print axioms Poincare.D11.ballVolume_ratio_deriv_nonpos
#print axioms Poincare.D11.ballVolume_ratio_antitoneOn
#print axioms Poincare.D11.bishopGromov_volume_comparison
#print axioms Poincare.D11.bishopGromov_volume_comparison_of_nonpos
#print axioms Poincare.D11.bishopGromov_volume_comparison_sphere

-- LaplacianComparison.lean
#print axioms Poincare.D11.radialLaplacian
#print axioms Poincare.D11.divergenceLaplacian
#print axioms Poincare.D11.divergenceLaplacian_eq_radialLaplacian
#print axioms Poincare.D11.radialLaplacian_id
#print axioms Poincare.D11.radialLaplacian_id_jacobiSol
#print axioms Poincare.D11.divergenceLaplacian_id_jacobiSol
#print axioms Poincare.D11.laplacianComparison_model
#print axioms Poincare.D11.radialLaplacian_id_le_of_le
#print axioms Poincare.D11.laplacianComparison_jacobiDeriv
