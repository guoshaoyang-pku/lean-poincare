/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-entropy-variation)

# Task-local axiom audit for the D12-entropy-variation modules

One explicit `#print axioms` line per top-level declaration of the five modules
(`WeightedIntegral`, `EntropyDerivative`, `GaussianShrinker`, `FFlowModel`,
`SignDistinction`).  The programmatic fail-closed audit lives in
`tools/d12_axiom_audit.sh`: it regenerates exactly this list, compiles it, and
fails unless every declaration is reported with an axiom cone contained in
`{propext, Classical.choice, Quot.sound}` (task allowlist), including a
negative control that verifies the checker really detects a fake axiom.
-/
import Poincare.D12.EntropyVariation.All

#print axioms Poincare.D12.EntropyVariation.hasDerivAt_weightedIntegral
#print axioms Poincare.D12.EntropyVariation.hasDerivAt_weightedIntegral_constWeight
#print axioms Poincare.D12.EntropyVariation.hasDerivAt_integral_param
#print axioms Poincare.D12.EntropyVariation.FDissipationCorrected
#print axioms Poincare.D12.EntropyVariation.FDissipation_eq_corrected_of_idempotent
#print axioms Poincare.D12.EntropyVariation.FDissipationCorrected_nonneg
#print axioms Poincare.D12.EntropyVariation.hasDerivAt_F_of_pointwise
#print axioms Poincare.D12.EntropyVariation.fDerivativeCorrected_at_of_pointwise
#print axioms Poincare.D12.EntropyVariation.fDerivativeCorrected_of_pointwise
#print axioms Poincare.D12.EntropyVariation.fDerivativeStatement_of_corrected_of_idempotent
#print axioms Poincare.D12.EntropyVariation.eventually_of_forall
#print axioms Poincare.D12.EntropyVariation.Euc
#print axioms Poincare.D12.EntropyVariation.hasDerivAt_neg_mul_const
#print axioms Poincare.D12.EntropyVariation.integrable_exp_neg_mul_normSq
#print axioms Poincare.D12.EntropyVariation.integrable_gaussianKernel
#print axioms Poincare.D12.EntropyVariation.normSq_exp_neg_mul_le
#print axioms Poincare.D12.EntropyVariation.integral_normSq_mul_exp_neg_mul
#print axioms Poincare.D12.EntropyVariation.integrable_normSq_mul_exp_neg_mul
#print axioms Poincare.D12.EntropyVariation.integral_normSq_mul_gaussianKernel
#print axioms Poincare.D12.EntropyVariation.integrable_normSq_mul_gaussianKernel
#print axioms Poincare.D12.EntropyVariation.shrinkerGradSq
#print axioms Poincare.D12.EntropyVariation.shrinkerFpot
#print axioms Poincare.D12.EntropyVariation.shrinkerRiccHess
#print axioms Poincare.D12.EntropyVariation.shrinkerEntropyData
#print axioms Poincare.D12.EntropyVariation.shrinkerEntropyData_mass
#print axioms Poincare.D12.EntropyVariation.shrinkerEntropyData_secondMoment
#print axioms Poincare.D12.EntropyVariation.shrinkerEntropyData_F_value
#print axioms Poincare.D12.EntropyVariation.shrinkerEntropyData_W_value
#print axioms Poincare.D12.EntropyVariation.shrinkerEntropyData_FDissipation_value
#print axioms Poincare.D12.EntropyVariation.shrinkerEntropyData_FDissipationCorrected_value
#print axioms Poincare.D12.EntropyVariation.shrinkerEntropyData_FDissipation_ne_corrected_one
#print axioms Poincare.D12.EntropyVariation.hasFDerivAt_shrinkerFpot
#print axioms Poincare.D12.EntropyVariation.iteratedFDeriv_two_shrinkerFpot
#print axioms Poincare.D12.EntropyVariation.shrinker_hessian_eq_metricOverTwoTau
#print axioms Poincare.D12.EntropyVariation.shrinker_w_dissipation_density_zero
#print axioms Poincare.D12.EntropyVariation.shrinker_riccHess_justified
#print axioms Poincare.D12.EntropyVariation.fflowMetricScale
#print axioms Poincare.D12.EntropyVariation.fflowScaleInv
#print axioms Poincare.D12.EntropyVariation.hasDerivAt_fflowMetricScale
#print axioms Poincare.D12.EntropyVariation.fflowMetricFlow_consistency
#print axioms Poincare.D12.EntropyVariation.fflowScaleInv_eq_inv_metricScale
#print axioms Poincare.D12.EntropyVariation.fflowScaleInv_pos
#print axioms Poincare.D12.EntropyVariation.hasDerivAt_fflowScaleInv
#print axioms Poincare.D12.EntropyVariation.fflowGradSq
#print axioms Poincare.D12.EntropyVariation.fflowGradSqVariation
#print axioms Poincare.D12.EntropyVariation.fflowRiccHess
#print axioms Poincare.D12.EntropyVariation.fflowEntropyData
#print axioms Poincare.D12.EntropyVariation.fflow_rho_timeIndep
#print axioms Poincare.D12.EntropyVariation.fflow_rho_deriv_zero
#print axioms Poincare.D12.EntropyVariation.hasDerivAt_fflowGradSq
#print axioms Poincare.D12.EntropyVariation.fflow_riccHess_eq_scaleInvSq_mul_shrinkerRiccHess
#print axioms Poincare.D12.EntropyVariation.fflow_riccHess_justified
#print axioms Poincare.D12.EntropyVariation.fflow_two_riccHess_pos
#print axioms Poincare.D12.EntropyVariation.fflow_variation_ne_two_riccHess_at_zero
#print axioms Poincare.D12.EntropyVariation.fflow_variation_eq_two_riccHess_of_normSq_eq
#print axioms Poincare.D12.EntropyVariation.fflow_variation_integral
#print axioms Poincare.D12.EntropyVariation.fflow_FDissipationCorrected_value
#print axioms Poincare.D12.EntropyVariation.fflow_integrated_variation_eq_dissipation
#print axioms Poincare.D12.EntropyVariation.fflow_FDissipation_value
#print axioms Poincare.D12.EntropyVariation.fflow_F_value
#print axioms Poincare.D12.EntropyVariation.fflow_F_hasDerivAt
#print axioms Poincare.D12.EntropyVariation.fflow_F_hasDerivAt_closedForm
#print axioms Poincare.D12.EntropyVariation.fflow_corrected_FDerivative_on_domain
#print axioms Poincare.D12.EntropyVariation.fflow_F_deriv_pos
#print axioms Poincare.D12.EntropyVariation.fflow_F_strictMonoOn
#print axioms Poincare.D12.EntropyVariation.fflow_F_increasing_on_Iio
#print axioms Poincare.D12.EntropyVariation.fflow_FDissipation_ne_corrected_one
#print axioms Poincare.D12.EntropyVariation.fflow_literal_FDerivative_inconsistent
#print axioms Poincare.D12.EntropyVariation.fflow_literal_FDerivativeStatement_of_idempotent
#print axioms Poincare.D12.EntropyVariation.fflow_variation_eq_two_riccHess_iff
#print axioms Poincare.D12.EntropyVariation.fflow_riccHess_eq_zero_of_zero_dim
#print axioms Poincare.D12.EntropyVariation.fflow_idempotency_holds_zero_dim
#print axioms Poincare.D12.EntropyVariation.fflow_idempotency_forces_zero_dim
#print axioms Poincare.D12.EntropyVariation.fflow_idempotency_iff_zero_dim
#print axioms Poincare.D12.EntropyVariation.fflow_literal_FDerivativeStatement_zero_dim
#print axioms Poincare.D12.EntropyVariation.perelmanFFlow_increasing_toy_nonincreasing
#print axioms Poincare.D12.EntropyVariation.derivative_sign_distinction
#print axioms Poincare.D12.EntropyVariation.toy_heatEnergy_nonincreasing
#print axioms Poincare.D12.EntropyVariation.shrinkerWOfTau
#print axioms Poincare.D12.EntropyVariation.shrinkerWOfTau_eq_zero
#print axioms Poincare.D12.EntropyVariation.shrinkerWOfTau_hasDerivAt
#print axioms Poincare.D12.EntropyVariation.shrinkerWDissipationDensity
#print axioms Poincare.D12.EntropyVariation.shrinkerWDissipationDensity_zero
#print axioms Poincare.D12.EntropyVariation.integrable_shrinkerWDissipationDensity_mul
#print axioms Poincare.D12.EntropyVariation.shrinkerWDissipation
#print axioms Poincare.D12.EntropyVariation.shrinkerWDissipation_zero
#print axioms Poincare.D12.EntropyVariation.shrinker_W_derivative_identity
