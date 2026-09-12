/-
Task-local axiom audit for D12-parabolic-local-existence.

Fail-closed audit module: `#print axioms` for every declaration authored in this
task directory. The acceptance gate requires the axiom cone of every declaration
to be contained in {propext, Classical.choice, Quot.sound}.
-/
import Poincare.D12.ParabolicLocal.Obligations

open Poincare.D12.ParabolicLocal

-- GaussianConv.lean
#print axioms BCFn
#print axioms heatConvPoint
#print axioms gaussianKernel_integrable
#print axioms gaussianKernel_sub_integrable
#print axioms heatConvIntegrand_integrable
#print axioms heatConvPoint_le_norm
#print axioms continuous_heatConvPoint
#print axioms heatConvPos
#print axioms heatConvPos_apply
#print axioms heatConv
#print axioms heatConv_of_pos
#print axioms heatConv_of_nonpos
#print axioms heatConv_apply
#print axioms heatConv_norm_le
#print axioms heatConv_norm_le'
#print axioms heatConv_nonneg
#print axioms heatConv_const
#print axioms heatOperator
#print axioms heatOperator_apply
#print axioms heatOperatorCLM
#print axioms heatOperatorCLM_norm_le
-- ParametricIntegral.lean
#print axioms continuous_parametric_intervalIntegral
#print axioms continuous_parametric_intervalIntegral_of_base
-- Duhamel.lean
#print axioms DuhamelSetup
#print axioms DuhamelSetup.clamp
#print axioms DuhamelSetup.clamp_continuous
#print axioms DuhamelSetup.clamp_mem
#print axioms DuhamelSetup.clamp_eq_self
#print axioms DuhamelSetup.clampSubtype
#print axioms DuhamelSetup.SolutionSpace
#print axioms DuhamelSetup.extendToInterval
#print axioms DuhamelSetup.extendToInterval_apply
#print axioms DuhamelSetup.extendToInterval_eq_of_mem
#print axioms DuhamelSetup.extendToInterval_norm_le
#print axioms DuhamelSetup.duhamelIntegrand_continuous
#print axioms DuhamelSetup.duhamelMap
#print axioms DuhamelSetup.duhamelMap_apply
#print axioms DuhamelSetup.duhamelMap_pointwise_lipschitz
#print axioms DuhamelSetup.duhamelMap_lipschitzWith
-- MildExistence.lean
#print axioms DuhamelSetup.contractionConstant
#print axioms DuhamelSetup.contractionConstant_eq
#print axioms DuhamelSetup.solutionSpace_nonempty
#print axioms DuhamelSetup.existsUnique_mildSolution
#print axioms DuhamelSetup.mildSolution
#print axioms DuhamelSetup.mildSolution_isFixedPt
#print axioms DuhamelSetup.mildSolution_unique
#print axioms DuhamelSetup.mildSolution_duhamel_eq
#print axioms DuhamelSetup.mildSolution_initial
#print axioms DuhamelSetup.mildSolution_continuous

-- BUC.lean
#print axioms BUCf.ext
#print axioms BUCf.dist_eq_dist_val
#print axioms BUCf.dist_coe_le_dist
#print axioms BUCf.uniformContinuous_of_tendsto_uniform

-- GaussianSemigroup.lean
#print axioms heatConv_apply_translated
#print axioms heatConv_semigroup
#print axioms heatConv_uniformContinuous
#print axioms heatConv_tendsto_self_BUC
#print axioms bucHeatOperator
#print axioms gaussianS
#print axioms gaussianS_of_zero
#print axioms gaussianS_of_pos
#print axioms gaussianS_val_of_pos
#print axioms gaussianS_val_of_ne_zero
#print axioms gaussianS_abs
#print axioms gaussianS_semigroup
#print axioms gaussianS_semigroup'
#print axioms gaussianS_add
#print axioms gaussianS_norm_le
#print axioms gaussianS_tendsto_self
#print axioms jointContinuous_of_absSemigroup
#print axioms gaussianSmap_continuous

-- GaussianSetup.lean
#print axioms gaussianSetup
#print axioms existsUnique_heatMildSolution
#print axioms heatMildSolution
#print axioms heatMildSolution_duhamel_eq
#print axioms heatMildSolution_initial
#print axioms valCLM
#print axioms heatMildSolution_duhamel_eq_kernel

-- Examples.lean
#print axioms bucConst
#print axioms linearSmulF
#print axioms linearSmulF_lipschitz
#print axioms linearCandidate
#print axioms linearCandidate_continuous
#print axioms linearCandidate_norm_le
#print axioms linearCandidateSolution
#print axioms intervalIntegral_exp_mul_eq
#print axioms linearCandidate_isFixedPt
#print axioms heatMildSolution_linear_eq
#print axioms linearHeat_example
#print axioms linearHeat_example_nontrivial
#print axioms lipschitzWith_arctan
#print axioms abs_arctan_le_pi_div_two
#print axioms arctanBCF
#print axioms arctanF
#print axioms arctanF_lipschitz
#print axioms arctanF_not_additive
#print axioms existsUnique_arctanHeatMildSolution
#print axioms arctanHeat_example

-- Obligations.lean
#print axioms deturckFlowSymbol_eq_negativeLaplacian
#print axioms deturckSymbol_quadratic
#print axioms not_lipschitz_of_homogeneous_two
#print axioms squareF
#print axioms squareF_not_lipschitz
#print axioms mildToClassicalBridge
#print axioms derivativeLossBarrier
#print axioms quasilinearRicciDeTurckBarrier
#print axioms quasilinearRicciDeTurckBarrier_discharged

-- Obligations.lean (discharge of the derivative-loss barrier)
#print axioms derivativeLossBarrier_discharged

-- DerivativeLoss.lean
#print axioms gaussianKernel_hasFDerivAt
#print axioms gaussianKernel_sub_hasFDerivAt
#print axioms kernelIntegrand
#print axioms kernelIntegrandFderiv
#print axioms kernelIntegrand_hasFDerivAt
#print axioms domBound
#print axioms sq_mul_exp_neg_mul_sq_le
#print axioms normSq_mul_exp_neg_mul_normSq_le
#print axioms integrable_exp_neg_mul_normSq
#print axioms domBound_integrable
#print axioms gaussianKernel_sub_le_quarter
#print axioms kernelIntegrandFderiv_norm_le_domBound
#print axioms kernelIntegrandFderiv_zero_aestronglyMeasurable
#print axioms kernelIntegrandFderiv_zero_integrable
#print axioms heatConvPoint_hasFDerivAt_zero
#print axioms heatConv_hasFDerivAt_zero
#print axioms heatConv_fderiv_zero_apply
#print axioms integral_exp_neg_mul_normSq_sq_coord
#print axioms kernelMoment_const
#print axioms abs_mul_exp_neg_mul_sq_le
#print axioms coordCLM
#print axioms testF
#print axioms testF_norm_le
#print axioms testF_contDiff
#print axioms fderiv_heatConv_testF_coord
#print axioms derivativeLossBarrier_holds

