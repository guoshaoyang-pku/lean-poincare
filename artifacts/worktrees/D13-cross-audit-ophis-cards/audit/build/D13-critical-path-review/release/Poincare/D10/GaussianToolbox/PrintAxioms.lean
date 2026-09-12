/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D10-gaussian-toolbox builder
-/
module

public import Poincare.D10.GaussianToolbox.Basic
public import Poincare.D10.GaussianToolbox.Convolution
public import Poincare.D10.GaussianToolbox.Multivariate

/-!
# Poincare.GaussianToolbox.PrintAxioms

Per-declaration logical-dependency report for the D10 Gaussian integral toolbox.

Each `#print axioms` line below is a kernel command: it lists the logical postulates on which
the declaration depends.  Every declaration of this development is expected to depend only on
`propext`, `Classical.choice` and `Quot.sound`, and never on a project-specific postulate, a
`sorry`, `unsafe` or `native_decide`.
-/

@[expose] public section

/-! ## Definitions -/

#print axioms Poincare.GaussianToolbox.gaussianKernel
#print axioms Poincare.GaussianToolbox.gaussianDensity
#print axioms Poincare.GaussianToolbox.gaussianVariance
#print axioms Poincare.GaussianToolbox.gaussianVec
#print axioms Poincare.GaussianToolbox.gaussianVecNormalized
#print axioms Poincare.GaussianToolbox.standardGaussianVec
#print axioms Poincare.GaussianToolbox.standardGaussianDensity

/-! ## Scaling law and 1D moments -/

#print axioms Poincare.GaussianToolbox.integral_gaussianKernel
#print axioms Poincare.GaussianToolbox.integral_gaussianKernel_of_pos
#print axioms Poincare.GaussianToolbox.integrable_pow_mul_gaussianKernel
#print axioms Poincare.GaussianToolbox.tendsto_pow_mul_gaussianKernel_atTop
#print axioms Poincare.GaussianToolbox.tendsto_pow_mul_gaussianKernel_atBot
#print axioms Poincare.GaussianToolbox.hasDerivAt_pow_mul_gaussianKernel
#print axioms Poincare.GaussianToolbox.integral_moment_succ
#print axioms Poincare.GaussianToolbox.integral_moment_zero
#print axioms Poincare.GaussianToolbox.integral_moment_two
#print axioms Poincare.GaussianToolbox.integral_moment_four
#print axioms Poincare.GaussianToolbox.integral_moment_six
#print axioms Poincare.GaussianToolbox.integral_gaussianDensity
#print axioms Poincare.GaussianToolbox.integral_gaussianDensity_mul_sq

/-! ## Convolution of two Gaussians -/

#print axioms Poincare.GaussianToolbox.gaussianKernel_exponent_identity
#print axioms Poincare.GaussianToolbox.gaussianKernel_convolution
#print axioms Poincare.GaussianToolbox.sqrt_convolution_param
#print axioms Poincare.GaussianToolbox.gaussianDensity_convolution
#print axioms Poincare.GaussianToolbox.gaussianVariance_convolutionParam

/-! ## The `n`-dimensional Gaussian -/

#print axioms Poincare.GaussianToolbox.integral_gaussianVec_fubini
#print axioms Poincare.GaussianToolbox.integral_gaussianVec
#print axioms Poincare.GaussianToolbox.integral_gaussianVec_eq_pi_rpow
#print axioms Poincare.GaussianToolbox.integral_gaussianVecNormalized
#print axioms Poincare.GaussianToolbox.gaussianVec_eq_exp_neg_sum_sq
#print axioms Poincare.GaussianToolbox.gaussianVec_eq_exp_neg_normSq
#print axioms Poincare.GaussianToolbox.integral_gaussianKernel_half
#print axioms Poincare.GaussianToolbox.integral_standardGaussianVec_fubini
#print axioms Poincare.GaussianToolbox.integral_standardGaussianVec
#print axioms Poincare.GaussianToolbox.standardGaussianVec_eq_exp_neg_sum_sq
#print axioms Poincare.GaussianToolbox.integral_standardGaussianDensity
