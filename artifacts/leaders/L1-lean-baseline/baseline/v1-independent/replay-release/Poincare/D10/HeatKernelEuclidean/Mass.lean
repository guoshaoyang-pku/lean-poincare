/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Total mass of the Euclidean heat kernel

The heat kernel on `ℝⁿ` has total mass `1` for every positive time:
`∫ x, gaussianKernel n t x = 1`. This is the classical multivariate Gaussian
integral, obtained here from `integral_exp_neg_mul_norm_sq`.

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs
in this file; every declaration is proved unconditionally.
-/
module

public import Poincare.D10.HeatKernelEuclidean.GaussianIntegral

@[expose] public section

open MeasureTheory Real
open scoped InnerProductSpace Laplacian RealInnerProductSpace

namespace Poincare.D10.HeatKernelEuclidean

/-- The exponential part of the kernel, written with the constant `1 / (4 t)`. -/
theorem exp_part_eq (n : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Real.exp (-‖x‖ ^ 2 / (4 * t)) = Real.exp (-(1 / (4 * t)) * ‖x‖ ^ 2) := by
  congr 1
  ring

/-- **Total mass of the heat kernel.** For every `t > 0` the kernel integrates to `1`. -/
theorem gaussianKernel_integral (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ x : EuclideanSpace ℝ (Fin n), gaussianKernel n t x = 1 := by
  have h4t : 0 < 4 * t := by positivity
  have ha : 0 < 1 / (4 * t) := by positivity
  have hbase : 0 < 4 * π * t := by positivity
  have hfun : (fun x : EuclideanSpace ℝ (Fin n) => gaussianKernel n t x) =
      fun x : EuclideanSpace ℝ (Fin n) =>
        (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-(1 / (4 * t)) * ‖x‖ ^ 2) := by
    funext x
    rw [gaussianKernel_apply, exp_part_eq]
  rw [hfun, integral_const_mul, integral_exp_neg_mul_norm_sq ha,
    finrank_euclideanSpace_fin_real n]
  have hratio : π / (1 / (4 * t)) = 4 * π * t := by
    field_simp
  rw [hratio, ← Real.rpow_add hbase,
    show -(n : ℝ) / 2 + (n : ℝ) / 2 = 0 by ring, Real.rpow_zero]

end Poincare.D10.HeatKernelEuclidean
