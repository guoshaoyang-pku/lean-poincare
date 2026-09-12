/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D10-gaussian-toolbox builder
-/
module

public import Poincare.D10.GaussianToolbox.Basic

/-!
# Poincare.GaussianToolbox.Convolution

**The 1D convolution of two Gaussians is a Gaussian, with added variances.**

The computation is unconditional and complete:

* `gaussianKernel_exponent_identity` — completing the square,
  `a t² + b (x - t)² = (a+b)(t - bx/(a+b))² + (ab/(a+b)) x²`;
* `gaussianKernel_convolution` — the unnormalised convolution identity
  `∫ t, exp (-(a t²)) exp (-(b (x-t)²)) = √(π/(a+b)) · exp (-((ab/(a+b)) x²))`;
* `sqrt_convolution_param` — the square-root bookkeeping
  `√(a/π) · √(b/π) · √(π/(a+b)) = √((ab/(a+b))/π)`;
* `gaussianDensity_convolution` — **the normalised convolution is a Gaussian**:
  `(p_a * p_b)(x) = p_{ab/(a+b)}(x)`;
* `gaussianVariance_convolutionParam` — **the variances add**:
  `gaussianVariance (ab/(a+b)) = gaussianVariance a + gaussianVariance b`.

The only measure-theoretic input is mathlib's translation invariance of Lebesgue measure on `ℝ`,
`MeasureTheory.integral_sub_right_eq_self`; no hypothesis is left unproved.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Filter Topology
open scoped Real Topology

namespace Poincare.GaussianToolbox

/-! ## Completing the square -/

/-- **Completing the square** for the convolution exponent. -/
theorem gaussianKernel_exponent_identity {a b x t : ℝ} (h : a + b ≠ 0) :
    -(a * t ^ 2) + -(b * (x - t) ^ 2)
      = -((a + b) * (t - b * x / (a + b)) ^ 2) + -((a * b / (a + b)) * x ^ 2) := by
  field_simp
  ring

/-! ## The unnormalised convolution -/

/-- **Convolution of two Gaussian kernels.**  For `a, b > 0`,
`∫ t, exp (-(a t²)) exp (-(b (x-t)²)) = √(π/(a+b)) · exp (-((ab/(a+b)) x²))`.

The proof is the complete-square identity followed by translation invariance of Lebesgue
measure and the scaling law `integral_gaussianKernel`. -/
theorem gaussianKernel_convolution {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    ∫ t : ℝ, gaussianKernel a t * gaussianKernel b (x - t)
      = sqrt (π / (a + b)) * gaussianKernel (a * b / (a + b)) x := by
  have hab : 0 < a + b := add_pos ha hb
  have hab' : a + b ≠ 0 := ne_of_gt hab
  have hpoint : ∀ t : ℝ, gaussianKernel a t * gaussianKernel b (x - t)
      = gaussianKernel (a + b) (t - b * x / (a + b))
        * gaussianKernel (a * b / (a + b)) x := by
    intro t
    rw [gaussianKernel_def, gaussianKernel_def, gaussianKernel_def, gaussianKernel_def,
      ← exp_add, ← exp_add, gaussianKernel_exponent_identity hab']
  calc ∫ t : ℝ, gaussianKernel a t * gaussianKernel b (x - t)
      = ∫ t : ℝ, gaussianKernel (a + b) (t - b * x / (a + b))
          * gaussianKernel (a * b / (a + b)) x :=
        integral_congr_ae (Eventually.of_forall hpoint)
    _ = ∫ t : ℝ, gaussianKernel (a * b / (a + b)) x
          * gaussianKernel (a + b) (t - b * x / (a + b)) :=
        integral_congr_ae (Eventually.of_forall fun t => mul_comm _ _)
    _ = gaussianKernel (a * b / (a + b)) x
          * ∫ t : ℝ, gaussianKernel (a + b) (t - b * x / (a + b)) := by
        rw [integral_const_mul]
    _ = gaussianKernel (a * b / (a + b)) x * ∫ u : ℝ, gaussianKernel (a + b) u := by
        rw [MeasureTheory.integral_sub_right_eq_self]
    _ = gaussianKernel (a * b / (a + b)) x * sqrt (π / (a + b)) := by
        rw [integral_gaussianKernel]
    _ = sqrt (π / (a + b)) * gaussianKernel (a * b / (a + b)) x := by ring

/-! ## Square-root bookkeeping -/

/-- The normalising constants multiply correctly under convolution. -/
theorem sqrt_convolution_param {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    sqrt (a / π) * sqrt (b / π) * sqrt (π / (a + b))
      = sqrt (a * b / (a + b) / π) := by
  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ a / π)]
  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ a / π * (b / π))]
  congr 1
  field_simp

/-! ## The normalised convolution and the variance -/

/-- **Convolution of two normalised Gaussian densities is a Gaussian density.**  For `a, b > 0`
and every `x`, `∫ t, p_a(t) p_b(x - t) = p_{ab/(a+b)}(x)`, i.e. the variances add. -/
theorem gaussianDensity_convolution {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    ∫ t : ℝ, gaussianDensity a t * gaussianDensity b (x - t)
      = gaussianDensity (a * b / (a + b)) x := by
  have hfun : (fun t : ℝ => gaussianDensity a t * gaussianDensity b (x - t))
      = fun t : ℝ => (sqrt (a / π) * sqrt (b / π))
          * (gaussianKernel a t * gaussianKernel b (x - t)) := by
    funext t
    rw [gaussianDensity_def, gaussianDensity_def]
    ring
  rw [hfun, integral_const_mul, gaussianKernel_convolution ha hb x, gaussianDensity_def,
    ← mul_assoc (sqrt (a / π) * sqrt (b / π)) (sqrt (π / (a + b))),
    sqrt_convolution_param ha hb]

/-- **The variances add under convolution**: with `gaussianVariance a = 1/(2a)`, the convolution
parameter `ab/(a+b)` has variance `1/(2a) + 1/(2b)`. -/
theorem gaussianVariance_convolutionParam {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    gaussianVariance (a * b / (a + b)) = gaussianVariance a + gaussianVariance b := by
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  rw [gaussianVariance, gaussianVariance, gaussianVariance]
  field_simp
  ring

end Poincare.GaussianToolbox
