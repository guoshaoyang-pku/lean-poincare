/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The semigroup (convolution) property of the Euclidean heat kernel

The heat kernel on `ℝⁿ` satisfies the convolution identity
`K_t * K_s = K_{t+s}`, i.e.

`∫ y, gaussianKernel n t y * gaussianKernel n s (x - y) = gaussianKernel n (t + s) x`

for all positive `t`, `s`. The proof is an explicit computation: complete the
square in the exponent,

`‖y‖²/(4t) + ‖x - y‖²/(4s) = a ‖y - c‖² + ‖x‖²/(4(t+s))`,
`a = (t+s)/(4ts)`, `c = (t/(t+s)) x`,

and then use the multivariate Gaussian integral `∫ exp (-a ‖z‖²) = (π/a)^{n/2}`
together with the elementary identity
`(4πt)^{-n/2} (4πs)^{-n/2} (4πts/(t+s))^{n/2} = (4π(t+s))^{-n/2}`.

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs
in this file; every declaration is proved unconditionally.
-/
module

public import Poincare.D10.HeatKernelEuclidean.Mass

@[expose] public section

open MeasureTheory Real
open scoped InnerProductSpace Laplacian RealInnerProductSpace

namespace Poincare.D10.HeatKernelEuclidean

/-! ## Completing the square -/

/-- Completing the square for the convolution of two Gaussian kernels:
`‖y‖²/(4t) + ‖x - y‖²/(4s) = a ‖y - c‖² + ‖x‖²/(4(t+s))` with
`a = (t+s)/(4ts)` and `c = (t/(t+s)) x`. -/
theorem conv_exponent_identity {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (x y : V) :
    ‖y‖ ^ 2 / (4 * t) + ‖x - y‖ ^ 2 / (4 * s) =
      (t + s) / (4 * t * s) * ‖y - (t / (t + s)) • x‖ ^ 2 +
        ‖x‖ ^ 2 / (4 * (t + s)) := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq (x - y),
    ← real_inner_self_eq_norm_sq (y - (t / (t + s)) • x), ← real_inner_self_eq_norm_sq x]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm x y]
  field_simp
  ring

/-! ## The prefactor identity -/

/-- The exponents of the prefactors combine: for positive `t`, `s`,
`(4πt)^{-n/2} (4πs)^{-n/2} (4πts/(t+s))^{n/2} = (4π(t+s))^{-n/2}`. -/
theorem prefactor_mul (n : ℕ) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    (4 * π * t) ^ (-(n : ℝ) / 2) * (4 * π * s) ^ (-(n : ℝ) / 2) *
        (4 * π * t * s / (t + s)) ^ ((n : ℝ) / 2) =
      (4 * π * (t + s)) ^ (-(n : ℝ) / 2) := by
  set N : ℝ := (n : ℝ) / 2 with hN
  rw [show (-(n : ℝ)) / 2 = -N by rw [hN, neg_div]]
  have hts : 0 < t + s := by linarith
  have h1 : (4 * π * t) ^ (-N) * (4 * π * s) ^ (-N) = (16 * π ^ 2 * t * s) ^ (-N) := by
    rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 * π * t)
      (by positivity : (0 : ℝ) ≤ 4 * π * s)]
    congr 1
    ring
  have h2 : (16 * π ^ 2 * t * s) ^ (-N) * (4 * π * t * s / (t + s)) ^ N
      = ((4 * π * t * s / (t + s)) / (16 * π ^ 2 * t * s)) ^ N := by
    rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ 4 * π * t * s / (t + s))
        (by positivity : (0 : ℝ) ≤ 16 * π ^ 2 * t * s),
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ 16 * π ^ 2 * t * s)]
    field_simp
  have h3 : (4 * π * t * s / (t + s)) / (16 * π ^ 2 * t * s) = (4 * π * (t + s))⁻¹ := by
    field_simp
    ring
  have h4 : ((4 * π * (t + s))⁻¹) ^ N = (4 * π * (t + s)) ^ (-N) := by
    rw [Real.inv_rpow (by positivity : (0 : ℝ) ≤ 4 * π * (t + s)),
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ 4 * π * (t + s))]
  rw [h1, h2, h3, h4]

/-! ## The convolution identity -/

/-- The semigroup property of the heat kernel, stated as a convolution identity. -/
def SemigroupConvolutionIdentity (n : ℕ) : Prop :=
  ∀ t s : ℝ, 0 < t → 0 < s → ∀ x : EuclideanSpace ℝ (Fin n),
    ∫ y : EuclideanSpace ℝ (Fin n),
        gaussianKernel n t y * gaussianKernel n s (x - y) = gaussianKernel n (t + s) x

/-- **The heat kernel satisfies the semigroup / convolution identity** `K_t * K_s = K_{t+s}`,
in every dimension `n` and unconditionally. -/
theorem semigroupConvolutionIdentity (n : ℕ) : SemigroupConvolutionIdentity n := by
  intro t s ht hs x
  have hts : 0 < t + s := by linarith
  have ha : 0 < (t + s) / (4 * t * s) := by positivity
  have hbase : π / ((t + s) / (4 * t * s)) = 4 * π * t * s / (t + s) := by
    field_simp
  have hpoint : ∀ y : EuclideanSpace ℝ (Fin n),
      gaussianKernel n t y * gaussianKernel n s (x - y) =
        (4 * π * t) ^ (-(n : ℝ) / 2) * (4 * π * s) ^ (-(n : ℝ) / 2) *
          Real.exp (-‖x‖ ^ 2 / (4 * (t + s))) *
          Real.exp (-((t + s) / (4 * t * s)) * ‖y - (t / (t + s)) • x‖ ^ 2) := by
    intro y
    have hexp : Real.exp (-‖y‖ ^ 2 / (4 * t)) * Real.exp (-‖x - y‖ ^ 2 / (4 * s)) =
        Real.exp (-‖x‖ ^ 2 / (4 * (t + s))) *
          Real.exp (-((t + s) / (4 * t * s)) * ‖y - (t / (t + s)) • x‖ ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      have h := conv_exponent_identity ht hs x y
      linear_combination -h
    rw [gaussianKernel_apply, gaussianKernel_apply]
    calc (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)) *
          ((4 * π * s) ^ (-(n : ℝ) / 2) * Real.exp (-‖x - y‖ ^ 2 / (4 * s)))
        = (4 * π * t) ^ (-(n : ℝ) / 2) * (4 * π * s) ^ (-(n : ℝ) / 2) *
            (Real.exp (-‖y‖ ^ 2 / (4 * t)) *
              Real.exp (-‖x - y‖ ^ 2 / (4 * s))) := by ring
      _ = (4 * π * t) ^ (-(n : ℝ) / 2) * (4 * π * s) ^ (-(n : ℝ) / 2) *
            (Real.exp (-‖x‖ ^ 2 / (4 * (t + s))) *
              Real.exp (-((t + s) / (4 * t * s)) * ‖y - (t / (t + s)) • x‖ ^ 2)) := by
            rw [hexp]
      _ = (4 * π * t) ^ (-(n : ℝ) / 2) * (4 * π * s) ^ (-(n : ℝ) / 2) *
            Real.exp (-‖x‖ ^ 2 / (4 * (t + s))) *
            Real.exp (-((t + s) / (4 * t * s)) *
              ‖y - (t / (t + s)) • x‖ ^ 2) := by ring
  simp_rw [hpoint]
  rw [integral_const_mul, integral_exp_neg_mul_norm_sq_sub ha,
    finrank_euclideanSpace_fin_real, hbase]
  rw [show (4 * π * t) ^ (-(n : ℝ) / 2) * (4 * π * s) ^ (-(n : ℝ) / 2) *
        Real.exp (-‖x‖ ^ 2 / (4 * (t + s))) *
        (4 * π * t * s / (t + s)) ^ ((n : ℝ) / 2) =
      (4 * π * t) ^ (-(n : ℝ) / 2) * (4 * π * s) ^ (-(n : ℝ) / 2) *
        (4 * π * t * s / (t + s)) ^ ((n : ℝ) / 2) *
        Real.exp (-‖x‖ ^ 2 / (4 * (t + s))) by ring,
    prefactor_mul n ht hs, gaussianKernel_apply]

/-- The convolution identity unfolded, in the form of a plain integral equality. -/
theorem gaussianKernel_convolution (n : ℕ) {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∫ y : EuclideanSpace ℝ (Fin n),
        gaussianKernel n t y * gaussianKernel n s (x - y) = gaussianKernel n (t + s) x :=
  semigroupConvolutionIdentity n t s ht hs x

end Poincare.D10.HeatKernelEuclidean
