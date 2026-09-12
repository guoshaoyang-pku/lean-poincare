/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-heat-semigroup-analysis)
-/

import Poincare.D11.HeatKernelBridge.EuclideanInstance
import Poincare.D10.HeatKernelEuclidean.Semigroup

/-!
# Poincare.D12.HeatSemigroup.Basic

**D12 heat-semigroup analysis, part 1: the heat operator on `ℝⁿ` and its first estimates.**

For `t > 0` and a function `f : EuclideanSpace ℝ (Fin n) → ℝ` we study the *heat operator*
(convolution with the explicit D10 Gaussian kernel against Lebesgue measure `volume`)

`heatOperator n t f x = ∫ y, gaussianKernel n t (x - y) * f y`.

This is the standard heat semigroup `P_t f = K_t ⋆ f` written with the two-point kernel
`K(x,y,t) = (4πt)^{-n/2} exp(-‖x - y‖²/(4t))`; it is exactly the operator attached to the D11
bridge datum `flatHeatKernelCore n`.

This file proves, with all measurability and integrability obligations explicit:

* **compatibility**: `heatOperator` agrees with the integral of the D11 `flatKernel` for `t > 0`
  (so all D11 results transfer), and with the one-point form `∫ z, gaussianKernel n t z * f (x - z)`;
* **positivity**: `0 ≤ᵐ f → ∀ x, 0 ≤ heatOperator n t f x` for a.e.-strongly-measurable `f`;
* **L∞ contraction in pointwise form**: a uniform bound `∀ y, ‖f y‖ ≤ M` transfers to the image,
  `∀ x, ‖heatOperator n t f x‖ ≤ M`, using the mass-one identity `∫ y, gaussianKernel n t (x-y) = 1`;
* kernel-section integrability `integrable_gaussianKernel_sub` and the mass identity in
  two-point form.

Every proof is complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Real Filter
open scoped Topology

set_option linter.unusedVariables false

namespace Poincare.D12.HeatSemigroup

noncomputable section

open Poincare.D10.HeatKernelEuclidean
open Poincare.D11.HeatKernelBridge

/-! ## The heat operator -/

/-- **The heat operator** `P_t f` on `ℝⁿ`: convolution of `f` with the explicit D10 Gaussian
heat kernel against Lebesgue measure `volume`. -/
def heatOperator (n : ℕ) (t : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * f y

/-- The heat operator applied to the constant zero function vanishes. -/
@[simp]
theorem heatOperator_zero (n : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    heatOperator n t (0 : EuclideanSpace ℝ (Fin n) → ℝ) x = 0 := by
  simp [heatOperator]

/-- The heat operator is additive when both kernel sections are integrable. -/
theorem heatOperator_add_of_integrable (n : ℕ) (t : ℝ) (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (hif : Integrable (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (x - y) * f y) volume)
    (hig : Integrable (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (x - y) * g y) volume) :
    heatOperator n t (f + g) x = heatOperator n t f x + heatOperator n t g x := by
  unfold heatOperator
  calc ∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * (f y + g y)
      = ∫ y : EuclideanSpace ℝ (Fin n),
          (gaussianKernel n t (x - y) * f y + gaussianKernel n t (x - y) * g y) :=
        integral_congr_ae (Eventually.of_forall fun y => by ring)
    _ = (∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * f y) +
          ∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * g y :=
        integral_add hif hig

/-- The heat operator commutes with scalar multiplication. -/
theorem heatOperator_smul (n : ℕ) (t : ℝ) (c : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    heatOperator n t (c • f) x = c * heatOperator n t f x := by
  unfold heatOperator
  change ∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * (c * f y)
      = c * ∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * f y
  calc ∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * (c * f y)
      = ∫ y : EuclideanSpace ℝ (Fin n), c * (gaussianKernel n t (x - y) * f y) :=
        integral_congr_ae (Eventually.of_forall fun y => by ring)
    _ = c * ∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * f y :=
        integral_const_mul c (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (x - y) * f y)

/-! ## Compatibility with the D11 bridge kernel -/

/-- **Compatibility with the D11 bridge kernel.** For `t > 0` the heat operator agrees with the
integral against the two-point bridge kernel `flatKernel n x y t`. -/
theorem heatOperator_eq_integral_flatKernel (n : ℕ) {t : ℝ} (ht : 0 < t)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    heatOperator n t f x = ∫ y : EuclideanSpace ℝ (Fin n), flatKernel n x y t * f y := by
  unfold heatOperator
  refine integral_congr_ae (Eventually.of_forall ?_)
  intro y
  change gaussianKernel n t (x - y) * f y = flatKernel n x y t * f y
  rw [flatKernel_of_pos n x y ht]

/-- **Compatibility with the one-point form.** After the translation `y ↦ x - y` the heat operator
is the convolution with the kernel in one-point form. -/
theorem heatOperator_eq_integral_sub (n : ℕ) (t : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    heatOperator n t f x = ∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n t z * f (x - z) := by
  unfold heatOperator
  have hfun : (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (x - y) * f y)
      = fun y => (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z * f (x - z)) (x - y) := by
    funext y
    change gaussianKernel n t (x - y) * f y =
      gaussianKernel n t (x - y) * f (x - (x - y))
    rw [show x - (x - y) = y by abel]
  rw [hfun, integral_sub_left_eq_self
    (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z * f (x - z)) volume x]

/-! ## Kernel sections: integrability and mass -/

/-- For `t > 0` the kernel section `y ↦ gaussianKernel n t (x - y)` is integrable. -/
theorem integrable_gaussianKernel_sub (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (x - y)) volume :=
  (integrable_of_integral_eq_one (gaussianKernel_integral n ht)).comp_sub_left x

/-- **Mass one in two-point form**: `∫ y, gaussianKernel n t (x - y) = 1` for `t > 0`. -/
theorem integral_gaussianKernel_sub (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) = 1 := by
  rw [integral_sub_left_eq_self (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z) volume x,
    gaussianKernel_integral n ht]

/-- For `t > 0` the reflected kernel section `y ↦ gaussianKernel n t (y - x)` is integrable. -/
theorem integrable_gaussianKernel_sub_left (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (y - x)) volume :=
  (integrable_of_integral_eq_one (gaussianKernel_integral n ht)).comp_sub_right x

/-- **Mass one in reflected two-point form**: `∫ y, gaussianKernel n t (y - x) = 1` for `t > 0`. -/
theorem integral_gaussianKernel_sub_left (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (y - x) = 1 := by
  rw [integral_sub_right_eq_self (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z) x]
  exact gaussianKernel_integral n ht

/-- The kernel section is bounded by the prefactor `(4πt)^{-n/2}`, pointwise in `y`. -/
theorem gaussianKernel_sub_le_prefactor (n : ℕ) {t : ℝ} (ht : 0 < t)
    (u v : EuclideanSpace ℝ (Fin n)) :
    gaussianKernel n t (u - v) ≤ (4 * π * t) ^ (-(n : ℝ) / 2) := by
  rw [gaussianKernel_apply]
  have hbase : (0 : ℝ) ≤ 4 * π * t := by positivity
  have hexp : Real.exp (-‖u - v‖ ^ 2 / (4 * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.mpr (div_nonneg (sq_nonneg ‖u - v‖) (by positivity : (0 : ℝ) ≤ 4 * t))
  calc (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖u - v‖ ^ 2 / (4 * t))
      ≤ (4 * π * t) ^ (-(n : ℝ) / 2) * 1 :=
        mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hbase (-(n : ℝ) / 2))
    _ = (4 * π * t) ^ (-(n : ℝ) / 2) := mul_one _

/-! ## Positivity -/

/-- **Positivity preservation.** If `f ≥ 0` almost everywhere then `P_t f ≥ 0` everywhere
(for `t > 0`). The Bochner integral of the kernel multiple is nonnegative when integrable,
and is `0` otherwise, so the almost-everywhere sign of `f` suffices. -/
theorem heatOperator_nonneg (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf0 : 0 ≤ᵐ[volume] f) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ heatOperator n t f x := by
  by_cases h : Integrable (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (x - y) * f y) volume
  · have hnonneg : 0 ≤ᵐ[volume] fun y : EuclideanSpace ℝ (Fin n) =>
        gaussianKernel n t (x - y) * f y := by
      filter_upwards [hf0] with y hy
      exact mul_nonneg (gaussianKernel_nonneg n ht.le (x - y)) hy
    exact integral_nonneg_of_ae hnonneg
  · unfold heatOperator
    rw [integral_undef h]

/-! ## L∞ contraction, pointwise (uniform bound) form -/

/-- **L∞ contraction, pointwise form.** If `f` is a.e.-strongly-measurable and uniformly bounded
by `M ≥ 0` (i.e. `∀ y, ‖f y‖ ≤ M`), then `P_t f` is bounded by `M` everywhere. This is the
sup-norm contraction `‖P_t f‖_∞ ≤ ‖f‖_∞` for the space of bounded functions with the pointwise
bound norm, proved from `K ≥ 0` and `∫ K = 1`. -/
theorem heatOperator_norm_le_of_forall_norm_le (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ y : EuclideanSpace ℝ (Fin n), ‖f y‖ ≤ M)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖heatOperator n t f x‖ ≤ M := by
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun y => M * gaussianKernel n t (x - y)
  have hgInt : Integrable g volume :=
    (integrable_gaussianKernel_sub n ht x).const_mul M
  have hpoint : ∀ᵐ y ∂volume, ‖gaussianKernel n t (x - y) * f y‖ ≤ g y := by
    refine Eventually.of_forall ?_
    intro y
    calc ‖gaussianKernel n t (x - y) * f y‖
        = gaussianKernel n t (x - y) * ‖f y‖ := by
            rw [norm_mul, Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le (x - y))]
      _ ≤ gaussianKernel n t (x - y) * M :=
            mul_le_mul_of_nonneg_left (hf y) (gaussianKernel_nonneg n ht.le (x - y))
      _ = g y := by simp [g, mul_comm]
  have hnorm := norm_integral_le_of_norm_le hgInt hpoint
  have hgval : ∫ y : EuclideanSpace ℝ (Fin n), g y = M := by
    rw [show g = fun y => M * gaussianKernel n t (x - y) by rfl]
    rw [integral_const_mul M (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (x - y)),
      integral_gaussianKernel_sub n ht x, mul_one]
  rwa [hgval] at hnorm

/-- **L∞ contraction for the absolute value**: a uniform bound on `f` gives the same bound on
`|P_t f|`. -/
theorem heatOperator_abs_le_of_forall_abs_le (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ y : EuclideanSpace ℝ (Fin n), |f y| ≤ M)
    (x : EuclideanSpace ℝ (Fin n)) :
    |heatOperator n t f x| ≤ M := by
  simpa only [Real.norm_eq_abs] using
    heatOperator_norm_le_of_forall_norm_le n ht hM
      (fun y => by simpa [Real.norm_eq_abs] using hf y) x

/-- **L∞ contraction with the exact sup-bound constant**: the image is bounded by the same
constant that bounds `‖f‖`, i.e. by `‖f‖` when `f` is a bounded continuous function. -/
theorem heatOperator_norm_le_of_forall_norm_le' (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ}
    (hM : ∀ y : EuclideanSpace ℝ (Fin n), ‖f y‖ ≤ M)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖heatOperator n t f x‖ ≤ max M 0 := by
  have hnonneg : 0 ≤ max M 0 := le_max_right _ _
  apply heatOperator_norm_le_of_forall_norm_le n ht hnonneg
  intro y
  exact (hM y).trans (le_max_left _ _)

end

end Poincare.D12.HeatSemigroup
