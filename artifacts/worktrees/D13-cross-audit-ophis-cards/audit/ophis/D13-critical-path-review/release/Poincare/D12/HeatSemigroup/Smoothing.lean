/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-heat-semigroup-analysis)
-/

import Poincare.D12.HeatSemigroup.Basic
import Poincare.D11.HeatKernelBridge.InitialCondition
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Poincare.D12.HeatSemigroup.Smoothing

**D12 heat-semigroup analysis, part 3: smoothing — differentiation under the integral.**

For `t > 0` and a measurable function `f : EuclideanSpace ℝ (Fin n) → ℝ` with a pointwise bound
`∀ y, ‖f y‖ ≤ M`, we prove that the heat operator `x ↦ P_t f x` is **differentiable at every
point**, with Fréchet derivative

`fderiv ℝ (heatOperator n t f) x₀ = ∫ y, heatKernelMulFDerivCLM n t f x₀ y ∂volume`,

where `heatKernelMulFDerivCLM n t f x y v = gaussianKernel n t (x - y) * f y * ⟪y - x, v⟫ / (2t)`
is the derivative of the kernel multiple `z ↦ gaussianKernel n t (z - y) * f y`. The proof is
mathlib's dominated differentiation lemma `hasFDerivAt_integral_of_dominated_of_fderiv_le`; the
integrable domination is the explicit Gaussian estimate

`‖K(x - y) f y (y - x)·‖/(2t) ≤ C(n,t,x₀,M) · exp(-‖y‖²/(16t))`  for `x ∈ ball x₀ 1`.

Consequently `x ↦ P_t f x` is **continuous** (and, iterating the same lemma, smooth — the
C¹ step is proved here; the iteration to C^k is a recorded follow-up obligation).

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Real Filter
open scoped Topology InnerProductSpace RealInnerProductSpace

namespace Poincare.D12.HeatSemigroup

noncomputable section

open Poincare.D10.HeatKernelEuclidean
open Poincare.D11.HeatKernelBridge

set_option linter.unusedVariables false

/-! ## The derivative of the kernel in the space variable -/

/-- The derivative of `z ↦ gaussianKernel n t (z - y)` at `x`, as a continuous linear map:
`v ↦ gaussianKernel n t (x - y) * ⟪y - x, v⟫ / (2t)`. -/
def gaussianKernelFDerivCLM (n : ℕ) (t : ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  (gaussianKernel n t (x - y) / (2 * t)) • (innerCLM (EuclideanSpace ℝ (Fin n)) (y - x))

@[simp]
theorem gaussianKernelFDerivCLM_apply (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x y v : EuclideanSpace ℝ (Fin n)) :
    gaussianKernelFDerivCLM n t x y v =
      gaussianKernel n t (x - y) / (2 * t) * ⟪y - x, v⟫_ℝ := by
  unfold gaussianKernelFDerivCLM
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul, innerCLM_apply]

/-- The derivative of the kernel multiple `z ↦ gaussianKernel n t (z - y) * f y` at `x`. -/
def heatKernelMulFDerivCLM (n : ℕ) (t : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  (gaussianKernelFDerivCLM n t x y).smulRight (f y)

@[simp]
theorem heatKernelMulFDerivCLM_apply (n : ℕ) {t : ℝ} (ht : 0 < t)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x y v : EuclideanSpace ℝ (Fin n)) :
    heatKernelMulFDerivCLM n t f x y v =
      gaussianKernel n t (x - y) * f y * ⟪y - x, v⟫_ℝ / (2 * t) := by
  unfold heatKernelMulFDerivCLM gaussianKernelFDerivCLM
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [innerCLM_apply]
  change gaussianKernel n t (x - y) / (2 * t) * ⟪y - x, v⟫_ℝ * f y =
    gaussianKernel n t (x - y) * f y * ⟪y - x, v⟫_ℝ / (2 * t)
  field_simp [show (2 : ℝ) * t ≠ 0 by positivity]

/-- The kernel multiple is differentiable in `x` with derivative `heatKernelMulFDerivCLM`. -/
theorem hasFDerivAt_gaussianKernel_mul (n : ℕ) {t : ℝ} (ht : 0 < t)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (y x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (z - y) * f y)
      (heatKernelMulFDerivCLM n t f x y) x := by
  -- Step 1: derivative of the shifted quadratic `u ↦ -(1/(4t)) ‖u‖²`
  have hφ : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin n) => -(1 / (4 * t)) * ‖u‖ ^ 2)
      (-(1 / (4 * t)) • (2 • (innerSL ℝ) (x - y))) (x - y) := by
    simpa using (hasStrictFDerivAt_norm_sq (x - y)).hasFDerivAt.const_mul (-(1 / (4 * t)))
  -- Step 2: derivative of `u ↦ exp (-(1/(4t)) ‖u‖²)`
  have hexp := (Real.hasDerivAt_exp (-(1 / (4 * t)) * ‖x - y‖ ^ 2)).comp_hasFDerivAt (x - y) hφ
  -- Step 3: compose with `z ↦ z - y`
  have hsub : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => z - y)
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) x :=
    (hasFDerivAt_id (𝕜 := ℝ) (x := x)).sub_const y
  have hcomp := hexp.comp x hsub
  -- Step 4: multiply by the prefactor: derivative of the prefactor form of the kernel
  have hKpre : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) =>
      (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-(1 / (4 * t)) * ‖z - y‖ ^ 2))
      ((4 * π * t) ^ (-(n : ℝ) / 2) •
        (Real.exp (-(1 / (4 * t)) * ‖x - y‖ ^ 2) •
          (-(1 / (4 * t)) • (2 • (innerSL ℝ) (x - y))))) x :=
    hcomp.const_mul ((4 * π * t) ^ (-(n : ℝ) / 2))
  -- Step 5: the prefactor form equals the kernel, and the derivative equals
  -- `gaussianKernelFDerivCLM`
  have hK : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (z - y))
      (gaussianKernelFDerivCLM n t x y) x := by
    refine (hKpre.congr_of_eventuallyEq ?_).congr_fderiv ?_
    · filter_upwards with z
      rw [gaussianKernel_apply]
      congr 1
      ring
    · ext v
      rw [gaussianKernelFDerivCLM_apply n ht]
      simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_smul, Pi.smul_apply,
        smul_eq_mul, innerCLM, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
        innerSL_apply_apply]
      rw [show ⟪x - y, v⟫_ℝ = -⟪y - x, v⟫_ℝ by rw [← neg_sub, inner_neg_left]]
      rw [gaussianKernel_apply]
      ring
  -- Step 6: multiply by the constant `f y`
  refine (hK.const_mul (f y) |>.congr_of_eventuallyEq ?_).congr_fderiv ?_
  · filter_upwards with z
    rw [mul_comm (gaussianKernel n t (z - y)) (f y)]
  · ext v
    rw [heatKernelMulFDerivCLM_apply n ht]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    rw [gaussianKernelFDerivCLM_apply n ht]
    ring

/-- The derivative kernel is continuous in the pair `(x, y)`. -/
theorem continuous_gaussianKernelFDerivCLM (n : ℕ) {t : ℝ} :
    Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      gaussianKernelFDerivCLM n t p.1 p.2) := by
  unfold gaussianKernelFDerivCLM
  exact Continuous.smul
    (((continuous_gaussianKernel n).comp (continuous_fst.sub continuous_snd)).div_const (2 * t))
    ((innerCLM (EuclideanSpace ℝ (Fin n))).continuous.comp
      (continuous_snd.sub continuous_fst))

/-! ## Operator norm bounds for the derivative kernel -/

/-- The operator norm of the kernel derivative is bounded by the Gaussian times the linear
factor. -/
theorem gaussianKernelFDerivCLM_norm_le (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ‖gaussianKernelFDerivCLM n t x y‖ ≤
      gaussianKernel n t (x - y) * ‖y - x‖ / (2 * t) := by
  have hnonneg : 0 ≤ gaussianKernel n t (x - y) * ‖y - x‖ / (2 * t) := by
    exact div_nonneg (mul_nonneg (gaussianKernel_nonneg n ht.le (x - y)) (norm_nonneg _))
      (by positivity)
  rw [ContinuousLinearMap.opNorm_le_iff hnonneg]
  intro v
  rw [gaussianKernelFDerivCLM_apply n ht]
  calc ‖gaussianKernel n t (x - y) / (2 * t) * ⟪y - x, v⟫_ℝ‖
      = |gaussianKernel n t (x - y) / (2 * t)| * |⟪y - x, v⟫_ℝ| := norm_mul _ _
    _ = gaussianKernel n t (x - y) / (2 * t) * |⟪y - x, v⟫_ℝ| := by
          rw [abs_of_nonneg (div_nonneg (gaussianKernel_nonneg n ht.le (x - y)) (by positivity))]
    _ ≤ gaussianKernel n t (x - y) / (2 * t) * (‖y - x‖ * ‖v‖) := by
          have hinner : |⟪y - x, v⟫_ℝ| ≤ ‖y - x‖ * ‖v‖ := by
            simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (y - x) v
          exact mul_le_mul_of_nonneg_left hinner
            (div_nonneg (gaussianKernel_nonneg n ht.le (x - y)) (by positivity))
    _ = (gaussianKernel n t (x - y) * ‖y - x‖ / (2 * t)) * ‖v‖ := by
          ring_nf

/-- The operator norm of the derivative of the kernel multiple. -/
theorem heatKernelMulFDerivCLM_norm_le (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ y : EuclideanSpace ℝ (Fin n), ‖f y‖ ≤ M) (x y : EuclideanSpace ℝ (Fin n)) :
    ‖heatKernelMulFDerivCLM n t f x y‖ ≤
      gaussianKernel n t (x - y) * M * ‖y - x‖ / (2 * t) := by
  have hnonneg : 0 ≤ gaussianKernel n t (x - y) * M * ‖y - x‖ / (2 * t) := by
    exact div_nonneg (mul_nonneg (mul_nonneg (gaussianKernel_nonneg n ht.le (x - y)) hM)
      (norm_nonneg _)) (by positivity)
  rw [ContinuousLinearMap.opNorm_le_iff hnonneg]
  intro v
  rw [heatKernelMulFDerivCLM_apply n ht]
  calc ‖gaussianKernel n t (x - y) * f y * ⟪y - x, v⟫_ℝ / (2 * t)‖
      = ‖gaussianKernel n t (x - y) * f y / (2 * t) * ⟪y - x, v⟫_ℝ‖ := by ring_nf
    _ = |gaussianKernel n t (x - y) * f y / (2 * t)| * |⟪y - x, v⟫_ℝ| := norm_mul _ _
    _ = gaussianKernel n t (x - y) * ‖f y‖ / (2 * t) * |⟪y - x, v⟫_ℝ| := by
          rw [abs_div, abs_mul, abs_of_nonneg (gaussianKernel_nonneg n ht.le (x - y)),
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * t), Real.norm_eq_abs]
    _ ≤ gaussianKernel n t (x - y) * ‖f y‖ / (2 * t) * (‖y - x‖ * ‖v‖) := by
          have hinner : |⟪y - x, v⟫_ℝ| ≤ ‖y - x‖ * ‖v‖ := by
            simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (y - x) v
          exact mul_le_mul_of_nonneg_left hinner
            (div_nonneg (mul_nonneg (gaussianKernel_nonneg n ht.le (x - y)) (norm_nonneg _))
              (by positivity))
    _ = (gaussianKernel n t (x - y) / (2 * t) * (‖y - x‖ * ‖v‖)) * ‖f y‖ := by ring_nf
    _ ≤ (gaussianKernel n t (x - y) / (2 * t) * (‖y - x‖ * ‖v‖)) * M := by
          exact mul_le_mul_of_nonneg_left (hf y)
            (mul_nonneg (div_nonneg (gaussianKernel_nonneg n ht.le (x - y)) (by positivity))
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ = (gaussianKernel n t (x - y) * M * ‖y - x‖ / (2 * t)) * ‖v‖ := by ring_nf

/-! ## Elementary bounds for the domination -/

/-- `‖z‖ ≤ 1 + ‖z‖²`. -/
theorem norm_le_one_add_norm_sq (z : EuclideanSpace ℝ (Fin n)) : ‖z‖ ≤ 1 + ‖z‖ ^ 2 := by
  nlinarith [sq_nonneg (‖z‖ - 1 / 2)]

/-- The shifted quadratic lower bound: `‖y‖²/2 - ‖x‖² ≤ ‖x - y‖²`. -/
theorem norm_sub_sq_ge_half (x y : EuclideanSpace ℝ (Fin n)) :
    ‖y‖ ^ 2 / 2 - ‖x‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
  have h1 : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * ⟪x, y⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq (x - y), real_inner_sub_sub_self]
    rw [real_inner_self_eq_norm_sq x, real_inner_self_eq_norm_sq y]
    ring
  have h2 : 2 * ‖x‖ * ‖y‖ ≤ 2 * ‖x‖ ^ 2 + ‖y‖ ^ 2 / 2 := by
    have hsq : 0 ≤ (‖x‖ - ‖y‖ / 2) ^ 2 := sq_nonneg _
    nlinarith
  have h3 : |⟪x, y⟫_ℝ| ≤ ‖x‖ * ‖y‖ := by
    simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) x y
  nlinarith [le_abs_self ⟪x, y⟫_ℝ, h3]

/-- `(1 + ‖z‖²) exp (-‖z‖² / (4t)) ≤ (1 + 32t·e⁻¹) exp (-‖z‖² / (8t))` for `t > 0`. -/
theorem one_add_norm_sq_mul_exp_neg_le (n : ℕ) {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin n)) :
    (1 + ‖z‖ ^ 2) * Real.exp (-‖z‖ ^ 2 / (4 * t))
      ≤ (1 + 32 * t * Real.exp (-1)) * Real.exp (-‖z‖ ^ 2 / (8 * t)) := by
  have hlin : ‖z‖ ^ 2 / (8 * t) * Real.exp (-(‖z‖ ^ 2 / (8 * t))) ≤ Real.exp (-1) :=
    Real.mul_exp_neg_le_exp_neg_one (‖z‖ ^ 2 / (8 * t))
  have hq : ‖z‖ ^ 2 * Real.exp (-(‖z‖ ^ 2 / (8 * t))) ≤ 8 * t * Real.exp (-1) := by
    have hm := mul_le_mul_of_nonneg_left hlin (by positivity : (0 : ℝ) ≤ 8 * t)
    have hscale : ‖z‖ ^ 2 * Real.exp (-(‖z‖ ^ 2 / (8 * t)))
        = 8 * t * (‖z‖ ^ 2 / (8 * t) * Real.exp (-(‖z‖ ^ 2 / (8 * t)))) := by
      field_simp [show (8 : ℝ) * t ≠ 0 by positivity]
    rw [hscale]
    exact hm
  calc (1 + ‖z‖ ^ 2) * Real.exp (-‖z‖ ^ 2 / (4 * t))
      = ((1 + ‖z‖ ^ 2) * Real.exp (-(‖z‖ ^ 2 / (8 * t)))) *
          Real.exp (-(‖z‖ ^ 2 / (8 * t))) := by
            rw [show -‖z‖ ^ 2 / (4 * t) = -(‖z‖ ^ 2 / (8 * t)) + -(‖z‖ ^ 2 / (8 * t)) by ring]
            rw [Real.exp_add]
            ring
    _ ≤ (1 + 8 * t * Real.exp (-1)) * Real.exp (-(‖z‖ ^ 2 / (8 * t))) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
          have he₁ : Real.exp (-(‖z‖ ^ 2 / (8 * t))) ≤ 1 := by
            exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
              (div_nonneg (sq_nonneg ‖z‖) (by positivity)))
          calc (1 + ‖z‖ ^ 2) * Real.exp (-(‖z‖ ^ 2 / (8 * t)))
              = Real.exp (-(‖z‖ ^ 2 / (8 * t))) + ‖z‖ ^ 2 * Real.exp (-(‖z‖ ^ 2 / (8 * t))) :=
                by ring
            _ ≤ 1 + 8 * t * Real.exp (-1) := by
                nlinarith [hq, he₁]
    _ ≤ (1 + 32 * t * Real.exp (-1)) * Real.exp (-‖z‖ ^ 2 / (8 * t)) := by
          rw [neg_div]
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
          nlinarith [mul_le_mul_of_nonneg_right (by nlinarith [ht] : (8 : ℝ) * t ≤ 32 * t)
            (Real.exp_nonneg (-(1 : ℝ)))]

/-- The smoothing constant appearing in the domination bound. -/
def heatSmoothingBoundConst (n : ℕ) (t : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (M : ℝ) : ℝ :=
  (4 * π * t) ^ (-(n : ℝ) / 2) * M / (2 * t) * (1 + 32 * t * Real.exp (-1)) *
    Real.exp ((‖x₀‖ + 1) ^ 2 / (4 * t))

/-- The smoothing constant is nonnegative. -/
theorem heatSmoothingBoundConst_nonneg (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x₀ : EuclideanSpace ℝ (Fin n)) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ heatSmoothingBoundConst n t x₀ M := by
  unfold heatSmoothingBoundConst
  have h1 : 0 ≤ (4 * π * t) ^ (-(n : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
  have h2 : 0 ≤ (4 * π * t) ^ (-(n : ℝ) / 2) * M / (2 * t) :=
    div_nonneg (mul_nonneg h1 hM) (by positivity)
  have h3 : 0 ≤ 1 + 32 * t * Real.exp (-1) :=
    add_nonneg zero_le_one (mul_nonneg (by positivity) (Real.exp_nonneg _))
  have h4 : 0 ≤ Real.exp ((‖x₀‖ + 1) ^ 2 / (4 * t)) := Real.exp_nonneg _
  exact mul_nonneg (mul_nonneg h2 h3) h4

/-- **Uniform domination on the unit ball.** For `x ∈ ball x₀ 1` the derivative kernel is bounded
by `heatSmoothingBoundConst n t x₀ M * exp (-‖y‖² / (16t))`. -/
theorem heatKernelMulFDerivCLM_bound_ball (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ y : EuclideanSpace ℝ (Fin n), ‖f y‖ ≤ M)
    (x₀ x y : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball x₀ 1) :
    ‖heatKernelMulFDerivCLM n t f x y‖ ≤
      heatSmoothingBoundConst n t x₀ M * Real.exp (-‖y‖ ^ 2 / (16 * t)) := by
  have hlin : ‖y - x‖ ≤ 1 + ‖x - y‖ ^ 2 := by
    simpa [norm_sub_rev] using norm_le_one_add_norm_sq (x - y)
  have hexpshift : Real.exp (-‖x - y‖ ^ 2 / (8 * t))
      ≤ Real.exp ((‖x₀‖ + 1) ^ 2 / (4 * t)) * Real.exp (-‖y‖ ^ 2 / (16 * t)) := by
    have hge : ‖y‖ ^ 2 / 2 - ‖x‖ ^ 2 ≤ ‖x - y‖ ^ 2 := norm_sub_sq_ge_half x y
    have hineq : -‖x - y‖ ^ 2 / (8 * t) ≤ (‖x‖ ^ 2 / (8 * t)) + -(‖y‖ ^ 2 / (16 * t)) := by
      have hge'' : ‖y‖ ^ 2 - 2 * ‖x‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hge (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp [show (8 : ℝ) * t ≠ 0 by positivity]
      linarith [hge'']
    have hxnorm : ‖x‖ ≤ ‖x₀‖ + 1 := by
      have hd : ‖x - x₀‖ < 1 := by
        rw [Metric.mem_ball] at hx
        rw [dist_eq_norm] at hx
        exact hx
      have htri : ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := by
        simpa [show x₀ - (x₀ - x) = x by abel, norm_sub_rev, add_comm] using
          norm_sub_le x₀ (x₀ - x)
      nlinarith
    calc Real.exp (-‖x - y‖ ^ 2 / (8 * t))
        ≤ Real.exp ((‖x‖ ^ 2 / (8 * t)) + -(‖y‖ ^ 2 / (16 * t))) := Real.exp_le_exp.mpr hineq
      _ = Real.exp (‖x‖ ^ 2 / (8 * t)) * Real.exp (-(‖y‖ ^ 2 / (16 * t))) := Real.exp_add _ _
      _ ≤ Real.exp ((‖x₀‖ + 1) ^ 2 / (4 * t)) * Real.exp (-‖y‖ ^ 2 / (16 * t)) := by
          have hx' : ‖x‖ ^ 2 ≤ (‖x₀‖ + 1) ^ 2 := by
            have h1 : 0 ≤ ((‖x₀‖ + 1) - ‖x‖) * ((‖x₀‖ + 1) + ‖x‖) :=
              mul_nonneg (sub_nonneg.mpr hxnorm)
                (add_nonneg (le_trans (norm_nonneg _) hxnorm) (norm_nonneg _))
            nlinarith [h1]
          rw [show -(‖y‖ ^ 2 / (16 * t)) = -‖y‖ ^ 2 / (16 * t) by rw [neg_div]]
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
          exact Real.exp_le_exp.mpr (le_trans (div_le_div_of_nonneg_right hx' (by positivity))
            (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
              (by nlinarith [ht] : (4 : ℝ) * t ≤ 8 * t)))
  calc ‖heatKernelMulFDerivCLM n t f x y‖
      ≤ gaussianKernel n t (x - y) * M * ‖y - x‖ / (2 * t) :=
          heatKernelMulFDerivCLM_norm_le n ht hM hf x y
    _ = (4 * π * t) ^ (-(n : ℝ) / 2) * M / (2 * t) *
          (‖y - x‖ * Real.exp (-‖x - y‖ ^ 2 / (4 * t))) := by
          rw [gaussianKernel_apply]
          ring
    _ ≤ (4 * π * t) ^ (-(n : ℝ) / 2) * M / (2 * t) *
          ((1 + ‖x - y‖ ^ 2) * Real.exp (-‖x - y‖ ^ 2 / (4 * t))) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hlin (Real.exp_nonneg _)) ?_
          exact div_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) hM) (by positivity)
    _ ≤ (4 * π * t) ^ (-(n : ℝ) / 2) * M / (2 * t) *
          ((1 + 32 * t * Real.exp (-1)) * Real.exp (-‖x - y‖ ^ 2 / (8 * t))) := by
          refine mul_le_mul_of_nonneg_left (one_add_norm_sq_mul_exp_neg_le n ht (x - y)) ?_
          exact div_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) hM) (by positivity)
    _ ≤ (4 * π * t) ^ (-(n : ℝ) / 2) * M / (2 * t) *
          ((1 + 32 * t * Real.exp (-1)) *
            (Real.exp ((‖x₀‖ + 1) ^ 2 / (4 * t)) * Real.exp (-‖y‖ ^ 2 / (16 * t)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpshift ?_) ?_
          · exact add_nonneg zero_le_one (mul_nonneg (by positivity) (Real.exp_nonneg _))
          · exact div_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) hM) (by positivity)
    _ = heatSmoothingBoundConst n t x₀ M * Real.exp (-‖y‖ ^ 2 / (16 * t)) := by
          unfold heatSmoothingBoundConst
          ring

/-! ## The domination bound is integrable -/

/-- The domination bound `heatSmoothingBoundConst n t x₀ M * exp(-‖y‖²/(16t))` is integrable. -/
theorem integrable_heatSmoothingBound (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x₀ : EuclideanSpace ℝ (Fin n)) {M : ℝ} (hM : 0 ≤ M) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      heatSmoothingBoundConst n t x₀ M * Real.exp (-‖y‖ ^ 2 / (16 * t))) volume := by
  refine ((Poincare.D11.HeatKernelBridge.integrable_exp_neg_mul_norm_sq
      (n := n) (a := 1 / (16 * t)) (by positivity)).const_mul
      (heatSmoothingBoundConst n t x₀ M)).congr (Eventually.of_forall fun y => ?_)
  congr 1
  ring

/-! ## Differentiation under the integral -/

set_option maxHeartbeats 4000000 in
/-- **The smoothing lemma.** For `t > 0` and measurable `f` with `∀ y, ‖f y‖ ≤ M`, the heat
operator `P_t f` is differentiable at every point `x₀`, with derivative
`∫ y, heatKernelMulFDerivCLM n t f x₀ y ∂volume`. -/
theorem hasFDerivAt_heatOperator (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfm : AEStronglyMeasurable f volume)
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ y : EuclideanSpace ℝ (Fin n), ‖f y‖ ≤ M)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (heatOperator n t f)
      (∫ y : EuclideanSpace ℝ (Fin n), heatKernelMulFDerivCLM n t f x₀ y ∂volume) x₀ := by
  -- hoist the six conditions with fully annotated types (fast elaboration)
  have hFmeas : ∀ x : EuclideanSpace ℝ (Fin n),
      AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin n) =>
        gaussianKernel n t (x - y) * f y) volume := by
    intro x
    exact AEStronglyMeasurable.mul
      ((continuous_gaussianKernel n).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      hfm
  have hFint : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      gaussianKernel n t (x₀ - y) * f y) volume := by
    refine Integrable.mono' ((integrable_gaussianKernel_sub n ht x₀).const_mul M) ?_ ?_
    · exact AEStronglyMeasurable.mul
        ((continuous_gaussianKernel n).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
        hfm
    · refine Eventually.of_forall ?_
      intro y
      calc ‖gaussianKernel n t (x₀ - y) * f y‖
          = gaussianKernel n t (x₀ - y) * ‖f y‖ := by
              rw [norm_mul, Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le (x₀ - y))]
        _ ≤ gaussianKernel n t (x₀ - y) * M :=
              mul_le_mul_of_nonneg_left (hf y) (gaussianKernel_nonneg n ht.le (x₀ - y))
        _ = M * gaussianKernel n t (x₀ - y) := mul_comm _ _
  have hF'meas : AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin n) =>
      heatKernelMulFDerivCLM n t f x₀ y) volume := by
    have hA : AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin n) =>
        gaussianKernelFDerivCLM n t x₀ y) volume :=
      (continuous_gaussianKernelFDerivCLM n).comp
        (continuous_const.prodMk continuous_id) |>.aestronglyMeasurable
    have hcont : Continuous (fun p : (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) × ℝ =>
        p.1.smulRight p.2) := by fun_prop
    exact hcont.comp_aestronglyMeasurable (hA.prodMk hfm)
  have hbound : ∀ᵐ y ∂volume, ∀ x ∈ Metric.ball x₀ 1,
      ‖heatKernelMulFDerivCLM n t f x y‖ ≤
        heatSmoothingBoundConst n t x₀ M * Real.exp (-‖y‖ ^ 2 / (16 * t)) := by
    refine Eventually.of_forall ?_
    intro y x hx
    exact heatKernelMulFDerivCLM_bound_ball n ht hM hf x₀ x y hx
  have hbint : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      heatSmoothingBoundConst n t x₀ M * Real.exp (-‖y‖ ^ 2 / (16 * t))) volume :=
    integrable_heatSmoothingBound n ht x₀ hM
  have hdiff : ∀ᵐ y ∂volume, ∀ x ∈ Metric.ball x₀ 1,
      HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (z - y) * f y)
        (heatKernelMulFDerivCLM n t f x y) x := by
    refine Eventually.of_forall ?_
    intro y x _
    exact hasFDerivAt_gaussianKernel_mul n ht f y x
  unfold heatOperator
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball x₀ 1) (Metric.ball_mem_nhds x₀ one_pos)
    (F := fun x y : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (x - y) * f y)
    (F' := fun x y : EuclideanSpace ℝ (Fin n) => heatKernelMulFDerivCLM n t f x y)
    (bound := fun y : EuclideanSpace ℝ (Fin n) =>
      heatSmoothingBoundConst n t x₀ M * Real.exp (-‖y‖ ^ 2 / (16 * t)))
    ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall hFmeas
  · exact hFint
  · exact hF'meas
  · exact hbound
  · exact hbint
  · -- differentiability of the kernel multiple
    refine Eventually.of_forall ?_
    intro y x _
    exact hasFDerivAt_gaussianKernel_mul n ht f y x

/-- The heat operator is differentiable everywhere on bounded measurable functions. -/
theorem differentiable_heatOperator (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfm : AEStronglyMeasurable f volume)
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ y : EuclideanSpace ℝ (Fin n), ‖f y‖ ≤ M) :
    Differentiable ℝ (heatOperator n t f) :=
  fun x => (hasFDerivAt_heatOperator n ht hfm hM hf x).differentiableAt

/-- **Smoothing: continuity.** For `t > 0` the heat operator maps bounded measurable functions
to continuous functions. -/
theorem continuous_heatOperator (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfm : AEStronglyMeasurable f volume)
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ y : EuclideanSpace ℝ (Fin n), ‖f y‖ ≤ M) :
    Continuous (heatOperator n t f) :=
  (differentiable_heatOperator n ht hfm hM hf).continuous

/-- The derivative formula as an identity of Fréchet derivatives. -/
theorem fderiv_heatOperator (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfm : AEStronglyMeasurable f volume)
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ y : EuclideanSpace ℝ (Fin n), ‖f y‖ ≤ M)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (heatOperator n t f) x₀ =
      ∫ y : EuclideanSpace ℝ (Fin n), heatKernelMulFDerivCLM n t f x₀ y ∂volume :=
  (hasFDerivAt_heatOperator n ht hfm hM hf x₀).fderiv

end

end Poincare.D12.HeatSemigroup
