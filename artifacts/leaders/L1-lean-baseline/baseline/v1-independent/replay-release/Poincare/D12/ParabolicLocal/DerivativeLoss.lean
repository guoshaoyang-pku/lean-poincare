/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare longrun D12-parabolic-local-existence

# Derivative loss of the Gaussian heat convolution

This module discharges the named obligation `derivativeLossBarrier` of `Obligations.lean`:

  **There is no constant `C` with `‖fderiv (K_t * f)(0)‖ ≤ C ‖f‖` uniformly in `t ∈ (0,∞)` and
  smooth bounded `f`.**

The proof has three layers.

1. **Differentiation under the integral** (`heatConvPoint_hasFDerivAt_zero`,
   `heatConv_fderiv_zero_apply`): for `t > 0` and bounded continuous `f`, the convolution
   `x ↦ (K_t * f)(x)` is Fréchet differentiable at `0` with derivative
   `v ↦ (1/(2t)) ∫ y, gaussianKernel n t y * ⟪y, v⟫ * f y`. This is the mathlib parametric
   integral theorem `hasFDerivAt_integral_of_dominated_of_fderiv_le` with the explicit
   domination `‖∇_x (K_t(x-y) f y)‖ ≤ C_t (‖y‖ + 1) exp(-‖y‖²/(8t))`, whose integrability is
   the Gaussian polynomial-moment fact proved here.

2. **The quadratic Gaussian moment** (`integral_exp_neg_mul_normSq_sq_coord`): via the
   measure-preserving identification `PiLp.volume_preserving_toLp` and Fubini
   (`integral_fintype_prod_volume_eq_prod`), combined with the D10 one-dimensional moments
   (`integral_gaussianKernel`, `integral_moment_succ`),
   `∫ y, (y i)² exp (-b ‖y‖²) = π^(n/2) / (2 b^(n/2+1))`.

3. **The barrier** (`derivativeLossBarrier_holds`): the test functions
   `fₘ(y) = y₁ exp (-m ‖y‖²)` (bounded with `‖fₘ‖ ≤ 1/(2√m)`, smooth) give, by 1. and 2. with
   `t = 1/m`, the exact value `fderiv (K_{1/m} fₘ)(0) (e₁) = 5^(-(n/2+1))`, independent of `m`,
   while `‖fₘ‖ ≤ 1/(2√m) → 0`. Hence `‖fderiv (K_{1/m} fₘ)(0)‖ / ‖fₘ‖ ≥ 2√m · 5^(-(n/2+1)) → ∞`,
   so no uniform `C` can exist. This is the quantitative derivative-loss signature: the L∞
   contraction of `GaussianSetup.lean` controls no spatial derivative of the solution.

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs in this file;
every declaration is proved unconditionally from D10 and pinned mathlib.
-/
module

public import Poincare.D12.ParabolicLocal.GaussianConv
public import Poincare.D10.HeatKernelEuclidean.GaussianIntegral
public import Poincare.D10.GaussianToolbox.Multivariate
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Normed.Operator.Bilinear

@[expose] public section

noncomputable section

open MeasureTheory Real Filter
open scoped Topology InnerProductSpace BoundedContinuousFunction BigOperators

namespace Poincare.D12.ParabolicLocal

open Poincare.D10.HeatKernelEuclidean
open Poincare.GaussianToolbox

/-- The ambient finite-dimensional Euclidean space `ℝⁿ`. -/
abbrev Vn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-! ## 1. The Fréchet derivative of the kernel in the space variable -/

/-- **The kernel gradient.** For `t > 0`, `∇_z K_t(z) · v = -(1/(2t)) K_t(z) ⟪z, v⟫`, stated as
a `HasFDerivAt` with the derivative represented through the `ℝ`-linear inner-product model
`innerCLM` of D10. -/
theorem gaussianKernel_hasFDerivAt (n : ℕ) (t : ℝ) (x : Vn n) :
    HasFDerivAt (fun z : Vn n => gaussianKernel n t z)
      ((innerCLM (Vn n) x).smulRight (-(1 / (2 * t)) * gaussianKernel n t x)) x := by
  have hnsq : HasFDerivAt (fun z : Vn n => ‖z‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hφ : HasFDerivAt (fun z : Vn n => -‖z‖ ^ 2 / (4 * t)) ((-1 / (2 * t)) • innerSL ℝ x) x := by
    have h1 : HasFDerivAt (fun z : Vn n => (-1 / (4 * t)) * ‖z‖ ^ 2)
        ((-1 / (4 * t)) • (2 • innerSL ℝ x)) x := hnsq.const_mul (-1 / (4 * t))
    have h1' : HasFDerivAt (fun z : Vn n => -‖z‖ ^ 2 / (4 * t))
        ((-1 / (4 * t)) • (2 • innerSL ℝ x)) x := by
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards with z
      ring
    refine h1'.congr_fderiv ?_
    ext v
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
    ring
  have hexp : HasFDerivAt (fun z : Vn n => Real.exp (-‖z‖ ^ 2 / (4 * t)))
      (Real.exp (-‖x‖ ^ 2 / (4 * t)) • ((-1 / (2 * t)) • innerSL ℝ x)) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-‖x‖ ^ 2 / (4 * t))).comp_hasFDerivAt x hφ
  have hK := hexp.const_mul ((4 * π * t) ^ (-(n : ℝ) / 2))
  have hK' : HasFDerivAt (fun z : Vn n => gaussianKernel n t z)
      ((4 * π * t) ^ (-(n : ℝ) / 2) • (Real.exp (-‖x‖ ^ 2 / (4 * t)) • ((-1 / (2 * t)) • innerSL ℝ x))) x := by
    refine hK.congr_of_eventuallyEq ?_
    filter_upwards with z
    rw [gaussianKernel_apply]
  refine hK'.congr_fderiv ?_
  ext v
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul,
    ContinuousLinearMap.smulRight_apply, innerCLM_apply]
  rw [gaussianKernel_apply]
  ring

/-- **The translated kernel gradient.** `∇_x K_t(x - y) · v = (1/(2t)) K_t(x-y) ⟪y - x, v⟫`. -/
theorem gaussianKernel_sub_hasFDerivAt (n : ℕ) (t : ℝ) (x y : Vn n) :
    HasFDerivAt (fun z : Vn n => gaussianKernel n t (z - y))
      ((innerCLM (Vn n) (y - x)).smulRight ((1 / (2 * t)) * gaussianKernel n t (x - y))) x := by
  have hsub : HasFDerivAt (fun z : Vn n => z - y) (ContinuousLinearMap.id ℝ (Vn n)) x := by
    simpa using (hasFDerivAt_id x).sub_const y
  have hcomp := (gaussianKernel_hasFDerivAt n t (x - y)).comp x hsub
  refine hcomp.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerCLM_apply, inner_sub_left]
  ring

/-! ## 2. The parametric integrand and its derivative -/

/-- The convolution integrand `(x, y) ↦ K_t (x - y) · f y`. -/
def kernelIntegrand (n : ℕ) (t : ℝ) (f : BCFn n) (x y : Vn n) : ℝ :=
  gaussianKernel n t (x - y) * f y

/-- Its `x`-derivative, as a continuous linear functional: `v ↦ (1/(2t)) K_t(x-y) ⟪y-x, v⟫ f y`. -/
def kernelIntegrandFderiv (n : ℕ) (t : ℝ) (f : BCFn n) (x y : Vn n) : Vn n →L[ℝ] ℝ :=
  (innerCLM (Vn n) (y - x)).smulRight ((1 / (2 * t)) * gaussianKernel n t (x - y) * f y)

/-- The pointwise `x`-derivative of the integrand, for every base point `y`. -/
theorem kernelIntegrand_hasFDerivAt (n : ℕ) (t : ℝ) (f : BCFn n) (x y : Vn n) :
    HasFDerivAt (fun z : Vn n => kernelIntegrand n t f z y) (kernelIntegrandFderiv n t f x y) x := by
  have h := (gaussianKernel_sub_hasFDerivAt n t x y).mul_const (f y)
  refine h.congr_fderiv ?_
  ext v
  simp only [smul_apply, ContinuousLinearMap.smulRight_apply,
    innerCLM_apply, smul_eq_mul, kernelIntegrandFderiv]
  ring

/-! ## 3. The domination bound and its integrability -/

/-- The integrable domination function for the derivative: a polynomial multiple of a Gaussian
at a slightly slower rate. -/
def domBound (n : ℕ) {t : ℝ} (_ht : 0 < t) (f : BCFn n) : Vn n → ℝ :=
  fun y => ‖f‖ / (2 * t) * (4 * π * t) ^ (-(n : ℝ) / 2) * exp (1 / (4 * t)) * (‖y‖ + 1) *
    exp (-(‖y‖ ^ 2 / (8 * t)))

/-- The elementary inequality `x² exp (-c x²) ≤ 1/(c·e)` for `c > 0`, in the form used for
Gaussian moment domination. -/
theorem sq_mul_exp_neg_mul_sq_le (c x : ℝ) (hc : 0 < c) :
    x ^ 2 * exp (-(c * x ^ 2)) ≤ 1 / (c * exp 1) := by
  have hu : c * x ^ 2 ≤ exp (c * x ^ 2 - 1) := by
    have h := Real.add_one_le_exp (c * x ^ 2 - 1)
    rwa [sub_add_cancel] at h
  have h := mul_le_mul_of_nonneg_right hu (le_of_lt (Real.exp_pos (-(c * x ^ 2))))
  have h' : exp (c * x ^ 2 - 1) * exp (-(c * x ^ 2)) = exp (-1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h'' : (c * x ^ 2) * exp (-(c * x ^ 2)) ≤ exp (-1) := by
    simpa [mul_assoc] using (calc
      (c * x ^ 2) * exp (-(c * x ^ 2)) ≤ exp (c * x ^ 2 - 1) * exp (-(c * x ^ 2)) := h
      _ = exp (-1) := h')
  have hdiv : x ^ 2 * exp (-(c * x ^ 2)) ≤ exp (-1) / c := by
    have hx : x ^ 2 * exp (-(c * x ^ 2)) = c⁻¹ * ((c * x ^ 2) * exp (-(c * x ^ 2))) := by
      field_simp [ne_of_gt hc]
    rw [hx, div_eq_mul_inv]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left h'' (le_of_lt (inv_pos.mpr hc))
  exact hdiv.trans_eq (show exp (-1) / c = 1 / (c * exp 1) by
    rw [Real.exp_neg, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev, one_mul])

/-- `‖y‖² exp (-b ‖y‖²) ≤ (2/(b·e)) exp (-(b/2) ‖y‖²)`: the quadratic moment is dominated by the
half-rate Gaussian. -/
theorem normSq_mul_exp_neg_mul_normSq_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {b : ℝ} (hb : 0 < b) (y : V) :
    ‖y‖ ^ 2 * exp (-(b * ‖y‖ ^ 2)) ≤ (2 / (b * exp 1)) * exp (-(b / 2 * ‖y‖ ^ 2)) := by
  have hc : 0 < b / 2 := half_pos hb
  have h1 := sq_mul_exp_neg_mul_sq_le (b / 2) ‖y‖ hc
  calc ‖y‖ ^ 2 * exp (-(b * ‖y‖ ^ 2))
      = ‖y‖ ^ 2 * exp (-(b / 2 * ‖y‖ ^ 2)) * exp (-(b / 2 * ‖y‖ ^ 2)) := by
          rw [show b * ‖y‖ ^ 2 = b / 2 * ‖y‖ ^ 2 + b / 2 * ‖y‖ ^ 2 by ring]
          rw [show -(b / 2 * ‖y‖ ^ 2 + b / 2 * ‖y‖ ^ 2)
            = -(b / 2 * ‖y‖ ^ 2) + -(b / 2 * ‖y‖ ^ 2) by ring]
          rw [Real.exp_add]
          ring
    _ ≤ (1 / ((b / 2) * exp 1)) * exp (-(b / 2 * ‖y‖ ^ 2)) := by
          exact mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos _))
    _ = (2 / (b * exp 1)) * exp (-(b / 2 * ‖y‖ ^ 2)) := by
          congr 1
          field_simp

/-- The half-rate pure Gaussian is integrable over `ℝⁿ` (the D10 multivariate Gaussian integral
gives its exact total mass; a scaled copy has mass `1`, which forces integrability). -/
theorem integrable_exp_neg_mul_normSq (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun y : Vn n => exp (-(b * ‖y‖ ^ 2))) volume := by
  have hval : ∫ y : Vn n, exp (-(b * ‖y‖ ^ 2)) = (π / b) ^ ((n : ℝ) / 2) := by
    simpa [finrank_euclideanSpace_fin] using integral_exp_neg_mul_norm_sq (V := Vn n) hb
  have hvalne : (π / b) ^ ((n : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos (div_pos (by positivity) hb) _).ne'
  let c : ℝ := (π / b) ^ ((n : ℝ) / 2)
  have hscaled : (∫ y : Vn n, c⁻¹ * exp (-(b * ‖y‖ ^ 2))) = 1 := by
    rw [integral_const_mul, hval]
    exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (div_pos (by positivity) hb) _))
  have hI : Integrable (fun y : Vn n => c⁻¹ * exp (-(b * ‖y‖ ^ 2))) volume :=
    integrable_of_integral_eq_one hscaled
  have hback : Integrable (fun y : Vn n => c * (c⁻¹ * exp (-(b * ‖y‖ ^ 2)))) volume :=
    hI.const_mul c
  refine hback.congr ?_
  filter_upwards with y
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (div_pos (by positivity) hb) _)),
    one_mul]

/-- The domination function `domBound` is integrable: `(‖y‖ + 1) exp (-‖y‖²/(8t))` is bounded by
a constant multiple of the quarter-rate Gaussian. -/
theorem domBound_integrable (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BCFn n) :
    Integrable (domBound n ht f) volume := by
  have hquarter : Integrable (fun y : Vn n => exp (-((1 / (32 * t)) * ‖y‖ ^ 2))) volume :=
    integrable_exp_neg_mul_normSq n (b := 1 / (32 * t)) (by positivity)
  have hmain : Integrable (fun y : Vn n =>
      (‖f‖ / (2 * t) * (4 * π * t) ^ (-(n : ℝ) / 2) * exp (1 / (4 * t)) *
        (2 + 64 * t / exp 1)) * exp (-((1 / (32 * t)) * ‖y‖ ^ 2))) volume :=
    hquarter.const_mul _
  refine hmain.mono' ?_ ?_
  · have hcont : Continuous (domBound n ht f) := by
      change Continuous (fun y : Vn n => ‖f‖ / (2 * t) * (4 * π * t) ^ (-(n : ℝ) / 2) *
        exp (1 / (4 * t)) * (‖y‖ + 1) * exp (-(‖y‖ ^ 2 / (8 * t))))
      exact (((continuous_const.mul continuous_const).mul continuous_const).mul
        (continuous_id.norm.add continuous_const)).mul
        (Real.continuous_exp.comp
          (((contDiff_norm_sq ℝ (E := Vn n) (n := ⊤)).continuous).div_const (8 * t) |>.neg))
    exact hcont.measurable.aestronglyMeasurable
  · filter_upwards with y
    have hlin : ‖y‖ + 1 ≤ 2 * (‖y‖ ^ 2 + 1) := by
      nlinarith [sq_nonneg (‖y‖ - (1 / 4 : ℝ))]
    have hquad : ‖y‖ ^ 2 * exp (-(‖y‖ ^ 2 / (16 * t))) ≤
        (32 * t / exp 1) * exp (-(‖y‖ ^ 2 / (32 * t))) := by
      have h := normSq_mul_exp_neg_mul_normSq_le (V := Vn n) (b := 1 / (16 * t)) (by positivity) y
      have h' : (2 / ((1 / (16 * t)) * exp 1)) = 32 * t / exp 1 := by
        field_simp
        ring
      rwa [h', show 1 / (16 * t) * ‖y‖ ^ 2 = ‖y‖ ^ 2 / (16 * t) by ring,
        show 1 / (16 * t) / 2 * ‖y‖ ^ 2 = ‖y‖ ^ 2 / (32 * t) by field_simp; ring] at h
    have hlin' : (‖y‖ + 1) * exp (-(‖y‖ ^ 2 / (8 * t))) ≤
        2 * (‖y‖ ^ 2 + 1) * exp (-(‖y‖ ^ 2 / (16 * t))) := by
      calc (‖y‖ + 1) * exp (-(‖y‖ ^ 2 / (8 * t)))
          ≤ 2 * (‖y‖ ^ 2 + 1) * exp (-(‖y‖ ^ 2 / (8 * t))) :=
              mul_le_mul_of_nonneg_right hlin (le_of_lt (Real.exp_pos _))
        _ ≤ 2 * (‖y‖ ^ 2 + 1) * exp (-(‖y‖ ^ 2 / (16 * t))) := by
              exact mul_le_mul_of_nonneg_left
                (Real.exp_le_exp.mpr (by
                  have hle0 : ‖y‖ ^ 2 / (16 * t) ≤ ‖y‖ ^ 2 / (8 * t) :=
                    div_le_div_of_nonneg_left (sq_nonneg ‖y‖) (by positivity : 0 < 8 * t)
                      (by nlinarith : (8 : ℝ) * t ≤ 16 * t)
                  linarith))
                (by nlinarith [sq_nonneg ‖y‖])
    have htotal : (‖y‖ + 1) * exp (-(‖y‖ ^ 2 / (8 * t))) ≤
        (2 + 64 * t / exp 1) * exp (-(‖y‖ ^ 2 / (32 * t))) := by
      calc (‖y‖ + 1) * exp (-(‖y‖ ^ 2 / (8 * t)))
          ≤ 2 * (‖y‖ ^ 2 + 1) * exp (-(‖y‖ ^ 2 / (16 * t))) := hlin'
        _ = 2 * exp (-(‖y‖ ^ 2 / (16 * t))) + 2 * (‖y‖ ^ 2 * exp (-(‖y‖ ^ 2 / (16 * t)))) := by
              ring
        _ ≤ 2 * exp (-(‖y‖ ^ 2 / (32 * t))) + 2 * ((32 * t / exp 1) * exp (-(‖y‖ ^ 2 / (32 * t)))) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left
                  (Real.exp_le_exp.mpr (by
                    have hle0 : ‖y‖ ^ 2 / (32 * t) ≤ ‖y‖ ^ 2 / (16 * t) :=
                      div_le_div_of_nonneg_left (sq_nonneg ‖y‖) (by positivity : 0 < 16 * t)
                        (by nlinarith : (16 : ℝ) * t ≤ 32 * t)
                    linarith)) (by norm_num))
                (mul_le_mul_of_nonneg_left hquad (by norm_num))
        _ = (2 + 64 * t / exp 1) * exp (-(‖y‖ ^ 2 / (32 * t))) := by ring
    calc ‖domBound n ht f y‖
        = ‖f‖ / (2 * t) * (4 * π * t) ^ (-(n : ℝ) / 2) * exp (1 / (4 * t)) *
            (‖y‖ + 1) * exp (-(‖y‖ ^ 2 / (8 * t))) := by
              rw [domBound]
              simp only [Real.norm_eq_abs]
              have hnn : 0 ≤ ‖f‖ / (2 * t) * (4 * π * t) ^ (-(n : ℝ) / 2) * exp (1 / (4 * t)) *
                  (‖y‖ + 1) * exp (-(‖y‖ ^ 2 / (8 * t))) := by
                positivity
              exact abs_of_nonneg hnn
      _ ≤ ‖f‖ / (2 * t) * (4 * π * t) ^ (-(n : ℝ) / 2) * exp (1 / (4 * t)) *
            ((2 + 64 * t / exp 1) * exp (-(‖y‖ ^ 2 / (32 * t)))) := by
              have hnn : 0 ≤ ‖f‖ / (2 * t) * (4 * π * t) ^ (-(n : ℝ) / 2) * exp (1 / (4 * t)) := by
                positivity
              simpa [mul_assoc] using mul_le_mul_of_nonneg_left htotal hnn
      _ = (‖f‖ / (2 * t) * (4 * π * t) ^ (-(n : ℝ) / 2) * exp (1 / (4 * t)) *
            (2 + 64 * t / exp 1)) * exp (-((1 / (32 * t)) * ‖y‖ ^ 2)) := by
              ring

/-! ## 4. The domination of the derivative -/

/-- The kernel at a translated point is controlled by the quarter-rate Gaussian: for
`‖x‖ ≤ 1`, `K_t (x - y) ≤ (4πt)^(-n/2) e^{1/(4t)} e^(-‖y‖²/(8t))`. This uses
`|x-y|² ≥ ‖y‖²/2 - ‖x‖²`, an exact quadratic inequality. -/
theorem gaussianKernel_sub_le_quarter (n : ℕ) {t : ℝ} (ht : 0 < t) {x y : Vn n}
    (hx : x ∈ Metric.ball (0 : Vn n) 1) :
    gaussianKernel n t (x - y) ≤
      (4 * π * t) ^ (-(n : ℝ) / 2) * exp (1 / (4 * t)) * exp (-(‖y‖ ^ 2 / (8 * t))) := by
  have hxle : ‖x‖ ≤ 1 := by
    have hd : dist x 0 < 1 := Metric.mem_ball.mp hx
    rw [dist_zero_right] at hd
    exact le_of_lt hd
  have hsqmain : ‖y‖ ^ 2 / 2 - ‖x‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    have htri : ‖y‖ - ‖x‖ ≤ ‖x - y‖ := by
      have htri' : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
        simpa [show (y - x) + x = y by abel] using norm_add_le (y - x) x
      have htri'' : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := by linarith
      simpa [norm_sub_rev] using htri''
    have hsqtri : (‖y‖ - ‖x‖) ^ 2 ≤ ‖x - y‖ ^ 2 := by
      have h1 : ‖y‖ - ‖x‖ ≤ ‖x - y‖ := by
        have htri : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
          simpa [show (y - x) + x = y by abel] using norm_add_le (y - x) x
        have htri'' : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := by linarith
        simpa [norm_sub_rev] using htri''
      have h2 : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := by
        have htri : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
          simpa [show (x - y) + y = x by abel] using norm_add_le (x - y) y
        linarith
      have hcd : 0 ≤ (‖x - y‖ - (‖y‖ - ‖x‖)) * (‖x - y‖ + (‖y‖ - ‖x‖)) :=
        mul_nonneg (sub_nonneg.mpr h1) (by linarith)
      nlinarith [hcd]
    nlinarith [sq_nonneg (‖y‖ - 2 * ‖x‖)]
  have hneg : -(‖x - y‖ ^ 2 / (4 * t)) ≤ -((‖y‖ ^ 2 / 2 - ‖x‖ ^ 2) / (4 * t)) := by
    have hdiv : (‖y‖ ^ 2 / 2 - ‖x‖ ^ 2) / (4 * t) ≤ ‖x - y‖ ^ 2 / (4 * t) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hsqmain (le_of_lt (by positivity : 0 < (4 * t)⁻¹))
    exact neg_le_neg hdiv
  calc gaussianKernel n t (x - y)
      = (4 * π * t) ^ (-(n : ℝ) / 2) * exp (-(‖x - y‖ ^ 2 / (4 * t))) := by
          rw [gaussianKernel_apply]
          ring
    _ ≤ (4 * π * t) ^ (-(n : ℝ) / 2) * exp (-((‖y‖ ^ 2 / 2 - ‖x‖ ^ 2) / (4 * t))) := by
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hneg)
            (le_of_lt (Real.rpow_pos_of_pos (by positivity : 0 < 4 * π * t) _))
    _ ≤ (4 * π * t) ^ (-(n : ℝ) / 2) * (exp (1 / (4 * t)) * exp (-(‖y‖ ^ 2 / (8 * t)))) := by
          have hx2 : ‖x‖ ^ 2 ≤ 1 := by
            have habs : |‖x‖| ≤ |(1 : ℝ)| := by
              simpa [abs_of_nonneg (norm_nonneg x), abs_of_nonneg (by norm_num : 0 ≤ (1 : ℝ))]
                using hxle
            simpa using sq_le_sq.mpr habs
          have hmid : exp (-((‖y‖ ^ 2 / 2 - ‖x‖ ^ 2) / (4 * t))) =
              exp (‖x‖ ^ 2 / (4 * t)) * exp (-(‖y‖ ^ 2 / (8 * t))) := by
            rw [show -((‖y‖ ^ 2 / 2 - ‖x‖ ^ 2) / (4 * t))
              = ‖x‖ ^ 2 / (4 * t) + -(‖y‖ ^ 2 / (8 * t)) by
                field_simp
                ring]
            rw [Real.exp_add]
          rw [hmid]
          have hle' : ‖x‖ ^ 2 / (4 * t) ≤ 1 / (4 * t) := by
            have hmul := mul_le_mul_of_nonneg_right hx2 (le_of_lt (by positivity : 0 < (4 * t)⁻¹))
            simpa [div_eq_mul_inv] using hmul
          have hexp' : exp (‖x‖ ^ 2 / (4 * t)) ≤ exp (1 / (4 * t)) := Real.exp_le_exp.mpr hle'
          have hm : exp (‖x‖ ^ 2 / (4 * t)) * exp (-(‖y‖ ^ 2 / (8 * t))) ≤
              exp (1 / (4 * t)) * exp (-(‖y‖ ^ 2 / (8 * t))) :=
            mul_le_mul_of_nonneg_right hexp' (le_of_lt (Real.exp_pos _))
          exact mul_le_mul_of_nonneg_left hm
            (le_of_lt (Real.rpow_pos_of_pos (by positivity : 0 < 4 * π * t) _))
    _ = (4 * π * t) ^ (-(n : ℝ) / 2) * exp (1 / (4 * t)) * exp (-(‖y‖ ^ 2 / (8 * t))) := by ring

/-- The operator-norm bound of the parametric derivative against `domBound`. -/
theorem kernelIntegrandFderiv_norm_le_domBound (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BCFn n)
    {x y : Vn n} (hx : x ∈ Metric.ball (0 : Vn n) 1) :
    ‖kernelIntegrandFderiv n t f x y‖ ≤ domBound n ht f y := by
  have hinner : ‖innerCLM (Vn n) (y - x)‖ ≤ ‖y - x‖ := by
    refine (innerCLM (Vn n) (y - x)).opNorm_le_bound (norm_nonneg _) ?_
    intro v
    rw [innerCLM_apply, Real.norm_eq_abs]
    exact abs_real_inner_le_norm _ _
  have hc : ‖(1 / (2 * t)) * gaussianKernel n t (x - y) * f y‖ ≤
      (1 / (2 * t)) * gaussianKernel n t (x - y) * ‖f‖ := by
    calc ‖(1 / (2 * t)) * gaussianKernel n t (x - y) * f y‖
        = (1 / (2 * t)) * gaussianKernel n t (x - y) * ‖f y‖ := by
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * t)),
              abs_of_nonneg (gaussianKernel_nonneg n ht.le (x - y)), Real.norm_eq_abs]
      _ ≤ (1 / (2 * t)) * gaussianKernel n t (x - y) * ‖f‖ := by
            exact mul_le_mul_of_nonneg_left
              (BoundedContinuousFunction.norm_coe_le_norm f y)
              (mul_nonneg (le_of_lt (by positivity : 0 < 1 / (2 * t)))
                (gaussianKernel_nonneg n ht.le (x - y)))
  have hnormsmul : ‖kernelIntegrandFderiv n t f x y‖ =
      ‖innerCLM (Vn n) (y - x)‖ * ‖(1 / (2 * t)) * gaussianKernel n t (x - y) * f y‖ := by
    rw [kernelIntegrandFderiv, ContinuousLinearMap.norm_smulRight_apply]
  have hprod : ‖innerCLM (Vn n) (y - x)‖ *
      ‖(1 / (2 * t)) * gaussianKernel n t (x - y) * f y‖ ≤
      ‖y - x‖ * ((1 / (2 * t)) * gaussianKernel n t (x - y) * ‖f‖) := by
    exact mul_le_mul hinner hc
      (norm_nonneg ((1 / (2 * t)) * gaussianKernel n t (x - y) * f y)) (norm_nonneg (y - x))
  calc ‖kernelIntegrandFderiv n t f x y‖
      = ‖innerCLM (Vn n) (y - x)‖ * ‖(1 / (2 * t)) * gaussianKernel n t (x - y) * f y‖ :=
          hnormsmul
    _ ≤ ‖y - x‖ * ((1 / (2 * t)) * gaussianKernel n t (x - y) * ‖f‖) := hprod
    _ ≤ (‖y‖ + 1) * ((1 / (2 * t)) * gaussianKernel n t (x - y) * ‖f‖) := by
          exact mul_le_mul_of_nonneg_right (by
            have htri : ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le y x
            have hd : dist x 0 < 1 := Metric.mem_ball.mp hx
            rw [dist_zero_right] at hd
            linarith) (mul_nonneg (mul_nonneg (le_of_lt (by positivity : 0 < 1 / (2 * t)))
              (gaussianKernel_nonneg n ht.le (x - y))) (norm_nonneg f))
    _ ≤ (‖y‖ + 1) * ((1 / (2 * t)) * ((4 * π * t) ^ (-(n : ℝ) / 2) * exp (1 / (4 * t)) *
            exp (-(‖y‖ ^ 2 / (8 * t)))) * ‖f‖) := by
          have hK' : (1 / (2 * t)) * gaussianKernel n t (x - y) * ‖f‖ ≤
              (1 / (2 * t)) * ((4 * π * t) ^ (-(n : ℝ) / 2) * exp (1 / (4 * t)) *
                exp (-(‖y‖ ^ 2 / (8 * t)))) * ‖f‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (gaussianKernel_sub_le_quarter n ht hx)
                (le_of_lt (by positivity : 0 < 1 / (2 * t)))) (norm_nonneg f)
          exact mul_le_mul_of_nonneg_left hK' (by positivity : 0 ≤ ‖y‖ + 1)
    _ = domBound n ht f y := by
          rw [domBound]
          ring

/-! ## 5. Differentiation under the integral -/

/-- The derivative of the convolution integrand is strongly measurable in `y`. -/
theorem kernelIntegrandFderiv_zero_aestronglyMeasurable (n : ℕ) {t : ℝ} (_ht : 0 < t) (f : BCFn n) :
    AEStronglyMeasurable (fun y : Vn n => kernelIntegrandFderiv n t f 0 y) volume := by
  have hL : Continuous (fun y : Vn n => innerCLM (Vn n) y) := (innerCLM (Vn n)).continuous
  have hc : Continuous (fun y : Vn n => (1 / (2 * t)) * gaussianKernel n t y * f y) :=
    (continuous_const.mul (continuous_gaussianKernel n)).mul f.continuous
  have hsm : Continuous (fun p : (Vn n →L[ℝ] ℝ) × ℝ => p.1.smulRight p.2) :=
    (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := Vn n) (F := ℝ)).continuous
  have hcont : Continuous (fun y : Vn n => kernelIntegrandFderiv n t f 0 y) := by
    refine (hsm.comp₂ hL hc).congr ?_
    intro y
    simp [kernelIntegrandFderiv, gaussianKernel_apply, norm_neg]
  exact hcont.aestronglyMeasurable

/-- The `x`-derivative of the convolution integrand is integrable in `y` at `x = 0`. -/
theorem kernelIntegrandFderiv_zero_integrable (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BCFn n) :
    Integrable (fun y : Vn n => kernelIntegrandFderiv n t f 0 y) volume := by
  refine (domBound_integrable n ht f).mono' (kernelIntegrandFderiv_zero_aestronglyMeasurable n ht f) ?_
  filter_upwards with y
  exact kernelIntegrandFderiv_norm_le_domBound n ht f (x := 0) (by simp)

/-- **Differentiation under the integral for the heat convolution at `0`.** For `t > 0` and
bounded continuous `f`, the map `x ↦ (K_t * f)(x)` is Fréchet differentiable at `0` with
derivative `v ↦ ∫ y, (1/(2t)) K_t(y) ⟪y, v⟫ f y dy`. This is the exact interchange that the
`mildToClassicalBridge` obligation of `Obligations.lean` names: the integral and the spatial
derivative commute, with an explicit integrable domination. -/
theorem heatConvPoint_hasFDerivAt_zero (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BCFn n) :
    HasFDerivAt (fun x : Vn n => heatConvPoint n t x f)
      (∫ y : Vn n, kernelIntegrandFderiv n t f 0 y) (0 : Vn n) := by
  let F : Vn n → Vn n → ℝ := fun x y => kernelIntegrand n t f x y
  let F' : Vn n → Vn n → Vn n →L[ℝ] ℝ := fun x y => kernelIntegrandFderiv n t f x y
  have hF_meas : ∀ᶠ x in 𝓝 (0 : Vn n), AEStronglyMeasurable (fun y : Vn n => F x y) volume := by
    filter_upwards with x
    have hcont : Continuous (fun y : Vn n => kernelIntegrand n t f x y) :=
      ((continuous_gaussianKernel n).comp (continuous_const.sub continuous_id)).mul f.continuous
    exact hcont.measurable.aestronglyMeasurable
  have hF_int : Integrable (fun y : Vn n => F (0 : Vn n) y) volume := by
    simpa [F, kernelIntegrand] using heatConvIntegrand_integrable n ht f 0
  have hF'_meas : AEStronglyMeasurable (fun y : Vn n => F' (0 : Vn n) y) volume := by
    simpa [F'] using kernelIntegrandFderiv_zero_aestronglyMeasurable n ht f
  have h_bound : ∀ᵐ y ∂(volume : Measure (Vn n)),
      ∀ x ∈ Metric.ball (0 : Vn n) 1, ‖F' x y‖ ≤ domBound n ht f y := by
    filter_upwards with y x hx
    simpa [F'] using kernelIntegrandFderiv_norm_le_domBound n ht f hx
  have hbound_int : Integrable (domBound n ht f) volume := domBound_integrable n ht f
  have h_diff : ∀ᵐ y ∂(volume : Measure (Vn n)),
      ∀ x ∈ Metric.ball (0 : Vn n) 1, HasFDerivAt (fun z : Vn n => F z y) (F' x y) x := by
    filter_upwards with y x hx
    simpa [F, F'] using kernelIntegrand_hasFDerivAt n t f x y
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := F) (F' := F') (s := Metric.ball (0 : Vn n) 1) (x₀ := (0 : Vn n))
    (μ := (volume : Measure (Vn n))) (bound := domBound n ht f)
    (Metric.ball_mem_nhds (0 : Vn n) one_pos)
    hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  simpa [F, F', kernelIntegrand, heatConvPoint] using hmain

/-- The same derivative in terms of the truncated `heatConv` (positive time). -/
theorem heatConv_hasFDerivAt_zero (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BCFn n) :
    HasFDerivAt (fun x : Vn n => (heatConv n t f) x)
      (∫ y : Vn n, kernelIntegrandFderiv n t f 0 y) (0 : Vn n) := by
  refine (heatConvPoint_hasFDerivAt_zero n ht f).congr_of_eventuallyEq ?_
  filter_upwards with x
  rw [heatConvPoint, heatConv_apply n ht f x]

/-- The Fréchet derivative of `x ↦ (K_t * f)(x)` at `0`, evaluated at a direction `v`:
`fderiv (K_t * f)(0) v = (1/(2t)) ∫ y, K_t(y) ⟪y, v⟫ f y dy`. -/
theorem heatConv_fderiv_zero_apply (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BCFn n) (v : Vn n) :
    fderiv ℝ (fun x : Vn n => (heatConv n t f) x) 0 v
      = (1 / (2 * t)) * ∫ y : Vn n, gaussianKernel n t y * ⟪y, v⟫_ℝ * f y := by
  have h := heatConv_hasFDerivAt_zero n ht f
  rw [h.fderiv, ContinuousLinearMap.integral_apply (kernelIntegrandFderiv_zero_integrable n ht f) v]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [kernelIntegrandFderiv, ContinuousLinearMap.smulRight_apply, innerCLM_apply,
    smul_eq_mul]
  simp [gaussianKernel_apply, norm_neg]
  ring

/-! ## 6. The quadratic Gaussian moment (Fubini) -/

/-- **The quadratic coordinate moment of the multivariate Gaussian.**
`∫ y, (y i)² exp (-b ‖y‖²) = π^(n/2) / (2 b^(n/2+1))`, computed by transporting to the
coordinate product space (`PiLp.volume_preserving_toLp`), Fubini
(`integral_fintype_prod_volume_eq_prod`) and the D10 one-dimensional moments. -/
theorem integral_exp_neg_mul_normSq_sq_coord (n : ℕ) {b : ℝ} (hb : 0 < b) (i : Fin n) :
    ∫ y : Vn n, (y i) ^ 2 * exp (-(b * ‖y‖ ^ 2))
      = π ^ ((n : ℝ) / 2) / (2 * b ^ ((n : ℝ) / 2 + 1)) := by
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding]
  have hnorm : ∀ x : Fin n → ℝ, ‖(WithLp.toLp 2 x : Vn n)‖ ^ 2 = ∑ j : Fin n, (x j) ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
    · simp [Real.norm_eq_abs, sq_abs]
    · exact Finset.sum_nonneg (fun j _ => by positivity)
  have hfun : (fun x : Fin n → ℝ =>
        ((WithLp.toLp 2 x : Vn n) i) ^ 2 * exp (-(b * ‖(WithLp.toLp 2 x : Vn n)‖ ^ 2))) =
      fun x : Fin n → ℝ =>
        ∏ j : Fin n, (if j = i then (x j) ^ 2 * exp (-(b * (x j) ^ 2)) else exp (-(b * (x j) ^ 2))) := by
    funext x
    rw [PiLp.toLp_apply, hnorm x]
    rw [show - (b * ∑ j : Fin n, (x j) ^ 2) = ∑ j : Fin n, -(b * (x j) ^ 2) by
      rw [Finset.mul_sum]
      simp only [neg_mul, Finset.sum_neg_distrib]]
    rw [Real.exp_sum]
    have hsplit : (∏ j : Fin n, exp (-(b * (x j) ^ 2))) =
        (∏ j ∈ (Finset.univ.erase i : Finset (Fin n)), exp (-(b * (x j) ^ 2))) *
          exp (-(b * (x i) ^ 2)) := by
      rw [Finset.prod_erase_mul (s := (Finset.univ : Finset (Fin n)))
        (f := fun j => exp (-(b * (x j) ^ 2))) (a := i) (Finset.mem_univ i)]
    rw [hsplit]
    have hprod : (∏ j : Fin n, (if j = i then (x j) ^ 2 * exp (-(b * (x j) ^ 2))
          else exp (-(b * (x j) ^ 2)))) =
        ((x i) ^ 2 * exp (-(b * (x i) ^ 2))) *
          ∏ j ∈ (Finset.univ.erase i : Finset (Fin n)), exp (-(b * (x j) ^ 2)) := by
      rw [← Finset.prod_erase_mul (s := (Finset.univ : Finset (Fin n)))
        (f := fun j => if j = i then (x j) ^ 2 * exp (-(b * (x j) ^ 2))
          else exp (-(b * (x j) ^ 2))) (a := i) (Finset.mem_univ i)]
      rw [if_pos rfl]
      rw [show (∏ j ∈ (Finset.univ.erase i : Finset (Fin n)),
          (if j = i then (x j) ^ 2 * exp (-(b * (x j) ^ 2)) else exp (-(b * (x j) ^ 2)))) =
          ∏ j ∈ (Finset.univ.erase i : Finset (Fin n)), exp (-(b * (x j) ^ 2)) by
        refine Finset.prod_congr rfl ?_
        intro j hj
        rw [if_neg (Finset.ne_of_mem_erase hj)]]
      ring
    rw [hprod]
    ring
  have hfunint : (∫ (x : Fin n → ℝ), (WithLp.toLp 2 x).ofLp i ^ 2 *
        rexp (-(b * ‖WithLp.toLp 2 x‖ ^ 2)) ∂volume) =
      ∫ (x : Fin n → ℝ), (∏ j : Fin n, (if j = i then (x j) ^ 2 * rexp (-(b * (x j) ^ 2))
        else rexp (-(b * (x j) ^ 2)))) ∂volume := by
    apply integral_congr_ae
    filter_upwards with x
    exact congrFun hfun x
  rw [hfunint]
  rw [MeasureTheory.integral_fintype_prod_volume_eq_prod
    (f := fun j t => if j = i then t ^ 2 * exp (-(b * t ^ 2)) else exp (-(b * t ^ 2)))]
  have hsplit : (∏ j : Fin n, ∫ t : ℝ, (if j = i then t ^ 2 * exp (-(b * t ^ 2))
        else exp (-(b * t ^ 2)))) =
      (∫ t : ℝ, t ^ 2 * exp (-(b * t ^ 2))) *
        (∏ j ∈ (Finset.univ.erase i : Finset (Fin n)), ∫ t : ℝ, exp (-(b * t ^ 2))) := by
    calc (∏ j : Fin n, ∫ t : ℝ, (if j = i then t ^ 2 * exp (-(b * t ^ 2)) else exp (-(b * t ^ 2))))
        = (∏ j ∈ (Finset.univ.erase i : Finset (Fin n)), ∫ t : ℝ, (if j = i then t ^ 2 * exp (-(b * t ^ 2))
              else exp (-(b * t ^ 2)))) * (∫ t : ℝ, t ^ 2 * exp (-(b * t ^ 2))) := by
            rw [← Finset.prod_erase_mul (s := (Finset.univ : Finset (Fin n)))
              (f := fun j => ∫ t : ℝ, if j = i then t ^ 2 * exp (-(b * t ^ 2)) else exp (-(b * t ^ 2)))
              (a := i) (Finset.mem_univ i)]
            congr 1
            simp
      _ = (∫ t : ℝ, t ^ 2 * exp (-(b * t ^ 2))) *
            ∏ j ∈ (Finset.univ.erase i : Finset (Fin n)), ∫ t : ℝ, exp (-(b * t ^ 2)) := by
            rw [mul_comm]
            congr 1
            exact Finset.prod_congr rfl (by intro j hj; simp [Finset.ne_of_mem_erase hj])
  rw [hsplit]
  have hmom : ∫ t : ℝ, t ^ 2 * exp (-(b * t ^ 2)) = Real.sqrt (π / b) / (2 * b) := by
    have h := integral_moment_succ (a := b) hb 0
    have h0 : (∫ x : ℝ, x ^ (2 * 0) * gaussianKernel b x) = ∫ x : ℝ, gaussianKernel b x := by
      congr 1 with x
      norm_num
    rw [h0, integral_gaussianKernel] at h
    norm_num at h
    have hg : (fun t : ℝ => t ^ 2 * exp (-(b * t ^ 2))) = fun t => t ^ 2 * gaussianKernel b t := by
      funext t
      rw [gaussianKernel_def]
    rw [hg, h]
  have hmass : ∫ t : ℝ, exp (-(b * t ^ 2)) = Real.sqrt (π / b) := by
    have hg : (fun t : ℝ => exp (-(b * t ^ 2))) = fun t => gaussianKernel b t := by
      funext t
      rw [gaussianKernel_def]
    rw [hg, integral_gaussianKernel]
  have hcard : (Finset.univ.erase i : Finset (Fin n)).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have hprodE : (∏ j ∈ (Finset.univ.erase i : Finset (Fin n)), ∫ t : ℝ, exp (-(b * t ^ 2))) =
      (Real.sqrt (π / b)) ^ (n - 1) := by
    rw [Finset.prod_const, hcard, hmass]
  have hnpos : 0 < n := by
    have hcardpos := Fintype.card_pos_iff.mpr ⟨i⟩
    simpa using hcardpos
  have hn1 : 1 ≤ n := Nat.succ_le_iff.mpr hnpos
  have hnn : n - 1 + 1 = n := Nat.sub_add_cancel hn1
  rw [hmom, hprodE]
  calc Real.sqrt (π / b) / (2 * b) * (Real.sqrt (π / b)) ^ (n - 1)
      = (Real.sqrt π) ^ n / (2 * b * (Real.sqrt b) ^ n) := by
        rw [Real.sqrt_div (by positivity : 0 ≤ π)]
        rw [show (Real.sqrt π / Real.sqrt b) / (2 * b) * (Real.sqrt π / Real.sqrt b) ^ (n - 1)
          = (Real.sqrt π / Real.sqrt b) * ((Real.sqrt π / Real.sqrt b) ^ (n - 1)) * (2 * b)⁻¹ by
            ring]
        rw [← pow_succ' (Real.sqrt π / Real.sqrt b) (n - 1), hnn]
        rw [div_pow]
        ring_nf
  _ = π ^ ((n : ℝ) / 2) / (2 * b ^ ((n : ℝ) / 2 + 1)) := by
        rw [← Real.rpow_natCast (Real.sqrt π) n, Real.sqrt_eq_rpow,
          ← Real.rpow_mul (le_of_lt pi_pos)]
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (b ^ (1 / 2 : ℝ)) n,
          ← Real.rpow_mul (le_of_lt hb)]
        rw [show ((1 : ℝ) / 2) * (n : ℝ) = (n : ℝ) / 2 by ring]
        rw [show (n : ℝ) / 2 + 1 = 1 + (n : ℝ) / 2 by ring, Real.rpow_add hb, Real.rpow_one]
        ring


/-! ## 7. The rpow assembly: from the moment to `(4mt+1)^(-(n/2+1))` -/

/-- The rpow bookkeeping that combines the kernel prefactor with the moment:
`(1/(2t)) (4πt)^(-n/2) · π^(n/2) / (2 (m + 1/(4t))^(n/2+1)) = (4mt+1)^(-(n/2+1))`. -/
theorem kernelMoment_const (n : ℕ) {t m : ℝ} (ht : 0 < t) (hm : 0 < m) :
    (1 / (2 * t)) * (4 * π * t) ^ (-(n : ℝ) / 2) *
        (π ^ ((n : ℝ) / 2) / (2 * (m + 1 / (4 * t)) ^ ((n : ℝ) / 2 + 1)))
      = (4 * m * t + 1) ^ (-((n : ℝ) / 2 + 1)) := by
  have h4t : 0 < 4 * t := by positivity
  have hbm : 0 < m + 1 / (4 * t) := by positivity
  have h1 : (4 * π * t) ^ (-(n : ℝ) / 2) * π ^ ((n : ℝ) / 2) = (4 * t) ^ (-(n : ℝ) / 2) := by
    calc (4 * π * t) ^ (-(n : ℝ) / 2) * π ^ ((n : ℝ) / 2)
        = (4 ^ (-(n : ℝ) / 2) * π ^ (-(n : ℝ) / 2) * t ^ (-(n : ℝ) / 2)) * π ^ ((n : ℝ) / 2) := by
            rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 * π) (le_of_lt ht)]
            rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4) (by positivity : (0 : ℝ) ≤ π)]
      _ = 4 ^ (-(n : ℝ) / 2) * t ^ (-(n : ℝ) / 2) := by
            have hπ : π ^ (-(n : ℝ) / 2) * π ^ ((n : ℝ) / 2) = 1 := by
              rw [← Real.rpow_add (by positivity : 0 < π)]
              rw [show -(n : ℝ) / 2 + (n : ℝ) / 2 = 0 by ring, Real.rpow_zero]
            rw [show 4 ^ (-(n : ℝ) / 2) * π ^ (-(n : ℝ) / 2) * t ^ (-(n : ℝ) / 2) * π ^ ((n : ℝ) / 2)
              = 4 ^ (-(n : ℝ) / 2) * t ^ (-(n : ℝ) / 2) * (π ^ (-(n : ℝ) / 2) * π ^ ((n : ℝ) / 2)) by ring]
            rw [hπ, mul_one]
      _ = (4 * t) ^ (-(n : ℝ) / 2) := by
            rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4) (le_of_lt ht)]
  calc (1 / (2 * t)) * (4 * π * t) ^ (-(n : ℝ) / 2) *
        (π ^ ((n : ℝ) / 2) / (2 * (m + 1 / (4 * t)) ^ ((n : ℝ) / 2 + 1)))
      = (1 / (2 * t)) * ((4 * π * t) ^ (-(n : ℝ) / 2) * π ^ ((n : ℝ) / 2)) /
          (2 * (m + 1 / (4 * t)) ^ ((n : ℝ) / 2 + 1)) := by ring
    _ = (1 / (2 * t)) * (4 * t) ^ (-(n : ℝ) / 2) /
          (2 * (m + 1 / (4 * t)) ^ ((n : ℝ) / 2 + 1)) := by rw [h1]
    _ = (1 / (2 * t)) * (1 / 2) * (4 * t) ^ (-(n : ℝ) / 2) *
          ((m + 1 / (4 * t)) ^ ((n : ℝ) / 2 + 1))⁻¹ := by ring
    _ = (4 * t)⁻¹ * (4 * t) ^ (-(n : ℝ) / 2) * ((m + 1 / (4 * t)) ^ ((n : ℝ) / 2 + 1))⁻¹ := by
          ring
    _ = (4 * t) ^ (-1 - (n : ℝ) / 2) * ((m + 1 / (4 * t)) ^ ((n : ℝ) / 2 + 1))⁻¹ := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add h4t]
          congr 1
          ring
    _ = (4 * t) ^ (-((n : ℝ) / 2 + 1)) * ((m + 1 / (4 * t)) ^ ((n : ℝ) / 2 + 1))⁻¹ := by
          congr 1
          ring
    _ = (4 * t) ^ (-((n : ℝ) / 2 + 1)) * (m + 1 / (4 * t)) ^ (-((n : ℝ) / 2 + 1)) := by
          rw [Real.rpow_neg (le_of_lt hbm)]
    _ = ((4 * t) * (m + 1 / (4 * t))) ^ (-((n : ℝ) / 2 + 1)) := by
          rw [Real.mul_rpow (le_of_lt h4t) (le_of_lt hbm)]
    _ = (4 * m * t + 1) ^ (-((n : ℝ) / 2 + 1)) := by
          congr 1
          field_simp [ne_of_gt h4t]

/-! ## 8. The test functions and the exact value -/

/-- The coordinate projection `x ↦ x i` as a continuous linear functional on `ℝⁿ`. -/
noncomputable def coordCLM (n : ℕ) (i : Fin n) : Vn n →L[ℝ] ℝ :=
  ContinuousLinearMap.mk
    { toFun := fun x => (x i)
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
    (by
      have hcont : Continuous (fun x : Vn n =>
          innerCLM (Vn n) x (EuclideanSpace.basisFun (Fin n) ℝ i)) :=
        ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).comp
          (innerCLM (Vn n))).continuous
      exact hcont.congr (fun x => by
        rw [innerCLM_apply, real_inner_comm, inner_basisFun]))

/-- The elementary one-dimensional bound `|x| exp (-m x²) ≤ 1/(2√m)` for `m > 0`, from
`1 + m x² ≥ 2√m |x|` (the square `(√m|x| - 1)² ≥ 0`) and `e^{mx²} ≥ 1 + m x²`. -/
theorem abs_mul_exp_neg_mul_sq_le (m x : ℝ) (hm : 0 < m) :
    |x| * exp (-(m * x ^ 2)) ≤ 1 / (2 * Real.sqrt m) := by
  have h₁ : |x| ≤ (1 + m * x ^ 2) / (2 * Real.sqrt m) := by
    have hsq : 0 ≤ (Real.sqrt m * |x| - 1) ^ 2 := sq_nonneg _
    have hsq' : 0 ≤ m * x ^ 2 - 2 * Real.sqrt m * |x| + 1 := by
      simpa [sub_sq, mul_pow, sq_abs, Real.sq_sqrt (le_of_lt hm), mul_assoc] using hsq
    rw [le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt m)]
    nlinarith [hsq']
  have h₂ : |x| * exp (-(m * x ^ 2)) ≤ |x| / (1 + m * x ^ 2) := by
    have hexp : 1 + m * x ^ 2 ≤ exp (m * x ^ 2) := by
      simpa [add_comm] using Real.add_one_le_exp (m * x ^ 2)
    have hpos : 0 < 1 + m * x ^ 2 := by positivity
    calc |x| * exp (-(m * x ^ 2))
        = |x| / exp (m * x ^ 2) := by
            rw [Real.exp_neg, div_eq_mul_inv]
      _ ≤ |x| / (1 + m * x ^ 2) := div_le_div_of_nonneg_left (abs_nonneg x) hpos hexp
  calc |x| * exp (-(m * x ^ 2))
      ≤ |x| / (1 + m * x ^ 2) := h₂
    _ ≤ ((1 + m * x ^ 2) / (2 * Real.sqrt m)) / (1 + m * x ^ 2) := by
          have hpos : 0 < 1 + m * x ^ 2 := by positivity
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right h₁ (le_of_lt (inv_pos.mpr hpos))
    _ = 1 / (2 * Real.sqrt m) := by field_simp

/-- The test function `fₘ(x) = x_i · exp (-m ‖x‖²)`: smooth, bounded by `1/(2√m)`, and odd in
the `i`-th coordinate — the profile used to exhibit the derivative loss. -/
def testF (n : ℕ) (i : Fin n) (m : ℝ) (hm : 0 < m) : BCFn n :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x : Vn n => (x i) * exp (-(m * ‖x‖ ^ 2)),
      (coordCLM n i).continuous.mul
        (Real.continuous_exp.comp ((continuous_const.mul ((contDiff_norm_sq ℝ (E := Vn n) (n := ⊤)).continuous)).neg))⟩
    (1 / Real.sqrt m) (by
      intro x y
      have hx : |(x i) * exp (-(m * ‖x‖ ^ 2))| ≤ 1 / (2 * Real.sqrt m) := by
        calc |(x i) * exp (-(m * ‖x‖ ^ 2))|
            = |x i| * exp (-(m * ‖x‖ ^ 2)) := by
                rw [abs_mul, abs_of_nonneg (le_of_lt (Real.exp_pos _))]
          _ ≤ |x i| * exp (-(m * (x i) ^ 2)) := by
                exact mul_le_mul_of_nonneg_left
                  (Real.exp_le_exp.mpr (by
                    have hco : (x i) ^ 2 ≤ ‖x‖ ^ 2 := by
                      rw [norm_sq_eq_sum_sq]
                      exact Finset.single_le_sum (fun j _ => sq_nonneg (x.ofLp j)) (Finset.mem_univ i)
                    exact neg_le_neg (mul_le_mul_of_nonneg_left hco (le_of_lt hm)))) (abs_nonneg (x i))
          _ ≤ 1 / (2 * Real.sqrt m) := abs_mul_exp_neg_mul_sq_le m (x i) hm
      have hy : |(y i) * exp (-(m * ‖y‖ ^ 2))| ≤ 1 / (2 * Real.sqrt m) := by
        calc |(y i) * exp (-(m * ‖y‖ ^ 2))|
            = |y i| * exp (-(m * ‖y‖ ^ 2)) := by
                rw [abs_mul, abs_of_nonneg (le_of_lt (Real.exp_pos _))]
          _ ≤ |y i| * exp (-(m * (y i) ^ 2)) := by
                exact mul_le_mul_of_nonneg_left
                  (Real.exp_le_exp.mpr (by
                    have hco : (y i) ^ 2 ≤ ‖y‖ ^ 2 := by
                      rw [norm_sq_eq_sum_sq]
                      exact Finset.single_le_sum (fun j _ => sq_nonneg (y.ofLp j)) (Finset.mem_univ i)
                    exact neg_le_neg (mul_le_mul_of_nonneg_left hco (le_of_lt hm)))) (abs_nonneg (y i))
          _ ≤ 1 / (2 * Real.sqrt m) := abs_mul_exp_neg_mul_sq_le m (y i) hm
      calc dist ((x i) * exp (-(m * ‖x‖ ^ 2))) ((y i) * exp (-(m * ‖y‖ ^ 2)))
          = |(x i) * exp (-(m * ‖x‖ ^ 2)) - (y i) * exp (-(m * ‖y‖ ^ 2))| := by rw [Real.dist_eq]
        _ ≤ |(x i) * exp (-(m * ‖x‖ ^ 2))| + |(y i) * exp (-(m * ‖y‖ ^ 2))| := by
              simpa [sub_eq_add_neg, abs_neg] using
                abs_add_le ((x i) * exp (-(m * ‖x‖ ^ 2))) (-((y i) * exp (-(m * ‖y‖ ^ 2))))
        _ ≤ 1 / (2 * Real.sqrt m) + 1 / (2 * Real.sqrt m) := add_le_add hx hy
        _ = 1 / Real.sqrt m := by ring)

/-- The pointwise norm bound of the test function: `‖fₘ‖ ≤ 1/(2√m)`. -/
theorem testF_norm_le (n : ℕ) (i : Fin n) {m : ℝ} (hm : 0 < m) :
    ‖testF n i m hm‖ ≤ 1 / (2 * Real.sqrt m) := by
  refine (BoundedContinuousFunction.norm_le ?_).mpr ?_
  · positivity
  · intro x
    change |(x i) * exp (-(m * ‖x‖ ^ 2))| ≤ 1 / (2 * Real.sqrt m)
    calc |(x i) * exp (-(m * ‖x‖ ^ 2))|
        = |x i| * exp (-(m * ‖x‖ ^ 2)) := by rw [abs_mul, abs_of_nonneg (le_of_lt (Real.exp_pos _))]
      _ ≤ |x i| * exp (-(m * (x i) ^ 2)) := by
            exact mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (by
                have hco : (x i) ^ 2 ≤ ‖x‖ ^ 2 := by
                  rw [norm_sq_eq_sum_sq]
                  exact Finset.single_le_sum (fun j _ => sq_nonneg (x.ofLp j)) (Finset.mem_univ i)
                exact neg_le_neg (mul_le_mul_of_nonneg_left hco (le_of_lt hm)))) (abs_nonneg (x i))
      _ ≤ 1 / (2 * Real.sqrt m) := abs_mul_exp_neg_mul_sq_le m (x i) hm

/-- The test function is smooth. -/
theorem testF_contDiff (n : ℕ) (i : Fin n) {m : ℝ} (hm : 0 < m) :
    ContDiff ℝ ⊤ (fun x : Vn n => (testF n i m hm) x) := by
  have h : (fun x : Vn n => (testF n i m hm) x) = fun x : Vn n => (x i) * exp (-(m * ‖x‖ ^ 2)) := by
    funext x
    change (x i) * exp (-(m * ‖x‖ ^ 2)) = (x i) * exp (-(m * ‖x‖ ^ 2))
    rfl
  rw [h]
  exact (coordCLM n i).contDiff.mul
    ((contDiff_const.mul (contDiff_norm_sq ℝ)).neg.exp)

/-- **The exact value of the derivative of `K_t * fₘ` at `0`.** For `t, m > 0`,
`fderiv (K_t * fₘ)(0) (e_i) = (4mt+1)^(-(n/2+1))`, computed from the fderiv formula
(`heatConv_fderiv_zero_apply`) and the quadratic Gaussian moment. -/
theorem fderiv_heatConv_testF_coord (n : ℕ) {t m : ℝ} (ht : 0 < t) (hm : 0 < m) (i : Fin n) :
    fderiv ℝ (fun x : Vn n => (heatConv n t (testF n i m hm)) x) 0
        (EuclideanSpace.basisFun (Fin n) ℝ i) = (4 * m * t + 1) ^ (-((n : ℝ) / 2 + 1)) := by
  rw [heatConv_fderiv_zero_apply n ht (testF n i m hm) (EuclideanSpace.basisFun (Fin n) ℝ i)]
  have hinner : ∀ y : Vn n, ⟪y, (EuclideanSpace.basisFun (Fin n) ℝ) i⟫_ℝ = (y i) := by
    intro y
    rw [real_inner_comm, inner_basisFun]
  have htest : ∀ y : Vn n, (testF n i m hm) y = (y i) * exp (-(m * ‖y‖ ^ 2)) := by
    intro y
    change (y i) * exp (-(m * ‖y‖ ^ 2)) = (y i) * exp (-(m * ‖y‖ ^ 2))
    rfl
  have hcongr : (∫ y : Vn n, gaussianKernel n t y * ⟪y, (EuclideanSpace.basisFun (Fin n) ℝ) i⟫_ℝ *
        (testF n i m hm) y) =
      ∫ y : Vn n, gaussianKernel n t y * (y i) * ((y i) * exp (-(m * ‖y‖ ^ 2))) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [hinner y, htest y]
  rw [hcongr]
  have hK : ∀ y : Vn n, gaussianKernel n t y = (4 * π * t) ^ (-(n : ℝ) / 2) * exp (-(‖y‖ ^ 2 / (4 * t))) := by
    intro y
    rw [gaussianKernel_apply]
    ring
  have hfun : ∀ y : Vn n, gaussianKernel n t y * (y i) * ((y i) * exp (-(m * ‖y‖ ^ 2)))
      = (4 * π * t) ^ (-(n : ℝ) / 2) * ((y i) ^ 2 * exp (-((m + 1 / (4 * t)) * ‖y‖ ^ 2))) := by
    intro y
    rw [hK y]
    have hexp : exp (-(‖y‖ ^ 2 / (4 * t))) * exp (-(m * ‖y‖ ^ 2)) = exp (-((m + 1 / (4 * t)) * ‖y‖ ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    calc (4 * π * t) ^ (-(n : ℝ) / 2) * exp (-(‖y‖ ^ 2 / (4 * t))) * (y i) * ((y i) * exp (-(m * ‖y‖ ^ 2)))
        = (4 * π * t) ^ (-(n : ℝ) / 2) * (y i) ^ 2 * (exp (-(‖y‖ ^ 2 / (4 * t))) * exp (-(m * ‖y‖ ^ 2))) := by
            ring
      _ = (4 * π * t) ^ (-(n : ℝ) / 2) * ((y i) ^ 2 * exp (-((m + 1 / (4 * t)) * ‖y‖ ^ 2))) := by
            rw [hexp]
            ring
  have hcongr' : (∫ y : Vn n, gaussianKernel n t y * (y i) * ((y i) * exp (-(m * ‖y‖ ^ 2)))) =
      (4 * π * t) ^ (-(n : ℝ) / 2) *
        ∫ y : Vn n, (y i) ^ 2 * exp (-((m + 1 / (4 * t)) * ‖y‖ ^ 2)) := by
    rw [integral_congr_ae (ae_of_all _ hfun)]
    rw [integral_const_mul]
  rw [hcongr']
  rw [integral_exp_neg_mul_normSq_sq_coord n (b := m + 1 / (4 * t)) (by positivity) i]
  simpa [mul_assoc] using kernelMoment_const n ht hm

/-! ## 9. The derivative-loss barrier -/

/-- **The derivative-loss barrier, discharged.** There is no constant `C` bounding
`‖fderiv (K_t * f)(0)‖` by `C ‖f‖` uniformly over `t > 0` and smooth bounded `f`: the test
functions `fₘ` have `‖fₘ‖ ≤ 1/(2√m)` while `‖fderiv (K_{1/m} fₘ)(0)‖ ≥ 5^(-(n/2+1))`
independently of `m`. -/
theorem derivativeLossBarrier_holds (n : ℕ) (hn : 0 < n) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (_ht : 0 < t) (f : BCFn n)
      (_hf : Differentiable ℝ (fun x : EuclideanSpace ℝ (Fin n) => f x)),
      ‖fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => (heatConv n t f) x) 0‖ ≤ C * ‖f‖ := by
  rintro ⟨C, hC0, hC⟩
  let i : Fin n := ⟨0, hn⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, C ^ 2 * (5 : ℝ) ^ (n + 2) / 4 < (m : ℝ) :=
    exists_nat_gt (C ^ 2 * (5 : ℝ) ^ (n + 2) / 4)
  have hm0 : 0 < m := by
    have hnn : (0 : ℝ) ≤ C ^ 2 * (5 : ℝ) ^ (n + 2) / 4 := by positivity
    have : (0 : ℝ) < (m : ℝ) := lt_of_le_of_lt hnn hm
    exact_mod_cast this
  let t : ℝ := 1 / (m : ℝ)
  have ht : 0 < t := by
    dsimp [t]
    positivity
  let f : BCFn n := testF n i (m : ℝ) (by exact_mod_cast hm0)
  have hf : Differentiable ℝ (fun x : Vn n => f x) := by
    dsimp [f]
    exact (testF_contDiff n i (by exact_mod_cast hm0)).differentiable (by decide)
  have hCapplied := hC t ht f hf
  have hfbound : ‖f‖ ≤ 1 / (2 * Real.sqrt (m : ℝ)) := by
    dsimp [f]
    exact testF_norm_le n i (by exact_mod_cast hm0)
  have hvalue : fderiv ℝ (fun x : Vn n => (heatConv n t f) x) 0
      (EuclideanSpace.basisFun (Fin n) ℝ i) = (5 : ℝ) ^ (-((n : ℝ) / 2 + 1)) := by
    dsimp [f]
    have h := fderiv_heatConv_testF_coord n (t := t) (m := (m : ℝ)) ht (by exact_mod_cast hm0) i
    rw [h]
    congr 1
    dsimp [t]
    have hmne : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hm0)
    field_simp [hmne]
    ring
  have hpos : (0 : ℝ) < (5 : ℝ) ^ (-((n : ℝ) / 2 + 1)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hnormvalue : ‖fderiv ℝ (fun x : Vn n => (heatConv n t f) x) 0
      (EuclideanSpace.basisFun (Fin n) ℝ i)‖ = (5 : ℝ) ^ (-((n : ℝ) / 2 + 1)) := by
    rw [hvalue, Real.norm_eq_abs, abs_of_nonneg hpos.le]
  have hlow : (5 : ℝ) ^ (-((n : ℝ) / 2 + 1)) ≤ ‖fderiv ℝ (fun x : Vn n => (heatConv n t f) x) 0‖ := by
    rw [← hnormvalue]
    have hle := ContinuousLinearMap.le_opNorm
      (fderiv ℝ (fun x : Vn n => (heatConv n t f) x) 0) (EuclideanSpace.basisFun (Fin n) ℝ i)
    simpa [(EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i, mul_one] using hle
  have hupper : ‖fderiv ℝ (fun x : Vn n => (heatConv n t f) x) 0‖ ≤ C * (1 / (2 * Real.sqrt (m : ℝ))) :=
    le_trans hCapplied (mul_le_mul_of_nonneg_left hfbound hC0)
  have hcontra : (5 : ℝ) ^ (-((n : ℝ) / 2 + 1)) ≤ C * (1 / (2 * Real.sqrt (m : ℝ))) :=
    le_trans hlow hupper
  -- the strict converse from m > C² 5^(n+2) / 4
  have hsqrt : C * (5 : ℝ) ^ ((n : ℝ) / 2 + 1) / 2 < Real.sqrt (m : ℝ) := by
    have h1 : Real.sqrt (C ^ 2 * (5 : ℝ) ^ (n + 2) / 4) < Real.sqrt (m : ℝ) :=
      Real.sqrt_lt_sqrt (by positivity : 0 ≤ C ^ 2 * (5 : ℝ) ^ (n + 2) / 4) hm
    have hval : Real.sqrt (C ^ 2 * (5 : ℝ) ^ (n + 2) / 4) = C * (5 : ℝ) ^ ((n : ℝ) / 2 + 1) / 2 := by
      rw [Real.sqrt_div (by positivity : 0 ≤ C ^ 2 * (5 : ℝ) ^ (n + 2)), Real.sqrt_mul (sq_nonneg C),
        Real.sqrt_sq_eq_abs, abs_of_nonneg hC0]
      rw [show Real.sqrt (4 : ℝ) = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (5 : ℝ) (n + 2),
        ← Real.rpow_mul (by norm_num : 0 ≤ (5 : ℝ))]
      rw [show (((n + 2 : ℕ) : ℝ) * (1 / 2 : ℝ)) = (n : ℝ) / 2 + 1 by norm_num [Nat.cast_add]; ring]
    rwa [hval] at h1
  have hstrict : C * (1 / (2 * Real.sqrt (m : ℝ))) < (5 : ℝ) ^ (-((n : ℝ) / 2 + 1)) := by
    have h2 : C * (5 : ℝ) ^ ((n : ℝ) / 2 + 1) < 2 * Real.sqrt (m : ℝ) := by linarith
    have hsqrtpos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm0)
    have hdiv : C * (5 : ℝ) ^ ((n : ℝ) / 2 + 1) / (2 * Real.sqrt (m : ℝ)) < 1 := by
      rw [div_lt_one (mul_pos zero_lt_two hsqrtpos)]
      exact h2
    have hpow : (5 : ℝ) ^ ((n : ℝ) / 2 + 1) * (5 : ℝ) ^ (-((n : ℝ) / 2 + 1)) = 1 := by
      rw [← Real.rpow_add (by norm_num : 0 < (5 : ℝ))]
      rw [show (n : ℝ) / 2 + 1 + (-((n : ℝ) / 2 + 1)) = 0 by ring]
      exact Real.rpow_zero 5
    have hmul : C * (1 / (2 * Real.sqrt (m : ℝ))) *
        ((5 : ℝ) ^ ((n : ℝ) / 2 + 1) * (5 : ℝ) ^ (-((n : ℝ) / 2 + 1))) <
        (5 : ℝ) ^ (-((n : ℝ) / 2 + 1)) := by
      have hmul' : (C * (5 : ℝ) ^ ((n : ℝ) / 2 + 1) / (2 * Real.sqrt (m : ℝ))) *
          (5 : ℝ) ^ (-((n : ℝ) / 2 + 1)) < 1 * (5 : ℝ) ^ (-((n : ℝ) / 2 + 1)) :=
        mul_lt_mul_of_pos_right hdiv
          (Real.rpow_pos_of_pos (by norm_num) (-((n : ℝ) / 2 + 1)))
      rwa [show (C * (5 : ℝ) ^ ((n : ℝ) / 2 + 1) / (2 * Real.sqrt (m : ℝ))) *
            (5 : ℝ) ^ (-((n : ℝ) / 2 + 1))
          = C * (1 / (2 * Real.sqrt (m : ℝ))) *
              ((5 : ℝ) ^ ((n : ℝ) / 2 + 1) * (5 : ℝ) ^ (-((n : ℝ) / 2 + 1))) by
        field_simp, one_mul] at hmul'
    rw [hpow, mul_one] at hmul
    exact hmul
  exact (not_le_of_gt hstrict) hcontra

end Poincare.D12.ParabolicLocal
