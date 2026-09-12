/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare longrun D12-parabolic-local-existence

# Gaussian heat convolution on bounded continuous functions of ℝⁿ

The spatial Banach space of the flat semilinear model is

  `BCFn n = (EuclideanSpace ℝ (Fin n)) →ᵇ ℝ`,

the bounded continuous functions on `ℝⁿ` with the uniform norm. For every
`t > 0` the heat operator is the convolution with the explicit D10 Gaussian
kernel

  `(K_t * f)(x) = ∫ y, gaussianKernel n t (x - y) * f y`.

This file proves the analytic input needed by the abstract Duhamel machinery
(`Duhamel.lean` / `MildExistence.lean`):

* the integrand is integrable for every bounded continuous `f` (comparison with
  the kernel mass, D10 `gaussianKernel_integral`);
* the convolution is a bounded continuous function;
* the **L∞ contraction bound** `‖K_t * f‖∞ ≤ ‖f‖∞`;
* positivity: nonnegative data stay nonnegative;
* constants are preserved (mass one, checked non-vacuity);
* `K_t *` is an ℝ-linear operator on `BCFn n` with operator norm `≤ 1`.

Everything here is proved from the D10 kernel theorems; no `sorry`, `axiom`,
`unsafe`, `native_decide` or `proof_wanted` is used.
-/
module

public import Poincare.D10.HeatKernelEuclidean.Mass
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

noncomputable section

open MeasureTheory Real
open scoped Topology InnerProductSpace BoundedContinuousFunction

namespace Poincare.D12.ParabolicLocal

open Poincare.D10.HeatKernelEuclidean

/-! ## The spatial Banach space of the flat model -/

/-- The spatial Banach space of the flat model: bounded continuous functions on `ℝⁿ` with the
uniform (supremum) norm. -/
abbrev BCFn (n : ℕ) := (EuclideanSpace ℝ (Fin n)) →ᵇ ℝ

/-! ## The heat convolution -/

/-- The heat-kernel convolution of a bounded continuous function, pointwise in the space
variable: `∫ y, gaussianKernel n t (x - y) * f y`. -/
def heatConvPoint (n : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (f : BCFn n) : ℝ :=
  ∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * f y

/-- The Gaussian heat kernel `y ↦ gaussianKernel n t y` is integrable for `t > 0`; this follows
from the D10 mass theorem `gaussianKernel_integral` by `integrable_of_integral_eq_one`. -/
theorem gaussianKernel_integrable (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n t y) volume :=
  integrable_of_integral_eq_one (gaussianKernel_integral n ht)

/-- The translated kernel `y ↦ gaussianKernel n t (x - y)` is integrable for `t > 0`, for every
base point `x` (translation invariance of Lebesgue measure plus the mass theorem). -/
theorem gaussianKernel_sub_integrable (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (x - y)) volume := by
  have h : (∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) ∂volume) = 1 := by
    rw [integral_sub_left_eq_self (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z)
      volume x, gaussianKernel_integral n ht]
  exact integrable_of_integral_eq_one h

/-- The heat-convolution integrand `y ↦ gaussianKernel n t (x - y) * f y` is integrable for every
bounded continuous `f`: it is dominated by `‖f‖ * gaussianKernel n t (x - y)`, which has finite
mass. -/
theorem heatConvIntegrand_integrable (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BCFn n)
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (x - y) * f y) volume := by
  refine ((gaussianKernel_sub_integrable n ht x).const_mul ‖f‖).mono ?_ ?_
  · have hcont : Continuous fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (x - y) * f y :=
      ((continuous_gaussianKernel n).comp (continuous_const.sub continuous_id)).mul f.continuous
    exact hcont.measurable.aestronglyMeasurable
  · filter_upwards with y
    calc ‖gaussianKernel n t (x - y) * f y‖
        = gaussianKernel n t (x - y) * ‖f y‖ := by
            rw [norm_mul, Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le (x - y))]
      _ ≤ gaussianKernel n t (x - y) * ‖f‖ :=
          mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm f y)
            (gaussianKernel_nonneg n ht.le (x - y))
      _ = ‖f‖ * gaussianKernel n t (x - y) := by ring
      _ = ‖‖f‖ * gaussianKernel n t (x - y)‖ := by
          rw [norm_mul, Real.norm_of_nonneg (norm_nonneg f),
            Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le (x - y))]

/-- **Pointwise L∞ contraction**: for `t > 0` and bounded continuous `f`,
`|(K_t * f)(x)| ≤ ‖f‖∞` for every `x`. The proof is the mass normalisation of the kernel:
`∫ |K f| ≤ ‖f‖ ∫ K = ‖f‖`. -/
theorem heatConvPoint_le_norm (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BCFn n)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖heatConvPoint n t x f‖ ≤ ‖f‖ := by
  have hInt := heatConvIntegrand_integrable n ht f x
  have hKint := gaussianKernel_sub_integrable n ht x
  calc ‖heatConvPoint n t x f‖
      = ‖∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * f y‖ := by
          rw [heatConvPoint]
    _ ≤ ∫ y : EuclideanSpace ℝ (Fin n), ‖gaussianKernel n t (x - y) * f y‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y : EuclideanSpace ℝ (Fin n), ‖f‖ * gaussianKernel n t (x - y) := by
        apply integral_mono hInt.norm (hKint.const_mul ‖f‖)
        intro y
        calc ‖gaussianKernel n t (x - y) * f y‖
            = gaussianKernel n t (x - y) * ‖f y‖ := by
                rw [norm_mul, Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le (x - y))]
          _ ≤ gaussianKernel n t (x - y) * ‖f‖ :=
              mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm f y)
                (gaussianKernel_nonneg n ht.le (x - y))
          _ = ‖f‖ * gaussianKernel n t (x - y) := by ring
    _ = ‖f‖ * ∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) := by
        rw [integral_const_mul]
    _ = ‖f‖ := by
        rw [integral_sub_left_eq_self (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z)
          volume x, gaussianKernel_integral n ht, mul_one]

/-- **Continuity in the space variable**: `x ↦ (K_t * f)(x)` is continuous. By translation
invariance the convolution equals `∫ y, gaussianKernel n t y * f (x - y)`; continuity of the
latter in `x` is mathlib's dominated convergence with the `x`-independent bound
`‖f‖ * gaussianKernel n t y`. -/
theorem continuous_heatConvPoint (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BCFn n) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) => heatConvPoint n t x f) := by
  have htrans : (fun x : EuclideanSpace ℝ (Fin n) => heatConvPoint n t x f)
      = fun x => ∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t y * f (x - y) := by
    funext x
    rw [heatConvPoint]
    have hg : (∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * f y)
        = ∫ y : EuclideanSpace ℝ (Fin n),
            (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z * f (x - z)) (x - y) := by
      apply integral_congr_ae
      filter_upwards with y
      congr 1
      abel_nf
    rw [hg, integral_sub_left_eq_self (fun z : EuclideanSpace ℝ (Fin n) =>
      gaussianKernel n t z * f (x - z)) volume x]
  rw [htrans]
  exact continuous_of_dominated
    (fun x : EuclideanSpace ℝ (Fin n) => by
      have hcont : Continuous fun y : EuclideanSpace ℝ (Fin n) =>
          gaussianKernel n t y * f (x - y) :=
        (continuous_gaussianKernel n).mul
          (f.continuous.comp (continuous_const.sub continuous_id))
      exact hcont.measurable.aestronglyMeasurable)
    (fun x => by
      filter_upwards with y
      rw [norm_mul, Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le y)]
      exact (mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm f (x - y))
        (gaussianKernel_nonneg n ht.le y)).trans_eq (mul_comm _ _))
    ((gaussianKernel_integrable n ht).const_mul ‖f‖)
    (by
      filter_upwards with y
      have h1 : Continuous fun x : EuclideanSpace ℝ (Fin n) => f (x - y) :=
        f.continuous.comp (continuous_id.sub continuous_const)
      exact (continuous_const :
          Continuous fun _ : EuclideanSpace ℝ (Fin n) => gaussianKernel n t y).mul h1)

/-! ## The heat operator as a bounded linear map on `BCFn n` -/

/-- The positive-time heat convolution as an element of `BCFn n`, using the pointwise bound
`|(K_t * f)(x)| ≤ ‖f‖` and the continuity of `x ↦ (K_t * f)(x)`. -/
def heatConvPos (n : ℕ) (t : ℝ) (ht : 0 < t) (f : BCFn n) : BCFn n :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x : EuclideanSpace ℝ (Fin n) => heatConvPoint n t x f, continuous_heatConvPoint n ht f⟩
    (2 * ‖f‖) (by
      intro x y
      have hx := heatConvPoint_le_norm n ht f x
      have hy := heatConvPoint_le_norm n ht f y
      calc dist (heatConvPoint n t x f) (heatConvPoint n t y f)
          ≤ dist (heatConvPoint n t x f) 0 + dist 0 (heatConvPoint n t y f) :=
              dist_triangle _ _ _
        _ = ‖heatConvPoint n t x f‖ + ‖heatConvPoint n t y f‖ := by
            rw [dist_zero_right, dist_zero_left]
        _ ≤ ‖f‖ + ‖f‖ := add_le_add hx hy
        _ = 2 * ‖f‖ := by ring)

@[simp]
theorem heatConvPos_apply (n : ℕ) (t : ℝ) (ht : 0 < t) (f : BCFn n)
    (x : EuclideanSpace ℝ (Fin n)) :
    (heatConvPos n t ht f) x = heatConvPoint n t x f := by
  simp [heatConvPos, heatConvPoint]

/-- The heat operator on `BCFn n`, truncated at nonpositive times: it is the honest kernel
convolution for `t > 0` and vanishes for `t ≤ 0`. (The truncation is only used to make the
operator total; every analytic statement below is about positive times.) -/
def heatConv (n : ℕ) (t : ℝ) (f : BCFn n) : BCFn n :=
  if ht : 0 < t then heatConvPos n t ht f else 0

theorem heatConv_of_pos (n : ℕ) (t : ℝ) (ht : 0 < t) (f : BCFn n) :
    heatConv n t f = heatConvPos n t ht f := by
  simp [heatConv, ht]

theorem heatConv_of_nonpos (n : ℕ) (t : ℝ) (ht : t ≤ 0) (f : BCFn n) :
    heatConv n t f = 0 := by
  simp [heatConv, not_lt.mpr ht]

/-- The pointwise value of the heat convolution at positive times. -/
theorem heatConv_apply (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BCFn n)
    (x : EuclideanSpace ℝ (Fin n)) :
    (heatConv n t f) x = ∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * f y := by
  rw [heatConv_of_pos n t ht, heatConvPos_apply, heatConvPoint]

/-- **L∞ contraction of the heat operator** at positive times: `‖K_t * f‖∞ ≤ ‖f‖∞`. -/
theorem heatConv_norm_le (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BCFn n) :
    ‖heatConv n t f‖ ≤ ‖f‖ := by
  rw [heatConv_of_pos n t ht]
  exact (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr fun x => by
    rw [heatConvPos_apply, heatConvPoint]
    exact heatConvPoint_le_norm n ht f x

/-- **L∞ contraction of the heat operator at every time**: for `t ≤ 0` the truncated operator is
zero, so the bound `‖heatConv n t f‖ ≤ ‖f‖` holds unconditionally. -/
theorem heatConv_norm_le' (n : ℕ) (t : ℝ) (f : BCFn n) :
    ‖heatConv n t f‖ ≤ ‖f‖ := by
  by_cases ht : 0 < t
  · exact heatConv_norm_le n ht f
  · rw [heatConv_of_nonpos n t (not_lt.mp ht) f]
    simpa only [norm_zero] using (norm_nonneg f)

/-- **Positivity**: the heat convolution preserves pointwise nonnegativity for `t > 0`. -/
theorem heatConv_nonneg (n : ℕ) {t : ℝ} (ht : 0 < t) {f : BCFn n} (hf : ∀ x, 0 ≤ f x) :
    ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ (heatConv n t f) x := by
  intro x
  rw [heatConv_apply n ht]
  exact integral_nonneg fun y => mul_nonneg (gaussianKernel_nonneg n ht.le (x - y)) (hf y)

/-- **Constants are preserved** (mass one, checked): `K_t * c = c` for every real constant `c`
and every `t > 0`. This is the non-vacuity check that the contraction bound is attained with
equality on constant data. -/
theorem heatConv_const (n : ℕ) {t : ℝ} (ht : 0 < t) (c : ℝ) :
    heatConv n t (BoundedContinuousFunction.const (EuclideanSpace ℝ (Fin n)) c)
      = BoundedContinuousFunction.const (EuclideanSpace ℝ (Fin n)) c := by
  apply BoundedContinuousFunction.ext
  intro x
  rw [heatConv_apply n ht]
  calc (∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * c)
      = ∫ y : EuclideanSpace ℝ (Fin n), c * gaussianKernel n t (x - y) := by
          apply integral_congr_ae
          filter_upwards with y
          ring
    _ = c * ∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) := by
          rw [integral_const_mul c (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (x - y))]
    _ = c := by
          rw [integral_sub_left_eq_self (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z)
            volume x, gaussianKernel_integral n ht, mul_one]

/-! ## Linearity -/

/-- The heat operator `K_t *` is ℝ-linear on `BCFn n` (at positive times by linearity of the
Bochner integral, trivially at nonpositive times). -/
def heatOperator (n : ℕ) (t : ℝ) : BCFn n →ₗ[ℝ] BCFn n where
  toFun := heatConv n t
  map_add' := by
    intro f g
    by_cases ht : 0 < t
    · apply BoundedContinuousFunction.ext
      intro x
      rw [heatConv_of_pos n t ht, heatConv_of_pos n t ht, heatConv_of_pos n t ht]
      simp [heatConvPoint]
      calc ∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * (f y + g y)
          = ∫ y : EuclideanSpace ℝ (Fin n),
              gaussianKernel n t (x - y) * f y + gaussianKernel n t (x - y) * g y := by
              apply integral_congr_ae
              filter_upwards with y
              ring
        _ = (∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * f y)
              + ∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * g y := by
              exact integral_add (heatConvIntegrand_integrable n ht f x)
                (heatConvIntegrand_integrable n ht g x)
    · simp [heatConv, ht]
  map_smul' := by
    intro a f
    by_cases ht : 0 < t
    · apply BoundedContinuousFunction.ext
      intro x
      rw [heatConv_of_pos n t ht, heatConv_of_pos n t ht]
      simp [heatConvPoint]
      calc (∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * (a • f y))
          = ∫ y : EuclideanSpace ℝ (Fin n), a * (gaussianKernel n t (x - y) * f y) := by
              apply integral_congr_ae
              filter_upwards with y
              rw [smul_eq_mul]
              ring
        _ = a • ∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * f y := by
              rw [integral_const_mul a
                (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (x - y) * f y), smul_eq_mul]
        _ = a • heatConvPoint n t x f := by
              rw [heatConvPoint]
    · simp [heatConv, ht]

@[simp]
theorem heatOperator_apply (n : ℕ) (t : ℝ) (f : BCFn n) :
    heatOperator n t f = heatConv n t f := rfl

/-- The heat operator as a continuous linear map with operator norm at most `1`. -/
def heatOperatorCLM (n : ℕ) (t : ℝ) : BCFn n →L[ℝ] BCFn n :=
  LinearMap.mkContinuous (heatOperator n t) 1 fun f => by
    simpa only [heatOperator_apply, one_mul] using heatConv_norm_le' n t f

/-- **Operator-norm bound**: `‖K_t *‖ ≤ 1` for every time `t`. -/
theorem heatOperatorCLM_norm_le (n : ℕ) (t : ℝ) : ‖heatOperatorCLM n t‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num : (0 : ℝ) ≤ 1) _

end Poincare.D12.ParabolicLocal
