/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D11-heat-kernel-manifold-bridge)
-/

import Poincare.D11.HeatKernelBridge.EuclideanInstance
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D11.HeatKernelBridge.InitialCondition

**D11 heat-kernel bridge, part 4: the weak (distributional) initial condition in the flat case.**

The D7 interface asks that `∫ y, K x y t * f y → f x` as `t → 0⁺` for *every* continuous test
function `f`. For the explicit Euclidean kernel this literal field is not provable: the Bochner
integral of a non-integrable integrand is `0`, so a continuous test function growing faster than
every Gaussian makes the integral vanish identically. The correct flat statement keeps the
integrability of the test function (automatic for continuous compactly supported functions):

`Continuous f → Integrable f volume → Tendsto (fun t => ∫ y, flatKernel n x y t * f y) (𝓝[>] 0) (𝓝 (f x))`.

The proof is the standard approximation-of-identity argument, formalised through mathlib's peak
function theorem `tendsto_integral_peak_smul_of_integrable_of_tendsto`:

* translate the integral to `∫ z, gaussianKernel n t z * f (x - z)`;
* the Gaussian is a peak function: it is nonnegative, has mass one on a finite-measure ball, and
  decays uniformly away from the origin;
* the reflected test function `z ↦ f (x - z)` is continuous at `0` and integrable.

The analytic inputs are the elementary limits

* `tendsto_rpow_neg_mul_exp_neg_div`: `t ^ (-n/2) * exp (-c/t) → 0` as `t → 0⁺` (from
  `Real.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` after `t ↦ t⁻¹`),
* `tendsto_prefactor_mul_exp_neg_div`: the same with the full prefactor `(4 π t) ^ (-n/2)`,
* `tendsto_setIntegral_compl_ball_gaussianKernel`: the Gaussian tail on the complement of a ball
  tends to zero, obtained by dominating it with `exp (-‖z‖²/(8t))` and evaluating the Gaussian
  integral of D10.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter Real
open scoped Topology InnerProductSpace Laplacian RealInnerProductSpace

namespace Poincare.D11.HeatKernelBridge

open Poincare.D10.HeatKernelEuclidean

/-! ## Elementary limits at `t → 0⁺` -/

/-- `t ^ (-n/2) * exp (-c/t) → 0` as `t → 0⁺`, for `c > 0`. -/
theorem tendsto_rpow_neg_mul_exp_neg_div (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => t ^ (-((n : ℝ) / 2)) * Real.exp (-c / t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hcomp := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((n : ℝ) / 2) c hc).comp
    (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
  refine Tendsto.congr' ?_ hcomp
  filter_upwards [self_mem_nhdsWithin] with t ht
  change (t⁻¹) ^ ((n : ℝ) / 2) * Real.exp (-c * t⁻¹)
    = t ^ (-((n : ℝ) / 2)) * Real.exp (-c / t)
  rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
  congr 1

/-- `exp (-c/t) → 0` as `t → 0⁺`, for `c > 0`. -/
theorem tendsto_exp_neg_div {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => Real.exp (-c / t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  simpa using tendsto_rpow_neg_mul_exp_neg_div 0 hc

/-- The full Gaussian prefactor times `exp (-c/t)` tends to `0` as `t → 0⁺`, for `c > 0`. -/
theorem tendsto_prefactor_mul_exp_neg_div (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-c / t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := (tendsto_rpow_neg_mul_exp_neg_div n hc).const_mul ((4 * π) ^ (-(n : ℝ) / 2))
  have h' : Tendsto (fun t : ℝ => (4 * π) ^ (-(n : ℝ) / 2) *
      (t ^ (-((n : ℝ) / 2)) * Real.exp (-c / t))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using h
  refine Tendsto.congr' ?_ h'
  filter_upwards [self_mem_nhdsWithin] with t ht
  conv_rhs =>
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 * π) ht.le,
      show (-(n : ℝ)) / 2 = -((n : ℝ) / 2) by ring]
  ring

/-! ## Uniform decay of the Gaussian away from the origin -/

/-- **Uniform decay away from the origin.** On the complement of any open neighbourhood of `0` the
Gaussian kernel converges uniformly to `0` as `t → 0⁺`. -/
theorem tendstoUniformlyOn_gaussianKernel_compl (n : ℕ)
    {u : Set (EuclideanSpace ℝ (Fin n))} (hu : IsOpen u)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ u) :
    TendstoUniformlyOn (fun t : ℝ => fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z)
      0 (𝓝[>] (0 : ℝ)) uᶜ := by
  obtain ⟨δ, hδpos, hδu⟩ := Metric.isOpen_iff.mp hu 0 h0
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlim := tendsto_prefactor_mul_exp_neg_div n (c := δ ^ 2 / 4) (by positivity)
  filter_upwards [hlim.eventually (Iio_mem_nhds hε), self_mem_nhdsWithin] with t htbound ht
  have htpos : (0 : ℝ) < t := ht
  intro z hz
  have hzδ : δ ≤ ‖z‖ := by
    by_contra h
    exact hz (hδu (by simpa [Metric.mem_ball, dist_eq_norm] using lt_of_not_ge h))
  have hsq : δ ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hδpos.le hzδ 2
  have hexp : Real.exp (-‖z‖ ^ 2 / (4 * t)) ≤ Real.exp (-(δ ^ 2 / 4) / t) := by
    apply Real.exp_le_exp.mpr
    have ht' : (0 : ℝ) < t := ht
    rw [neg_div, neg_div, neg_le_neg_iff]
    field_simp
    nlinarith
  have hK : gaussianKernel n t z
      ≤ (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-(δ ^ 2 / 4) / t) := by
    rw [gaussianKernel_apply]
    exact mul_le_mul_of_nonneg_left hexp
      (Real.rpow_nonneg (le_of_lt (by positivity : (0 : ℝ) < 4 * π * t)) _)
  rw [Real.dist_eq, Pi.zero_apply, zero_sub, abs_neg,
    abs_of_nonneg (gaussianKernel_nonneg n ht.le z)]
  exact lt_of_le_of_lt hK htbound

/-! ## The Gaussian tail on the complement of a ball -/

/-- Integrability of the Gaussian `z ↦ exp (-a ‖z‖²)` from the D10 Gaussian integral. -/
theorem integrable_exp_neg_mul_norm_sq {n : ℕ} {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) => Real.exp (-a * ‖z‖ ^ 2)) volume :=
  Integrable.of_integral_ne_zero (by
    rw [integral_exp_neg_mul_norm_sq ha, finrank_euclideanSpace_fin_real]
    positivity)

/-- The constant `(2 : ℝ) ^ (n/2)` coming from the Gaussian integral over the whole space:
`(4 π t) ^ (-n/2) * (π / (1/(8t))) ^ (n/2) = 2 ^ (n/2)`. -/
theorem prefactor_mul_eight (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (4 * π * t) ^ (-(n : ℝ) / 2) * (π / (1 / (8 * t))) ^ ((n : ℝ) / 2)
      = (2 : ℝ) ^ ((n : ℝ) / 2) := by
  have h4 : (0 : ℝ) < 4 * π * t := by positivity
  have h8 : (0 : ℝ) < 8 * π * t := by positivity
  have hratio : π / (1 / (8 * t)) = 8 * π * t := by field_simp
  rw [hratio, show (-(n : ℝ)) / 2 = -((n : ℝ) / 2) by ring, Real.rpow_neg h4.le]
  rw [show ((4 * π * t) ^ ((n : ℝ) / 2))⁻¹ * (8 * π * t) ^ ((n : ℝ) / 2)
      = (8 * π * t) ^ ((n : ℝ) / 2) / (4 * π * t) ^ ((n : ℝ) / 2) by ring]
  rw [← Real.div_rpow h8.le h4.le]
  congr 1
  field_simp
  ring

/-- **Gaussian tail bound.** On the complement of the ball of radius `R` the Gaussian kernel is
dominated by `2 ^ (n/2) * exp (-(R²/8)/t)`, uniformly in the space variable. -/
theorem setIntegral_compl_ball_gaussianKernel_le (n : ℕ) {R t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    ∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ, gaussianKernel n t z
      ≤ (2 : ℝ) ^ ((n : ℝ) / 2) * Real.exp (-(R ^ 2 / 8) / t) := by
  have hIntK : Integrable (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z) volume :=
    integrable_of_integral_eq_one (gaussianKernel_integral n ht)
  have ha : (0 : ℝ) < 1 / (8 * t) := by positivity
  have hIntG : Integrable
      (fun z : EuclideanSpace ℝ (Fin n) => Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2)) volume :=
    integrable_exp_neg_mul_norm_sq ha
  have hmeas : MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ :=
    measurableSet_ball.compl
  have hmono : ∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ, gaussianKernel n t z
      ≤ ∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ,
          ((4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-(R ^ 2 / 8) / t)) *
            Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2) := by
    refine setIntegral_mono_on hIntK.integrableOn (hIntG.const_mul _).integrableOn hmeas ?_
    intro z hz
    have hzR : R ≤ ‖z‖ := by
      by_contra h
      exact hz (by simpa [Metric.mem_ball, dist_eq_norm] using lt_of_not_ge h)
    have hsq : R ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hR.le hzR 2
    have hexp : -‖z‖ ^ 2 / (4 * t)
        ≤ -(R ^ 2 / 8) / t + -(1 / (8 * t)) * ‖z‖ ^ 2 := by
      have ht' : (0 : ℝ) < t := ht
      field_simp
      nlinarith
    have hexp' : Real.exp (-‖z‖ ^ 2 / (4 * t))
        ≤ Real.exp (-(R ^ 2 / 8) / t) * Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hexp
    rw [gaussianKernel_apply]
    calc (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (4 * t))
        ≤ (4 * π * t) ^ (-(n : ℝ) / 2) *
            (Real.exp (-(R ^ 2 / 8) / t) * Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hexp' (Real.rpow_nonneg (by positivity) _)
      _ = (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-(R ^ 2 / 8) / t) *
            Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2) := by ring
  calc ∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ, gaussianKernel n t z
      ≤ ∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ,
          ((4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-(R ^ 2 / 8) / t)) *
            Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2) := hmono
    _ ≤ ∫ z, ((4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-(R ^ 2 / 8) / t)) *
            Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2) :=
        setIntegral_le_integral (hIntG.const_mul _)
          (Eventually.of_forall fun z => mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
            (Real.exp_nonneg _)) (Real.exp_nonneg _))
    _ = ((4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-(R ^ 2 / 8) / t)) *
          ∫ z, Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2) := by
        rw [integral_const_mul]
    _ = ((4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-(R ^ 2 / 8) / t)) *
          (π / (1 / (8 * t))) ^ ((n : ℝ) / 2) := by
        rw [integral_exp_neg_mul_norm_sq ha, finrank_euclideanSpace_fin_real]
    _ = (2 : ℝ) ^ ((n : ℝ) / 2) * Real.exp (-(R ^ 2 / 8) / t) := by
        rw [mul_right_comm, prefactor_mul_eight n ht]

/-- **The Gaussian tail tends to zero.** On the complement of a ball of positive radius the integral
of the Gaussian kernel tends to `0` as `t → 0⁺`. -/
theorem tendsto_setIntegral_compl_ball_gaussianKernel (n : ℕ) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun t : ℝ =>
        ∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ, gaussianKernel n t z)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hc : 0 < R ^ 2 / 8 := by positivity
  have hlim : Tendsto (fun t : ℝ => (2 : ℝ) ^ ((n : ℝ) / 2) * Real.exp (-(R ^ 2 / 8) / t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_exp_neg_div hc).const_mul ((2 : ℝ) ^ ((n : ℝ) / 2))
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact integral_nonneg fun z => gaussianKernel_nonneg n ht.le z
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact setIntegral_compl_ball_gaussianKernel_le n hR ht

/-- **The Gaussian mass on a ball tends to one.** -/
theorem tendsto_setIntegral_ball_gaussianKernel (n : ℕ) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun t : ℝ => ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R,
        gaussianKernel n t z) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have htail := tendsto_setIntegral_compl_ball_gaussianKernel n hR
  have hcongr : (fun t : ℝ => ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R,
        gaussianKernel n t z)
      =ᶠ[𝓝[>] (0 : ℝ)]
      fun t : ℝ => 1 - ∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ,
        gaussianKernel n t z := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hInt : Integrable (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z) volume :=
      integrable_of_integral_eq_one (gaussianKernel_integral n ht)
    have hsum := integral_add_compl (μ := volume) (s := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
      (f := fun z => gaussianKernel n t z) measurableSet_ball hInt
    rw [gaussianKernel_integral n ht] at hsum
    linarith
  have h1 : Tendsto (fun t : ℝ => 1 - ∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ,
        gaussianKernel n t z) (𝓝[>] (0 : ℝ)) (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub htail
  rw [sub_zero] at h1
  exact Tendsto.congr' hcongr.symm h1

/-! ## The weak initial condition -/

/-- **The weak (distributional) initial condition for the explicit Euclidean heat kernel.** For
every continuous integrable test function `f` (in particular for every continuous compactly
supported one), the explicit D10 kernel reproduces `f` as `t → 0⁺`:
`∫ y, flatKernel n x y t * f y → f x`. -/
theorem flatKernel_tendsto_integral (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f) (hfi : Integrable f volume) :
    Tendsto (fun t : ℝ => ∫ y, flatKernel n x y t * f y) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  have hpeak : Tendsto (fun t : ℝ => ∫ z, gaussianKernel n t z * f (x - z))
      (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
    have h := tendsto_integral_peak_smul_of_integrable_of_tendsto
      (μ := volume) (l := 𝓝[>] (0 : ℝ)) (x₀ := (0 : EuclideanSpace ℝ (Fin n)))
      (a := f x) (φ := fun t z => gaussianKernel n t z) (g := fun z => f (x - z))
      (t := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      measurableSet_ball (Metric.ball_mem_nhds 0 zero_lt_one)
      (measure_ball_ne_top (μ := volume) (x := (0 : EuclideanSpace ℝ (Fin n))) (r := 1))
      (by
        filter_upwards [self_mem_nhdsWithin] with t ht z
        exact gaussianKernel_nonneg n ht.le z)
      (fun u hu hu0 => tendstoUniformlyOn_gaussianKernel_compl n hu hu0)
      (tendsto_setIntegral_ball_gaussianKernel n zero_lt_one)
      (Eventually.of_forall fun t => (continuous_gaussianKernel n).aestronglyMeasurable)
      (hfi.comp_sub_left x)
      (by
        have hcont : Continuous fun z : EuclideanSpace ℝ (Fin n) => f (x - z) :=
          hf.comp (continuous_const.sub continuous_id)
        simpa only [ContinuousAt, sub_zero] using
          hcont.continuousAt (x := (0 : EuclideanSpace ℝ (Fin n))))
    simpa only [smul_eq_mul] using h
  have hInt : (fun t : ℝ => ∫ z, gaussianKernel n t z * f (x - z))
      =ᶠ[𝓝[>] (0 : ℝ)]
      fun t : ℝ => ∫ y, flatKernel n x y t * f y := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hfun : (fun y : EuclideanSpace ℝ (Fin n) => flatKernel n x y t * f y)
        = fun y => (fun z => gaussianKernel n t z * f (x - z)) (x - y) := by
      funext y
      rw [flatKernel_of_pos n x y ht]
      simp
    rw [hfun, integral_sub_left_eq_self (fun z => gaussianKernel n t z * f (x - z)) volume x]
  exact Tendsto.congr' hInt hpeak

/-- **The weak initial condition, compactly supported form.** Continuous compactly supported test
functions are integrable, so the weak initial condition applies to them. -/
theorem flatKernel_tendsto_integral_of_hasCompactSupport (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f) :
    Tendsto (fun t : ℝ => ∫ y, flatKernel n x y t * f y) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) :=
  flatKernel_tendsto_integral n x hf (hf.integrable_of_hasCompactSupport hfs)

/-- **The weak initial condition for the bridge datum.** -/
theorem flatHeatKernelCore_weakInitialCondition (n : ℕ) :
    (flatHeatKernelCore n).WeakInitialCondition := by
  intro x f hf hfi
  exact flatKernel_tendsto_integral n x hf hfi

/-- The bridge datum satisfies the weak initial condition, hence every field of the D7 interface
except the (unprovable for arbitrary continuous test functions) literal pointwise one. -/
theorem flatHeatKernelCore_weakInitialCondition_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f) (hfi : Integrable f volume) :
    Tendsto (fun t : ℝ => ∫ y, (flatHeatKernelCore n).kernel x y t * f y)
      (𝓝[>] (0 : ℝ)) (𝓝 (f x)) :=
  flatHeatKernelCore_weakInitialCondition n x f hf hfi

end Poincare.D11.HeatKernelBridge
