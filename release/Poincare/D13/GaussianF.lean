/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (Gaussian F-functional)

# The `F`-functional of the backward Gaussian and its time derivative

On the chart `Vec 2`, with the backward Gaussian density `ρ_τ(x) = (4πτ)⁻¹ e^{-S(x)/4τ}`
and the potential `f_τ = S/(4τ)` (`S = radSq`), the Perelman `F`-functional is

`F(τ) = ∫ (R + |∇f_τ|²) ρ_τ = ∫ S/(4τ²) · ρ_τ = 1/τ`,

and the pointwise dissipation density is `|Ric + ∇²f_τ|² = 1/(2τ²)`, so

`FDissipation(τ) = 2 ∫ |Ric + ∇²f_τ|² ρ_τ = 1/τ²`.

This module proves both integral identities and the resulting time derivative along
`τ(t) = τ₀ - t` on the finite lifetime `t < τ₀`:

* `integral_gradSq_mul_gaussDensity` — `F = 1/τ`;
* `integral_FDissipation_gauss` — `FDissipation = 1/τ²`;
* `hasDerivAt_gaussianF` — `d/dt F(τ₀ - t) = 1/(τ₀ - t)² = FDissipation` (the
  `FDerivativeStatement` content of blocker `I4` in explicit form);
* `contDiffOn_gaussianF` — `C¹` regularity of `t ↦ 1/(τ₀ - t)` on `[0, t₁]`, `t₁ < τ₀`.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.GaussianMoment

open scoped BigOperators Topology

noncomputable section

open MeasureTheory Filter Set

namespace Poincare.D13.GaussianF

open Poincare.D12.VolumeIBP
open Poincare.D13.EuclideanChart
open Poincare.D13.EuclideanChart.ChartMetric
open Poincare.D13.HeatBridge
open Poincare.D13.GaussianMoment

/-- **The Gaussian `F`-functional is `1/τ`**: `∫ S/(4τ²) · ρ_τ = 1/τ`. -/
theorem integral_gradSq_mul_gaussDensity (τ : ℝ) (hτ : 0 < τ) :
    ∫ x : Vec 2, (radSq x / (4 * τ ^ 2)) * gaussDensity τ x = 1 / τ := by
  rw [show (fun x : Vec 2 => (radSq x / (4 * τ ^ 2)) * gaussDensity τ x) =
      fun x => (4 * τ ^ 2)⁻¹ * (radSq x * gaussDensity τ x) by
    funext x
    ring]
  rw [integral_const_mul, integral_radSq_mul_gaussDensity τ hτ]
  field_simp

/-- **The Gaussian dissipation is `1/τ²`**: `2 ∫ |∇²f_τ|² ρ_τ = 1/τ²` for the
Hessian norm `|∇²f_τ| = 1/(τ√2)`. -/
theorem integral_FDissipation_gauss (τ : ℝ) (hτ : 0 < τ) :
    ∫ x : Vec 2, 2 * (1 / (τ * Real.sqrt 2)) ^ 2 * gaussDensity τ x = 1 / τ ^ 2 := by
  have hsq : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  rw [show (fun x : Vec 2 => 2 * (1 / (τ * Real.sqrt 2)) ^ 2 * gaussDensity τ x) =
      fun x => (1 / τ ^ 2) * gaussDensity τ x by
    funext x
    rw [div_pow, one_pow, mul_pow, hsq]
    field_simp]
  rw [integral_const_mul, integral_gaussDensity τ hτ]
  ring

/-- The explicit Gaussian functional `t ↦ F(τ₀ - t) = 1/(τ₀ - t)` on the finite lifetime. -/
theorem hasDerivAt_gaussianF (τ0 s : ℝ) (hs : 0 < s) (hs1 : s < τ0) :
    HasDerivAt (fun t : ℝ => 1 / (τ0 - t)) (1 / (τ0 - s) ^ 2) s := by
  have hτs : τ0 - s ≠ 0 := ne_of_gt (sub_pos.mpr hs1)
  have h1 : HasDerivAt (fun t : ℝ => τ0 - t) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub τ0
  have h2 : HasDerivAt (fun t : ℝ => (τ0 - t)⁻¹) (-(-1) / (τ0 - s) ^ 2) s :=
    h1.inv hτs
  have h3 : (-(-1) / (τ0 - s) ^ 2 : ℝ) = 1 / (τ0 - s) ^ 2 := by ring
  rw [h3] at h2
  have hfun : (fun t : ℝ => 1 / (τ0 - t)) = fun t : ℝ => (τ0 - t)⁻¹ := by
    funext t
    rw [one_div]
  rw [hfun]
  exact h2

/-- **The `F`-derivative of the backward Gaussian** (explicit form): along `τ(t) = τ₀ - t`,
`d/dt ∫ S/(4τ²) ρ_τ = 1/τ² = FDissipation` on `(0, τ₀)`. -/
theorem hasDerivAt_gaussianF_integral (τ0 s : ℝ) (hs : 0 < s) (hs1 : s < τ0) :
    HasDerivAt
      (fun t : ℝ => ∫ x : Vec 2, (radSq x / (4 * (τ0 - t) ^ 2)) * gaussDensity (τ0 - t) x)
      (∫ x : Vec 2, 2 * (1 / ((τ0 - s) * Real.sqrt 2)) ^ 2 * gaussDensity (τ0 - s) x) s := by
  have hτs : 0 < τ0 - s := sub_pos.mpr hs1
  have hderiv := hasDerivAt_gaussianF τ0 s hs hs1
  rw [integral_FDissipation_gauss (τ0 - s) hτs]
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_id continuous_const).mem_nhds hs1] with t ht
  exact integral_gradSq_mul_gaussDensity (τ0 - t) (sub_pos.mpr ht)

/-- **`C¹` regularity of the Gaussian functional on `[0, t₁]`** for `t₁ < τ₀`. -/
theorem contDiffOn_gaussianF (τ0 t1 : ℝ) (ht1 : t1 < τ0) :
    ContDiffOn ℝ 1 (fun t : ℝ => 1 / (τ0 - t)) (Icc 0 t1) := by
  have hne : ∀ t ∈ Icc (0 : ℝ) t1, τ0 - t ≠ 0 := by
    intro t ht
    exact ne_of_gt (sub_pos.mpr (lt_of_le_of_lt ht.2 ht1))
  have hnum : ContDiffOn ℝ 1 (fun _ : ℝ => (1 : ℝ)) (Icc (0 : ℝ) t1) := contDiffOn_const
  have hden : ContDiffOn ℝ 1 (fun t : ℝ => τ0 - t) (Icc (0 : ℝ) t1) :=
    contDiffOn_const.sub contDiffOn_id
  exact hnum.div hden hne

end Poincare.D13.GaussianF

/-! ## Axiom audit -/

#print axioms Poincare.D13.GaussianF.integral_gradSq_mul_gaussDensity
#print axioms Poincare.D13.GaussianF.integral_FDissipation_gauss
#print axioms Poincare.D13.GaussianF.hasDerivAt_gaussianF
#print axioms Poincare.D13.GaussianF.hasDerivAt_gaussianF_integral
#print axioms Poincare.D13.GaussianF.contDiffOn_gaussianF
