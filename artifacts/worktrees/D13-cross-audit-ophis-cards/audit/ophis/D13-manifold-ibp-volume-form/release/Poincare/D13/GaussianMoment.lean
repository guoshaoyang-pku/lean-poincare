/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (Gaussian moments)

# Gaussian moments on the chart `Vec 2`

The F-functional of the backward Gaussian needs the second moment
`∫_{Vec 2} S(x) ρ_τ(x) dx = 4τ` (equivalently `∫_{Vec 2} S e^{-bS} = π/b²`).
The pinned mathlib (`7974e751be`) has the Gaussian integral `∫ e^{-b‖x‖²}` but no second
moment. This module proves it:

* `integral_sq_mul_exp_neg_mul_sq_Ioi` / `integral_sq_mul_exp_neg_mul_sq` — the
  one-dimensional second moment `∫_ℝ x² e^{-b x²} = (2b)⁻¹ √(π/b)`, from the explicit
  primitive `x ↦ -(2b)⁻¹ x e^{-b x²}` and
  `integral_Ioi_of_hasDerivAt_of_tendsto'` + `integral_gaussian_Ioi`;
* `integral_exp_neg_mul_radSq`, `integral_radSq_mul_exp_neg_mul_radSq` — the two-dimensional
  normalization and second moment on `Vec 2 = Fin 2 → ℝ`, by Fubini through the
  measure-preserving equivalence `MeasurableEquiv.finTwoArrow`;
* `integrable_radSq_mul_exp_neg_mul_radSq`, `integrable_exp_neg_mul_radSq` — the matching
  integrability statements;
* `integral_gaussDensity`, `integral_radSq_mul_gaussDensity` — `∫ ρ_τ = 1` and
  `∫ S ρ_τ = 4τ` for the backward Gaussian density.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.HeatBridge

open scoped BigOperators Topology

noncomputable section

open MeasureTheory Filter Set

namespace Poincare.D13.GaussianMoment

open Poincare.D12.VolumeIBP
open Poincare.D13.EuclideanChart
open Poincare.D13.EuclideanChart.ChartMetric
open Poincare.D13.HeatBridge

/-! ## The one-dimensional second moment -/

/-- The Gaussian profile `x ↦ x² e^{-b x²}` has the primitive
`x ↦ -(2b)⁻¹ x e^{-b x²}`. -/
lemma hasDerivAt_sq_mul_exp_neg_mul_sq (b x : ℝ) (hb : b ≠ 0) :
    HasDerivAt (fun y : ℝ => -(2 * b)⁻¹ * (y * Real.exp (-b * y ^ 2)))
      (x ^ 2 * Real.exp (-b * x ^ 2) - (2 * b)⁻¹ * Real.exp (-b * x ^ 2)) x := by
  have hx2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-b * y ^ 2))
      (Real.exp (-b * x ^ 2) * (-b * (2 * x))) x := (hx2.const_mul (-b)).exp
  have hmul := (hasDerivAt_id x).mul hexp
  have hfin := hmul.const_mul (-(2 * b)⁻¹)
  rw [show x ^ 2 * Real.exp (-b * x ^ 2) - (2 * b)⁻¹ * Real.exp (-b * x ^ 2)
      = (-(2 * b)⁻¹) * (1 * Real.exp (-b * x ^ 2) +
          x * (Real.exp (-b * x ^ 2) * (-b * (2 * x)))) by
    field_simp
    ring]
  exact hfin

/-- `x e^{-b x²} → 0` at `+∞`. -/
lemma tendsto_mul_exp_neg_mul_sq_atTop (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => x * Real.exp (-b * x ^ 2)) Filter.atTop (𝓝 0) := by
  have h1 : (fun x : ℝ => Real.exp (-b * x ^ 2)) =o[Filter.atTop]
      (fun x : ℝ => Real.exp (-x)) :=
    exp_neg_mul_sq_isLittleO_exp_neg hb
  have h2 : (fun x : ℝ => x * Real.exp (-b * x ^ 2)) =o[Filter.atTop]
      (fun x : ℝ => x * Real.exp (-x)) := by
    simpa [mul_comm] using
      h1.mul_isBigO (Asymptotics.isBigO_refl (fun x : ℝ => x) Filter.atTop)
  have h3 : Tendsto (fun x : ℝ => x * Real.exp (-x)) Filter.atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  exact h2.isBigO.trans_tendsto h3

/-- **One-dimensional second moment on the half-line.**
`∫_{x>0} x² e^{-b x²} = (2b)⁻¹ · √(π/b)/2` for `b > 0`. -/
lemma integral_sq_mul_exp_neg_mul_sq_Ioi (b : ℝ) (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-b * x ^ 2) =
      (2 * b)⁻¹ * (Real.sqrt (Real.pi / b) / 2) := by
  have hIntA : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-b * x ^ 2)) (Ioi 0) := by
    refine ((integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)).congr ?_).integrableOn
    filter_upwards with x
    norm_num [Real.rpow_natCast]
  have hIntB : IntegrableOn (fun x : ℝ => Real.exp (-b * x ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq hb).integrableOn
  have hInt : IntegrableOn
      (fun x : ℝ => x ^ 2 * Real.exp (-b * x ^ 2) - (2 * b)⁻¹ * Real.exp (-b * x ^ 2))
      (Ioi 0) := hIntA.sub (hIntB.const_mul _)
  have hlim : Tendsto (fun y : ℝ => -(2 * b)⁻¹ * (y * Real.exp (-b * y ^ 2))) atTop (𝓝 0) := by
    simpa using (tendsto_mul_exp_neg_mul_sq_atTop b hb).const_mul (-(2 * b)⁻¹)
  have hfund := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun x _ => hasDerivAt_sq_mul_exp_neg_mul_sq b x (ne_of_gt hb)) hInt hlim
  rw [integral_sub hIntA (hIntB.const_mul _), integral_const_mul, integral_gaussian_Ioi b]
    at hfund
  have hzero : (0 : ℝ) - -(2 * b)⁻¹ * (0 * Real.exp (-b * 0 ^ 2)) = 0 := by ring
  rw [hzero] at hfund
  linarith only [hfund]

/-- **One-dimensional second moment.** `∫_ℝ x² e^{-b x²} = (2b)⁻¹ √(π/b)` for `b > 0`. -/
lemma integral_sq_mul_exp_neg_mul_sq (b : ℝ) (hb : 0 < b) :
    ∫ x : ℝ, x ^ 2 * Real.exp (-b * x ^ 2) = (2 * b)⁻¹ * Real.sqrt (Real.pi / b) := by
  have hIntA : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-b * x ^ 2)) := by
    refine (integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)).congr ?_
    filter_upwards with x
    norm_num [Real.rpow_natCast]
  have hEven : ∫ x in Iic (0 : ℝ), x ^ 2 * Real.exp (-b * x ^ 2) =
      ∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-b * x ^ 2) := by
    have h := integral_comp_neg_Ioi (0 : ℝ) (fun x : ℝ => x ^ 2 * Real.exp (-b * x ^ 2))
    rw [show (-(0 : ℝ)) = 0 by ring] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [neg_sq]
  have hsum := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hIntA
  rw [compl_Ioi] at hsum
  rw [← hsum, hEven, integral_sq_mul_exp_neg_mul_sq_Ioi b hb]
  rw [← Real.mul_self_sqrt (div_nonneg Real.pi_pos.le hb.le)]
  ring

/-! ## Two-dimensional moments on `Vec 2` -/

/-- Transfer of a `Vec 2` integral to `ℝ × ℝ` through `finTwoArrow`. -/
lemma integral_vec_two_eq_prod (g : ℝ × ℝ → ℝ) :
    ∫ x : Vec 2, g (MeasurableEquiv.finTwoArrow x) = ∫ p : ℝ × ℝ, g p :=
  (volume_preserving_finTwoArrow ℝ).integral_comp
    MeasurableEquiv.finTwoArrow.measurableEmbedding g

/-- The chart squared radius in `finTwoArrow` coordinates. -/
lemma radSq_eq_finTwoArrow (x : Vec 2) :
    radSq x = (MeasurableEquiv.finTwoArrow x).1 ^ 2 + (MeasurableEquiv.finTwoArrow x).2 ^ 2 := by
  rw [MeasurableEquiv.finTwoArrow_apply]
  unfold radSq
  rw [Fin.sum_univ_two]

/-- **Two-dimensional Gaussian normalization on the chart.**
`∫_{Vec 2} e^{-b S(x)} dx = π/b`. -/
lemma integral_exp_neg_mul_radSq (b : ℝ) (hb : 0 < b) :
    ∫ x : Vec 2, Real.exp (-b * radSq x) = Real.pi / b := by
  have hfun : (fun x : Vec 2 => Real.exp (-b * radSq x)) =
      fun x => Real.exp (-b * ((MeasurableEquiv.finTwoArrow x).1 ^ 2 +
        (MeasurableEquiv.finTwoArrow x).2 ^ 2)) := by
    funext x
    rw [radSq_eq_finTwoArrow]
  rw [hfun]
  rw [show (∫ x : Vec 2, Real.exp (-b * ((MeasurableEquiv.finTwoArrow x).1 ^ 2 +
        (MeasurableEquiv.finTwoArrow x).2 ^ 2)))
      = ∫ p : ℝ × ℝ, Real.exp (-b * (p.1 ^ 2 + p.2 ^ 2)) from
    integral_vec_two_eq_prod (fun p : ℝ × ℝ => Real.exp (-b * (p.1 ^ 2 + p.2 ^ 2)))]
  have hprod : ∫ p : ℝ × ℝ, Real.exp (-b * p.1 ^ 2) * Real.exp (-b * p.2 ^ 2)
      ∂(volume.prod volume) = Real.pi / b := by
    rw [integral_prod_mul (μ := volume) (ν := volume)
      (f := fun x : ℝ => Real.exp (-b * x ^ 2))
      (g := fun y : ℝ => Real.exp (-b * y ^ 2)), integral_gaussian]
    rw [← sq, Real.sq_sqrt (div_nonneg Real.pi_pos.le hb.le)]
  have hpoint : (fun p : ℝ × ℝ => Real.exp (-b * (p.1 ^ 2 + p.2 ^ 2))) =
      fun p => Real.exp (-b * p.1 ^ 2) * Real.exp (-b * p.2 ^ 2) := by
    funext p
    rw [← Real.exp_add]
    ring_nf
  rw [hpoint]
  exact hprod

/-- **Two-dimensional second moment on the chart.**
`∫_{Vec 2} S(x) e^{-b S(x)} dx = π/b²`. -/
lemma integral_radSq_mul_exp_neg_mul_radSq (b : ℝ) (hb : 0 < b) :
    ∫ x : Vec 2, radSq x * Real.exp (-b * radSq x) = Real.pi / b ^ 2 := by
  have hA : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-b * x ^ 2)) volume := by
    refine (integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)).congr ?_
    filter_upwards with x
    norm_num [Real.rpow_natCast]
  have hInt1 : Integrable (fun p : ℝ × ℝ =>
      (p.1 ^ 2 * Real.exp (-b * p.1 ^ 2)) * Real.exp (-b * p.2 ^ 2))
      (volume.prod volume) := hA.mul_prod (integrable_exp_neg_mul_sq hb)
  have hInt2 : Integrable (fun p : ℝ × ℝ =>
      Real.exp (-b * p.1 ^ 2) * (p.2 ^ 2 * Real.exp (-b * p.2 ^ 2)))
      (volume.prod volume) := (integrable_exp_neg_mul_sq hb).mul_prod hA
  have hfun : (fun x : Vec 2 => radSq x * Real.exp (-b * radSq x)) =
      fun x => ((MeasurableEquiv.finTwoArrow x).1 ^ 2 +
        (MeasurableEquiv.finTwoArrow x).2 ^ 2) *
        Real.exp (-b * ((MeasurableEquiv.finTwoArrow x).1 ^ 2 +
          (MeasurableEquiv.finTwoArrow x).2 ^ 2)) := by
    funext x
    rw [radSq_eq_finTwoArrow]
  rw [hfun]
  rw [show (∫ x : Vec 2, ((MeasurableEquiv.finTwoArrow x).1 ^ 2 +
        (MeasurableEquiv.finTwoArrow x).2 ^ 2) *
        Real.exp (-b * ((MeasurableEquiv.finTwoArrow x).1 ^ 2 +
          (MeasurableEquiv.finTwoArrow x).2 ^ 2)))
      = ∫ p : ℝ × ℝ, (p.1 ^ 2 + p.2 ^ 2) * Real.exp (-b * (p.1 ^ 2 + p.2 ^ 2)) from
    integral_vec_two_eq_prod (fun p : ℝ × ℝ =>
      (p.1 ^ 2 + p.2 ^ 2) * Real.exp (-b * (p.1 ^ 2 + p.2 ^ 2)))]
  have hsum : (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) * Real.exp (-b * (p.1 ^ 2 + p.2 ^ 2))) =
      fun p => (p.1 ^ 2 * Real.exp (-b * p.1 ^ 2)) * Real.exp (-b * p.2 ^ 2) +
        Real.exp (-b * p.1 ^ 2) * (p.2 ^ 2 * Real.exp (-b * p.2 ^ 2)) := by
    funext p
    rw [show -b * (p.1 ^ 2 + p.2 ^ 2) = -b * p.1 ^ 2 + -b * p.2 ^ 2 by ring, Real.exp_add]
    ring
  rw [hsum]
  have hprod : ∫ p : ℝ × ℝ, ((p.1 ^ 2 * Real.exp (-b * p.1 ^ 2)) * Real.exp (-b * p.2 ^ 2) +
        Real.exp (-b * p.1 ^ 2) * (p.2 ^ 2 * Real.exp (-b * p.2 ^ 2))) ∂(volume.prod volume) =
      Real.pi / b ^ 2 := by
    rw [integral_add hInt1 hInt2,
      integral_prod_mul (μ := volume) (ν := volume)
        (f := fun x : ℝ => x ^ 2 * Real.exp (-b * x ^ 2))
        (g := fun y : ℝ => Real.exp (-b * y ^ 2)),
      integral_prod_mul (μ := volume) (ν := volume)
        (f := fun x : ℝ => Real.exp (-b * x ^ 2))
        (g := fun y : ℝ => y ^ 2 * Real.exp (-b * y ^ 2)),
      integral_sq_mul_exp_neg_mul_sq b hb, integral_gaussian]
    rw [show (2 * b)⁻¹ * √(Real.pi / b) * √(Real.pi / b) +
          √(Real.pi / b) * ((2 * b)⁻¹ * √(Real.pi / b)) =
        2 * ((2 * b)⁻¹ * (√(Real.pi / b) * √(Real.pi / b))) by ring,
      Real.mul_self_sqrt (div_nonneg Real.pi_pos.le hb.le)]
    field_simp
  exact hprod

/-- Integrability transfer from `ℝ × ℝ` to `Vec 2` through `finTwoArrow`. -/
lemma integrable_vec_two_iff (g : ℝ × ℝ → ℝ) :
    Integrable (fun x : Vec 2 => g (MeasurableEquiv.finTwoArrow x)) volume ↔
      Integrable g volume :=
  (volume_preserving_finTwoArrow ℝ).integrable_comp_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding

/-- Integrability version of the two-dimensional second moment. -/
lemma integrable_radSq_mul_exp_neg_mul_radSq (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : Vec 2 => radSq x * Real.exp (-b * radSq x)) volume := by
  have hA : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-b * x ^ 2)) volume := by
    refine (integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)).congr ?_
    filter_upwards with x
    norm_num [Real.rpow_natCast]
  have h1 : Integrable (fun p : ℝ × ℝ =>
      (p.1 ^ 2 * Real.exp (-b * p.1 ^ 2)) * Real.exp (-b * p.2 ^ 2))
      (volume.prod volume) := hA.mul_prod (integrable_exp_neg_mul_sq hb)
  have h2 : Integrable (fun p : ℝ × ℝ =>
      Real.exp (-b * p.1 ^ 2) * (p.2 ^ 2 * Real.exp (-b * p.2 ^ 2)))
      (volume.prod volume) := (integrable_exp_neg_mul_sq hb).mul_prod hA
  have hsplit : (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) *
      Real.exp (-b * (p.1 ^ 2 + p.2 ^ 2))) =
      fun p => (p.1 ^ 2 * Real.exp (-b * p.1 ^ 2)) * Real.exp (-b * p.2 ^ 2) +
        Real.exp (-b * p.1 ^ 2) * (p.2 ^ 2 * Real.exp (-b * p.2 ^ 2)) := by
    funext p
    rw [show -b * (p.1 ^ 2 + p.2 ^ 2) = -b * p.1 ^ 2 + -b * p.2 ^ 2 by ring, Real.exp_add]
    ring
  have hprod : Integrable (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) *
      Real.exp (-b * (p.1 ^ 2 + p.2 ^ 2))) (volume.prod volume) := by
    rw [hsplit]
    exact h1.add h2
  have hg := (integrable_vec_two_iff (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) *
    Real.exp (-b * (p.1 ^ 2 + p.2 ^ 2)))).mpr hprod
  refine hg.congr ?_
  exact Filter.Eventually.of_forall fun x => by simp [radSq_eq_finTwoArrow]

/-- Integrability version of the two-dimensional normalization. -/
lemma integrable_exp_neg_mul_radSq (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : Vec 2 => Real.exp (-b * radSq x)) volume := by
  have hprod : Integrable (fun p : ℝ × ℝ =>
      Real.exp (-b * p.1 ^ 2) * Real.exp (-b * p.2 ^ 2)) (volume.prod volume) :=
    (integrable_exp_neg_mul_sq hb).mul_prod (integrable_exp_neg_mul_sq hb)
  have hEq : (fun p : ℝ × ℝ => Real.exp (-b * p.1 ^ 2) * Real.exp (-b * p.2 ^ 2)) =
      fun p => Real.exp (-b * (p.1 ^ 2 + p.2 ^ 2)) := by
    funext p
    rw [show -b * (p.1 ^ 2 + p.2 ^ 2) = -b * p.1 ^ 2 + -b * p.2 ^ 2 by ring,
      Real.exp_add]
  rw [hEq] at hprod
  have hg := (integrable_vec_two_iff (fun p : ℝ × ℝ =>
    Real.exp (-b * (p.1 ^ 2 + p.2 ^ 2)))).mpr hprod
  refine hg.congr ?_
  exact Filter.Eventually.of_forall fun x => by simp [radSq_eq_finTwoArrow]

/-! ## The backward Gaussian density: normalization and second moment -/

/-- **Normalization of the backward Gaussian**: `∫ ρ_τ = 1` on `Vec 2`. -/
lemma integral_gaussDensity (τ : ℝ) (hτ : 0 < τ) :
    ∫ x : Vec 2, gaussDensity τ x = 1 := by
  have hb : 0 < 1 / (4 * τ) := by positivity
  have hfun : (fun x : Vec 2 => gaussDensity τ x) =
      fun x => (4 * Real.pi * τ)⁻¹ * Real.exp (-(1 / (4 * τ)) * radSq x) := rfl
  rw [hfun, integral_const_mul, integral_exp_neg_mul_radSq (1 / (4 * τ)) hb]
  field_simp

/-- **Second moment of the backward Gaussian**: `∫ S ρ_τ = 4τ` on `Vec 2`. -/
lemma integral_radSq_mul_gaussDensity (τ : ℝ) (hτ : 0 < τ) :
    ∫ x : Vec 2, radSq x * gaussDensity τ x = 4 * τ := by
  have hb : 0 < 1 / (4 * τ) := by positivity
  have hfun : (fun x : Vec 2 => radSq x * gaussDensity τ x) =
      fun x => (4 * Real.pi * τ)⁻¹ *
        (radSq x * Real.exp (-(1 / (4 * τ)) * radSq x)) := by
    funext x
    unfold gaussDensity
    ring
  rw [hfun, integral_const_mul, integral_radSq_mul_exp_neg_mul_radSq (1 / (4 * τ)) hb]
  field_simp

end Poincare.D13.GaussianMoment

/-! ## Axiom audit -/

#print axioms Poincare.D13.GaussianMoment.hasDerivAt_sq_mul_exp_neg_mul_sq
#print axioms Poincare.D13.GaussianMoment.tendsto_mul_exp_neg_mul_sq_atTop
#print axioms Poincare.D13.GaussianMoment.integral_sq_mul_exp_neg_mul_sq_Ioi
#print axioms Poincare.D13.GaussianMoment.integral_sq_mul_exp_neg_mul_sq
#print axioms Poincare.D13.GaussianMoment.integral_vec_two_eq_prod
#print axioms Poincare.D13.GaussianMoment.radSq_eq_finTwoArrow
#print axioms Poincare.D13.GaussianMoment.integral_exp_neg_mul_radSq
#print axioms Poincare.D13.GaussianMoment.integral_radSq_mul_exp_neg_mul_radSq
#print axioms Poincare.D13.GaussianMoment.integrable_vec_two_iff
#print axioms Poincare.D13.GaussianMoment.integrable_radSq_mul_exp_neg_mul_radSq
#print axioms Poincare.D13.GaussianMoment.integrable_exp_neg_mul_radSq
#print axioms Poincare.D13.GaussianMoment.integral_gaussDensity
#print axioms Poincare.D13.GaussianMoment.integral_radSq_mul_gaussDensity
