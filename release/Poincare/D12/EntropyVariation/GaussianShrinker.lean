/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-entropy-variation)

# The Gaussian shrinker: a proved nontrivial model of Perelman's F and W

On `X = EuclideanSpace ℝ (Fin n)` with Lebesgue (`volume`), take the flat metric
(`Ric = 0`, `R = 0`) and, for a positive time-scale parameter `τ`, the Gaussian
shrinker data

* `ρ τ x = gaussianKernel n τ x = (4πτ)^{-n/2} exp(-‖x‖²/(4τ))`  — the D10 Euclidean
  heat kernel, the entropy-measure density `u` of Perelman §1–§3;
* `f τ x = ‖x‖² / (4τ)`, `gradSq τ x = ‖x‖² / (4τ²)` (`|∇f|²` for the flat metric);
* `riccHess τ x = n / (4τ²)`  — the pointwise dissipation density
  `|Ric + ∇²f|² = |∇²f|²`, justified below by the explicit Hessian computation
  `∇²f = (1/(2τ)) g` (the field is *not* an opaque assumption).

Proved here:

1. **normalization**: `∫ ρ = 1` (D10 `gaussianKernel_integral`);
2. **the second moment** `∫ ‖x‖² ρ dx = 2nτ`, obtained by differentiating the
   Gaussian integral in its parameter through the general theorem
   `Poincare.D12.EntropyVariation.hasDerivAt_integral_param` — the delivered
   differentiation-under-the-integral theorem is exercised nontrivially;
3. **integrability obligations** for every functional integrand (explicit);
4. **F value**: `F = ∫ (R + |∇f|²) dm = n/(2τ)`, strictly decreasing in `τ`,
   hence *increasing* when `τ = τ₀ - 2t` decreases (the D7 chain's sign);
5. **W value**: `W = τ F + ∫ (f - n) dm = 0` — Perelman's shrinker `W ≡ 0`, the
   equality case of his monotonicity;
6. **the Hessian identity** `∇²f = (1/(2τ)) g` (second Fréchet derivative,
   `iteratedFDeriv_two_shrinkerFpot`), giving
   * `|Ric + ∇²f|² = n/(4τ²)` (the `riccHess` field, justified pointwise), and
   * the W-dissipation density vanishes: `|Ric + ∇²f - g/(2τ)|² ≡ 0`
     (`shrinker_w_dissipation_density_zero`), so `dW/dτ = -2τ ∫ |Ric + ∇²f - g/(2τ)|² dm = 0`
     holds on the model with both sides computed independently;
7. **dissipation values** for both the D3 `FDissipation` and the corrected
   `FDissipationCorrected` (documenting the double-square defect of the D3 definition
   on a model where `riccHess = n/(4τ²) ∉ {0,1}`).

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs
in this file.
-/
import Poincare.D12.EntropyVariation.EntropyDerivative
import Poincare.D10.HeatKernelEuclidean.Mass
import Poincare.D10.HeatKernelEuclidean.HeatEquation
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

open MeasureTheory Real Filter TopologicalSpace Metric Set
open scoped Topology Filter InnerProductSpace RealInnerProductSpace
open Poincare.Longrun.Entropy
open Poincare.D10.HeatKernelEuclidean

namespace Poincare.D12.EntropyVariation

/-- Local alias for the a.e.-version constructor of the filter `Eventually`. -/
theorem eventually_of_forall {α : Type*} {p : α → Prop} {f : Filter α} (hp : ∀ x, p x) :
    ∀ᶠ x in f, p x :=
  Filter.Eventually.of_forall hp

noncomputable section

abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-! ## A small derivative helper -/

/-- `deriv (fun v => -v * c) = -c`, in `HasDerivAt` form. -/
theorem hasDerivAt_neg_mul_const (u c : ℝ) :
    HasDerivAt (fun v : ℝ => -v * c) (-c) u := by
  have h1 : HasDerivAt (fun v : ℝ => -(v * c)) (-(1 * c)) u := ((hasDerivAt_id u).mul_const c).neg
  have h2 : HasDerivAt (fun v : ℝ => -(v * c)) (-c) u := by
    rwa [show -(1 * c) = -c by ring] at h1
  exact h2.congr_of_eventuallyEq (eventually_of_forall (fun v => by ring))

/-! ## Integrability of the multivariate Gaussian -/

/-- The multivariate Gaussian `exp (-a ‖x‖²)` is integrable on `ℝⁿ` for `a > 0`,
obtained from mathlib's complex Gaussian integrability
(`GaussianFourier.integrable_cexp_neg_mul_sq_norm_add`). -/
theorem integrable_exp_neg_mul_normSq (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Euc n => Real.exp (-a * ‖x‖ ^ 2)) := by
  have hb : 0 < ((a : ℂ)).re := by simpa using ha
  have hI : Integrable (fun x : Euc n => Complex.exp (-(a : ℂ) * ‖x‖ ^ 2)) := by
    simpa using
      (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Euc n) (b := (a : ℂ)) hb
        (0 : ℂ) (0 : Euc n))
  have hIre : Integrable (fun x : Euc n => (Complex.exp (-(a : ℂ) * ‖x‖ ^ 2)).re) := hI.re
  have heq : (fun x : Euc n => (Complex.exp (-(a : ℂ) * ‖x‖ ^ 2)).re) =ᵐ[volume]
      fun x : Euc n => Real.exp (-a * ‖x‖ ^ 2) := by
    filter_upwards with x
    rw [Complex.exp_re]
    have hre : (-(a : ℂ) * ‖x‖ ^ 2).re = -a * ‖x‖ ^ 2 := by
      change (-(a : ℂ) * (‖x‖ : ℂ) ^ 2).re = -a * ‖x‖ ^ 2
      rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        ← Complex.ofReal_pow ‖x‖ 2, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have him : (-(a : ℂ) * ‖x‖ ^ 2).im = 0 := by
      change (-(a : ℂ) * (‖x‖ : ℂ) ^ 2).im = 0
      rw [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        ← Complex.ofReal_pow ‖x‖ 2, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hre, him, Real.cos_zero, mul_one]
  exact hIre.congr heq

/-- The Gaussian kernel `gaussianKernel n τ` is integrable for `τ > 0`. -/
theorem integrable_gaussianKernel (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun x : Euc n => gaussianKernel n τ x) := by
  have ha : 0 < 1 / (4 * τ) := by positivity
  refine ((integrable_exp_neg_mul_normSq n ha).const_mul ((4 * π * τ) ^ (-(n : ℝ) / 2))).congr
    (eventually_of_forall fun x => by
      change (4 * π * τ) ^ (-(n : ℝ) / 2) * Real.exp (-(1 / (4 * τ)) * ‖x‖ ^ 2) = gaussianKernel n τ x
      rw [gaussianKernel_apply, exp_part_eq])

/-! ## Pointwise domination lemma -/

/-- For `a > 0`: `‖x‖² exp(-a‖x‖²) ≤ (2/a) exp(-(a/2)‖x‖²)`.  The proof is the
elementary bound `u e^{-u} ≤ 1` for `u ≥ 0` (from mathlib's
`mul_exp_neg_le_exp_neg_one`), applied with `u = (a/2)‖x‖²`. -/
theorem normSq_exp_neg_mul_le (n : ℕ) {a : ℝ} (ha : 0 < a) (x : Euc n) :
    ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2) ≤ (2 / a) * Real.exp (-(a / 2) * ‖x‖ ^ 2) := by
  have hmul : ((a / 2) * ‖x‖ ^ 2) * Real.exp (-((a / 2) * ‖x‖ ^ 2)) ≤ 1 := by
    have := mul_exp_neg_le_exp_neg_one ((a / 2) * ‖x‖ ^ 2)
    have hlt : Real.exp (-(1 : ℝ)) < 1 := by
      have := Real.exp_lt_exp.mpr (show -(1 : ℝ) < 0 by norm_num)
      rwa [Real.exp_zero] at this
    exact this.trans (le_of_lt hlt)
  have h1 : ((a / 2) * ‖x‖ ^ 2) * Real.exp (-a * ‖x‖ ^ 2) ≤ Real.exp (-(a / 2) * ‖x‖ ^ 2) := by
    have hmul' := mul_le_mul_of_nonneg_right hmul (le_of_lt (Real.exp_pos (-(a / 2) * ‖x‖ ^ 2)))
    have hA : ((a / 2) * ‖x‖ ^ 2) * Real.exp (-((a / 2) * ‖x‖ ^ 2)) * Real.exp (-(a / 2) * ‖x‖ ^ 2)
        = ((a / 2) * ‖x‖ ^ 2) * Real.exp (-a * ‖x‖ ^ 2) := by
      rw [mul_assoc ((a / 2) * ‖x‖ ^ 2) (Real.exp (-((a / 2) * ‖x‖ ^ 2))) (Real.exp (-(a / 2) * ‖x‖ ^ 2)),
        ← Real.exp_add]
      congr 1
      field_simp
      ring
    have hB : 1 * Real.exp (-(a / 2) * ‖x‖ ^ 2) = Real.exp (-(a / 2) * ‖x‖ ^ 2) := one_mul _
    rwa [hA, hB] at hmul'
  have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt (by positivity : 0 < 2 / a))
  have hcoef : (2 / a) * ((a / 2) * ‖x‖ ^ 2) = ‖x‖ ^ 2 := by
    field_simp [ha.ne']
  have hreassoc : (2 / a) * (((a / 2) * ‖x‖ ^ 2) * Real.exp (-a * ‖x‖ ^ 2))
      = ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2) := by
    rw [← mul_assoc (2 / a) ((a / 2) * ‖x‖ ^ 2) (Real.exp (-a * ‖x‖ ^ 2)), hcoef]
  rwa [hreassoc] at h2

/-! ## The second moment, by differentiation of the Gaussian integral in its parameter -/

/-- **The second moment of the multivariate Gaussian**, obtained by differentiating
`a ↦ ∫ exp (-a ‖x‖²) dx = (π/a)^{n/2}` through
`Poincare.D12.EntropyVariation.hasDerivAt_integral_param`: this is the delivered
differentiation-under-the-integral theorem, applied with explicit domination
(`normSq_exp_neg_mul_le`) and integrability obligations. -/
theorem integral_normSq_mul_exp_neg_mul (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ x : Euc n, ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2) =
      ((n : ℝ) / (2 * a)) * (π / a) ^ ((n : ℝ) / 2) := by
  let g : ℝ → Euc n → ℝ := fun u x => Real.exp (-u * ‖x‖ ^ 2)
  let g' : ℝ → Euc n → ℝ := fun u x => Real.exp (-u * ‖x‖ ^ 2) * -‖x‖ ^ 2
  let bound : Euc n → ℝ := fun x => (4 / a) * Real.exp (-(a / 4) * ‖x‖ ^ 2)
  let s : Set ℝ := ball a (a / 2)
  have hball : s ∈ 𝓝 a := ball_mem_nhds a (by positivity)
  have hmeas : ∀ᶠ u in 𝓝 a, AEStronglyMeasurable (g u) := by
    filter_upwards with u
    unfold g
    fun_prop
  have hint : Integrable (g a) := by
    unfold g
    exact integrable_exp_neg_mul_normSq n ha
  have hmeas' : AEStronglyMeasurable (g' a) := by
    unfold g'
    fun_prop
  have hderiv : ∀ x : Euc n, ∀ u ∈ s, HasDerivAt (fun v => g v x) (g' u x) u := by
    intro x u hu
    unfold g g'
    have hin : HasDerivAt (fun v : ℝ => -v * ‖x‖ ^ 2) (-‖x‖ ^ 2) u :=
      hasDerivAt_neg_mul_const u (‖x‖ ^ 2)
    exact (Real.hasDerivAt_exp (-u * ‖x‖ ^ 2)).comp u hin
  have hdom : ∀ x : Euc n, ∀ u ∈ s, ‖g' u x‖ ≤ bound x := by
    intro x u hu
    have hua : a / 2 < u := by
      have hthis := (mem_ball.mp hu)
      have habs : |u - a| < a / 2 := by simpa [dist_eq_norm] using hthis
      have : a - a / 2 < u := by
        have := (abs_lt.mp habs).1
        linarith
      linarith [show a - a / 2 = a / 2 by field_simp; ring]
    unfold g' bound
    rw [norm_mul, norm_neg, norm_of_nonneg (Real.exp_nonneg _), norm_of_nonneg (sq_nonneg ‖x‖)]
    have hmono : Real.exp (-u * ‖x‖ ^ 2) ≤ Real.exp (-(a / 2) * ‖x‖ ^ 2) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg (le_of_lt hua)) (sq_nonneg ‖x‖)
    have hstep1 : Real.exp (-u * ‖x‖ ^ 2) * ‖x‖ ^ 2 ≤
        Real.exp (-(a / 2) * ‖x‖ ^ 2) * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hmono (sq_nonneg ‖x‖)
    have hstep2 : Real.exp (-(a / 2) * ‖x‖ ^ 2) * ‖x‖ ^ 2 ≤
        (4 / a) * Real.exp (-(a / 4) * ‖x‖ ^ 2) := by
      have := normSq_exp_neg_mul_le n (by positivity : 0 < a / 2) x
      simpa [mul_comm, mul_left_comm, mul_assoc,
        show 2 / (a / 2) = 4 / a by field_simp [ha.ne']; ring,
        show a / 2 / 2 = a / 4 by field_simp; ring] using this
    exact hstep1.trans hstep2
  have hbound : Integrable bound := by
    unfold bound
    refine ((integrable_exp_neg_mul_normSq n (by positivity : 0 < a / 4)).const_mul (4 / a)).congr
      (eventually_of_forall fun _ => rfl)
  have hmain := hasDerivAt_integral_param (g := g) (g' := g') (bound := bound)
    hball hmeas hint hmeas'
    (eventually_of_forall (by simpa [g, g'] using hderiv))
    (eventually_of_forall (by simpa [g', bound] using hdom)) hbound
  -- The two HasDerivAt statements for the same function force the derivative values to agree.
  have hinv : HasDerivAt (fun u : ℝ => u⁻¹) ((-1 : ℝ) / a ^ 2) a :=
    (hasDerivAt_id a).inv (ne_of_gt ha)
  have hinvcm : HasDerivAt (fun u : ℝ => π * u⁻¹) (π * ((-1 : ℝ) / a ^ 2)) a :=
    hinv.const_mul π
  have hrpow : HasDerivAt (fun u : ℝ => (π * u⁻¹) ^ ((n : ℝ) / 2))
      (π * ((-1 : ℝ) / a ^ 2) * ((n : ℝ) / 2) * (π * a⁻¹) ^ ((n : ℝ) / 2 - 1)) a :=
    hinvcm.rpow_const (Or.inl (ne_of_gt (mul_pos pi_pos (inv_pos.mpr ha))))
  have hval : π * ((-1 : ℝ) / a ^ 2) * ((n : ℝ) / 2) * (π * a⁻¹) ^ ((n : ℝ) / 2 - 1)
      = -((n : ℝ) / (2 * a)) * (π / a) ^ ((n : ℝ) / 2) := by
    rw [show (n : ℝ) / 2 - 1 = (n : ℝ) / 2 + (-1) by ring,
      Real.rpow_add (mul_pos pi_pos (inv_pos.mpr ha)),
      Real.rpow_neg (le_of_lt (mul_pos pi_pos (inv_pos.mpr ha))), Real.rpow_one]
    rw [show (π / a) = π * a⁻¹ by rfl]
    field_simp [ha.ne', ne_of_gt pi_pos]
  have hpi_pre : HasDerivAt (fun u : ℝ => (π * u⁻¹) ^ ((n : ℝ) / 2))
      (-((n : ℝ) / (2 * a)) * (π / a) ^ ((n : ℝ) / 2)) a := by
    rwa [hval] at hrpow
  have hpi : HasDerivAt (fun u : ℝ => (π / u) ^ ((n : ℝ) / 2))
      (-((n : ℝ) / (2 * a)) * (π / a) ^ ((n : ℝ) / 2)) a := by
    exact hpi_pre.congr_of_eventuallyEq (eventually_of_forall (fun _ => rfl))
  have hsame : (fun u : ℝ => ∫ x : Euc n, Real.exp (-u * ‖x‖ ^ 2)) =ᶠ[𝓝 a]
      fun u : ℝ => (π / u) ^ ((n : ℝ) / 2) := by
    filter_upwards [ball_mem_nhds a (by positivity : 0 < a / 2)] with u hu
    have hua : a / 2 < u := by
      have hthis := (mem_ball.mp hu)
      have habs : |u - a| < a / 2 := by simpa [dist_eq_norm] using hthis
      have : a - a / 2 < u := by
        have := (abs_lt.mp habs).1
        linarith
      linarith [show a - a / 2 = a / 2 by field_simp; ring]
    have hu' : 0 < u := lt_trans (by positivity : 0 < a / 2) hua
    rw [integral_exp_neg_mul_norm_sq hu', finrank_euclideanSpace_fin_real]
  have hpi' : HasDerivAt (fun u : ℝ => ∫ x : Euc n, Real.exp (-u * ‖x‖ ^ 2))
      (-((n : ℝ) / (2 * a)) * (π / a) ^ ((n : ℝ) / 2)) a :=
    hpi.congr_of_eventuallyEq hsame
  have hder_eq := hmain.2.unique hpi'
  dsimp only [g'] at hder_eq
  have hcongr : (fun x : Euc n => Real.exp (-a * ‖x‖ ^ 2) * -‖x‖ ^ 2) =
      fun x : Euc n => -(‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2)) := by
    funext x
    ring
  have hder_eq' : -∫ x : Euc n, ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2) =
      -((n : ℝ) / (2 * a)) * (π / a) ^ ((n : ℝ) / 2) := by
    rw [hcongr, integral_neg (fun x : Euc n => ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2))] at hder_eq
    simpa using hder_eq
  rw [neg_eq_iff_eq_neg] at hder_eq'
  simpa using hder_eq'

/-- Integrability of the second moment integrand. -/
theorem integrable_normSq_mul_exp_neg_mul (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Euc n => ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2)) := by
  have hmain := hasDerivAt_integral_param
    (g := fun u x => Real.exp (-u * ‖x‖ ^ 2)) (g' := fun u x => Real.exp (-u * ‖x‖ ^ 2) * -‖x‖ ^ 2)
    (bound := fun x => (4 / a) * Real.exp (-(a / 4) * ‖x‖ ^ 2))
    (ball_mem_nhds a (by positivity : 0 < a / 2))
    (by filter_upwards with u; fun_prop)
    (integrable_exp_neg_mul_normSq n ha)
    (by fun_prop)
    (eventually_of_forall (by
      intro x u hu
      have hin : HasDerivAt (fun v : ℝ => -v * ‖x‖ ^ 2) (-‖x‖ ^ 2) u :=
        hasDerivAt_neg_mul_const u (‖x‖ ^ 2)
      exact (Real.hasDerivAt_exp (-u * ‖x‖ ^ 2)).comp u hin))
    (eventually_of_forall (by
      intro x u hu
      have hua : a / 2 < u := by
        have hthis := (mem_ball.mp hu)
        have habs : |u - a| < a / 2 := by simpa [dist_eq_norm] using hthis
        have : a - a / 2 < u := by
          have := (abs_lt.mp habs).1
          linarith
        linarith [show a - a / 2 = a / 2 by field_simp; ring]
      rw [norm_mul, norm_neg, norm_of_nonneg (Real.exp_nonneg _), norm_of_nonneg (sq_nonneg ‖x‖)]
      have hmono : Real.exp (-u * ‖x‖ ^ 2) ≤ Real.exp (-(a / 2) * ‖x‖ ^ 2) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right (neg_le_neg (le_of_lt hua)) (sq_nonneg ‖x‖)
      have hstep1 : Real.exp (-u * ‖x‖ ^ 2) * ‖x‖ ^ 2 ≤
          Real.exp (-(a / 2) * ‖x‖ ^ 2) * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hmono (sq_nonneg ‖x‖)
      have hstep2 : Real.exp (-(a / 2) * ‖x‖ ^ 2) * ‖x‖ ^ 2 ≤
          (4 / a) * Real.exp (-(a / 4) * ‖x‖ ^ 2) := by
        have := normSq_exp_neg_mul_le n (by positivity : 0 < a / 2) x
        simpa [mul_comm, mul_left_comm, mul_assoc,
          show 2 / (a / 2) = 4 / a by field_simp [ha.ne']; ring,
          show a / 2 / 2 = a / 4 by field_simp; ring] using this
      exact hstep1.trans hstep2))
    (by
      refine ((integrable_exp_neg_mul_normSq n (by positivity : 0 < a / 4)).const_mul (4 / a)).congr
        (eventually_of_forall fun _ => rfl))
  refine hmain.1.neg.congr (eventually_of_forall fun x => by
    change -(Real.exp (-a * ‖x‖ ^ 2) * -‖x‖ ^ 2) = ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2)
    ring)

/-- **The second moment of the Gaussian shrinker density**: `∫ ‖x‖² ρ dx = 2nτ`. -/
theorem integral_normSq_mul_gaussianKernel (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∫ x : Euc n, ‖x‖ ^ 2 * gaussianKernel n τ x = 2 * (n : ℝ) * τ := by
  have ha : 0 < 1 / (4 * τ) := by positivity
  have hbase : 0 < 4 * π * τ := by positivity
  have hfun : (fun x : Euc n => ‖x‖ ^ 2 * gaussianKernel n τ x) =
      fun x : Euc n => (4 * π * τ) ^ (-(n : ℝ) / 2) * (‖x‖ ^ 2 * Real.exp (-(1 / (4 * τ)) * ‖x‖ ^ 2)) := by
    funext x
    rw [gaussianKernel_apply, exp_part_eq]
    ring
  rw [hfun, integral_const_mul ((4 * π * τ) ^ (-(n : ℝ) / 2))
    (fun x : Euc n => ‖x‖ ^ 2 * Real.exp (-(1 / (4 * τ)) * ‖x‖ ^ 2)), integral_normSq_mul_exp_neg_mul n ha]
  have h1 : π / (1 / (4 * τ)) = 4 * π * τ := by
    field_simp
  have h2 : (n : ℝ) / (2 * (1 / (4 * τ))) = 2 * (n : ℝ) * τ := by
    field_simp
    ring
  rw [h1, h2]
  rw [← mul_assoc, mul_comm ((4 * π * τ) ^ (-(n : ℝ) / 2)) (2 * (n : ℝ) * τ), mul_assoc]
  rw [← Real.rpow_add hbase, show -(n : ℝ) / 2 + (n : ℝ) / 2 = 0 by ring, Real.rpow_zero, mul_one]

/-- Integrability of the second-moment integrand against the kernel. -/
theorem integrable_normSq_mul_gaussianKernel (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun x : Euc n => ‖x‖ ^ 2 * gaussianKernel n τ x) := by
  have ha : 0 < 1 / (4 * τ) := by positivity
  refine (((integrable_normSq_mul_exp_neg_mul n ha).const_mul ((4 * π * τ) ^ (-(n : ℝ) / 2))).congr
    (eventually_of_forall fun x => by
      change (4 * π * τ) ^ (-(n : ℝ) / 2) * (‖x‖ ^ 2 * Real.exp (-(1 / (4 * τ)) * ‖x‖ ^ 2))
        = ‖x‖ ^ 2 * gaussianKernel n τ x
      rw [gaussianKernel_apply, exp_part_eq]
      ring))

/-! ## The shrinker entropy datum -/

/-- `|∇f|²` for `f = ‖x‖²/(4τ)` with the flat metric. -/
noncomputable def shrinkerGradSq (τ : ℝ) (x : Euc n) : ℝ := ‖x‖ ^ 2 / (4 * τ ^ 2)

/-- The potential `f = ‖x‖²/(4τ)`. -/
noncomputable def shrinkerFpot (τ : ℝ) (x : Euc n) : ℝ := ‖x‖ ^ 2 / (4 * τ)

/-- The pointwise dissipation density `|Ric + ∇²f|² = n/(4τ²)` of the shrinker
(justified by `shrinker_riccHess_justified`). -/
noncomputable def shrinkerRiccHess (n : ℕ) (τ : ℝ) : ℝ := (n : ℝ) / (4 * τ ^ 2)

/-- **The Gaussian shrinker entropy datum.**  `Ric = 0`, `f = ‖x‖²/(4τ)`,
`ρ = (4πτ)^{-n/2} exp(-‖x‖²/(4τ))` (the normalized Gaussian), coupling `τ > 0`,
dimension `n`.  All integrability fields are discharged by the moment lemmas above. -/
noncomputable def shrinkerEntropyData (n : ℕ) (τ : ℝ) (hτ : 0 < τ) : EntropyData (Euc n) volume where
  R := 0
  gradSq := shrinkerGradSq τ
  f := shrinkerFpot τ
  ρ := gaussianKernel n τ
  τ := τ
  τ_pos := hτ
  n := (n : ℝ)
  riccHess := fun _ => shrinkerRiccHess n τ
  ρ_nonneg := fun x => gaussianKernel_nonneg n (le_of_lt hτ) x
  integrable_F := by
    have hI := integrable_normSq_mul_gaussianKernel n hτ
    exact (hI.const_mul (1 / (4 * τ ^ 2))).congr (eventually_of_forall fun x => by
      change (1 / (4 * τ ^ 2)) * (‖x‖ ^ 2 * gaussianKernel n τ x) = (0 + shrinkerGradSq τ x) * gaussianKernel n τ x
      rw [shrinkerGradSq]
      ring)
  integrable_W := by
    have hK : Integrable (fun x : Euc n => gaussianKernel n τ x) := integrable_gaussianKernel n hτ
    have hNS : Integrable (fun x : Euc n => ‖x‖ ^ 2 * gaussianKernel n τ x) :=
      integrable_normSq_mul_gaussianKernel n hτ
    have hA : Integrable (fun x : Euc n => τ * (shrinkerGradSq τ x * gaussianKernel n τ x)) := by
      exact (hNS.const_mul (τ / (4 * τ ^ 2))).congr (eventually_of_forall fun x => by
        change (τ / (4 * τ ^ 2)) * (‖x‖ ^ 2 * gaussianKernel n τ x) = τ * (shrinkerGradSq τ x * gaussianKernel n τ x)
        rw [shrinkerGradSq]
        ring)
    have hB : Integrable (fun x : Euc n => (shrinkerFpot τ x - (n : ℝ)) * gaussianKernel n τ x) := by
      exact ((hNS.const_mul (1 / (4 * τ))).sub (hK.const_mul (n : ℝ))).congr
        (eventually_of_forall fun x => by
          change (1 / (4 * τ)) * (‖x‖ ^ 2 * gaussianKernel n τ x) - (n : ℝ) * gaussianKernel n τ x
            = (shrinkerFpot τ x - (n : ℝ)) * gaussianKernel n τ x
          rw [shrinkerFpot]
          ring)
    exact (hA.add hB).congr (eventually_of_forall fun x => by
      change τ * (shrinkerGradSq τ x * gaussianKernel n τ x) + (shrinkerFpot τ x - (n : ℝ)) * gaussianKernel n τ x
        = (τ * (shrinkerGradSq τ x + 0) + (shrinkerFpot τ x - (n : ℝ))) * gaussianKernel n τ x
      rw [shrinkerGradSq, shrinkerFpot]
      ring)

/-! ## Normalization and the moment -/

/-- **Normalization**: the entropy measure of the shrinker has total mass `1`. -/
theorem shrinkerEntropyData_mass (n : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    ∫ x : Euc n, (shrinkerEntropyData n τ hτ).ρ x = 1 := by
  unfold shrinkerEntropyData
  exact gaussianKernel_integral n hτ

/-- **The second moment**: `∫ ‖x‖² ρ dx = 2nτ`. -/
theorem shrinkerEntropyData_secondMoment (n : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    ∫ x : Euc n, ‖x‖ ^ 2 * (shrinkerEntropyData n τ hτ).ρ x = 2 * (n : ℝ) * τ := by
  unfold shrinkerEntropyData
  exact integral_normSq_mul_gaussianKernel n hτ

/-! ## F and W values -/

/-- **The F-functional of the shrinker**: `F = n/(2τ)`. -/
theorem shrinkerEntropyData_F_value (n : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    EntropyData.F (shrinkerEntropyData n τ hτ) = (n : ℝ) / (2 * τ) := by
  simp only [EntropyData.F, shrinkerEntropyData]
  change ∫ x : Euc n, (0 + shrinkerGradSq τ x) * gaussianKernel n τ x = (n : ℝ) / (2 * τ)
  have hfun : (fun x : Euc n => (0 + shrinkerGradSq τ x) * gaussianKernel n τ x) =
      fun x : Euc n => (1 / (4 * τ ^ 2)) * (‖x‖ ^ 2 * gaussianKernel n τ x) := by
    funext x
    rw [shrinkerGradSq]
    ring
  rw [hfun, integral_const_mul (1 / (4 * τ ^ 2)) (fun x : Euc n => ‖x‖ ^ 2 * gaussianKernel n τ x),
    integral_normSq_mul_gaussianKernel n hτ]
  field_simp [pow_ne_zero 2 (ne_of_gt hτ)]
  ring

/-- **The W-functional of the shrinker vanishes identically**: `W = τ F + ∫ (f - n) dm = 0`.
This is Perelman's Gaussian shrinker, the equality case `W ≡ 0` of his monotonicity;
both the normalization `∫ ρ = 1` and the moment `∫ ‖x‖²ρ = 2nτ` enter the computation. -/
theorem shrinkerEntropyData_W_value (n : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    EntropyData.W (shrinkerEntropyData n τ hτ) = 0 := by
  rw [EntropyData.W_eq, shrinkerEntropyData_F_value n τ hτ]
  simp only [EntropyData.extra, shrinkerEntropyData]
  have hfun : (fun x : Euc n => (shrinkerFpot τ x - (n : ℝ)) * gaussianKernel n τ x) =
      fun x : Euc n => (1 / (4 * τ)) * (‖x‖ ^ 2 * gaussianKernel n τ x)
        - (n : ℝ) * gaussianKernel n τ x := by
    funext x
    rw [shrinkerFpot]
    ring
  rw [hfun,
    integral_sub ((integrable_normSq_mul_gaussianKernel n hτ).const_mul (1 / (4 * τ)))
      ((integrable_gaussianKernel n hτ).const_mul (n : ℝ)),
    integral_const_mul (1 / (4 * τ)) (fun x : Euc n => ‖x‖ ^ 2 * gaussianKernel n τ x),
    integral_normSq_mul_gaussianKernel n hτ,
    integral_const_mul (n : ℝ) (fun x : Euc n => gaussianKernel n τ x),
    gaussianKernel_integral n hτ]
  field_simp [ne_of_gt hτ]
  ring

/-! ## Dissipation values -/

/-- The D3 `FDissipation` of the shrinker: `n²/(8τ⁴)`.  (Note the extra square:
Perelman's dissipation is `2∫|Ric+∇²f|²dm`, which here equals `n/(2τ²)`; the D3
definition squares the density `n/(4τ²)` once more.) -/
theorem shrinkerEntropyData_FDissipation_value (n : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    EntropyData.FDissipation (shrinkerEntropyData n τ hτ) = (n : ℝ) ^ 2 / (8 * τ ^ 4) := by
  simp only [EntropyData.FDissipation, shrinkerEntropyData, shrinkerRiccHess]
  rw [integral_const_mul (2 * ((n : ℝ) / (4 * τ ^ 2)) ^ 2) (fun x : Euc n => gaussianKernel n τ x),
    gaussianKernel_integral n hτ]
  field_simp [pow_ne_zero 2 (ne_of_gt hτ)]
  ring

/-- The **corrected** dissipation of the shrinker: `n/(2τ²)` — Perelman's
`2∫|Ric+∇²f|²dm` computed exactly. -/
theorem shrinkerEntropyData_FDissipationCorrected_value (n : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    FDissipationCorrected (shrinkerEntropyData n τ hτ) = (n : ℝ) / (2 * τ ^ 2) := by
  simp only [FDissipationCorrected, shrinkerEntropyData, shrinkerRiccHess]
  rw [integral_const_mul (2 * ((n : ℝ) / (4 * τ ^ 2))) (fun x : Euc n => gaussianKernel n τ x),
    gaussianKernel_integral n hτ]
  field_simp [pow_ne_zero 2 (ne_of_gt hτ)]
  ring

/-- On the shrinker the dissipation density is not idempotent in general, so the D3
`FDissipation` genuinely differs from the corrected one: the double-square defect is
witnessed by a nontrivial model, not merely suspected.  (Concrete witness: the
dimension-1 shrinker with `τ ≠ 1/2`, below.) -/
theorem shrinkerEntropyData_FDissipation_ne_corrected_one (τ : ℝ) (hτ : 0 < τ)
    (hτne : τ ≠ 1 / 2) :
    EntropyData.FDissipation (shrinkerEntropyData 1 τ hτ) ≠
      FDissipationCorrected (shrinkerEntropyData 1 τ hτ) := by
  rw [shrinkerEntropyData_FDissipation_value 1 τ hτ, shrinkerEntropyData_FDissipationCorrected_value 1 τ hτ]
  intro h
  have h' : (1 : ℝ) / (8 * τ ^ 4) = 1 / (2 * τ ^ 2) := by simpa using h
  have h1 : 2 * τ ^ 2 = 8 * τ ^ 4 := by
    have hiv : (8 * τ ^ 4)⁻¹ = (2 * τ ^ 2)⁻¹ := by
      rwa [one_div, one_div] at h'
    rw [inv_inj] at hiv
    exact hiv.symm
  have h2 : 1 = 4 * τ ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hτ)]
  have h3 : τ = 1 / 2 ∨ τ = -(1 / 2) := by
    have hsq : τ ^ 2 = (1 / 4 : ℝ) := by nlinarith
    have hhalf : (1 / 4 : ℝ) = (1 / 2) ^ 2 := by norm_num
    exact sq_eq_sq_iff_eq_or_eq_neg.mp (hsq.trans hhalf)
  rcases h3 with h3 | h3
  · exact hτne h3
  · nlinarith [hτ, h3, show (-1 / 2 : ℝ) < 0 by norm_num]

/-! ## The Hessian identity: ∇²f = (1/(2τ)) g -/

/-- The gradient (first Fréchet derivative) of `f = ‖x‖²/(4τ)` is `(1/(2τ)) x`
as a covector: `fderiv f x = (1/(2τ)) • innerCLM x`. -/
theorem hasFDerivAt_shrinkerFpot (τ : ℝ) (hτ : τ ≠ 0) (x : Euc n) :
    HasFDerivAt (fun y : Euc n => ‖y‖ ^ 2 / (4 * τ)) ((1 / (2 * τ)) • (innerCLM (Euc n)) x) x := by
  have h0 : HasFDerivAt (fun y : Euc n => ‖y‖ ^ 2) ((2 : ℕ) • (innerSL ℝ) x) x :=
    hasStrictFDerivAt_norm_sq x |>.hasFDerivAt
  have h1 : HasFDerivAt (fun y : Euc n => (1 / (4 * τ)) * ‖y‖ ^ 2)
      ((1 / (4 * τ)) • ((2 : ℕ) • (innerSL ℝ) x)) x :=
    h0.const_mul (1 / (4 * τ))
  have hder : (1 / (4 * τ)) • ((2 : ℕ) • (innerSL ℝ) x) = (1 / (2 * τ)) • (innerCLM (Euc n)) x := by
    ext w
    simp only [innerCLM, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
      innerSL_apply_apply, smul_apply, nsmul_eq_mul]
    field_simp [hτ]
    ring
  have h1' : HasFDerivAt (fun y : Euc n => (1 / (4 * τ)) * ‖y‖ ^ 2)
      ((1 / (2 * τ)) • (innerCLM (Euc n)) x) x := by
    rwa [hder] at h1
  exact h1'.congr_of_eventuallyEq (eventually_of_forall (fun y => by rw [div_eq_mul_inv]; ring))

/-- The second Fréchet derivative (Hessian) of `f = ‖x‖²/(4τ)` is
`(1/(2τ)) · ⟨·,·⟩`: `∇²f = (1/(2τ)) g`, the defining equality case of Perelman's
shrinker. -/
theorem iteratedFDeriv_two_shrinkerFpot (τ : ℝ) (hτ : τ ≠ 0) (x v w : Euc n) :
    iteratedFDeriv ℝ 2 (fun y : Euc n => ‖y‖ ^ 2 / (4 * τ)) x ![v, w] = (1 / (2 * τ)) * ⟪v, w⟫_ℝ := by
  have hderiv_fun : fderiv ℝ (fun y : Euc n => ‖y‖ ^ 2 / (4 * τ)) =
      fun y : Euc n => (1 / (2 * τ)) • (innerCLM (Euc n)) y := by
    funext y
    exact (hasFDerivAt_shrinkerFpot τ hτ y).fderiv
  have hL : HasFDerivAt (fun y : Euc n => (1 / (2 * τ)) • (innerCLM (Euc n)) y)
      ((1 / (2 * τ)) • (innerCLM (Euc n))) x :=
    (ContinuousLinearMap.hasFDerivAt (innerCLM (Euc n))).const_smul (1 / (2 * τ))
  have hfderiv := hL.fderiv
  rw [iteratedFDeriv_two_apply, hderiv_fun, hfderiv]
  simp only [innerCLM, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
    innerSL_apply_apply, smul_apply, ContinuousLinearMap.coe_smul', Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.isValue]
  ring

/-- **The Hessian of the shrinker potential equals the metric over `2τ`**: the defining
identity `∇²f = (1/(2τ)) g` of the Gaussian shrinker, proved pointwise from the second
Fréchet derivative.  Since the model is flat (`Ric = 0` by the model's definition),
this is the equality case of Perelman's `W`-monotonicity. -/
theorem shrinker_hessian_eq_metricOverTwoTau (τ : ℝ) (hτ : τ ≠ 0) (x v w : Euc n) :
    iteratedFDeriv ℝ 2 (shrinkerFpot τ) x ![v, w] = (1 / (2 * τ)) * ⟪v, w⟫_ℝ := by
  unfold shrinkerFpot
  exact iteratedFDeriv_two_shrinkerFpot τ hτ x v w

/-- **The W-dissipation density vanishes pointwise**: with `Ric = 0` (flat model) and
`∇²f = (1/(2τ)) g`, one has `|Ric + ∇²f - g/(2τ)|² ≡ 0`.  The pointwise statement
`(∇²f - g/(2τ))(v,w) = 0` is proved here; the norm-squared vanishing follows. -/
theorem shrinker_w_dissipation_density_zero (τ : ℝ) (hτ : τ ≠ 0) (x v w : Euc n) :
    iteratedFDeriv ℝ 2 (shrinkerFpot τ) x ![v, w] - (1 / (2 * τ)) * ⟪v, w⟫_ℝ = 0 := by
  rw [shrinker_hessian_eq_metricOverTwoTau τ hτ]
  ring

/-- **The dissipation density of the shrinker is `n/(4τ²)`**: the Hilbert–Schmidt
norm-squared of `∇²f = (1/(2τ))g` in the standard orthonormal basis of `ℝⁿ`,
justifying the field `riccHess` of `shrinkerEntropyData`. -/
theorem shrinker_riccHess_justified (n : ℕ) (τ : ℝ) (hτ : τ ≠ 0) :
    ∀ x : Euc n, shrinkerRiccHess n τ =
      ∑ i : Fin n, ∑ j : Fin n, (((1 / (2 * τ)) * ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
        EuclideanSpace.basisFun (Fin n) ℝ j⟫_ℝ)) ^ 2 := by
  intro x
  unfold shrinkerRiccHess
  have hinner : ∀ i j : Fin n, (1 / (2 * τ)) * ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
      EuclideanSpace.basisFun (Fin n) ℝ j⟫_ℝ =
      (1 / (2 * τ)) * (if i = j then (1 : ℝ) else 0) := by
    intro i j
    rw [inner_basisFun]
    simp [EuclideanSpace.basisFun_apply, Pi.single_apply]
  simp_rw [hinner]
  calc
    (n : ℝ) / (4 * τ ^ 2) = ∑ i : Fin n, (1 / (2 * τ)) ^ 2 := by
      rw [Finset.sum_const]
      simp [Finset.card_fin, nsmul_eq_mul]
      rw [mul_pow, sq, sq]
      field_simp [hτ]
      ring
    _ = ∑ i : Fin n, ∑ j : Fin n, ((1 / (2 * τ)) * (if i = j then (1 : ℝ) else 0)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [sq]
      calc
        (1 / (2 * τ)) * (1 / (2 * τ))
            = ∑ j : Fin n, (if j = i then ((1 / (2 * τ)) * (1 / (2 * τ))) else 0) := by
          rw [Finset.sum_ite_eq' Finset.univ i (fun _ => (1 / (2 * τ)) * (1 / (2 * τ)))]
          simp
        _ = ∑ j : Fin n, ((1 / (2 * τ)) * (if i = j then (1 : ℝ) else 0))
            * ((1 / (2 * τ)) * (if i = j then (1 : ℝ) else 0)) := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hji : j = i
          · simp [hji]
          · have hij : ¬i = j := fun h => hji h.symm
            simp [hji, hij]
        _ = ∑ j : Fin n, ((1 / (2 * τ)) * (if i = j then (1 : ℝ) else 0)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [sq]

end

end Poincare.D12.EntropyVariation
