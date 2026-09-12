/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D10-gaussian-toolbox builder
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Poincare.GaussianToolbox.Basic

**One-dimensional Gaussian integrals: scaling law, exact even moments and the normalised
density.**

This file is the computational substrate for heat-kernel and PDE work.  Everything is proved
unconditionally from mathlib's Gaussian integral `integral_gaussian`
(`∫ x : ℝ, exp (-b * x ^ 2) = √(π / b)`); no hypothesis is assumed beyond positivity of the
parameters, and no `sorry`/`axiom` is used.

Main results:

* `integral_gaussianKernel` — the scaling law `∫ x, exp (-(a x²)) = √(π / a)`;
* `integrable_pow_mul_gaussianKernel` — every polynomial multiple of a Gaussian is integrable;
* `tendsto_pow_mul_gaussianKernel_atTop` / `_atBot` — the decaying endpoints used by FTC-2;
* `hasDerivAt_pow_mul_gaussianKernel` — the derivative of the odd antiderivative;
* `integral_moment_succ` — the integration-by-parts recursion
  `∫ x, x ^ (2n+2) exp (-(a x²)) = (2n+1)/(2a) · ∫ x, x ^ (2n) exp (-(a x²))`;
* `integral_moment_zero`, `integral_moment_two`, `integral_moment_four`,
  `integral_moment_six` — the exact moments for `n = 0, 1, 2, 3`;
* `integral_gaussianDensity` — the normalised density has total mass `1`;
* `integral_gaussianDensity_mul_sq` — its second moment is `gaussianVariance a = 1/(2a)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Filter Topology
open scoped Real Topology

namespace Poincare.GaussianToolbox

/-! ## Definitions -/

/-- The unnormalised Gaussian kernel `x ↦ exp (-(a * x ^ 2))` with parameter `a`. -/
def gaussianKernel (a x : ℝ) : ℝ := exp (-(a * x ^ 2))

/-- The normalised one-dimensional Gaussian density with variance parameter `a`; for `a > 0`
its variance is `1/(2a)` and its total mass is `1`. -/
def gaussianDensity (a x : ℝ) : ℝ := sqrt (a / π) * gaussianKernel a x

/-- The variance `1/(2a)` of the normalised Gaussian density `gaussianDensity a`. -/
def gaussianVariance (a : ℝ) : ℝ := 1 / (2 * a)

lemma gaussianKernel_def (a x : ℝ) : gaussianKernel a x = exp (-(a * x ^ 2)) := rfl

lemma gaussianDensity_def (a x : ℝ) :
    gaussianDensity a x = sqrt (a / π) * gaussianKernel a x := rfl

lemma gaussianKernel_neg (a x : ℝ) : gaussianKernel a (-x) = gaussianKernel a x := by
  rw [gaussianKernel_def, gaussianKernel_def, neg_sq]

/-! ## The scaling law -/

/-- **Scaling law of the Gaussian integral**: `∫ x, exp (-(a x²)) = √(π / a)`.

For `a > 0` this is the standard normalisation; the statement is in fact unconditional because
both sides vanish at `a = 0` (the non-integrable integral is `0` by convention). -/
theorem integral_gaussianKernel (a : ℝ) :
    ∫ x : ℝ, gaussianKernel a x = sqrt (π / a) := by
  simpa only [gaussianKernel_def, neg_mul] using integral_gaussian a

set_option linter.unusedVariables false in
/-- The scaling law with the positivity hypothesis made explicit. -/
theorem integral_gaussianKernel_of_pos {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, gaussianKernel a x = sqrt (π / a) :=
  integral_gaussianKernel a

/-! ## Integrability, decay and the antiderivative -/

/-- Every polynomial multiple of a Gaussian is integrable. -/
theorem integrable_pow_mul_gaussianKernel {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n * gaussianKernel a x) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := a) ha (s := (n : ℝ))
    (by have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  simpa only [gaussianKernel_def, Real.rpow_natCast, neg_mul] using h

/-- A polynomial multiple of a Gaussian tends to `0` at `+∞`. -/
theorem tendsto_pow_mul_gaussianKernel_atTop {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ n * gaussianKernel a x) atTop (𝓝 0) := by
  have hlit := rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg (b := a) ha (n : ℝ)
  have hv : Tendsto (fun x : ℝ => exp (-(1 / 2) * x)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (show (-(1 / 2) : ℝ) < 0 by norm_num))
  have h0 : Tendsto (fun x : ℝ => x ^ (n : ℝ) * exp (-a * x ^ 2)) atTop (𝓝 0) :=
    hlit.tendsto_zero_of_tendsto hv
  refine Filter.Tendsto.congr' (Eventually.of_forall fun x => ?_) h0
  simp only [gaussianKernel_def, Real.rpow_natCast, neg_mul]

/-- A polynomial multiple of a Gaussian tends to `0` at `-∞`. -/
theorem tendsto_pow_mul_gaussianKernel_atBot {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ n * gaussianKernel a x) atBot (𝓝 0) := by
  have hsymm : Tendsto (fun x : ℝ => (fun y => y ^ n * gaussianKernel a y) (-x))
      atTop (𝓝 0) := by
    have h₁ : Tendsto (fun x : ℝ => (-1 : ℝ) ^ n * (x ^ n * gaussianKernel a x))
        atTop (𝓝 0) := by
      simpa using (tendsto_pow_mul_gaussianKernel_atTop ha n).const_mul ((-1 : ℝ) ^ n)
    exact Filter.Tendsto.congr (fun x => by
      simp only [gaussianKernel_def, neg_sq, neg_pow x n, mul_assoc]) h₁
  rw [← Filter.comap_neg_atTop, Filter.tendsto_def]
  intro s hs
  have ht : Neg.neg ⁻¹' ((fun y => y ^ n * gaussianKernel a y) ⁻¹' s) ∈ atTop := hsymm hs
  exact Filter.mem_comap.mpr ⟨_, ht, by intro x hx; simpa using hx⟩

/-- The derivative of the odd antiderivative `y ↦ y ^ (2n+1) * exp (-(a y²))`. -/
theorem hasDerivAt_pow_mul_gaussianKernel (a : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ (2 * n + 1) * gaussianKernel a y)
      ((2 * n + 1 : ℝ) * (x ^ (2 * n) * gaussianKernel a x)
        - (2 * a) * (x ^ (2 * n + 2) * gaussianKernel a x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ (2 * n + 1))
      ((2 * n + 1 : ℝ) * x ^ (2 * n)) x := by
    have h := hasDerivAt_pow (2 * n + 1) x
    rw [Nat.add_sub_cancel] at h
    simpa using h
  have h2 : HasDerivAt (fun y : ℝ => gaussianKernel a y)
      (-(2 * a * x) * gaussianKernel a x) x := by
    have hbase : HasDerivAt (fun y : ℝ => -(a * y ^ 2)) (-(2 * a * x)) x := by
      have h := (hasDerivAt_pow 2 x).const_mul a
      have h' : HasDerivAt (fun y : ℝ => a * y ^ 2) (a * (2 * x)) x := by
        simpa using h
      have h'' := h'.neg
      have hval : -(a * (2 * x)) = -(2 * a * x) := by ring
      rwa [hval] at h''
    have hthis : HasDerivAt (fun y : ℝ => exp (-(a * y ^ 2)))
        (exp (-(a * x ^ 2)) * (-(2 * a * x))) x := hbase.exp
    have hval : exp (-(a * x ^ 2)) * (-(2 * a * x)) = -(2 * a * x) * gaussianKernel a x := by
      rw [gaussianKernel_def]; ring
    rwa [hval] at hthis
  have hmain := h1.mul h2
  have hderiv : ((2 * n + 1 : ℝ) * x ^ (2 * n)) * gaussianKernel a x
      + x ^ (2 * n + 1) * (-(2 * a * x) * gaussianKernel a x)
      = (2 * n + 1 : ℝ) * (x ^ (2 * n) * gaussianKernel a x)
        - (2 * a) * (x ^ (2 * n + 2) * gaussianKernel a x) := by
    rw [show x ^ (2 * n + 2) = x ^ (2 * n + 1) * x by
      rw [show 2 * n + 2 = 2 * n + 1 + 1 by omega, pow_succ]]
    ring
  exact hmain.congr_deriv hderiv

/-! ## The moment recursion and the first four even moments -/

/-- **Integration-by-parts recursion for the even Gaussian moments**:
`∫ x, x ^ (2n+2) exp (-(a x²)) = ((2n+1) · ∫ x, x ^ (2n) exp (-(a x²))) / (2a)`.

It is proved by integrating the derivative `hasDerivAt_pow_mul_gaussianKernel` over `ℝ`, the
two endpoint limits being `tendsto_pow_mul_gaussianKernel_atTop` / `_atBot`. -/
theorem integral_moment_succ {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n + 2) * gaussianKernel a x
      = ((2 * n + 1 : ℝ) * ∫ x : ℝ, x ^ (2 * n) * gaussianKernel a x) / (2 * a) := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ (2 * n + 1) * gaussianKernel a y)
      ((2 * n + 1 : ℝ) * (x ^ (2 * n) * gaussianKernel a x)
        - (2 * a) * (x ^ (2 * n + 2) * gaussianKernel a x)) x :=
    hasDerivAt_pow_mul_gaussianKernel a n
  have hI₁ : Integrable
      (fun x : ℝ => (2 * n + 1 : ℝ) * (x ^ (2 * n) * gaussianKernel a x)) :=
    (integrable_pow_mul_gaussianKernel ha (2 * n)).const_mul _
  have hI₂ : Integrable
      (fun x : ℝ => (2 * a) * (x ^ (2 * n + 2) * gaussianKernel a x)) :=
    (integrable_pow_mul_gaussianKernel ha (2 * n + 2)).const_mul _
  have hint : Integrable (fun x : ℝ =>
      (2 * n + 1 : ℝ) * (x ^ (2 * n) * gaussianKernel a x)
        - (2 * a) * (x ^ (2 * n + 2) * gaussianKernel a x)) := hI₁.sub hI₂
  have htop := tendsto_pow_mul_gaussianKernel_atTop ha (2 * n + 1)
  have hbot := tendsto_pow_mul_gaussianKernel_atBot ha (2 * n + 1)
  have hftc := MeasureTheory.integral_of_hasDerivAt_of_tendsto hderiv hint hbot htop
  have hzero : ∫ x : ℝ, ((2 * n + 1 : ℝ) * (x ^ (2 * n) * gaussianKernel a x)
      - (2 * a) * (x ^ (2 * n + 2) * gaussianKernel a x)) = 0 := by
    simpa using hftc
  have hsplit : ∫ x : ℝ, ((2 * n + 1 : ℝ) * (x ^ (2 * n) * gaussianKernel a x)
      - (2 * a) * (x ^ (2 * n + 2) * gaussianKernel a x))
      = (2 * n + 1 : ℝ) * (∫ x : ℝ, x ^ (2 * n) * gaussianKernel a x)
        - (2 * a) * (∫ x : ℝ, x ^ (2 * n + 2) * gaussianKernel a x) := by
    rw [integral_sub hI₁ hI₂, integral_const_mul, integral_const_mul]
  have hmoment : (2 * a) * (∫ x : ℝ, x ^ (2 * n + 2) * gaussianKernel a x)
      = (2 * n + 1 : ℝ) * ∫ x : ℝ, x ^ (2 * n) * gaussianKernel a x := by
    linarith [hzero, hsplit]
  rw [eq_div_iff (by positivity : (2 : ℝ) * a ≠ 0)]
  linarith [hmoment]

/-- `∫ x, exp (-x²) = √π` — the `n = 0` moment. -/
theorem integral_moment_zero : ∫ x : ℝ, gaussianKernel 1 x = sqrt π := by
  simpa using integral_gaussianKernel 1

/-- `∫ x, x² exp (-x²) = √π / 2` — the `n = 1` moment. -/
theorem integral_moment_two : ∫ x : ℝ, x ^ 2 * gaussianKernel 1 x = sqrt π / 2 := by
  have h := integral_moment_succ (a := 1) one_pos 0
  norm_num at h
  rw [h, integral_moment_zero]

/-- `∫ x, x⁴ exp (-x²) = 3√π / 4` — the `n = 2` moment. -/
theorem integral_moment_four : ∫ x : ℝ, x ^ 4 * gaussianKernel 1 x = 3 * sqrt π / 4 := by
  have h := integral_moment_succ (a := 1) one_pos 1
  have h2 : ∫ x : ℝ, x ^ (2 * 1) * gaussianKernel 1 x = sqrt π / 2 := by
    simpa using integral_moment_two
  norm_num at h
  rw [h, h2]
  ring

/-- `∫ x, x⁶ exp (-x²) = 15√π / 8` — the `n = 3` moment. -/
theorem integral_moment_six : ∫ x : ℝ, x ^ 6 * gaussianKernel 1 x = 15 * sqrt π / 8 := by
  have h := integral_moment_succ (a := 1) one_pos 2
  have h4 : ∫ x : ℝ, x ^ (2 * 2) * gaussianKernel 1 x = 3 * sqrt π / 4 := by
    simpa using integral_moment_four
  norm_num at h
  rw [h, h4]
  ring

/-! ## The normalised density -/

/-- The normalised Gaussian density has total mass `1`. -/
theorem integral_gaussianDensity {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, gaussianDensity a x = 1 := by
  have h : ∫ x : ℝ, gaussianDensity a x
      = sqrt (a / π) * ∫ x : ℝ, gaussianKernel a x := by
    rw [← integral_const_mul]
    rfl
  rw [h, integral_gaussianKernel]
  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ a / π)]
  rw [show a / π * (π / a) = 1 by field_simp, Real.sqrt_one]

/-- The second moment of the normalised Gaussian density is its variance `1/(2a)`. -/
theorem integral_gaussianDensity_mul_sq {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, x ^ 2 * gaussianDensity a x = gaussianVariance a := by
  have hfun : (fun x : ℝ => x ^ 2 * gaussianDensity a x)
      = fun x : ℝ => sqrt (a / π) * (x ^ 2 * gaussianKernel a x) := by
    funext x
    rw [gaussianDensity_def]
    ring
  rw [hfun, integral_const_mul]
  have h2 := integral_moment_succ (a := a) ha 0
  norm_num at h2
  rw [h2, integral_gaussianKernel, gaussianVariance]
  have hsqrt : sqrt (a / π) * sqrt (π / a) = 1 := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ a / π)]
    rw [show a / π * (π / a) = 1 by field_simp, Real.sqrt_one]
  rw [← mul_div_assoc, hsqrt]

end Poincare.GaussianToolbox
