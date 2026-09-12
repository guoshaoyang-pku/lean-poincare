/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D11 — comparison geometry of the model spaces: basic lemmas

This file collects the elementary facts about the D10 normalised Jacobi fields
`Poincare.D10.jacobiSol K` that are needed for the comparison-geometry statements of D11:

* the first zero `π / √K` is antitone in `K` (on positive curvatures),
* strict positivity of `jacobiSol K` before the first zero,
* continuity / differentiability of `jacobiDeriv K` and of powers of `jacobiSol K`.

Everything is unconditional; the only ingredients are the D10 facts and mathlib's real
trigonometry / hyperbolic functions.
-/
import Poincare.D10.JacobiConstantCurvature.Comparison

noncomputable section

namespace Poincare.D11

open scoped Real
open Set

/-- The first positive zero `π / √K` of the spherical normalised Jacobi field is antitone in
the curvature: for `0 < K₂ ≤ K₁` one has `π / √K₁ ≤ π / √K₂`. -/
theorem firstZero_le_firstZero {K₂ K₁ : ℝ} (hK : K₂ ≤ K₁) (_hK₁ : 0 < K₁) (hK₂ : 0 < K₂) :
    Real.pi / Real.sqrt K₁ ≤ Real.pi / Real.sqrt K₂ :=
  div_le_div_of_nonneg_left Real.pi_pos.le (Real.sqrt_pos_of_pos hK₂) (Real.sqrt_le_sqrt hK)

/-- Strict positivity of the normalised Jacobi field before the first zero: for `t > 0` and,
in the spherical case `K > 0`, for `t < π / √K`, one has `0 < jacobiSol K t`. -/
theorem jacobiSol_pos {K t : ℝ} (ht : 0 < t) (hK : 0 < K → t < Real.pi / Real.sqrt K) :
    0 < Poincare.D10.jacobiSol K t := by
  rcases lt_trichotomy K 0 with h | h | h
  · rw [Poincare.D10.jacobiSol_of_neg h, Poincare.D10.jacobiSolHyperbolic]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos (Real.sqrt_pos_of_pos (neg_pos.mpr h)) ht))
      (Real.sqrt_pos_of_pos (neg_pos.mpr h))
  · subst h
    rw [Poincare.D10.jacobiSol_of_zero, Poincare.D10.jacobiSolFlat]
    exact ht
  · rw [Poincare.D10.jacobiSol_of_pos h, Poincare.D10.jacobiSolSphere]
    have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos_of_pos h
    have hb : Real.sqrt K * t < Real.pi := by
      have := mul_lt_mul_of_pos_left (hK h) hsqrt
      rwa [mul_div_cancel₀ Real.pi hsqrt.ne'] at this
    exact Poincare.D10.jacobiSolSphere_pos h ht hb

/-- Strict positivity of the normalised Jacobi field for nonpositive curvature: for `K ≤ 0`
the field `jacobiSol K` is strictly positive on `(0, ∞)`. -/
theorem jacobiSol_pos_of_nonpos {K t : ℝ} (hK : K ≤ 0) (ht : 0 < t) :
    0 < Poincare.D10.jacobiSol K t :=
  jacobiSol_pos ht fun h => absurd h (not_lt.mpr hK)

/-- If `K₂ ≤ K₁` then the domain of strict positivity of `jacobiSol K₂` contains the domain of
strict positivity of `jacobiSol K₁`: for `0 < t` before the first zero of `j_{K₁}` one has
`0 < jacobiSol K₂ t`. -/
theorem jacobiSol_pos_of_le {K₁ K₂ : ℝ} (hK : K₂ ≤ K₁) {t : ℝ} (ht : 0 < t)
    (hdom : 0 < K₁ → t < Real.pi / Real.sqrt K₁) : 0 < Poincare.D10.jacobiSol K₂ t :=
  jacobiSol_pos ht fun hK₂ =>
    lt_of_lt_of_le (hdom (lt_of_lt_of_le hK₂ hK))
      (firstZero_le_firstZero hK (lt_of_lt_of_le hK₂ hK) hK₂)

/-- If `K₂ ≤ K₁` then the domain of nonnegativity of `jacobiSol K₂` contains the domain of
nonnegativity of `jacobiSol K₁`: for `0 ≤ t` before the first zero of `j_{K₁}` one has
`0 ≤ jacobiSol K₂ t`. -/
theorem jacobiSol_nonneg_of_le {K₁ K₂ : ℝ} (hK : K₂ ≤ K₁) {t : ℝ} (ht : 0 ≤ t)
    (hdom : 0 < K₁ → t ≤ Real.pi / Real.sqrt K₁) : 0 ≤ Poincare.D10.jacobiSol K₂ t :=
  Poincare.D10.jacobiSol_nonneg ht fun hK₂ =>
    le_trans (hdom (lt_of_lt_of_le hK₂ hK))
      (firstZero_le_firstZero hK (lt_of_lt_of_le hK₂ hK) hK₂)

/-- The explicit derivative `jacobiDeriv K` is continuous (each branch is smooth in `t`). -/
theorem continuous_jacobiDeriv (K : ℝ) : Continuous (Poincare.D10.jacobiDeriv K) :=
  continuous_iff_continuousAt.mpr fun t => (Poincare.D10.hasDerivAt_jacobiDeriv K t).continuousAt

/-- The explicit derivative `jacobiDeriv K` is differentiable. -/
theorem differentiable_jacobiDeriv (K : ℝ) : Differentiable ℝ (Poincare.D10.jacobiDeriv K) :=
  fun t => (Poincare.D10.hasDerivAt_jacobiDeriv K t).differentiableAt

/-- Continuity of `t ↦ (jacobiSol K t) ^ n`. -/
theorem continuous_jacobiSol_pow (n : ℕ) (K : ℝ) :
    Continuous (fun t : ℝ => Poincare.D10.jacobiSol K t ^ n) :=
  (Poincare.D10.continuous_jacobiSol K).pow n

/-- Differentiability of `t ↦ (jacobiSol K t) ^ n`. -/
theorem differentiable_jacobiSol_pow (n : ℕ) (K : ℝ) :
    Differentiable ℝ (fun t : ℝ => Poincare.D10.jacobiSol K t ^ n) :=
  (Poincare.D10.differentiable_jacobiSol K).pow n

end Poincare.D11
