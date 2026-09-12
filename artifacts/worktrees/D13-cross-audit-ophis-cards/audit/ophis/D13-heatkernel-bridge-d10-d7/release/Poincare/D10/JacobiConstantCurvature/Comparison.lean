/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D10 — Rauch comparison for the scalar Jacobi equation in constant curvature

Let `j_K` be the normalised solution of `j'' + K j = 0`, `j 0 = 0`, `j' 0 = 1`
(`Poincare.D10.jacobiSol`).  This file proves the ODE-level **Rauch comparison theorem**

`K₁ ≤ K₂  →  j_{K₂} t ≤ j_{K₁} t`

for every `t ≥ 0` up to the first zero of `j_{K₂}`, i.e. for `K₂ > 0` for every
`t ≤ π / √K₂` (and for all `t ≥ 0` when `K₂ ≤ 0`, where `j_{K₂}` has no zero).

The proof is a Sturm-type argument, not a citation: the explicit first derivatives
`jacobiDeriv K` (i.e. `cos (√K ·)`, `1`, `cosh (√(-K) ·)`) are compared pointwise
(`jacobiDeriv_le_of_le`), and the difference `j_{K₁} - j_{K₂}` is shown to be monotone on
`[0,t]` by mathlib's `monotoneOn_of_deriv_nonneg`.

Everything is unconditional; no comparison theorem is assumed.
-/
import Poincare.D10.JacobiConstantCurvature.ODE

noncomputable section

namespace Poincare.D10

/-! ## Continuity and differentiability of `jacobiSol K` -/

theorem continuous_jacobiSol (K : ℝ) : Continuous (jacobiSol K) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_jacobiSol K t).continuousAt

theorem differentiable_jacobiSol (K : ℝ) : Differentiable ℝ (jacobiSol K) :=
  fun t => (hasDerivAt_jacobiSol K t).differentiableAt

/-! ## Comparison of the explicit first derivatives -/

/-- For fixed `s ≥ 0` the explicit first derivative `jacobiDeriv K s` is antitone in the
curvature `K`, provided `s` does not pass the first zero of the comparison curvature: if
`K₂ > 0` we require `√K₂ * s ≤ π`. -/
theorem jacobiDeriv_le_of_le {K₁ K₂ : ℝ} (hK : K₁ ≤ K₂) {s : ℝ} (hs : 0 ≤ s)
    (hs2 : 0 < K₂ → Real.sqrt K₂ * s ≤ Real.pi) :
    jacobiDeriv K₂ s ≤ jacobiDeriv K₁ s := by
  rcases lt_trichotomy K₂ 0 with h₂ | h₂ | h₂
  · -- both curvatures are negative: compare two `cosh` values
    have h₁ : K₁ < 0 := lt_of_le_of_lt hK h₂
    rw [jacobiDeriv_of_neg h₂, jacobiDeriv_of_neg h₁]
    refine Real.cosh_strictMonoOn.monotoneOn ?_ ?_ ?_
    · exact mul_nonneg (Real.sqrt_nonneg _) hs
    · exact mul_nonneg (Real.sqrt_nonneg _) hs
    · exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) hs
  · -- `K₂ = 0`
    subst h₂
    rcases lt_trichotomy K₁ 0 with h₁ | h₁ | h₁
    · rw [jacobiDeriv_of_zero, jacobiDeriv_of_neg h₁]
      exact Real.one_le_cosh _
    · subst h₁
      simp [jacobiDeriv]
    · exact absurd hK (not_le.mpr h₁)
  · -- `K₂ > 0`: here the first-zero hypothesis is used
    have hs2' : Real.sqrt K₂ * s ≤ Real.pi := hs2 h₂
    rcases lt_trichotomy K₁ 0 with h₁ | h₁ | h₁
    · rw [jacobiDeriv_of_pos h₂, jacobiDeriv_of_neg h₁]
      exact le_trans (Real.cos_le_one _) (Real.one_le_cosh _)
    · rw [h₁, jacobiDeriv_of_zero, jacobiDeriv_of_pos h₂]
      exact Real.cos_le_one _
    · rw [jacobiDeriv_of_pos h₂, jacobiDeriv_of_pos h₁]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg (Real.sqrt_nonneg _) hs) hs2'
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hK) hs)

/-! ## Nonnegativity up to the first zero -/

/-- The normalised Jacobi field is nonnegative before the first zero of the corresponding
space form: for `K > 0` this is the interval `[0, π / √K]`, while for `K ≤ 0` there is no
zero at all. -/
theorem jacobiSol_nonneg {K t : ℝ} (ht : 0 ≤ t)
    (hK : 0 < K → t ≤ Real.pi / Real.sqrt K) : 0 ≤ jacobiSol K t := by
  rcases lt_trichotomy K 0 with h | h | h
  · rw [jacobiSol_of_neg h, jacobiSolHyperbolic]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg (Real.sqrt_nonneg _) ht))
      (Real.sqrt_nonneg _)
  · subst h
    rw [jacobiSol_of_zero, jacobiSolFlat]
    exact ht
  · rw [jacobiSol_of_pos h, jacobiSolSphere]
    have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos_of_pos h
    have hb : Real.sqrt K * t ≤ Real.pi := by
      have := mul_le_mul_of_nonneg_left (hK h) hsqrt.le
      rwa [mul_div_cancel₀ Real.pi hsqrt.ne'] at this
    exact jacobiSolSphere_nonneg h ht hb

/-- For `K > 0` the first positive zero of `jacobiSol K` is `π / √K`. -/
theorem jacobiSol_firstZero {K : ℝ} (hK : 0 < K) :
    jacobiSol K (Real.pi / Real.sqrt K) = 0 := by
  rw [jacobiSol_of_pos hK, jacobiSolSphere_firstZero hK]

/-! ## Rauch comparison -/

/-- **Rauch comparison theorem at the ODE level.**  If `K₁ ≤ K₂` then the normalised Jacobi
fields satisfy `jacobiSol K₂ t ≤ jacobiSol K₁ t` for every `t ≥ 0` up to the first zero of
`jacobiSol K₂`, i.e. for `K₂ > 0` for every `t ≤ π / √K₂`. -/
theorem rauch_comparison {K₁ K₂ : ℝ} (hK : K₁ ≤ K₂) {t : ℝ} (ht : 0 ≤ t)
    (ht2 : 0 < K₂ → t ≤ Real.pi / Real.sqrt K₂) :
    jacobiSol K₂ t ≤ jacobiSol K₁ t := by
  have hmem0 : (0 : ℝ) ∈ Set.Icc 0 t := Set.left_mem_Icc.mpr ht
  have hmemt : t ∈ Set.Icc 0 t := Set.right_mem_Icc.mpr ht
  have hmono : MonotoneOn (fun u : ℝ => jacobiSol K₁ u - jacobiSol K₂ u) (Set.Icc 0 t) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t) ?_ ?_ ?_
    · exact (continuous_jacobiSol K₁).continuousOn.sub (continuous_jacobiSol K₂).continuousOn
    · exact (differentiable_jacobiSol K₁).differentiableOn.sub
        (differentiable_jacobiSol K₂).differentiableOn
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 ≤ x := hx.1.le
      have hxt : x ≤ t := hx.2.le
      have hsub : deriv (fun u : ℝ => jacobiSol K₁ u - jacobiSol K₂ u) x
          = jacobiDeriv K₁ x - jacobiDeriv K₂ x := by
        change deriv (jacobiSol K₁ - jacobiSol K₂) x = jacobiDeriv K₁ x - jacobiDeriv K₂ x
        rw [deriv_sub (differentiable_jacobiSol K₁ x) (differentiable_jacobiSol K₂ x),
          jacobiSol_deriv, jacobiSol_deriv]
      rw [hsub]
      have hle : jacobiDeriv K₂ x ≤ jacobiDeriv K₁ x := by
        refine jacobiDeriv_le_of_le hK hx0 ?_
        intro hK2
        have h1 : Real.sqrt K₂ * x ≤ Real.sqrt K₂ * t :=
          mul_le_mul_of_nonneg_left hxt (Real.sqrt_nonneg K₂)
        have h2 : Real.sqrt K₂ * t ≤ Real.pi := by
          have h3 := mul_le_mul_of_nonneg_left (ht2 hK2) (Real.sqrt_nonneg K₂)
          rwa [mul_div_cancel₀ Real.pi (Real.sqrt_pos_of_pos hK2).ne'] at h3
        linarith
      linarith
  have h := hmono hmem0 hmemt ht
  simp only [jacobiSol_zero, sub_zero] at h
  linarith

/-- Rauch comparison for a spherical comparison curvature `K₂ > 0`, stated with the first zero
`π / √K₂` explicitly. -/
theorem rauch_comparison_sphere {K₁ K₂ : ℝ} (hK : K₁ ≤ K₂) (_hK₂ : 0 < K₂) {t : ℝ}
    (ht : 0 ≤ t) (htle : t ≤ Real.pi / Real.sqrt K₂) :
    jacobiSol K₂ t ≤ jacobiSol K₁ t :=
  rauch_comparison hK ht fun _ => htle

/-- Rauch comparison when the comparison curvature is nonpositive: the conclusion then holds
for *all* `t ≥ 0`, since `jacobiSol K₂` has no zero. -/
theorem rauch_comparison_of_nonpos {K₁ K₂ : ℝ} (hK : K₁ ≤ K₂) (_hK₂ : K₂ ≤ 0) {t : ℝ}
    (ht : 0 ≤ t) : jacobiSol K₂ t ≤ jacobiSol K₁ t :=
  rauch_comparison hK ht fun h => absurd h (not_lt.mpr _hK₂)

end Poincare.D10
