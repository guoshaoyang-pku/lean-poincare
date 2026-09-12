/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D12 — Riccati comparison for the nonconstant scalar Jacobi equation

This file proves the **comparison of logarithmic derivatives** (the scalar Riccati
comparison) for two positive solutions `uᵢ` of `uᵢ'' + kᵢ·uᵢ = 0` with `k₂ ≤ k₁`:

    ρᵢ = uᵢ'/uᵢ,   ρ₁(a) ≤ ρ₂(a)   ⟹   ρ₁(t) ≤ ρ₂(t)  on [a,b],

and the corresponding one-sided solution comparison: with the same initial value and
derivative at `a`, `u₁(t) ≤ u₂(t)` on `[a,b]`.

The proof is the classical integrating-factor argument for the Riccati inequality
`δ' + p·δ ≤ 0` (with `δ = ρ₁ − ρ₂`, `p = ρ₁ + ρ₂`): the factor `exp(∫ₐᵗ p)` turns it into
a monotonicity statement.  There is **no division at zero**: the positivity hypothesis
`u₁, u₂ > 0` holds on the *closed* interval `[a,b]`, so every denominator is bounded away
from zero by continuity, and the initial comparison `ρ₁(a) ≤ ρ₂(a)` is a hypothesis about
positive quantities.
-/
import Poincare.D12.ComparisonGeodesics.Definitions
import Mathlib.MeasureTheory.Integral.IntegrableOn

noncomputable section

open Set Filter
open scoped Topology
open MeasureTheory

namespace Poincare.D12.ComparisonGeodesics

/-! ## The logarithmic derivative -/

/-- The logarithmic derivative `ρ = du/u` of a positive function. -/
def logDeriv (du u : ℝ → ℝ) : ℝ → ℝ := fun t => du t / u t

/-- The derivative of the logarithmic derivative (quotient rule). -/
theorem logDeriv_hasDerivAt {u du ddu : ℝ → ℝ} {t : ℝ}
    (hu : HasDerivAtR u (du t) t) (hdu : HasDerivAtR du (ddu t) t) (hu0 : u t ≠ 0) :
    HasDerivAtR (logDeriv du u) (ddu t / u t - (du t / u t) ^ 2) t := by
  have hd : HasDerivAtR (du / u) ((ddu t * u t - du t * du t) / u t ^ 2) t :=
    hdu.div hu hu0
  have h₂ : (ddu t * u t - du t * du t) / u t ^ 2 = ddu t / u t - (du t / u t) ^ 2 := by
    field_simp [hu0, pow_ne_zero 2 hu0]
  have h₁ : HasDerivAtR (logDeriv du u) ((ddu t * u t - du t * du t) / u t ^ 2) t := by
    change HasDerivAtR (du / u) ((ddu t * u t - du t * du t) / u t ^ 2) t
    exact hd
  simpa [h₂] using h₁

/-- The logarithmic derivative of a Jacobi solution satisfies the scalar Riccati equation
`ρ' + ρ² + k = 0` on the interval where the solution is nonzero. -/
theorem logDeriv_riccati {k u du ddu : ℝ → ℝ} {a b : ℝ}
    (h : JacobiSolutionOn k u du ddu a b) {t : ℝ} (ht : t ∈ Ioo a b) (hu0 : u t ≠ 0) :
    (ddu t / u t - (du t / u t) ^ 2) + (logDeriv du u t) ^ 2 + k t = 0 := by
  have hd := logDeriv_hasDerivAt (h.hasDerivAt_u ht) (h.hasDerivAt_du ht) hu0
  rw [h.eq_secondDeriv ht]
  simp only [logDeriv]
  field_simp [hu0]
  ring

/-! ## Comparison of logarithmic derivatives -/

/-- **Riccati comparison (logarithmic derivatives).**  If `k₂ ≤ k₁` on `[a,b]`, both
solutions are positive on the closed interval `[a,b]`, and `ρ₁(a) ≤ ρ₂(a)`, then
`ρ₁(t) ≤ ρ₂(t)` for every `t ∈ [a,b]`. -/
theorem logDeriv_le_of_le {k₁ k₂ u₁ du₁ ddu₁ u₂ du₂ ddu₂ : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hk : ∀ ⦃t : ℝ⦄, t ∈ Icc a b → k₂ t ≤ k₁ t)
    (h1 : JacobiSolutionOn k₁ u₁ du₁ ddu₁ a b)
    (h2 : JacobiSolutionOn k₂ u₂ du₂ ddu₂ a b)
    (hu1pos : ∀ ⦃t : ℝ⦄, t ∈ Icc a b → 0 < u₁ t)
    (hu2pos : ∀ ⦃t : ℝ⦄, t ∈ Icc a b → 0 < u₂ t)
    (hrhoa : logDeriv du₁ u₁ a ≤ logDeriv du₂ u₂ a) :
    ∀ ⦃t : ℝ⦄, t ∈ Icc a b → logDeriv du₁ u₁ t ≤ logDeriv du₂ u₂ t := by
  set ρ₁ : ℝ → ℝ := logDeriv du₁ u₁ with hρ₁def
  set ρ₂ : ℝ → ℝ := logDeriv du₂ u₂ with hρ₂def
  set δ : ℝ → ℝ := fun t => ρ₁ t - ρ₂ t with hδdef
  set p : ℝ → ℝ := fun t => ρ₁ t + ρ₂ t with hpdef
  have hρ₁cont : ContinuousOn ρ₁ (Icc a b) := by
    change ContinuousOn (logDeriv du₁ u₁) (Icc a b)
    unfold logDeriv
    exact h1.continuousOn_du.div h1.continuousOn_u (fun x hx => ne_of_gt (hu1pos hx))
  have hρ₂cont : ContinuousOn ρ₂ (Icc a b) := by
    change ContinuousOn (logDeriv du₂ u₂) (Icc a b)
    unfold logDeriv
    exact h2.continuousOn_du.div h2.continuousOn_u (fun x hx => ne_of_gt (hu2pos hx))
  have hpcont : ContinuousOn p (Icc a b) := by
    change ContinuousOn (fun t => ρ₁ t + ρ₂ t) (Icc a b)
    exact hρ₁cont.add hρ₂cont
  have hδcont : ContinuousOn δ (Icc a b) := by
    change ContinuousOn (fun t => ρ₁ t - ρ₂ t) (Icc a b)
    exact hρ₁cont.sub hρ₂cont
  -- The Riccati inequality for δ: δ' + p·δ = k₂ − k₁ ≤ 0 on (a,b).
  have hdelta_ineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b →
      ((ddu₁ t / u₁ t - (du₁ t / u₁ t) ^ 2) - (ddu₂ t / u₂ t - (du₂ t / u₂ t) ^ 2))
        + p t * δ t ≤ 0 := by
    intro t ht
    have hsum : ((ddu₁ t / u₁ t - (du₁ t / u₁ t) ^ 2) - (ddu₂ t / u₂ t - (du₂ t / u₂ t) ^ 2))
        + p t * δ t = k₂ t - k₁ t := by
      change ((ddu₁ t / u₁ t - (du₁ t / u₁ t) ^ 2) - (ddu₂ t / u₂ t - (du₂ t / u₂ t) ^ 2))
        + (ρ₁ t + ρ₂ t) * (ρ₁ t - ρ₂ t) = k₂ t - k₁ t
      change ((ddu₁ t / u₁ t - (du₁ t / u₁ t) ^ 2) - (ddu₂ t / u₂ t - (du₂ t / u₂ t) ^ 2))
        + (logDeriv du₁ u₁ t + logDeriv du₂ u₂ t) *
          (logDeriv du₁ u₁ t - logDeriv du₂ u₂ t) = k₂ t - k₁ t
      unfold logDeriv
      rw [h1.eq_secondDeriv ht, h2.eq_secondDeriv ht]
      field_simp [ne_of_gt (hu1pos (Ioo_subset_Icc_self ht)),
        ne_of_gt (hu2pos (Ioo_subset_Icc_self ht))]
      ring
    rw [hsum]
    exact sub_nonpos.mpr (hk (Ioo_subset_Icc_self ht))
  -- The integrating factor M = exp(∫ₐ p) and φ = δ·M.
  have hpint : IntervalIntegrable p volume a b :=
    (hpcont.mono (by intro x hx; rw [uIcc_of_le hab] at hx; exact hx)).intervalIntegrable
  have hMderiv : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b →
      HasDerivAtR (fun s => Real.exp (∫ x in a..s, p x)) (p t * Real.exp (∫ x in a..t, p x)) t := by
    intro t ht
    have hpint_t : IntervalIntegrable p volume a t :=
      (hpcont.mono (by
        intro x hx
        rw [uIcc_of_le (le_of_lt ht.1)] at hx
        exact Icc_subset_Icc_right (le_of_lt ht.2) hx)).intervalIntegrable
    have hprim : HasDerivAtR (fun s => ∫ x in a..s, p x) (p t) t := by
      have hmeas : StronglyMeasurableAtFilter p (𝓝 t) :=
        ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
          (hpcont.mono Ioo_subset_Icc_self) t ht
      have hb : ContinuousAt p t :=
        hpcont.continuousAt
          (mem_of_superset (show Ioo a b ∈ 𝓝 t from isOpen_Ioo.mem_nhds ht) Ioo_subset_Icc_self)
      exact intervalIntegral.integral_hasDerivAt_right hpint_t hmeas hb
    convert ((Real.hasDerivAt_exp _).comp t hprim) using 1
    · funext s
      rfl
    · rw [mul_comm]
  have hφderiv : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b →
      HasDerivAtR (fun s => δ s * Real.exp (∫ x in a..s, p x))
        ((((ddu₁ t / u₁ t - (du₁ t / u₁ t) ^ 2) - (ddu₂ t / u₂ t - (du₂ t / u₂ t) ^ 2))
          + p t * δ t) * Real.exp (∫ x in a..t, p x)) t := by
    intro t ht
    have hδd : HasDerivAtR δ ((ddu₁ t / u₁ t - (du₁ t / u₁ t) ^ 2)
        - (ddu₂ t / u₂ t - (du₂ t / u₂ t) ^ 2)) t := by
      change HasDerivAtR (fun t => ρ₁ t - ρ₂ t)
        ((ddu₁ t / u₁ t - (du₁ t / u₁ t) ^ 2) - (ddu₂ t / u₂ t - (du₂ t / u₂ t) ^ 2)) t
      change HasDerivAtR (fun t => logDeriv du₁ u₁ t - logDeriv du₂ u₂ t)
        ((ddu₁ t / u₁ t - (du₁ t / u₁ t) ^ 2) - (ddu₂ t / u₂ t - (du₂ t / u₂ t) ^ 2)) t
      exact (logDeriv_hasDerivAt (h1.hasDerivAt_u ht) (h1.hasDerivAt_du ht)
        (ne_of_gt (hu1pos (Ioo_subset_Icc_self ht)))).sub
        (logDeriv_hasDerivAt (h2.hasDerivAt_u ht) (h2.hasDerivAt_du ht)
        (ne_of_gt (hu2pos (Ioo_subset_Icc_self ht))))
    convert hδd.mul (hMderiv ht) using 1
    · ext s
      rfl
    · ring
  have hφcont : ContinuousOn (fun s => δ s * Real.exp (∫ x in a..s, p x)) (Icc a b) := by
    exact hδcont.mul ((Real.continuous_exp.comp_continuousOn
      ((intervalIntegral.continuousOn_primitive_interval' hpint Set.left_mem_uIcc).mono
        (by intro x hx; rw [uIcc_of_le hab]; exact hx))))
  have hφdiff : DifferentiableOn ℝ (fun s => δ s * Real.exp (∫ x in a..s, p x)) (Ioo a b) := by
    intro t ht
    exact (hφderiv ht).differentiableAt.differentiableWithinAt
  have hφantitone : AntitoneOn (fun s => δ s * Real.exp (∫ x in a..s, p x)) (Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b) hφcont ?_ ?_
    · simpa [interior_Icc] using hφdiff
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hφderiv ht).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (hdelta_ineq ht) (Real.exp_pos _).le
  -- φ(a) = δ(a) ≤ 0, so φ ≤ 0 on [a,b], so δ ≤ 0 on [a,b].
  have hφa : δ a * Real.exp (∫ x in a..a, p x) = δ a := by
    rw [intervalIntegral.integral_same, Real.exp_zero, mul_one]
  have hφa_nonpos : δ a * Real.exp (∫ x in a..a, p x) ≤ 0 := by
    rw [hφa]
    change ρ₁ a - ρ₂ a ≤ 0
    change logDeriv du₁ u₁ a - logDeriv du₂ u₂ a ≤ 0
    exact sub_nonpos.mpr hrhoa
  intro t ht
  have hφt : δ t * Real.exp (∫ x in a..t, p x) ≤
      δ a * Real.exp (∫ x in a..a, p x) :=
    hφantitone (Set.left_mem_Icc.mpr hab) ht ht.1
  have hδt_nonpos : δ t * Real.exp (∫ x in a..t, p x) ≤ 0 := hφt.trans hφa_nonpos
  have hδt : δ t ≤ 0 := by
    by_contra h
    have hδpos : 0 < δ t := lt_of_not_ge h
    have hposM : 0 < Real.exp (∫ x in a..t, p x) := Real.exp_pos _
    have hposprod : 0 < δ t * Real.exp (∫ x in a..t, p x) := mul_pos hδpos hposM
    linarith
  change ρ₁ t - ρ₂ t ≤ 0 at hδt
  change logDeriv du₁ u₁ t - logDeriv du₂ u₂ t ≤ 0 at hδt
  linarith

/-- **Solution comparison from initial data.**  With `k₂ ≤ k₁` on `[a,b]`, both solutions
positive on the closed interval, `u₁(a) ≤ u₂(a)` and `ρ₁(a) ≤ ρ₂(a)`, the solution `u₁`
stays below `u₂` on all of `[a,b]`.  The proof uses only the monotonicity of `u₁/u₂`; no
division at zero occurs because both solutions are positive on the closed interval. -/
theorem solution_le_of_initial {k₁ k₂ u₁ du₁ ddu₁ u₂ du₂ ddu₂ : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hk : ∀ ⦃t : ℝ⦄, t ∈ Icc a b → k₂ t ≤ k₁ t)
    (h1 : JacobiSolutionOn k₁ u₁ du₁ ddu₁ a b)
    (h2 : JacobiSolutionOn k₂ u₂ du₂ ddu₂ a b)
    (hu1pos : ∀ ⦃t : ℝ⦄, t ∈ Icc a b → 0 < u₁ t)
    (hu2pos : ∀ ⦃t : ℝ⦄, t ∈ Icc a b → 0 < u₂ t)
    (hu1a_le : u₁ a ≤ u₂ a)
    (hrhoa : logDeriv du₁ u₁ a ≤ logDeriv du₂ u₂ a) :
    ∀ ⦃t : ℝ⦄, t ∈ Icc a b → u₁ t ≤ u₂ t := by
  have hrho : ∀ ⦃t : ℝ⦄, t ∈ Icc a b → logDeriv du₁ u₁ t ≤ logDeriv du₂ u₂ t :=
    logDeriv_le_of_le hab hk h1 h2 hu1pos hu2pos hrhoa
  have hratio_cont : ContinuousOn (fun t => u₁ t / u₂ t) (Icc a b) :=
    h1.continuousOn_u.div h2.continuousOn_u (fun x hx => ne_of_gt (hu2pos hx))
  have hratio_diff : DifferentiableOn ℝ (fun t => u₁ t / u₂ t) (Ioo a b) := by
    intro t ht
    exact ((h1.hasDerivAt_u ht).div (h2.hasDerivAt_u ht)
      (ne_of_gt (hu2pos (Ioo_subset_Icc_self ht)))).differentiableAt.differentiableWithinAt
  have hratio_antitone : AntitoneOn (fun t => u₁ t / u₂ t) (Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b) hratio_cont ?_ ?_
    · simpa [interior_Icc] using hratio_diff
    · intro t ht
      rw [interior_Icc] at ht
      have hdiv : HasDerivAt (fun s => u₁ s / u₂ s)
          ((du₁ t * u₂ t - u₁ t * du₂ t) / u₂ t ^ 2) t :=
        (h1.hasDerivAt_u ht).div (h2.hasDerivAt_u ht)
          (ne_of_gt (hu2pos (Ioo_subset_Icc_self ht)))
      rw [hdiv.deriv]
      have hfact : (du₁ t * u₂ t - u₁ t * du₂ t) / u₂ t ^ 2
          = (u₁ t / u₂ t) * (logDeriv du₁ u₁ t - logDeriv du₂ u₂ t) := by
        simp only [logDeriv]
        field_simp [ne_of_gt (hu2pos (Ioo_subset_Icc_self ht)),
          ne_of_gt (hu1pos (Ioo_subset_Icc_self ht))]
      rw [hfact]
      exact mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (le_of_lt (hu1pos (Ioo_subset_Icc_self ht)))
          (le_of_lt (hu2pos (Ioo_subset_Icc_self ht))))
        (sub_nonpos.mpr (hrho (Ioo_subset_Icc_self ht)))
  intro t ht
  have hrat : u₁ t / u₂ t ≤ u₁ a / u₂ a :=
    hratio_antitone (Set.left_mem_Icc.mpr hab) ht ht.1
  have hra1 : u₁ a / u₂ a ≤ 1 :=
    div_le_one_of_le₀ hu1a_le (le_of_lt (hu2pos (Set.left_mem_Icc.mpr hab)))
  have hle1 : u₁ t / u₂ t ≤ 1 := hrat.trans hra1
  exact (div_le_one (hu2pos ht)).mp hle1

/-- **Solution comparison with the same initial conditions.**  If `k₂ ≤ k₁` on `[a,b]`,
both solutions are positive on `[a,b]`, and `u₁(a) = u₂(a)`, `u₁'(a) = u₂'(a)`, then
`u₁(t) ≤ u₂(t)` on `[a,b]`. -/
theorem solution_le_of_same_initial {k₁ k₂ u₁ du₁ ddu₁ u₂ du₂ ddu₂ : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hk : ∀ ⦃t : ℝ⦄, t ∈ Icc a b → k₂ t ≤ k₁ t)
    (h1 : JacobiSolutionOn k₁ u₁ du₁ ddu₁ a b)
    (h2 : JacobiSolutionOn k₂ u₂ du₂ ddu₂ a b)
    (hu1pos : ∀ ⦃t : ℝ⦄, t ∈ Icc a b → 0 < u₁ t)
    (hu2pos : ∀ ⦃t : ℝ⦄, t ∈ Icc a b → 0 < u₂ t)
    (hu1a : u₁ a = u₂ a) (hdu1a : du₁ a = du₂ a) :
    ∀ ⦃t : ℝ⦄, t ∈ Icc a b → u₁ t ≤ u₂ t := by
  refine solution_le_of_initial hab hk h1 h2 hu1pos hu2pos ?_ ?_
  · exact le_of_eq hu1a
  · simp [logDeriv, hu1a, hdu1a]

end Poincare.D12.ComparisonGeodesics
