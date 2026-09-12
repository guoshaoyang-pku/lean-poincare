/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D12 — Riccati comparison with Euclidean (singular) normalization (v2, corrected domain)

This file proves the **singular Riccati comparison** — the analytic engine behind the
volume-ratio (Bishop–Gromov) monotonicity and the one-sided Rauch comparisons:

    m' + m²/d + k ≤ 0  (actual Riccati inequality, d = n−1)
    m̄' + m̄²/d + k̄ = 0  (model Riccati equation)
    k̄ ≤ k  on (0,T),
    |m t − d/t| ≤ C  and  |m̄ t − d/t| ≤ C  on (0,t₀]   (quantitative Euclidean
                                                       normalization at the singular point)
    ⟹  m t ≤ m̄ t  for every t ∈ (0,T).

The comparison at the singular point `0` (where `m, m̄ → +∞` like `d/t`) is handled by the
classical ε-regularization: on `[ε, u]` the finite-interval comparison
(`riccati_delta_le_exp`) gives `δ u ≤ δ ε · exp(−∫_ε^u p)`, and the quantitative
normalization makes this bound `≤ 2C·(ε/u)²·exp(2C(u−ε)/d) → 0` as `ε → 0`.  There is
**no division at zero**: every division is by `ε > 0`, `s ≥ ε > 0`, or `d > 0`.

## Version 2 — corrected continuity domain (2026-09-11)

Version 1 of `riccati_le_of_singular_normalization` hypothesised
`ContinuousOn m (Icc 0 T)` *together with* `EuclideanNormalizedOn m d C t₀`.  These two
hypotheses are **jointly inconsistent**: the normalization forces `m t ≥ d/t − C → +∞` as
`t → 0⁺`, while continuity on `[0,T]` forces `m t → m 0 ∈ ℝ`.  A theorem with inconsistent
hypotheses is vacuous and must not be shipped as a comparison theorem.  Version 2 states
continuity on the correct interval `Ioc 0 T = (0,T]` (continuity is only ever used on
`[ε, u]` with `ε > 0`); the inconsistency of the v1 combination is proved as
`euclideanNormalizedOn_not_continuousOn_zero` below, and non-vacuity of v2 is witnessed by
the Euclidean model `m t = d/t` in `ModelEuclidean.lean`.

The mirrored direction (inequality `≥ 0` for `m`, `k ≤ k̄`) — the engine of the Rauch I
(lower) comparison — is `riccati_delta_ge_exp` / `riccati_ge_of_initial` /
`riccati_ge_of_singular_normalization`, with the shared ε-regularization bound factored
into the private lemma `exp_neg_integral_le_of_normalization`.
-/
import Poincare.D12.ComparisonGeodesics.Definitions
import Mathlib.MeasureTheory.Integral.IntegrableOn

noncomputable section

open Set Filter
open scoped Topology
open MeasureTheory

namespace Poincare.D12.ComparisonGeodesics

/-! ## Finite-interval Riccati comparison (regular point) -/

/-- **Finite-interval Riccati comparison (upper direction).**  If `m' + m²/d + k ≤ 0`,
`m̄' + m̄²/d + k̄ = 0` and `k̄ ≤ k` on `(a,b)`, then the difference `δ = m − m̄` satisfies
`δ t ≤ δ a · exp(−∫ₐᵗ (m + m̄)/d)` on `[a,b]`.  In particular `δ a ≤ 0` implies
`m ≤ m̄` on `[a,b]` (see `riccati_le_of_initial`). -/
theorem riccati_delta_le_exp {d : ℝ} {k kbar m dm mbar dmbar : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hdne : d ≠ 0)
    (hineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → dm t + m t ^ 2 / d + k t ≤ 0)
    (heq : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → dmbar t + mbar t ^ 2 / d + kbar t = 0)
    (hkk : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → kbar t ≤ k t)
    (hm : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → HasDerivAtR m (dm t) t)
    (hmbar : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → HasDerivAtR mbar (dmbar t) t)
    (hmcont : ContinuousOn m (Icc a b)) (hmbarcont : ContinuousOn mbar (Icc a b)) :
    ∀ ⦃t : ℝ⦄, t ∈ Icc a b →
      m t - mbar t ≤ (m a - mbar a) * Real.exp (-∫ x in a..t, (m x + mbar x) / d) := by
  set δ : ℝ → ℝ := fun t => m t - mbar t with hδdef
  set p : ℝ → ℝ := fun t => (m t + mbar t) / d with hpdef
  have hpcont : ContinuousOn p (Icc a b) := by
    change ContinuousOn (fun t => (m t + mbar t) / d) (Icc a b)
    exact (hmcont.add hmbarcont).div_const d
  have hδcont : ContinuousOn δ (Icc a b) := by
    change ContinuousOn (fun t => m t - mbar t) (Icc a b)
    exact hmcont.sub hmbarcont
  -- The Riccati inequality for δ: δ' + p·δ ≤ 0 on (a,b).
  have hdelta_ineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → (dm t - dmbar t) + p t * δ t ≤ 0 := by
    intro t ht
    have hmain : (dm t - dmbar t) + p t * δ t
        = (dm t + m t ^ 2 / d) - (dmbar t + mbar t ^ 2 / d) := by
      change (dm t - dmbar t) + (m t + mbar t) / d * (m t - mbar t)
        = (dm t + m t ^ 2 / d) - (dmbar t + mbar t ^ 2 / d)
      field_simp [hdne]
      ring
    rw [hmain]
    have h1 : dm t + m t ^ 2 / d ≤ -k t := by linarith [hineq ht]
    have h2 : dmbar t + mbar t ^ 2 / d = -kbar t := by linarith [heq ht]
    have hle : (dm t + m t ^ 2 / d) - (dmbar t + mbar t ^ 2 / d) ≤ -k t - -kbar t := by
      exact sub_le_sub h1 (by rw [h2])
    linarith [hle, hkk ht]
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
        (((dm t - dmbar t) + p t * δ t) * Real.exp (∫ x in a..t, p x)) t := by
    intro t ht
    have hδd : HasDerivAtR δ (dm t - dmbar t) t := by
      change HasDerivAtR (fun t => m t - mbar t) (dm t - dmbar t) t
      exact (hm ht).sub (hmbar ht)
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
  -- φ(a) = δ(a), so φ(t) ≤ δ(a), i.e. δ(t)·exp(∫ₐᵗ p) ≤ δ(a).
  intro t ht
  have hφt : δ t * Real.exp (∫ x in a..t, p x) ≤ δ a * Real.exp (∫ x in a..a, p x) :=
    hφantitone (Set.left_mem_Icc.mpr hab) ht ht.1
  have hφa : δ a * Real.exp (∫ x in a..a, p x) = δ a := by
    rw [intervalIntegral.integral_same, Real.exp_zero, mul_one]
  have hδtM : δ t * Real.exp (∫ x in a..t, p x) ≤ δ a := by
    rw [hφa] at hφt
    exact hφt
  have hδt : δ t ≤ δ a * (Real.exp (∫ x in a..t, p x))⁻¹ := by
    have hpos : 0 ≤ (Real.exp (∫ x in a..t, p x))⁻¹ :=
      inv_nonneg.mpr (Real.exp_pos _).le
    have hmul := mul_le_mul_of_nonneg_right hδtM hpos
    simpa [mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero _)] using hmul
  have hMinv : (Real.exp (∫ x in a..t, p x))⁻¹ = Real.exp (-∫ x in a..t, p x) := by
    rw [Real.exp_neg]
  change m t - mbar t ≤ (m a - mbar a) * Real.exp (-∫ x in a..t, (m x + mbar x) / d)
  change m t - mbar t ≤ (m a - mbar a) * Real.exp (-∫ x in a..t, p x)
  rw [← hMinv]
  change δ t ≤ δ a * (Real.exp (∫ x in a..t, p x))⁻¹
  exact hδt

/-- **Riccati comparison from a regular initial point.**  If `m a ≤ m̄ a` then `m ≤ m̄`
on all of `[a,b]`. -/
theorem riccati_le_of_initial {d : ℝ} {k kbar m dm mbar dmbar : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hdne : d ≠ 0)
    (hineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → dm t + m t ^ 2 / d + k t ≤ 0)
    (heq : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → dmbar t + mbar t ^ 2 / d + kbar t = 0)
    (hkk : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → kbar t ≤ k t)
    (hm : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → HasDerivAtR m (dm t) t)
    (hmbar : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → HasDerivAtR mbar (dmbar t) t)
    (hmcont : ContinuousOn m (Icc a b)) (hmbarcont : ContinuousOn mbar (Icc a b))
    (hδa : m a ≤ mbar a) :
    ∀ ⦃t : ℝ⦄, t ∈ Icc a b → m t ≤ mbar t := by
  intro t ht
  have hδ := riccati_delta_le_exp hab hdne hineq heq hkk hm hmbar hmcont hmbarcont ht
  have hδa_nonpos : (m a - mbar a) * Real.exp (-∫ x in a..t, (m x + mbar x) / d) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hδa) (Real.exp_pos _).le
  linarith

/-! ## Finite-interval Riccati comparison, lower direction -/

/-- **Finite-interval Riccati comparison (lower direction).**  If `0 ≤ m' + m²/d + k`,
`m̄' + m̄²/d + k̄ = 0` and `k ≤ k̄` on `(a,b)`, then the difference `δ = m − m̄` satisfies
`δ a · exp(−∫ₐᵗ (m + m̄)/d) ≤ δ t` on `[a,b]`.  In particular `m̄ a ≤ m a` implies
`m̄ ≤ m` on `[a,b]` (see `riccati_ge_of_initial`). -/
theorem riccati_delta_ge_exp {d : ℝ} {k kbar m dm mbar dmbar : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hdne : d ≠ 0)
    (hineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → 0 ≤ dm t + m t ^ 2 / d + k t)
    (heq : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → dmbar t + mbar t ^ 2 / d + kbar t = 0)
    (hkk : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → k t ≤ kbar t)
    (hm : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → HasDerivAtR m (dm t) t)
    (hmbar : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → HasDerivAtR mbar (dmbar t) t)
    (hmcont : ContinuousOn m (Icc a b)) (hmbarcont : ContinuousOn mbar (Icc a b)) :
    ∀ ⦃t : ℝ⦄, t ∈ Icc a b →
      (m a - mbar a) * Real.exp (-∫ x in a..t, (m x + mbar x) / d) ≤ m t - mbar t := by
  set δ : ℝ → ℝ := fun t => m t - mbar t with hδdef
  set p : ℝ → ℝ := fun t => (m t + mbar t) / d with hpdef
  have hpcont : ContinuousOn p (Icc a b) := by
    change ContinuousOn (fun t => (m t + mbar t) / d) (Icc a b)
    exact (hmcont.add hmbarcont).div_const d
  have hδcont : ContinuousOn δ (Icc a b) := by
    change ContinuousOn (fun t => m t - mbar t) (Icc a b)
    exact hmcont.sub hmbarcont
  -- The Riccati inequality for δ: 0 ≤ δ' + p·δ on (a,b).
  have hdelta_ineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → 0 ≤ (dm t - dmbar t) + p t * δ t := by
    intro t ht
    have hmain : (dm t - dmbar t) + p t * δ t
        = (dm t + m t ^ 2 / d) - (dmbar t + mbar t ^ 2 / d) := by
      change (dm t - dmbar t) + (m t + mbar t) / d * (m t - mbar t)
        = (dm t + m t ^ 2 / d) - (dmbar t + mbar t ^ 2 / d)
      field_simp [hdne]
      ring
    rw [hmain]
    have h1 : -k t ≤ dm t + m t ^ 2 / d := by linarith [hineq ht]
    have h2 : dmbar t + mbar t ^ 2 / d = -kbar t := by linarith [heq ht]
    have hle : -k t - -kbar t ≤ (dm t + m t ^ 2 / d) - (dmbar t + mbar t ^ 2 / d) := by
      exact sub_le_sub h1 (by rw [h2])
    linarith [hle, hkk ht]
  -- The integrating factor M = exp(∫ₐ p) and φ = δ·M; now φ is monotone.
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
        (((dm t - dmbar t) + p t * δ t) * Real.exp (∫ x in a..t, p x)) t := by
    intro t ht
    have hδd : HasDerivAtR δ (dm t - dmbar t) t := by
      change HasDerivAtR (fun t => m t - mbar t) (dm t - dmbar t) t
      exact (hm ht).sub (hmbar ht)
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
  have hφmono : MonotoneOn (fun s => δ s * Real.exp (∫ x in a..s, p x)) (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) hφcont ?_ ?_
    · simpa [interior_Icc] using hφdiff
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hφderiv ht).deriv]
      exact mul_nonneg (hdelta_ineq ht) (Real.exp_pos _).le
  -- φ(a) = δ(a), so δ(a) ≤ φ(t), i.e. δ(a) ≤ δ(t)·exp(∫ₐᵗ p).
  intro t ht
  have hφt : δ a * Real.exp (∫ x in a..a, p x) ≤ δ t * Real.exp (∫ x in a..t, p x) :=
    hφmono (Set.left_mem_Icc.mpr hab) ht ht.1
  have hφa : δ a * Real.exp (∫ x in a..a, p x) = δ a := by
    rw [intervalIntegral.integral_same, Real.exp_zero, mul_one]
  have hδtM : δ a ≤ δ t * Real.exp (∫ x in a..t, p x) := by
    rw [hφa] at hφt
    exact hφt
  have hδt : δ a * (Real.exp (∫ x in a..t, p x))⁻¹ ≤ δ t := by
    have hpos : 0 ≤ (Real.exp (∫ x in a..t, p x))⁻¹ :=
      inv_nonneg.mpr (Real.exp_pos _).le
    have hmul := mul_le_mul_of_nonneg_right hδtM hpos
    simpa [mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero _)] using hmul
  have hMinv : (Real.exp (∫ x in a..t, p x))⁻¹ = Real.exp (-∫ x in a..t, p x) := by
    rw [Real.exp_neg]
  change (m a - mbar a) * Real.exp (-∫ x in a..t, (m x + mbar x) / d) ≤ m t - mbar t
  change δ a * Real.exp (-∫ x in a..t, p x) ≤ δ t
  rw [← hMinv]
  exact hδt

/-- **Riccati comparison from a regular initial point, lower direction.**  If `m̄ a ≤ m a`
then `m̄ ≤ m` on all of `[a,b]`. -/
theorem riccati_ge_of_initial {d : ℝ} {k kbar m dm mbar dmbar : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hdne : d ≠ 0)
    (hineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → 0 ≤ dm t + m t ^ 2 / d + k t)
    (heq : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → dmbar t + mbar t ^ 2 / d + kbar t = 0)
    (hkk : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → k t ≤ kbar t)
    (hm : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → HasDerivAtR m (dm t) t)
    (hmbar : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → HasDerivAtR mbar (dmbar t) t)
    (hmcont : ContinuousOn m (Icc a b)) (hmbarcont : ContinuousOn mbar (Icc a b))
    (hδa : mbar a ≤ m a) :
    ∀ ⦃t : ℝ⦄, t ∈ Icc a b → mbar t ≤ m t := by
  intro t ht
  have hδ := riccati_delta_ge_exp hab hdne hineq heq hkk hm hmbar hmcont hmbarcont ht
  have hδa_nonneg : 0 ≤ (m a - mbar a) * Real.exp (-∫ x in a..t, (m x + mbar x) / d) :=
    mul_nonneg (sub_nonneg.mpr hδa) (Real.exp_pos _).le
  linarith

/-! ## ε-regularization at the singular point: shared quantitative bound -/

/-- Both directions of the singular comparison need `|m ε − m̄ ε| ≤ 2C` for `ε ∈ (0,t₀]`
from the two Euclidean normalizations. -/
private theorem abs_sub_le_two_C {d C t₀ ε : ℝ} {m mbar : ℝ → ℝ} (hεt₀ : ε ∈ Ioo 0 t₀)
    (hnorm : EuclideanNormalizedOn m d C t₀) (hnormbar : EuclideanNormalizedOn mbar d C t₀) :
    |m ε - mbar ε| ≤ 2 * C := by
  have h₁ : |m ε - d / ε| ≤ C := hnorm hεt₀
  have h₂ : |mbar ε - d / ε| ≤ C := hnormbar hεt₀
  have htri : |(m ε - d / ε) - (mbar ε - d / ε)| ≤ C + C := by
    rw [abs_sub_le_iff]
    constructor
    · linarith [abs_sub_le_iff.mp h₁ |>.1, abs_sub_le_iff.mp h₂ |>.2]
    · linarith [abs_sub_le_iff.mp h₁ |>.2, abs_sub_le_iff.mp h₂ |>.1]
  have htri' : |m ε - mbar ε| ≤ C + C := by
    have hsub : (m ε - d / ε) - (mbar ε - d / ε) = m ε - mbar ε := by ring
    simpa [hsub] using htri
  simpa [two_mul] using htri'

/-- **Quantitative upper bound for the model comparison exponential.**  If `m, m̄` both
satisfy the Euclidean normalization `|· − d/t| ≤ C` on `(0,t₀]` then
`exp(−∫_ε^u (m + m̄)/d) ≤ (ε/u)² · exp(2C(u − ε)/d)` for every `ε ∈ (0, u)`, `u ≤ t₀`.
This is the ε-regularization bound shared by both directions of the singular Riccati
comparison. -/
private theorem exp_neg_integral_le_of_normalization {d C u t₀ : ℝ} {m mbar : ℝ → ℝ}
    (hdpos : 0 < d) (_hC : 0 ≤ C) (hu : 0 < u) (hu_le_t₀ : u ≤ t₀)
    (hnorm : EuclideanNormalizedOn m d C t₀) (hnormbar : EuclideanNormalizedOn mbar d C t₀)
    (hpcont : ContinuousOn (fun t => (m t + mbar t) / d) (Ioc 0 u)) :
    ∀ ε ∈ Ioo 0 u,
      Real.exp (-∫ x in ε..u, (m x + mbar x) / d)
        ≤ (ε / u) ^ 2 * Real.exp (2 * C * (u - ε) / d) := by
  intro ε hε
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hp_lower : ∀ s ∈ Ioo ε u, 2 / s - 2 * C / d ≤ (m s + mbar s) / d := by
    intro s hs
    have hst₀ : s ∈ Ioo 0 t₀ := ⟨lt_trans hε.1 hs.1, lt_of_lt_of_le hs.2 hu_le_t₀⟩
    have hm₁ : |m s - d / s| ≤ C := hnorm hst₀
    have hm₂ : |mbar s - d / s| ≤ C := hnormbar hst₀
    have hm_lb : d / s - C ≤ m s := by linarith [abs_sub_le_iff.mp hm₁ |>.2]
    have hmbar_lb : d / s - C ≤ mbar s := by linarith [abs_sub_le_iff.mp hm₂ |>.2]
    have hsum : 2 * (d / s) - 2 * C ≤ m s + mbar s := by linarith
    have hdiv : (2 * (d / s) - 2 * C) / d ≤ (m s + mbar s) / d :=
      div_le_div_of_nonneg_right hsum (le_of_lt hdpos)
    have hcalc : 2 / s - 2 * C / d = (2 * (d / s) - 2 * C) / d := by
      field_simp [hdne]
    rw [hcalc]
    exact hdiv
  have hfcont : ContinuousOn (fun x : ℝ => 2 / x - 2 * C / d) (Icc ε u) := by
    exact ((continuousOn_inv₀.mono (by
      intro x hx
      exact ne_of_gt (lt_of_lt_of_le hε.1 hx.1))).const_mul 2).sub continuousOn_const
  have hfint : IntervalIntegrable (fun x : ℝ => 2 / x - 2 * C / d) volume ε u :=
    (hfcont.mono (by intro x hx; rw [uIcc_of_le (a := ε) (b := u) (le_of_lt hε.2)] at hx; exact hx)).intervalIntegrable
  have hgint : IntervalIntegrable (fun x : ℝ => (m x + mbar x) / d) volume ε u :=
    (hpcont.mono (by
      intro x hx
      rw [uIcc_of_le (a := ε) (b := u) (le_of_lt hε.2)] at hx
      exact ⟨lt_of_lt_of_le hε.1 hx.1, hx.2⟩)).intervalIntegrable
  have hint_lower : ∫ x in ε..u, 2 / x - 2 * C / d ≤ ∫ x in ε..u, (m x + mbar x) / d := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt hε.2) hfint hgint ?_
    intro x hx
    exact hp_lower x hx
  have hlog : ∫ x in ε..u, (fun x : ℝ => x⁻¹) x = Real.log u - Real.log ε := by
    have hderiv : ∀ x ∈ uIcc ε u, HasDerivAt Real.log (x⁻¹) x := by
      intro x hx
      rw [uIcc_of_le (a := ε) (b := u) (le_of_lt hε.2)] at hx
      exact Real.hasDerivAt_log (ne_of_gt (lt_of_lt_of_le hε.1 hx.1))
    have hint : IntervalIntegrable (fun x : ℝ => x⁻¹) volume ε u := by
      exact (continuousOn_inv₀.mono (by
        intro x hx
        rw [uIcc_of_le (a := ε) (b := u) (le_of_lt hε.2)] at hx
        exact ne_of_gt (lt_of_lt_of_le hε.1 hx.1))).intervalIntegrable
    have hlog' : ∫ x in ε..u, (fun x : ℝ => x⁻¹) x = Real.log u - Real.log ε :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    exact hlog'
  have hfint₁ : IntervalIntegrable (fun x : ℝ => 2 / x) volume ε u := by
    exact ((continuousOn_inv₀.mono (by
      intro x hx
      rw [uIcc_of_le (a := ε) (b := u) (le_of_lt hε.2)] at hx
      exact ne_of_gt (lt_of_lt_of_le hε.1 hx.1))).const_mul 2).intervalIntegrable
  have hgint₁ : IntervalIntegrable (fun _ : ℝ => (2 * C / d : ℝ)) volume ε u :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ => (2 * C / d : ℝ)) (uIcc ε u)).intervalIntegrable
  have hint_main : ∫ x in ε..u, (2 / x - 2 * C / d) =
      2 * (Real.log u - Real.log ε) - 2 * C * (u - ε) / d := by
    rw [intervalIntegral.integral_sub (f := fun x : ℝ => 2 / x) hfint₁ hgint₁]
    congr 1
    · change (∫ x in ε..u, (2 : ℝ) * x⁻¹) = 2 * (Real.log u - Real.log ε)
      rw [intervalIntegral.integral_const_mul]
      exact congrArg (fun z : ℝ => 2 * z) hlog
    · rw [intervalIntegral.integral_const]
      ring
  have hexp_upper : Real.exp (-∫ x in ε..u, (m x + mbar x) / d)
      ≤ (ε / u) ^ 2 * Real.exp (2 * C * (u - ε) / d) := by
    have h₁ : ∫ x in ε..u, (m x + mbar x) / d ≥
        2 * (Real.log u - Real.log ε) - 2 * C * (u - ε) / d := by
      rw [← hint_main]
      exact hint_lower
    have h₂ : -∫ x in ε..u, (m x + mbar x) / d ≤
        -(2 * (Real.log u - Real.log ε) - 2 * C * (u - ε) / d) := by
      linarith
    have h₃ : Real.exp (-∫ x in ε..u, (m x + mbar x) / d)
        ≤ Real.exp (-(2 * (Real.log u - Real.log ε) - 2 * C * (u - ε) / d)) := by
      exact Real.exp_le_exp.mpr h₂
    have h₄ : Real.exp (-(2 * (Real.log u - Real.log ε) - 2 * C * (u - ε) / d))
        = Real.exp (2 * (Real.log ε - Real.log u) + 2 * C * (u - ε) / d) := by
      congr 1
      ring
    have h₅ : Real.exp (2 * (Real.log ε - Real.log u) + 2 * C * (u - ε) / d)
        = (ε / u) ^ 2 * Real.exp (2 * C * (u - ε) / d) := by
      rw [Real.exp_add]
      congr 1
      have hεu : 0 < ε / u := div_pos hε.1 hu
      have hlogpow : Real.exp (2 * (Real.log ε - Real.log u)) = (ε / u) ^ 2 := by
        have h₁ : 2 * (Real.log ε - Real.log u) = Real.log ((ε / u) ^ 2) := by
          rw [← Real.log_div (ne_of_gt hε.1) (ne_of_gt hu)]
          rw [pow_two, Real.log_mul (ne_of_gt hεu) (ne_of_gt hεu)]
          ring
        rw [h₁]
        exact Real.exp_log (pow_pos hεu 2)
      exact hlogpow
    rw [h₄] at h₃
    rw [h₅] at h₃
    exact h₃
  exact hexp_upper

/-! ## Singular Riccati comparison, upper direction -/

/-- **Singular Riccati comparison (v2, corrected domain).**  With the quantitative
Euclidean normalization `|m t − d/t| ≤ C`, `|m̄ t − d/t| ≤ C` on `(0,t₀]`, the Riccati
inequality `m' + m²/d + k ≤ 0` for `m`, the Riccati equality for `m̄`, and `k̄ ≤ k` on
`(0,T)`, one has `m t ≤ m̄ t` for every `t ∈ (0,T)`.  Continuity of `m, m̄` is required on
`Ioc 0 T = (0,T]` — the normalization replaces the singular boundary condition, and (as
proved in `euclideanNormalizedOn_not_continuousOn_zero`) continuity up to `0` would be
inconsistent with the normalization.  The proof is the classical ε-regularization: the
finite-interval comparison gives `δ u ≤ δ ε · exp(−∫_ε^u p)`, which the normalization
bounds by `2C·(ε/u)²·exp(2C(u−ε)/d) → 0` as `ε → 0⁺`; then the regular comparison
propagates `δ ≤ 0` from `t₀` to all of `(0,T)`. -/
theorem riccati_le_of_singular_normalization {d : ℝ} {T C t₀ : ℝ} {k kbar m dm mbar dmbar : ℝ → ℝ}
    (hdpos : 0 < d) (_hT : 0 < T) (hC : 0 ≤ C) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (hineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → dm t + m t ^ 2 / d + k t ≤ 0)
    (heq : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → dmbar t + mbar t ^ 2 / d + kbar t = 0)
    (hkk : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → kbar t ≤ k t)
    (hm : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR m (dm t) t)
    (hmbar : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR mbar (dmbar t) t)
    (hmcont : ContinuousOn m (Ioc 0 T)) (hmbarcont : ContinuousOn mbar (Ioc 0 T))
    (hnorm : EuclideanNormalizedOn m d C t₀) (hnormbar : EuclideanNormalizedOn mbar d C t₀) :
    ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → m t ≤ mbar t := by
  have hdne : d ≠ 0 := ne_of_gt hdpos
  -- Step 1: on (0,t₀], δ ≤ 0 by the ε → 0 regularization.
  have hstage1 : ∀ ⦃u : ℝ⦄, u ∈ Ioc 0 t₀ → m u ≤ mbar u := by
    intro u hu
    have huT2 : u ≤ T := le_trans hu.2 ht₀T
    have hpcont : ContinuousOn (fun t => (m t + mbar t) / d) (Ioc 0 u) := by
      exact ((hmcont.mono (by intro x hx; exact ⟨hx.1, le_trans hx.2 huT2⟩)).add
        (hmbarcont.mono (by intro x hx; exact ⟨hx.1, le_trans hx.2 huT2⟩))).div_const d
    have hδle_eps : ∀ ε ∈ Ioo 0 u,
        m u - mbar u ≤ (m ε - mbar ε) * Real.exp (-∫ x in ε..u, (m x + mbar x) / d) := by
      intro ε hε
      have hδ := riccati_delta_le_exp (a := ε) (b := u) (le_of_lt hε.2) hdne
        (fun t ht => hineq (Ioo_subset_Ioo (le_of_lt hε.1) huT2 ht))
        (fun t ht => heq (Ioo_subset_Ioo (le_of_lt hε.1) huT2 ht))
        (fun t ht => hkk (Ioo_subset_Ioo (le_of_lt hε.1) huT2 ht))
        (fun t ht => hm (Ioo_subset_Ioo (le_of_lt hε.1) huT2 ht))
        (fun t ht => hmbar (Ioo_subset_Ioo (le_of_lt hε.1) huT2 ht))
        (hmcont.mono (by intro x hx; exact ⟨lt_of_lt_of_le hε.1 hx.1, le_trans hx.2 huT2⟩))
        (hmbarcont.mono (by intro x hx; exact ⟨lt_of_lt_of_le hε.1 hx.1, le_trans hx.2 huT2⟩))
        (Set.right_mem_Icc.mpr (le_of_lt hε.2))
      exact hδ
    -- The quantitative bound for each ε ∈ (0,u): δ u ≤ 2C·(ε/u)²·exp(2C(u−ε)/d).
    have hbound : ∀ ε ∈ Ioo 0 u,
        m u - mbar u ≤ 2 * C * (ε / u) ^ 2 * Real.exp (2 * C * (u - ε) / d) := by
      intro ε hε
      have hεt₀ : ε ∈ Ioo 0 t₀ := ⟨hε.1, lt_of_lt_of_le hε.2 hu.2⟩
      have hδε : |m ε - mbar ε| ≤ 2 * C := abs_sub_le_two_C hεt₀ hnorm hnormbar
      have hδε_le : m ε - mbar ε ≤ 2 * C := le_trans (le_abs_self _) hδε
      have hexp_upper :=
        exp_neg_integral_le_of_normalization hdpos hC hu.1 hu.2 hnorm hnormbar hpcont ε hε
      have hδ₁ := hδle_eps ε hε
      have hδε_nonneg_exp : (m ε - mbar ε) * Real.exp (-∫ x in ε..u, (m x + mbar x) / d) ≤
          2 * C * Real.exp (-∫ x in ε..u, (m x + mbar x) / d) :=
        mul_le_mul_of_nonneg_right hδε_le (Real.exp_pos _).le
      have hmain : (m ε - mbar ε) * Real.exp (-∫ x in ε..u, (m x + mbar x) / d) ≤
          2 * C * ((ε / u) ^ 2 * Real.exp (2 * C * (u - ε) / d)) := by
        exact le_trans hδε_nonneg_exp
          (mul_le_mul_of_nonneg_left hexp_upper (mul_nonneg zero_le_two hC))
      linarith
    -- ε → 0: the RHS tends to 0.
    have hlim : Tendsto (fun ε : ℝ => 2 * C * (ε / u) ^ 2 * Real.exp (2 * C * (u - ε) / d))
        (𝓝[>] 0) (𝓝 0) := by
      have hcont : ContinuousAt (fun ε : ℝ => 2 * C * (ε / u) ^ 2 * Real.exp (2 * C * (u - ε) / d)) 0 := by
        fun_prop
      have hval : 2 * C * (0 / u) ^ 2 * Real.exp (2 * C * (u - 0) / d) = 0 := by simp
      simpa only [hval] using hcont.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
    have hev : ∀ᶠ ε in 𝓝[>] 0,
        m u - mbar u ≤ 2 * C * (ε / u) ^ 2 * Real.exp (2 * C * (u - ε) / d) := by
      change {ε | m u - mbar u ≤ 2 * C * (ε / u) ^ 2 * Real.exp (2 * C * (u - ε) / d)} ∈ 𝓝[>] 0
      rw [mem_nhdsWithin]
      refine ⟨Ioo (-u) u, isOpen_Ioo, ⟨neg_lt_zero.mpr hu.1, hu.1⟩, ?_⟩
      intro ε hε
      have hεIoo : ε ∈ Ioo 0 u := ⟨hε.2, hε.1.2⟩
      exact hbound ε hεIoo
    have hδu_le : m u - mbar u ≤ 0 :=
      le_of_tendsto_of_tendsto_of_frequently tendsto_const_nhds hlim (Eventually.frequently hev)
    linarith
  -- Step 2: propagate from t₀ to all of (0,T) using the regular comparison.
  intro t ht
  by_cases hle : t ≤ t₀
  · exact hstage1 ⟨ht.1, hle⟩
  · have ht₀t : t₀ < t := lt_of_not_ge hle
    have hδt₀ : m t₀ ≤ mbar t₀ := hstage1 ⟨ht₀, le_rfl⟩
    exact riccati_le_of_initial (le_of_lt ht₀t) hdne
      (fun s hs => hineq (Ioo_subset_Ioo (le_of_lt ht₀) (show t ≤ T from le_of_lt ht.2) hs))
      (fun s hs => heq (Ioo_subset_Ioo (le_of_lt ht₀) (show t ≤ T from le_of_lt ht.2) hs))
      (fun s hs => hkk (Ioo_subset_Ioo (le_of_lt ht₀) (show t ≤ T from le_of_lt ht.2) hs))
      (fun s hs => hm (Ioo_subset_Ioo (le_of_lt ht₀) (show t ≤ T from le_of_lt ht.2) hs))
      (fun s hs => hmbar (Ioo_subset_Ioo (le_of_lt ht₀) (show t ≤ T from le_of_lt ht.2) hs))
      (hmcont.mono (by intro x hx; exact ⟨lt_of_lt_of_le ht₀ hx.1, le_trans hx.2 (le_of_lt ht.2)⟩))
      (hmbarcont.mono (by intro x hx; exact ⟨lt_of_lt_of_le ht₀ hx.1, le_trans hx.2 (le_of_lt ht.2)⟩))
      hδt₀ (Set.right_mem_Icc.mpr (le_of_lt ht₀t))

/-! ## Singular Riccati comparison, lower direction -/

/-- **Singular Riccati comparison, lower direction (v2).**  With the quantitative
Euclidean normalization `|m t − d/t| ≤ C`, `|m̄ t − d/t| ≤ C` on `(0,t₀]`, the Riccati
inequality `0 ≤ m' + m²/d + k` for `m`, the Riccati equality for `m̄`, and `k ≤ k̄` on
`(0,T)`, one has `m̄ t ≤ m t` for every `t ∈ (0,T)`.  Continuity is required on
`Ioc 0 T = (0,T]` (see the version-2 note in the header).  This is the engine of the
Rauch I (lower) comparison `u ≥ j_K` for the scalar Jacobi equation. -/
theorem riccati_ge_of_singular_normalization {d : ℝ} {T C t₀ : ℝ} {k kbar m dm mbar dmbar : ℝ → ℝ}
    (hdpos : 0 < d) (_hT : 0 < T) (hC : 0 ≤ C) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (hineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → 0 ≤ dm t + m t ^ 2 / d + k t)
    (heq : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → dmbar t + mbar t ^ 2 / d + kbar t = 0)
    (hkk : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → k t ≤ kbar t)
    (hm : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR m (dm t) t)
    (hmbar : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR mbar (dmbar t) t)
    (hmcont : ContinuousOn m (Ioc 0 T)) (hmbarcont : ContinuousOn mbar (Ioc 0 T))
    (hnorm : EuclideanNormalizedOn m d C t₀) (hnormbar : EuclideanNormalizedOn mbar d C t₀) :
    ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → mbar t ≤ m t := by
  have hdne : d ≠ 0 := ne_of_gt hdpos
  -- Step 1: on (0,t₀], m̄ ≤ m by the ε → 0 regularization.
  have hstage1 : ∀ ⦃u : ℝ⦄, u ∈ Ioc 0 t₀ → mbar u ≤ m u := by
    intro u hu
    have huT2 : u ≤ T := le_trans hu.2 ht₀T
    have hpcont : ContinuousOn (fun t => (m t + mbar t) / d) (Ioc 0 u) := by
      exact ((hmcont.mono (by intro x hx; exact ⟨hx.1, le_trans hx.2 huT2⟩)).add
        (hmbarcont.mono (by intro x hx; exact ⟨hx.1, le_trans hx.2 huT2⟩))).div_const d
    have hδge_eps : ∀ ε ∈ Ioo 0 u,
        (m ε - mbar ε) * Real.exp (-∫ x in ε..u, (m x + mbar x) / d) ≤ m u - mbar u := by
      intro ε hε
      have hδ := riccati_delta_ge_exp (a := ε) (b := u) (le_of_lt hε.2) hdne
        (fun t ht => hineq (Ioo_subset_Ioo (le_of_lt hε.1) huT2 ht))
        (fun t ht => heq (Ioo_subset_Ioo (le_of_lt hε.1) huT2 ht))
        (fun t ht => hkk (Ioo_subset_Ioo (le_of_lt hε.1) huT2 ht))
        (fun t ht => hm (Ioo_subset_Ioo (le_of_lt hε.1) huT2 ht))
        (fun t ht => hmbar (Ioo_subset_Ioo (le_of_lt hε.1) huT2 ht))
        (hmcont.mono (by intro x hx; exact ⟨lt_of_lt_of_le hε.1 hx.1, le_trans hx.2 huT2⟩))
        (hmbarcont.mono (by intro x hx; exact ⟨lt_of_lt_of_le hε.1 hx.1, le_trans hx.2 huT2⟩))
        (Set.right_mem_Icc.mpr (le_of_lt hε.2))
      exact hδ
    -- The quantitative bound for each ε ∈ (0,u): −δ u ≤ 2C·(ε/u)²·exp(2C(u−ε)/d).
    have hbound : ∀ ε ∈ Ioo 0 u,
        -(m u - mbar u) ≤ 2 * C * (ε / u) ^ 2 * Real.exp (2 * C * (u - ε) / d) := by
      intro ε hε
      have hεt₀ : ε ∈ Ioo 0 t₀ := ⟨hε.1, lt_of_lt_of_le hε.2 hu.2⟩
      have hδε : |m ε - mbar ε| ≤ 2 * C := abs_sub_le_two_C hεt₀ hnorm hnormbar
      have hδε_lower : -2 * C ≤ m ε - mbar ε := by
        have h₁ : -|m ε - mbar ε| ≤ m ε - mbar ε := neg_abs_le _
        linarith
      have hexp_upper :=
        exp_neg_integral_le_of_normalization hdpos hC hu.1 hu.2 hnorm hnormbar hpcont ε hε
      have hδ₁ := hδge_eps ε hε
      have hnonneg : 0 ≤ Real.exp (-∫ x in ε..u, (m x + mbar x) / d) := (Real.exp_pos _).le
      have hδ_low : -2 * C * ((ε / u) ^ 2 * Real.exp (2 * C * (u - ε) / d))
          ≤ (m ε - mbar ε) * Real.exp (-∫ x in ε..u, (m x + mbar x) / d) := by
        have h₁ : (-2 * C) * Real.exp (-∫ x in ε..u, (m x + mbar x) / d)
            ≤ (m ε - mbar ε) * Real.exp (-∫ x in ε..u, (m x + mbar x) / d) :=
          mul_le_mul_of_nonneg_right hδε_lower hnonneg
        have h₂ : (-2 * C) * ((ε / u) ^ 2 * Real.exp (2 * C * (u - ε) / d))
            ≤ (-2 * C) * Real.exp (-∫ x in ε..u, (m x + mbar x) / d) := by
          have hneg : -2 * C ≤ 0 := by linarith [mul_nonneg zero_le_two hC]
          exact mul_le_mul_of_nonpos_left hexp_upper hneg
        linarith
      have hmain : -2 * C * ((ε / u) ^ 2 * Real.exp (2 * C * (u - ε) / d)) ≤ m u - mbar u :=
        le_trans hδ_low hδ₁
      linarith
    -- ε → 0: the RHS tends to 0.
    have hlim : Tendsto (fun ε : ℝ => 2 * C * (ε / u) ^ 2 * Real.exp (2 * C * (u - ε) / d))
        (𝓝[>] 0) (𝓝 0) := by
      have hcont : ContinuousAt (fun ε : ℝ => 2 * C * (ε / u) ^ 2 * Real.exp (2 * C * (u - ε) / d)) 0 := by
        fun_prop
      have hval : 2 * C * (0 / u) ^ 2 * Real.exp (2 * C * (u - 0) / d) = 0 := by simp
      simpa only [hval] using hcont.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
    have hev : ∀ᶠ ε in 𝓝[>] 0,
        -(m u - mbar u) ≤ 2 * C * (ε / u) ^ 2 * Real.exp (2 * C * (u - ε) / d) := by
      change {ε | -(m u - mbar u) ≤ 2 * C * (ε / u) ^ 2 * Real.exp (2 * C * (u - ε) / d)} ∈ 𝓝[>] 0
      rw [mem_nhdsWithin]
      refine ⟨Ioo (-u) u, isOpen_Ioo, ⟨neg_lt_zero.mpr hu.1, hu.1⟩, ?_⟩
      intro ε hε
      have hεIoo : ε ∈ Ioo 0 u := ⟨hε.2, hε.1.2⟩
      exact hbound ε hεIoo
    have hδu_ge : 0 ≤ m u - mbar u := by
      have hneg : -(m u - mbar u) ≤ 0 :=
        le_of_tendsto_of_tendsto_of_frequently tendsto_const_nhds hlim (Eventually.frequently hev)
      linarith
    linarith
  -- Step 2: propagate from t₀ to all of (0,T) using the regular comparison.
  intro t ht
  by_cases hle : t ≤ t₀
  · exact hstage1 ⟨ht.1, hle⟩
  · have ht₀t : t₀ < t := lt_of_not_ge hle
    have hδt₀ : mbar t₀ ≤ m t₀ := hstage1 ⟨ht₀, le_rfl⟩
    exact riccati_ge_of_initial (le_of_lt ht₀t) hdne
      (fun s hs => hineq (Ioo_subset_Ioo (le_of_lt ht₀) (show t ≤ T from le_of_lt ht.2) hs))
      (fun s hs => heq (Ioo_subset_Ioo (le_of_lt ht₀) (show t ≤ T from le_of_lt ht.2) hs))
      (fun s hs => hkk (Ioo_subset_Ioo (le_of_lt ht₀) (show t ≤ T from le_of_lt ht.2) hs))
      (fun s hs => hm (Ioo_subset_Ioo (le_of_lt ht₀) (show t ≤ T from le_of_lt ht.2) hs))
      (fun s hs => hmbar (Ioo_subset_Ioo (le_of_lt ht₀) (show t ≤ T from le_of_lt ht.2) hs))
      (hmcont.mono (by intro x hx; exact ⟨lt_of_lt_of_le ht₀ hx.1, le_trans hx.2 (le_of_lt ht.2)⟩))
      (hmbarcont.mono (by intro x hx; exact ⟨lt_of_lt_of_le ht₀ hx.1, le_trans hx.2 (le_of_lt ht.2)⟩))
      hδt₀ (Set.right_mem_Icc.mpr (le_of_lt ht₀t))

/-! ## The v1 hypothesis combination is inconsistent (vacuity documentation) -/

/-- **The Euclidean normalization is incompatible with continuity at `0`.**  If
`|m t − d/t| ≤ C` holds on `(0, t₀]` with `d > 0` and `C ≥ 0`, then `m` cannot be
continuous on `[0, t₀]`: the normalization forces `m t ≥ d/t − C → +∞` as `t → 0⁺`.
This documents why the singular Riccati comparison must be stated with continuity on
`Ioc 0 T` (version 2): the version-1 hypothesis combination
`ContinuousOn m (Icc 0 T)` + `EuclideanNormalizedOn m d C t₀` is contradictory, so a
theorem stated under it would be vacuously true. -/
theorem euclideanNormalizedOn_not_continuousOn_zero {m : ℝ → ℝ} {d C t₀ : ℝ}
    (hdpos : 0 < d) (hC : 0 ≤ C) (ht₀ : 0 < t₀) (hnorm : EuclideanNormalizedOn m d C t₀) :
    ¬ ContinuousOn m (Icc 0 t₀) := by
  intro hcont
  have hten : Tendsto m (𝓝[Icc 0 t₀] 0) (𝓝 (m 0)) :=
    (hcont.continuousWithinAt (Set.left_mem_Icc.mpr ht₀.le)).tendsto
  have hdist : {y : ℝ | |y - m 0| < 1} ∈ 𝓝 (m 0) := by
    rw [mem_nhds_iff]
    refine ⟨Ioo (m 0 - 1) (m 0 + 1), ?_, ⟨isOpen_Ioo, ?_⟩⟩
    · intro y hy
      change |y - m 0| < 1
      rw [abs_sub_lt_iff]
      constructor <;> linarith [hy.1, hy.2]
    · constructor <;> linarith
  have hev : ∀ᶠ t in 𝓝[Icc 0 t₀] 0, |m t - m 0| < 1 := hten hdist
  change {t | |m t - m 0| < 1} ∈ 𝓝[Icc 0 t₀] 0 at hev
  rw [mem_nhdsWithin] at hev
  rcases hev with ⟨s, hso, hs0, hssub⟩
  rcases (Metric.isOpen_iff.mp hso) 0 hs0 with ⟨δ, hδpos, hδsub⟩
  let ε₀ : ℝ := d / (|m 0| + 1 + C)
  have hε₀pos : 0 < ε₀ := by
    unfold ε₀
    exact div_pos hdpos (by positivity)
  let t : ℝ := min (min (t₀ / 2) (δ / 2)) (ε₀ / 2)
  have htpos : 0 < t := by
    unfold t
    exact lt_min (lt_min (half_pos ht₀) (half_pos hδpos)) (half_pos hε₀pos)
  have ht_small : t < ε₀ := by
    unfold t
    exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε₀pos)
  have htδ : t < δ := by
    unfold t
    exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (half_lt_self hδpos)
  have ht₀lt : t < t₀ := by
    unfold t
    exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (half_lt_self ht₀)
  have htIoo : t ∈ Ioo 0 t₀ := ⟨htpos, ht₀lt⟩
  have htIcc : t ∈ Icc 0 t₀ := Ioo_subset_Icc_self htIoo
  have hts : t ∈ s := hδsub (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos]
    exact htδ)
  have hbnd₁ : |m t - m 0| < 1 := hssub ⟨hts, htIcc⟩
  have hm_upper : m t < |m 0| + 1 := by
    have htri : m t ≤ |m t - m 0| + |m 0| := by
      have h₁ : m t - m 0 ≤ |m t - m 0| := le_abs_self _
      linarith [h₁, le_abs_self (m 0)]
    linarith [htri, hbnd₁]
  have hm_lower : |m 0| + 1 ≤ m t := by
    have hnorm_t : |m t - d / t| ≤ C := hnorm htIoo
    have hgt : d / t - C ≥ |m 0| + 1 := by
      have htε₀ : t < ε₀ := ht_small
      -- d/t > d/ε₀ since t < ε₀ and d > 0
      have h₂ : d / ε₀ < d / t := div_lt_div_of_pos_left hdpos htpos htε₀
      have h₃ : d / ε₀ - C ≤ d / t - C := sub_le_sub_right (le_of_lt h₂) C
      have h₄ : d / ε₀ - C = |m 0| + 1 := by
        unfold ε₀
        field_simp [show d ≠ 0 from ne_of_gt hdpos]
        ring
      linarith
    have hmt : d / t - C ≤ m t := by
      have h₁ : d / t - m t ≤ |m t - d / t| := by
        have : |m t - d / t| = |d / t - m t| := abs_sub_comm _ _
        rw [this]
        exact le_abs_self _
      linarith [h₁, hnorm_t]
    linarith
  linarith

end Poincare.D12.ComparisonGeodesics
