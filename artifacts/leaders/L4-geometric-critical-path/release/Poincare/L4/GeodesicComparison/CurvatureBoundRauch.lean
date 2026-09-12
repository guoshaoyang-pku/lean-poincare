/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — Rauch I from a curvature bound (no separate second-derivative hypothesis)

`Poincare.L4.GeodesicComparison.RauchBridge` proves Rauch I from the quantitative
normalization `EuclideanNormalizedOn (u'/u) 1 (4B) t₀`, which it derives from the explicit
second-derivative bound `|u''| ≤ B`.  In the geometric reading, `u'' = −k·u`, so for `k ≥ 0`
and `0 ≤ u ≤ t` the bound `|u''| ≤ B` follows from the *curvature* bound `t·k(t) ≤ B` — a
strictly weaker, scale-correct hypothesis.  This file makes that derivation:

* `sub_le_of_deriv_le` — general (proved): the one-sided mean-value/FTC bound
  `f b − f a ≤ C (b−a)` from `f' ≤ C` on the interior.
* `rauch_upper_of_jacobi_of_curvBound` — **conditional** (proved): **Rauch I** `u'/u ≤ 1/t`
  on `(0,T)` from `k ≥ 0`, positivity of `u` on `(0,T]`, the Jacobi initial data
  `u 0 = 0`, `u' 0 = 1`, and the curvature bound `t·k(t) ≤ B` with `B t₀ ≤ 1/2`.
  The bound `|u''| ≤ B` is *derived*: `u' ≤ 1` (since `u'' = −k u ≤ 0`) gives `u ≤ t`
  (one-sided MVT), hence `|u''| = k·u ≤ k·t = t·k(t) ≤ B`, and the existing theorem
  `rauch_upper_of_jacobi` is then consumed with this constructed bound.
* `sin_rauch_curvBound_witness` — **model** (proved): the sine model satisfies the new
  curvature hypothesis `t·1 ≤ 1` on `(0,1/2)` and yields `cot t ≤ 1/t`.
* `jacobiSolTwo_rauch_curvBound_witness` — **model** (proved): the constant-curvature data
  `k = 2` satisfies `t·2 ≤ 1/2` on `(0,1/4)` and yields `j_2'(t)/j_2(t) ≤ 1/t`.

Semantic class: conditional analytic comparison, not the manifold-level Rauch theorem.
-/
import Poincare.L4.GeodesicComparison.ConstantCurvatureRauch
import Poincare.D10.JacobiConstantCurvature.Comparison

noncomputable section

open Set Filter
open scoped Topology
open MeasureTheory

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-! ## 1. The one-sided mean-value bound -/

/-- **One-sided mean-value/FTC bound.**  If `f` and `f'` are continuous on `[a,b]`, `f` has
derivative `f'` at every interior point, and `f' ≤ C` on `(a,b)`, then
`f b − f a ≤ C (b − a)`.  This is the inequality direction of
`abs_sub_le_of_deriv_bound`, with no lower bound on `f'`. -/
theorem sub_le_of_deriv_le {f f' : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hfcont : ContinuousOn f (Icc a b)) (hf'cont : ContinuousOn f' (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAtR f (f' t) t)
    (hbound : ∀ t ∈ Ioo a b, f' t ≤ C) :
    f b - f a ≤ C * (b - a) := by
  have hf'cont' : ContinuousOn f' (uIcc a b) := by rwa [uIcc_of_le hab]
  have hFTC : ∫ t in a..b, f' t = f b - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hfcont hderiv
      hf'cont'.intervalIntegrable
  have hmono : ∫ t in a..b, f' t ≤ ∫ t in a..b, C :=
    intervalIntegral.integral_mono_on_of_le_Ioo hab hf'cont'.intervalIntegrable
      intervalIntegrable_const hbound
  rw [hFTC, intervalIntegral.integral_const, smul_eq_mul] at hmono
  simpa [mul_comm] using hmono

/-! ## 2. Rauch I from the curvature bound `t·k(t) ≤ B` -/

/-- **Rauch I from a curvature bound.**  If `k ≥ 0` on `(0,T)`, the Jacobi solution is
positive on `(0,T]` with `u 0 = 0`, `u' 0 = 1`, and `t·k(t) ≤ B` with `0 ≤ B`,
`0 < t₀ ≤ T`, `B t₀ ≤ 1/2`, then `u' t/u t ≤ 1/t` on `(0,T)`.  The second-derivative bound
of `rauch_upper_of_jacobi` is derived from the curvature bound (via `u ≤ t`), so no
separate bound on `u''` is assumed. -/
theorem rauch_upper_of_jacobi_of_curvBound {k u du ddu : ℝ → ℝ} {T B t₀ : ℝ}
    (hT : 0 < T) (hBnn : 0 ≤ B) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hBt₀ : B * t₀ ≤ 1 / 2)
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) (hk : ∀ t ∈ Ioo 0 T, 0 ≤ k t)
    (hkbound : ∀ t ∈ Ioo 0 T, t * k t ≤ B) :
    ∀ t ∈ Ioo 0 T, du t / u t ≤ 1 / t := by
  -- `u'' = -k u ≤ 0`, hence `u'` is nonincreasing and `u' ≤ u' 0 = 1` on `(0,T)`.
  have hdu_le_one : ∀ t ∈ Ioo 0 T, du t ≤ 1 := by
    intro t ht
    have hmain := sub_le_of_deriv_le (f := du) (f' := ddu) (a := 0) (b := t) (C := 0) ht.1.le
      (h.continuousOn_du.mono (Icc_subset_Icc_right ht.2.le))
      (hdducont.mono (Icc_subset_Icc_right ht.2.le))
      (fun x hx => h.hasDerivAt_du ⟨hx.1, lt_trans hx.2 ht.2⟩)
      (fun x hx => by
        have hxT : x ∈ Ioo 0 T := ⟨hx.1, lt_trans hx.2 ht.2⟩
        rw [h.eq_secondDeriv hxT]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hk x hxT))
          (le_of_lt (hpos x ⟨hxT.1, hxT.2.le⟩)))
    simpa [hdu0] using hmain
  -- One-sided MVT with `u' ≤ 1`: `u t ≤ t` on `(0,T)`.
  have hu_le : ∀ t ∈ Ioo 0 T, u t ≤ t := by
    intro t ht
    have hmain := sub_le_of_deriv_le (f := u) (f' := du) (a := 0) (b := t) (C := 1) ht.1.le
      (h.continuousOn_u.mono (Icc_subset_Icc_right ht.2.le))
      (h.continuousOn_du.mono (Icc_subset_Icc_right ht.2.le))
      (fun x hx => h.hasDerivAt_u ⟨hx.1, lt_trans hx.2 ht.2⟩)
      (fun x hx => hdu_le_one x ⟨hx.1, lt_trans hx.2 ht.2⟩)
    simpa [hu0] using hmain
  -- Derive the second-derivative bound `|u''| ≤ B` from `t·k(t) ≤ B` and `u ≤ t`.
  have hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B := by
    intro t ht
    rw [h.eq_secondDeriv ht, abs_mul, abs_neg, abs_of_nonneg (hk t ht),
      abs_of_pos (hpos t ⟨ht.1, ht.2.le⟩)]
    have h1 : k t * u t ≤ k t * t := mul_le_mul_of_nonneg_left (hu_le t ht) (hk t ht)
    have h2 : k t * t = t * k t := by ring
    linarith [hkbound t ht]
  exact rauch_upper_of_jacobi hT hBnn ht₀ ht₀T hBt₀ h hdducont hB hu0 hdu0 hpos hk

/-! ## 3. Non-vacuity witnesses for the curvature-bound form -/

/-- **Curvature-bound witness (sine).**  `k = 1` satisfies `t·k(t) ≤ 1` on `(0,1/2)`, and
the conclusion `cot t ≤ 1/t` holds. -/
theorem sin_rauch_curvBound_witness :
    ∀ t ∈ Ioo (0 : ℝ) (1 / 2), Real.cos t / Real.sin t ≤ 1 / t := by
  have hmain := rauch_upper_of_jacobi_of_curvBound (T := 1 / 2) (B := 1) (t₀ := 1 / 2)
    (k := fun _ : ℝ => 1) (u := Real.sin) (du := Real.cos) (ddu := fun t => -Real.sin t)
    (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)
    sin_jacobiSolution
    (by fun_prop)
    (by simp) (by simp)
    (fun t ht => Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_gt_three]))
    (fun t ht => by norm_num)
    (fun t ht => by nlinarith [ht.2])
  intro t ht
  simpa using hmain t ht

/-- **Curvature-bound witness (constant curvature `k = 2`).**  The model Jacobi data with
`k = 2` satisfies `t·2 ≤ 1/2` on `(0,1/4)`, and the conclusion `j_2'(t)/j_2(t) ≤ 1/t`
(equivalently `√2·cot(√2 t) ≤ 1/t`) holds. -/
theorem jacobiSolTwo_rauch_curvBound_witness :
    ∀ t ∈ Ioo (0 : ℝ) (1 / 4), jacobiDeriv 2 t / jacobiSol 2 t ≤ 1 / t := by
  have hmain := rauch_upper_of_jacobi_of_curvBound (T := 1 / 4) (B := 1 / 2) (t₀ := 1 / 4)
    (k := fun _ : ℝ => 2) (u := jacobiSol 2) (du := jacobiDeriv 2)
    (ddu := fun t => -(2 * jacobiSol 2 t))
    (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)
    (jacobiSol_jacobiSolutionOn 2 (1 / 4))
    (((continuous_const.mul (continuous_jacobiSol 2)).neg).continuousOn)
    (jacobiSol_zero 2) (jacobiDeriv_zero 2)
    (fun t ht => jacobiSol_pos_of_nonneg (K := 2) (by norm_num) ht.1
      (Or.inr (by
        have h2 : Real.sqrt 2 < Real.pi := by
          have hlt : Real.sqrt 2 < 2 := by
            rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 2)]
            norm_num
          linarith [Real.pi_gt_three]
        calc Real.sqrt 2 * t ≤ Real.sqrt 2 * (1 / 4) :=
              mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg 2)
          _ < Real.pi := by nlinarith [h2, Real.sqrt_nonneg 2])))
    (fun t ht => by norm_num)
    (fun t ht => by nlinarith [ht.2])
  intro t ht
  exact hmain t ht

end Poincare.L4.GeodesicComparison
