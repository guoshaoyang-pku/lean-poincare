/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — the conjugate-point bound from Rauch comparison

`ConstantCurvatureRauch.lean` proves the sharp comparison `u ≤ j_K` on intervals `(0,T)`
with `√K T < π` (before the first zero of the model).  This file removes that hypothesis
from the *conclusion*: for `k ≥ K > 0` a positive Jacobi solution with the standard initial
data cannot live past `π/√K`.

* `JacobiSolutionOn.mono` — **general** (proved): restriction of a Jacobi solution to a
  smaller interval.
* `conjugate_point_bound` — **conditional** (proved): under the normalization hypotheses of
  `rauch_upper_of_jacobi_constCurv` (written for the full interval `(0,T)`), if `K > 0`,
  `k ≥ K` and `u > 0` on `(0,T]`, then `T ≤ π/√K`.
  Proof: for every `t < π/√K` choose `T''` with `t < T'' < min(T, π/√K)`; the integrated
  comparison on `(0,T'')` gives `u t ≤ j_K t`; pass to the limit `t → (π/√K)⁻` and use
  `j_K (π/√K) = 0` (D10 `jacobiSolSphere_firstZero`) against `u > 0` at `π/√K`.

Semantic class: conditional analytic (scalar ODE comparison).  This is not the
manifold-level conjugate-point theorem: the identification of `u` with a Jacobi field along
a geodesic is not formalized here.
-/
import Poincare.L4.GeodesicComparison.ConstantCurvatureRauch

noncomputable section

open Set Filter
open scoped Topology
open MeasureTheory

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-- **Restriction of a Jacobi solution.**  A `JacobiSolutionOn` on `(0,T)` restricts to any
smaller interval `(0,T')` with `T' ≤ T`. -/
theorem JacobiSolutionOn.mono {k u du ddu : ℝ → ℝ} {T T' : ℝ}
    (h : JacobiSolutionOn k u du ddu 0 T) (hT' : T' ≤ T) :
    JacobiSolutionOn k u du ddu 0 T' where
  hasDerivAt_u := fun _ ht => h.hasDerivAt_u ⟨ht.1, lt_of_lt_of_le ht.2 hT'⟩
  hasDerivAt_du := fun _ ht => h.hasDerivAt_du ⟨ht.1, lt_of_lt_of_le ht.2 hT'⟩
  eq_secondDeriv := fun _ ht => h.eq_secondDeriv ⟨ht.1, lt_of_lt_of_le ht.2 hT'⟩
  continuousOn_u := h.continuousOn_u.mono (Icc_subset_Icc_right hT')
  continuousOn_du := h.continuousOn_du.mono (Icc_subset_Icc_right hT')

/-- **Conjugate-point bound.**  If `k ≥ K > 0` on `(0,T)`, the Jacobi solution has the
standard initial data `u 0 = 0`, `u' 0 = 1`, is positive on `(0,T]`, has `|u''| ≤ B` with
`B t₀ ≤ 1/2`, and the model normalization threshold satisfies
`(K·max (1/√K) T) t₀ ≤ 1/2`, then `T ≤ π/√K`: no positive solution can pass the first
conjugate point of the comparison curvature. -/
theorem conjugate_point_bound {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ}
    (_hT : 0 < T) (hBnn : 0 ≤ B) (ht₀ : 0 < t₀) (_ht₀T : t₀ ≤ T) (hBt₀ : B * t₀ ≤ 1 / 2)
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B) (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) (hK : 0 < K) (hk : ∀ t ∈ Ioo 0 T, K ≤ k t)
    (hBmodel : (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2) :
    T ≤ Real.pi / Real.sqrt K := by
  by_contra hcon
  -- `x = π/√K` lies in the interior of `(0,T)`.
  have hxT : Real.pi / Real.sqrt K < T := not_le.mp hcon
  have hxpos : 0 < Real.pi / Real.sqrt K := div_pos Real.pi_pos (Real.sqrt_pos_of_pos hK)
  -- Comparison `u t ≤ j_K t` for every `t` below the conjugate point.
  have hcompare : ∀ t ∈ Ioo 0 (Real.pi / Real.sqrt K), u t ≤ jacobiSol K t := by
    intro t ht
    have hsqrtK : 0 < Real.sqrt K := Real.sqrt_pos_of_pos hK
    have htpi : Real.sqrt K * t < Real.pi := by
      have := mul_lt_mul_of_pos_left ht.2 hsqrtK
      rwa [mul_div_cancel₀ Real.pi hsqrtK.ne'] at this
    have htT : t < T := lt_trans ht.2 hxT
    -- `t₀` is strictly below the conjugate point, from the model threshold hypothesis.
    have ht₀pi : t₀ < Real.pi / Real.sqrt K := by
      have hsqrtK : 0 < Real.sqrt K := Real.sqrt_pos_of_pos hK
      have hKnn : 0 ≤ K := le_of_lt hK
      have hsqrtK_le : Real.sqrt K ≤ K * max (1 / Real.sqrt K) T := by
        have hsq : Real.sqrt K * Real.sqrt K = K := by
          simpa [sq] using Real.sq_sqrt hKnn
        have h1 : Real.sqrt K = K * (1 / Real.sqrt K) := by
          rw [mul_one_div, eq_div_iff hsqrtK.ne']
          exact hsq
        calc Real.sqrt K = K * (1 / Real.sqrt K) := h1
          _ ≤ K * max (1 / Real.sqrt K) T :=
              mul_le_mul_of_nonneg_left (le_max_left (1 / Real.sqrt K) T) hKnn
      have h2 : Real.sqrt K * t₀ ≤ 1 / 2 :=
        le_trans (mul_le_mul_of_nonneg_right hsqrtK_le ht₀.le) hBmodel
      have h3 : t₀ ≤ 1 / (2 * Real.sqrt K) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt K)]
        nlinarith [h2]
      have h4 : 1 / (2 * Real.sqrt K) < Real.pi / Real.sqrt K := by
        have heq : 1 / (2 * Real.sqrt K) = (1 / 2) / Real.sqrt K := by ring
        rw [heq, div_lt_div_iff_of_pos_right hsqrtK]
        linarith [Real.pi_gt_three]
      linarith
    -- pick `T''` with `max t t₀ < T'' < min T (π/√K)`.
    set m : ℝ := min T (Real.pi / Real.sqrt K) with hmdef
    have ht₀T_lt : t₀ < T := lt_trans ht₀pi hxT
    have htm : max t t₀ < m := max_lt (lt_min htT ht.2) (lt_min ht₀T_lt ht₀pi)
    set T'' : ℝ := (max t t₀ + m) / 2 with hT''def
    have htT'' : t < T'' := by
      rw [hT''def]; linarith [le_max_left t t₀]
    have ht₀T'' : t₀ ≤ T'' := by
      rw [hT''def]; linarith [le_max_right t t₀]
    have hT''m : T'' < m := by rw [hT''def]; linarith
    have hT''T : T'' ≤ T := le_of_lt (lt_of_lt_of_le hT''m (min_le_left _ _))
    have hT''pi : Real.sqrt K * T'' < Real.pi := by
      have h1 : T'' < Real.pi / Real.sqrt K := lt_of_lt_of_le hT''m (min_le_right _ _)
      have := mul_lt_mul_of_pos_left h1 hsqrtK
      rwa [mul_div_cancel₀ Real.pi hsqrtK.ne'] at this
    have hT''pos : 0 < T'' := lt_trans ht.1 htT''
    -- normalization threshold for the smaller interval
    have hBmodel'' : (K * max (1 / Real.sqrt K) T'') * t₀ ≤ 1 / 2 := by
      have hmax : max (1 / Real.sqrt K) T'' ≤ max (1 / Real.sqrt K) T :=
        max_le_max le_rfl hT''T
      have hKnn : 0 ≤ K := le_of_lt hK
      have h1 : K * max (1 / Real.sqrt K) T'' ≤ K * max (1 / Real.sqrt K) T :=
        mul_le_mul_of_nonneg_left hmax hKnn
      exact le_trans (mul_le_mul_of_nonneg_right h1 ht₀.le) hBmodel
    have hcmp := jacobi_le_constCurvModel (T := T'') (B := B) (t₀ := t₀) (K := K)
      hT''pos hBnn ht₀ ht₀T'' hBt₀ (JacobiSolutionOn.mono h hT''T)
      (hdducont.mono (Icc_subset_Icc_right hT''T))
      (fun s hs => hB s ⟨hs.1, lt_of_lt_of_le hs.2 hT''T⟩) hu0 hdu0
      (fun s hs => hpos s ⟨hs.1, le_trans hs.2 hT''T⟩) hK.le
      (fun s hs => hk s ⟨hs.1, lt_of_lt_of_le hs.2 hT''T⟩) hBmodel''
      (Or.inr hT''pi)
    exact hcmp t ⟨ht.1, htT''⟩
  -- Pass to the limit `t → (π/√K)⁻`.
  have hxmem : Real.pi / Real.sqrt K ∈ Icc (0 : ℝ) T := ⟨hxpos.le, hxT.le⟩
  have hcont_u : ContinuousWithinAt u (Icc 0 T) (Real.pi / Real.sqrt K) :=
    h.continuousOn_u _ hxmem
  have hcont_j : ContinuousWithinAt (jacobiSol K) (Icc 0 T) (Real.pi / Real.sqrt K) :=
    (continuous_jacobiSol K).continuousOn _ hxmem
  have hIcc_nhds : Icc (0 : ℝ) T ∈ 𝓝 (Real.pi / Real.sqrt K) :=
    Icc_mem_nhds hxpos hxT
  have htend_u : Tendsto u (𝓝[<] (Real.pi / Real.sqrt K)) (𝓝 (u (Real.pi / Real.sqrt K))) :=
    ((hcont_u.continuousAt hIcc_nhds).tendsto).mono_left inf_le_left
  have htend_j : Tendsto (jacobiSol K) (𝓝[<] (Real.pi / Real.sqrt K))
      (𝓝 (jacobiSol K (Real.pi / Real.sqrt K))) :=
    ((hcont_j.continuousAt hIcc_nhds).tendsto).mono_left inf_le_left
  have hev : ∀ᶠ t in 𝓝[<] (Real.pi / Real.sqrt K), u t ≤ jacobiSol K t := by
    filter_upwards [Ioo_mem_nhdsLT hxpos] with t ht
    exact hcompare t ht
  have hle : u (Real.pi / Real.sqrt K) ≤ jacobiSol K (Real.pi / Real.sqrt K) :=
    le_of_tendsto_of_tendsto htend_u htend_j hev
  rw [jacobiSol_of_pos hK, jacobiSolSphere_firstZero hK] at hle
  exact absurd hle (not_le.mpr (hpos _ ⟨hxpos, hxT.le⟩))

/-- **Conjugate-point witness.**  The `k = 2` model on `(0,3/2)` satisfies every hypothesis
of `conjugate_point_bound` with `K = 1` (and is positive up to `3/2 < π/√2`), giving the
consistent instance `3/2 ≤ π`. -/
theorem conjugate_point_bound_witness : (3 / 2 : ℝ) ≤ Real.pi / Real.sqrt 1 := by
  have hmain := conjugate_point_bound (T := 3 / 2) (B := 3) (t₀ := 1 / 6) (K := 1)
    (k := fun _ : ℝ => 2) (u := jacobiSol 2) (du := jacobiDeriv 2)
    (ddu := fun t => -(2 * jacobiSol 2 t))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (jacobiSol_jacobiSolutionOn 2 (3 / 2))
    (((continuous_const.mul (continuous_jacobiSol 2)).neg).continuousOn)
    (fun t ht => by
      have hb := jacobiSol_second_deriv_bound (K := 2) (T := 3 / 2) (by norm_num) t ht
      have hmax : max (1 / Real.sqrt 2) (3 / 2) = 3 / 2 := by
        rw [max_eq_right]
        rw [div_le_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2))]
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
      rw [hmax] at hb
      convert hb using 1
      ring)
    (jacobiSol_zero 2) (jacobiDeriv_zero 2)
    (fun t ht => jacobiSol_pos_of_nonneg (K := 2) (by norm_num) ht.1
      (Or.inr (by
        have hlt : Real.sqrt 2 < 2 := by
          rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 2)]
          norm_num
        calc Real.sqrt 2 * t ≤ Real.sqrt 2 * (3 / 2) :=
              mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg 2)
          _ < Real.pi := by nlinarith [hlt, Real.pi_gt_three, Real.sqrt_nonneg 2])))
    (by norm_num) (fun t ht => by norm_num) (by norm_num)
  exact hmain


end Poincare.L4.GeodesicComparison
