/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — the conjugate-point bound at the endpoint `π/√K`

`ConstantCurvatureRauch.lean` proves the integrated sharp Rauch I comparison `u ≤ j_K` on
an interval `(0,T)` *before* the first zero of the constant-curvature model, i.e. under the
hypothesis `K = 0 ∨ √K·T < π`.  This file removes that hypothesis from the conclusion for
positive curvature: for `k ≥ K > 0` on `(0,T)` and a positive Jacobi solution `u` with the
standard initial data `u 0 = 0`, `u' 0 = 1`, one has `T ≤ π/√K`.  No positive solution can
reach the first conjugate point of the comparison curvature.

Contents (all kernel-checked; semantic class marked per declaration):

* `JacobiSolutionOn.mono` — general (proved): restriction of a Jacobi solution to a smaller
  interval.
* `conjugate_point_bound` — **conditional** (proved): the endpoint bound `T ≤ π/√K` under the
  analytic normalization hypotheses of `rauch_upper_of_jacobi_constCurv`, with the *model
  zero hypothesis* `K = 0 ∨ √K·T < π` removed and `K > 0` assumed instead.
* `conjugate_point_bound_strict` — **conditional** (proved): the strict strengthening
  `T < π/√K`; equality is impossible for a strictly positive solution on `(0,T]`.
* `conjugate_point_bound_witness_k2_K1` — **model** (proved): the explicit non-vacuous
  instance `k = 2`, `K = 1`, `T = 2`, discharging every hypothesis, yielding
  `2 ≤ π/√1 = π`.
* `conjugate_point_bound_witness_k2_K2` — **model** (proved): the sharpened instance
  `k = 2`, `K = 2`, `T = 2`, yielding `2 ≤ π/√2`, a strictly stronger bound.
* `pi_div_sqrt_two_lt_pi` — general (proved): `π/√2 < π`, so the `K = 2` bound is strictly
  sharper than the `K = 1` bound on the same `k = 2` solution.
* `jacobiSol_pos_iff` — **sharpness** (proved): for every `K > 0` the constant-curvature
  model `jacobiSol K` is positive on `(0,T]` **iff** `T < π/√K`.  Hence the bound `π/√K`
  is attained and cannot be improved, and the positivity hypothesis cannot be weakened to
  allow `T = π/√K`.
* `jacobiSol_two_pos_iff` — the `K = 2` specialization: the `k = 2` model is positive on
  `(0,T]` iff `T < π/√2`.
* `jacobiSol_two_firstZero`, `jacobiSol_two_not_pos_at_firstZero` — the explicit zero
  `jacobiSol 2 (π/√2) = 0` and the non-positivity at the endpoint, witnessing attainment of
  the sharp threshold.

## Route (endpoint limit)

For `t < π/√K` restrict the solution to an interval `(0,T'')` with
`t < T'' < min T (π/√K)`; the model-positivity hypothesis `√K·T'' < π` of
`jacobi_le_constCurvModel` holds by construction, so `u t ≤ j_K t`.  Since
`j_K (π/√K) = 0` (D10 `jacobiSolSphere_firstZero`) while `u > 0` on `(0,T]`, the assumption
`π/√K ≤ T` is contradictory: pass to the limit `t → (π/√K)⁻` using continuity of `u` on
`[0,T]` (one-sided continuity at the endpoint is obtained from `ContinuousOn` by
`ContinuousWithinAt.mono_of_mem_nhdsWithin`) and of `jacobiSol K` everywhere.  No endpoint
value of `u` is assumed; the conclusion is derived, not postulated.

## Semantic class and honest scope

This is a **conditional analytic** scalar ODE comparison statement.  It is *not* the
manifold-level conjugate-point theorem: the identification of `u` with a Jacobi field along
a geodesic, and of `T` with the distance to the first conjugate point, is not formalized
here.  The hypotheses are exactly the analytic normalization hypotheses of
`rauch_upper_of_jacobi_constCurv`; the `hzero` hypothesis is what is removed.
-/
import Poincare.L4.GeodesicComparison.ConstantCurvatureRauch

noncomputable section

open Set Filter
open scoped Topology
open MeasureTheory

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-! ## 1. Restricting a Jacobi solution to a smaller interval -/

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

/-! ## 2. The normalization base point lies before the first zero -/

/-- **The normalization base point is before the first zero.**  From the model
normalization threshold `(K·max (1/√K) T)·t₀ ≤ 1/2` and `K > 0` one gets
`t₀ < π/√K`: indeed `√K·t₀ ≤ (K·max (1/√K) T)·t₀ ≤ 1/2 < π`. -/
theorem basePoint_lt_firstZero {T t₀ K : ℝ} (hK : 0 < K) (ht₀ : 0 < t₀)
    (hBmodel : (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2) :
    t₀ < Real.pi / Real.sqrt K := by
  have hsqrtK : 0 < Real.sqrt K := Real.sqrt_pos_of_pos hK
  have hKnn : 0 ≤ K := le_of_lt hK
  have hsq : Real.sqrt K * Real.sqrt K = K := by
    simpa [sq] using Real.sq_sqrt hKnn
  have hle : Real.sqrt K ≤ K * max (1 / Real.sqrt K) T := by
    have h1 : Real.sqrt K = K * (1 / Real.sqrt K) := by
      rw [mul_one_div, eq_div_iff hsqrtK.ne']
      exact hsq
    calc Real.sqrt K = K * (1 / Real.sqrt K) := h1
      _ ≤ K * max (1 / Real.sqrt K) T :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hKnn
  have h2 : Real.sqrt K * t₀ ≤ 1 / 2 :=
    le_trans (mul_le_mul_of_nonneg_right hle ht₀.le) hBmodel
  have h3 : t₀ ≤ 1 / (2 * Real.sqrt K) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt K)]
    nlinarith [h2]
  have h4 : 1 / (2 * Real.sqrt K) < Real.pi / Real.sqrt K := by
    have heq : 1 / (2 * Real.sqrt K) = (1 / 2) / Real.sqrt K := by ring
    rw [heq, div_lt_div_iff_of_pos_right hsqrtK]
    linarith [Real.pi_gt_three]
  linarith

/-! ## 3. The endpoint bound -/

/-- **Strict conjugate-point bound.**  If `k ≥ K > 0` on `(0,T)`, the Jacobi solution has
the standard initial data `u 0 = 0`, `u' 0 = 1`, is positive on `(0,T]`, has `|u''| ≤ B`
with `B t₀ ≤ 1/2`, and the model normalization threshold satisfies
`(K·max (1/√K) T)·t₀ ≤ 1/2`, then `T < π/√K`.

Proof: assume `π/√K ≤ T` and let `x = π/√K ∈ (0,T]`.  For `t < x` restrict to `(0,T'')`
with `t < T'' < min T x`; `jacobi_le_constCurvModel` gives `u t ≤ j_K t`.  Passing to the
limit `t → x⁻` (continuity of `u` on `[0,T]` and of `j_K` everywhere) gives
`u x ≤ j_K x = 0`, contradicting `u x > 0`. -/
theorem conjugate_point_bound_strict {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ}
    (_hT : 0 < T) (hBnn : 0 ≤ B) (ht₀ : 0 < t₀) (_ht₀T : t₀ ≤ T) (hBt₀ : B * t₀ ≤ 1 / 2)
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B) (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) (hK : 0 < K) (hk : ∀ t ∈ Ioo 0 T, K ≤ k t)
    (hBmodel : (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2) :
    T < Real.pi / Real.sqrt K := by
  by_contra hcon
  have hxT : Real.pi / Real.sqrt K ≤ T := le_of_not_gt hcon
  have hsqrtK : 0 < Real.sqrt K := Real.sqrt_pos_of_pos hK
  have hxpos : 0 < Real.pi / Real.sqrt K := div_pos Real.pi_pos hsqrtK
  have ht₀x : t₀ < Real.pi / Real.sqrt K := basePoint_lt_firstZero hK ht₀ hBmodel
  -- Comparison `u t ≤ j_K t` for every `t` below the conjugate point.
  have hcompare : ∀ t ∈ Ioo 0 (Real.pi / Real.sqrt K), u t ≤ jacobiSol K t := by
    intro t ht
    have htT : t < T := lt_of_lt_of_le ht.2 hxT
    have htpi : Real.sqrt K * t < Real.pi := by
      have h1 := mul_lt_mul_of_pos_left ht.2 hsqrtK
      rwa [mul_div_cancel₀ Real.pi hsqrtK.ne'] at h1
    have ht₀T : t₀ < T := lt_of_lt_of_le ht₀x hxT
    -- Pick `T''` with `max t t₀ < T'' < min T (π/√K)`.
    set m : ℝ := min T (Real.pi / Real.sqrt K) with hmdef
    have htm : max t t₀ < m := max_lt (lt_min htT ht.2) (lt_min ht₀T ht₀x)
    set T'' : ℝ := (max t t₀ + m) / 2 with hT''def
    have htT'' : t < T'' := by rw [hT''def]; linarith [le_max_left t t₀]
    have ht₀T'' : t₀ ≤ T'' := by rw [hT''def]; linarith [le_max_right t t₀]
    have hT''m : T'' < m := by rw [hT''def]; linarith
    have hT''T : T'' ≤ T := le_of_lt (lt_of_lt_of_le hT''m (min_le_left _ _))
    have hT''pi : Real.sqrt K * T'' < Real.pi := by
      have h1 : T'' < Real.pi / Real.sqrt K := lt_of_lt_of_le hT''m (min_le_right _ _)
      have h2 := mul_lt_mul_of_pos_left h1 hsqrtK
      rwa [mul_div_cancel₀ Real.pi hsqrtK.ne'] at h2
    have hT''pos : 0 < T'' := lt_trans ht.1 htT''
    have hBmodel'' : (K * max (1 / Real.sqrt K) T'') * t₀ ≤ 1 / 2 := by
      have hmax : max (1 / Real.sqrt K) T'' ≤ max (1 / Real.sqrt K) T :=
        max_le_max le_rfl hT''T
      have hKnn : 0 ≤ K := le_of_lt hK
      have h1 : K * max (1 / Real.sqrt K) T'' ≤ K * max (1 / Real.sqrt K) T :=
        mul_le_mul_of_nonneg_left hmax hKnn
      exact le_trans (mul_le_mul_of_nonneg_right h1 ht₀.le) hBmodel
    exact (jacobi_le_constCurvModel (T := T'') (B := B) (t₀ := t₀) (K := K)
      hT''pos hBnn ht₀ ht₀T'' hBt₀ (JacobiSolutionOn.mono h hT''T)
      (hdducont.mono (Icc_subset_Icc_right hT''T))
      (fun s hs => hB s ⟨hs.1, lt_of_lt_of_le hs.2 hT''T⟩) hu0 hdu0
      (fun s hs => hpos s ⟨hs.1, le_trans hs.2 hT''T⟩) hK.le
      (fun s hs => hk s ⟨hs.1, lt_of_lt_of_le hs.2 hT''T⟩) hBmodel''
      (Or.inr hT''pi)) t ⟨ht.1, htT''⟩
  -- One-sided continuity of `u` at `x = π/√K` from `ContinuousOn u (Icc 0 T)`.
  have hxmem : Real.pi / Real.sqrt K ∈ Icc (0 : ℝ) T := ⟨hxpos.le, hxT⟩
  have hmem : Icc (0 : ℝ) T ∈ 𝓝[Iio (Real.pi / Real.sqrt K)] (Real.pi / Real.sqrt K) := by
    rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [isOpen_Ioi.mem_nhds hxpos] with t ht htx
    exact ⟨le_of_lt ht, le_trans htx.le hxT⟩
  have htend_u : Tendsto u (𝓝[<] (Real.pi / Real.sqrt K))
      (𝓝 (u (Real.pi / Real.sqrt K))) :=
    ((h.continuousOn_u _ hxmem).mono_of_mem_nhdsWithin hmem).tendsto
  have htend_j : Tendsto (jacobiSol K) (𝓝[<] (Real.pi / Real.sqrt K))
      (𝓝 (jacobiSol K (Real.pi / Real.sqrt K))) :=
    ((continuous_jacobiSol K).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[<] (Real.pi / Real.sqrt K), u t ≤ jacobiSol K t := by
    filter_upwards [Ioo_mem_nhdsLT hxpos] with t ht
    exact hcompare t ht
  have hfin : u (Real.pi / Real.sqrt K) ≤ jacobiSol K (Real.pi / Real.sqrt K) :=
    le_of_tendsto_of_tendsto htend_u htend_j hev
  rw [jacobiSol_of_pos hK, jacobiSolSphere_firstZero hK] at hfin
  exact absurd hfin (not_le.mpr (hpos _ ⟨hxpos, hxT⟩))

/-- **Conjugate-point bound (endpoint form).**  If `k ≥ K > 0` on `(0,T)`, the Jacobi
solution has the standard initial data `u 0 = 0`, `u' 0 = 1`, is positive on `(0,T]`, has
`|u''| ≤ B` with `B t₀ ≤ 1/2`, and the model normalization threshold satisfies
`(K·max (1/√K) T)·t₀ ≤ 1/2`, then `T ≤ π/√K`: no positive solution can pass the first
conjugate point of the comparison curvature. -/
theorem conjugate_point_bound {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ}
    (hT : 0 < T) (hBnn : 0 ≤ B) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hBt₀ : B * t₀ ≤ 1 / 2)
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B) (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) (hK : 0 < K) (hk : ∀ t ∈ Ioo 0 T, K ≤ k t)
    (hBmodel : (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2) :
    T ≤ Real.pi / Real.sqrt K :=
  le_of_lt (conjugate_point_bound_strict hT hBnn ht₀ ht₀T hBt₀ h hdducont hB hu0 hdu0 hpos
    hK hk hBmodel)

/-! ## 4. Non-vacuous witnesses -/

/-- Second-derivative bound for the `k = 2` model on `(0,2)`, with the explicit constant
`B = 4 = 2·max (1/√2) 2`. -/
theorem jacobiSolTwo_second_deriv_bound_four :
    ∀ t ∈ Ioo (0 : ℝ) 2, |(-(2 * jacobiSol 2 t))| ≤ 4 := by
  intro t ht
  have hb := jacobiSol_second_deriv_bound (K := 2) (T := 2) (by norm_num) t ht
  have hmax : max (1 / Real.sqrt 2) (2 : ℝ) = 2 := by
    rw [max_eq_right]
    rw [div_le_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2))]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  rw [hmax] at hb
  linarith

/-- Positivity of the `k = 2` model on `(0,2]`: `2√2 < 3 < π`. -/
theorem jacobiSolTwo_pos_Ioc_two : ∀ t ∈ Ioc (0 : ℝ) 2, 0 < jacobiSol 2 t := by
  intro t ht
  have h2 : Real.sqrt 2 * t < Real.pi := by
    have hle : Real.sqrt 2 * t ≤ Real.sqrt 2 * 2 :=
      mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg 2)
    have hlt : Real.sqrt 2 * 2 < Real.pi := by
      have h3 : Real.sqrt 2 < 3 / 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      nlinarith [Real.pi_gt_three]
    linarith
  exact jacobiSol_pos_of_nonneg (K := 2) (by norm_num) ht.1 (Or.inr h2)

/-- **Non-vacuous witness, `k = 2` against `K = 1`.**  The explicit Jacobi solution
`sin(√2 t)/√2` on `(0,2)` satisfies every hypothesis of `conjugate_point_bound` with
`B = 4`, `t₀ = 1/8`, `K = 1`, so the endpoint bound gives `2 ≤ π/√1 = π`. -/
theorem conjugate_point_bound_witness_k2_K1 : (2 : ℝ) ≤ Real.pi / Real.sqrt 1 := by
  have hmain := conjugate_point_bound (T := 2) (B := 4) (t₀ := 1 / 8) (K := 1)
    (k := fun _ : ℝ => 2) (u := jacobiSol 2) (du := jacobiDeriv 2)
    (ddu := fun t => -(2 * jacobiSol 2 t))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (jacobiSol_jacobiSolutionOn 2 2)
    (((continuous_const.mul (continuous_jacobiSol 2)).neg).continuousOn)
    jacobiSolTwo_second_deriv_bound_four
    (jacobiSol_zero 2) (jacobiDeriv_zero 2)
    jacobiSolTwo_pos_Ioc_two
    (by norm_num) (fun _ _ => by norm_num) (by norm_num [Real.sqrt_one])
  simpa [Real.sqrt_one] using hmain

/-- **Non-vacuous witness, `k = 2` against `K = 2` (sharpened).**  The same explicit
solution satisfies every hypothesis with `K = 2` and the endpoint bound gives
`2 ≤ π/√2`, i.e. `2√2 ≤ π` — strictly stronger than the `K = 1` instance. -/
theorem conjugate_point_bound_witness_k2_K2 : (2 : ℝ) ≤ Real.pi / Real.sqrt 2 := by
  have hmain := conjugate_point_bound (T := 2) (B := 4) (t₀ := 1 / 8) (K := 2)
    (k := fun _ : ℝ => 2) (u := jacobiSol 2) (du := jacobiDeriv 2)
    (ddu := fun t => -(2 * jacobiSol 2 t))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (jacobiSol_jacobiSolutionOn 2 2)
    (((continuous_const.mul (continuous_jacobiSol 2)).neg).continuousOn)
    jacobiSolTwo_second_deriv_bound_four
    (jacobiSol_zero 2) (jacobiDeriv_zero 2)
    jacobiSolTwo_pos_Ioc_two
    (by norm_num) (fun _ _ => by norm_num)
    (by
      have hmax : max (1 / Real.sqrt 2) (2 : ℝ) = 2 := by
        rw [max_eq_right]
        rw [div_le_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2))]
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      rw [hmax]
      norm_num)
  exact hmain

/-- **The `K = 2` bound is strictly sharper.**  `π/√2 < π`, so the sharpened instance
`2 ≤ π/√2` is a strictly stronger statement than the `K = 1` instance `2 ≤ π`. -/
theorem pi_div_sqrt_two_lt_pi : Real.pi / Real.sqrt 2 < Real.pi := by
  rw [div_lt_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2))]
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    simpa [Real.sqrt_one] using
      Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 2)
  nlinarith [Real.pi_pos]

/-! ## 5. Sharpness: the first zero of the model is exactly `π/√K` -/

/-- **Sharpness of the endpoint bound.**  For every `K > 0`, the constant-curvature model
`jacobiSol K` is positive on `(0,T]` **iff** `T < π/√K`.  The forward direction is
`conjugate_point_bound` applied to the model itself (with `k = K`); the reverse direction
is the explicit spherical formula.  In particular the bound `π/√K` is attained: the
hypothesis `u > 0` on `(0,T]` cannot hold at `T = π/√K`. -/
theorem jacobiSol_pos_iff {K T : ℝ} (hK : 0 < K) :
    (∀ t ∈ Ioc 0 T, 0 < jacobiSol K t) ↔ T < Real.pi / Real.sqrt K := by
  have hsqrtK : 0 < Real.sqrt K := Real.sqrt_pos_of_pos hK
  constructor
  · intro hpos
    by_cases hT : T ≤ 0
    · have hxpos : 0 < Real.pi / Real.sqrt K := div_pos Real.pi_pos hsqrtK
      linarith
    · have hT : 0 < T := not_le.mp hT
      set B : ℝ := K * max (1 / Real.sqrt K) T with hBdef
      have hBpos : 0 < B := by
        rw [hBdef]
        exact mul_pos hK (lt_of_lt_of_le (one_div_pos.mpr hsqrtK) (le_max_left _ _))
      set t₀ : ℝ := min T (1 / (2 * B)) with ht₀def
      have ht₀pos : 0 < t₀ := by
        rw [ht₀def]
        exact lt_min hT (by positivity)
      have ht₀T : t₀ ≤ T := by rw [ht₀def]; exact min_le_left _ _
      have hBt₀ : B * t₀ ≤ 1 / 2 := by
        have h1 : B * t₀ ≤ B * (1 / (2 * B)) := by
          rw [ht₀def]
          exact mul_le_mul_of_nonneg_left (min_le_right _ _) hBpos.le
        have h2 : B * (1 / (2 * B)) = 1 / 2 := by field_simp
        linarith
      have hle := conjugate_point_bound (T := T) (B := B) (t₀ := t₀) (K := K)
        hT (le_of_lt hBpos) ht₀pos ht₀T hBt₀
        (jacobiSol_jacobiSolutionOn K T)
        (((continuous_const.mul (continuous_jacobiSol K)).neg).continuousOn)
        (by rw [hBdef]; exact jacobiSol_second_deriv_bound (K := K) (T := T) hK.le)
        (jacobiSol_zero K) (jacobiDeriv_zero K) hpos hK
        (fun _ _ => le_rfl)
        (by simpa only [← hBdef] using hBt₀)
      have hne : T ≠ Real.pi / Real.sqrt K := by
        intro heq
        have hxpos : 0 < Real.pi / Real.sqrt K := div_pos Real.pi_pos hsqrtK
        have hlt := hpos _ ⟨hxpos, le_of_eq heq.symm⟩
        rw [jacobiSol_of_pos hK, jacobiSolSphere_firstZero hK] at hlt
        exact lt_irrefl 0 hlt
      exact lt_of_le_of_ne hle hne
  · intro hT t ht
    refine jacobiSol_pos_of_nonneg hK.le ht.1 (Or.inr ?_)
    have h1 := mul_lt_mul_of_pos_left hT hsqrtK
    rw [mul_div_cancel₀ Real.pi hsqrtK.ne'] at h1
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht.2 hsqrtK.le) h1

/-- **The exact conjugate point of the `k = 2` solution.**  The `k = 2` model
`sin(√2 t)/√2` is positive on `(0,T]` iff `T < π/√2`.  So for the `k = 2` model the bound
`π/√K` with `K = 2` is exactly `π/√2` and cannot be improved. -/
theorem jacobiSol_two_pos_iff (T : ℝ) :
    (∀ t ∈ Ioc 0 T, 0 < jacobiSol 2 t) ↔ T < Real.pi / Real.sqrt 2 :=
  jacobiSol_pos_iff (K := 2) (T := T) (by norm_num)

/-- The `k = 2` model vanishes at its first conjugate point `π/√2`. -/
theorem jacobiSol_two_firstZero : jacobiSol 2 (Real.pi / Real.sqrt 2) = 0 := by
  rw [jacobiSol_of_pos (by norm_num : (0 : ℝ) < 2),
    jacobiSolSphere_firstZero (by norm_num : (0 : ℝ) < 2)]

/-- The `k = 2` model is not positive at `π/√2`: the endpoint `T = π/√2` is inadmissible,
so the sharp threshold `T < π/√2` of `jacobiSol_two_pos_iff` is attained and the positivity
hypothesis cannot be relaxed to the closed endpoint. -/
theorem jacobiSol_two_not_pos_at_firstZero :
    ¬ (0 < jacobiSol 2 (Real.pi / Real.sqrt 2)) := by
  rw [jacobiSol_two_firstZero]
  exact lt_irrefl 0

end Poincare.L4.GeodesicComparison
