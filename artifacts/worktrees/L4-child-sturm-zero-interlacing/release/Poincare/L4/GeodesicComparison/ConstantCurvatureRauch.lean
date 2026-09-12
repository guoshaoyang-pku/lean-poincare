/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — sharp Rauch I comparison against the constant-curvature model `j_K`

`Poincare.L4.GeodesicComparison.RauchBridge` compares a scalar Jacobi solution `u` with
`k ≥ 0` against the *flat* model `m̄ = 1/t`.  This file upgrades the comparison model to the
D10 constant-curvature Jacobi field `jacobiSol K` for `K ≥ 0`:

* `jacobiSol_pos_of_nonneg` — general (proved): `jacobiSol K t > 0` for `t > 0`, `K ≥ 0`,
  before the first zero (`K = 0` or `√K t < π`).
* `jacobiSol_jacobiSolutionOn` — general (proved): the model data
  `(K, jacobiSol K, jacobiDeriv K, t ↦ −K·jacobiSol K t)` is a `JacobiSolutionOn` on `(0,T)`
  for every `K`, `T`.
* `jacobiSol_second_deriv_bound` — general (proved): `|j_K''(t)| ≤ K·max (1/√K) T` on
  `(0,T)` for `K ≥ 0` (the maximum of the spherical branch is `1/√K`; the flat branch has
  zero second derivative).
* `rauch_upper_of_jacobi_constCurv` — **conditional** (proved): **sharp Rauch I**: for a
  genuine scalar Jacobi solution with `k ≥ K ≥ 0` on `(0,T)` and `T` before the first zero of
  `j_K`, the logarithmic derivative satisfies
  `u' t/u t ≤ j_K'(t)/j_K(t)` on `(0,T)`.
  The proof consumes the *constructed* Euclidean normalizations of both the unknown solution
  and the model (`euclideanNormalizedOn_of_jacobi`), the constructed Riccati identities
  (`riccati_identity_of_jacobi`), and the D12 singular engine
  `riccati_le_of_singular_normalization` with `k̄ = K`.
* `rauch_constCurv_witness` — **model** (proved): the solution with `k = 2` compared against
  the model `K = 1` on `(0,1)` gives the genuinely nontrivial inequality
  `j_2'(t)/j_2(t) ≤ j_1'(t)/j_1(t)`, i.e. `√2·cot(√2 t) ≤ cot t`.

The quantitative smallness hypothesis `(K·max (1/√K) T)·t₀ ≤ 1/2` is the price of feeding
the model's normalization through `euclideanNormalizedOn_of_jacobi`; it can always be met by
choosing `t₀` small, since the engine then propagates from `t₀` to `T`.  The geometric
identification of `u` with a Jacobi field of a Riemannian manifold is not claimed.
-/
import Poincare.L4.GeodesicComparison.DownstreamComparison
import Poincare.D10.JacobiConstantCurvature.Comparison

noncomputable section

open Set Filter
open scoped Topology
open MeasureTheory

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-! ## 1. Positivity and the Jacobi-solution structure of the model -/

/-- **Positivity of the constant-curvature model.**  For `K ≥ 0` and `0 < t` before the
first zero (`K = 0`, or `√K t < π`), `jacobiSol K t > 0`. -/
theorem jacobiSol_pos_of_nonneg {K t : ℝ} (hK : 0 ≤ K) (ht : 0 < t)
    (hzero : K = 0 ∨ Real.sqrt K * t < Real.pi) : 0 < jacobiSol K t := by
  rcases eq_or_lt_of_le hK with h | h
  · rw [← h, jacobiSol_of_zero]
    exact ht
  · rcases hzero with h0 | hpi
    · exact absurd h0 (ne_of_gt h)
    · rw [jacobiSol_of_pos h]
      exact jacobiSolSphere_pos h ht hpi

/-- **The constant-curvature model is a Jacobi solution.**  For every `K` and `T`, the data
`(K, jacobiSol K, jacobiDeriv K, t ↦ −K·jacobiSol K t)` satisfies the scalar Jacobi equation
`u'' + K u = 0` with the standard regularity on `[0,T]`. -/
theorem jacobiSol_jacobiSolutionOn (K T : ℝ) :
    JacobiSolutionOn (fun _ : ℝ => K) (jacobiSol K) (jacobiDeriv K)
      (fun t => -(K * jacobiSol K t)) 0 T where
  hasDerivAt_u := by
    intro t ht
    exact hasDerivAt_jacobiSol K t
  hasDerivAt_du := by
    intro t ht
    exact hasDerivAt_jacobiDeriv K t
  eq_secondDeriv := by
    intro t ht
    ring
  continuousOn_u := (continuous_jacobiSol K).continuousOn
  continuousOn_du :=
    (continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_jacobiDeriv K t).continuousAt).continuousOn

/-! ## 2. The quantitative second-derivative bound for the model -/

/-- **Second-derivative bound for the model.**  For `K ≥ 0`, `|j_K''(t)| = K·j_K(t) ≤
K·max (1/√K) T` on `(0,T)`: the spherical branch is bounded by `1/√K`, the flat branch has
`j_0'' = 0`. -/
theorem jacobiSol_second_deriv_bound {K T : ℝ} (hK : 0 ≤ K) :
    ∀ t ∈ Ioo 0 T, |(-(K * jacobiSol K t))| ≤ K * max (1 / Real.sqrt K) T := by
  intro t ht
  rcases eq_or_lt_of_le hK with h | h
  · subst h
    simp
  · rw [jacobiSol_of_pos h]
    have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos_of_pos h
    have hsin : |Real.sin (Real.sqrt K * t)| ≤ 1 := Real.abs_sin_le_one _
    have hsqrtK : K / Real.sqrt K = Real.sqrt K := by
      rw [div_eq_iff hsqrt.ne']
      simpa [sq] using (Real.sq_sqrt h.le).symm
    have hbound : |(-(K * (Real.sin (Real.sqrt K * t) / Real.sqrt K)))| ≤ Real.sqrt K := by
      rw [abs_neg, abs_mul, abs_of_nonneg h.le, abs_div, abs_of_nonneg hsqrt.le]
      have hrewrite : K * (|Real.sin (Real.sqrt K * t)| / Real.sqrt K)
          = (K * |Real.sin (Real.sqrt K * t)|) / Real.sqrt K := by ring
      rw [hrewrite, div_le_iff₀ hsqrt]
      calc K * |Real.sin (Real.sqrt K * t)| ≤ K * 1 :=
            mul_le_mul_of_nonneg_left hsin h.le
        _ = Real.sqrt K * Real.sqrt K := by simpa [sq] using (Real.sq_sqrt h.le).symm
    change |(-(K * (Real.sin (Real.sqrt K * t) / Real.sqrt K)))| ≤
      K * max (1 / Real.sqrt K) T
    have hle_max : Real.sqrt K ≤ K * max (1 / Real.sqrt K) T := by
      have h1 : Real.sqrt K = K * (1 / Real.sqrt K) := by
        rw [mul_one_div, hsqrtK]
      calc Real.sqrt K = K * (1 / Real.sqrt K) := h1
        _ ≤ K * max (1 / Real.sqrt K) T :=
            mul_le_mul_of_nonneg_left (le_max_left (1 / Real.sqrt K) T) h.le
    linarith

/-! ## 3. Sharp Rauch I against `j_K` -/

/-- **Sharp Rauch I comparison.**  If `k ≥ K ≥ 0` on `(0,T)`, `T` is before the first zero of
`j_K` (`K = 0` or `√K T < π`), the unknown solution has the Jacobi initial data
`u 0 = 0`, `u' 0 = 1`, is positive on `(0,T]`, has `|u''| ≤ B` with `B t₀ ≤ 1/2`, and the
model normalization threshold also satisfies `(K·max (1/√K) T) t₀ ≤ 1/2`, then
`u' t/u t ≤ j_K'(t)/j_K(t)` on `(0,T)`. -/
theorem rauch_upper_of_jacobi_constCurv {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ}
    (hT : 0 < T) (hBnn : 0 ≤ B) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hBt₀ : B * t₀ ≤ 1 / 2)
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B) (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) (hK : 0 ≤ K) (hk : ∀ t ∈ Ioo 0 T, K ≤ k t)
    (hBmodel : (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2)
    (hzero : K = 0 ∨ Real.sqrt K * T < Real.pi) :
    ∀ t ∈ Ioo 0 T, du t / u t ≤ jacobiDeriv K t / jacobiSol K t := by
  have hmodel := jacobiSol_jacobiSolutionOn K T
  have hmodelpos : ∀ t ∈ Ioc 0 T, 0 < jacobiSol K t := by
    intro t ht
    refine jacobiSol_pos_of_nonneg hK ht.1 ?_
    rcases hzero with h0 | hpi
    · exact Or.inl h0
    · exact Or.inr (lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg K)) hpi)
  have hmodelbound := jacobiSol_second_deriv_bound (K := K) (T := T) hK
  have hBmodelnn : 0 ≤ K * max (1 / Real.sqrt K) T := by
    refine mul_nonneg hK (le_trans ?_ (le_max_left _ _))
    exact div_nonneg zero_le_one (Real.sqrt_nonneg K)
  have hmodelcont : ContinuousOn (fun t => -(K * jacobiSol K t)) (Icc 0 T) :=
    ((continuous_const.mul (continuous_jacobiSol K)).neg).continuousOn
  have hid := riccati_identity_of_jacobi h hpos
  have hidmodel := riccati_identity_of_jacobi hmodel hmodelpos
  have hnorm := euclideanNormalizedOn_of_jacobi h hdducont hBnn hB hu0 hdu0 ht₀ ht₀T hBt₀
  have hnormbar := euclideanNormalizedOn_of_jacobi (k := fun _ : ℝ => K)
    (u := jacobiSol K) (du := jacobiDeriv K) (ddu := fun t => -(K * jacobiSol K t))
    hmodel hmodelcont hBmodelnn hmodelbound (jacobiSol_zero K) (jacobiDeriv_zero K)
    ht₀ ht₀T hBmodel
  have hBmodelC : 0 ≤ 4 * (K * max (1 / Real.sqrt K) T) := by positivity
  have hnorm' : EuclideanNormalizedOn (fun t => du t / u t) 1
      (max (4 * B) (4 * (K * max (1 / Real.sqrt K) T))) t₀ :=
    fun t ht => le_trans (hnorm ht) (le_max_left _ _)
  have hnormbar' : EuclideanNormalizedOn (fun t => jacobiDeriv K t / jacobiSol K t) 1
      (max (4 * B) (4 * (K * max (1 / Real.sqrt K) T))) t₀ :=
    fun t ht => le_trans (hnormbar ht) (le_max_right _ _)
  have hmain := riccati_le_of_singular_normalization (d := 1) (T := T)
    (C := max (4 * B) (4 * (K * max (1 / Real.sqrt K) T)))
    (t₀ := t₀) (k := k) (kbar := fun _ : ℝ => K) (m := fun t => du t / u t)
    (dm := fun t => (ddu t * u t - du t ^ 2) / u t ^ 2)
    (mbar := fun t => jacobiDeriv K t / jacobiSol K t)
    (dmbar := fun t => ((-(K * jacobiSol K t)) * jacobiSol K t - jacobiDeriv K t ^ 2) /
      jacobiSol K t ^ 2)
    (by norm_num) hT (by positivity) ht₀ ht₀T
    (fun t ht => le_of_eq (hid.2 t ht))
    (fun t ht => hidmodel.2 t ht)
    (fun t ht => hk t ht)
    (fun t ht => hid.1 t ht)
    (fun t ht => hidmodel.1 t ht)
    (logDeriv_continuousOn h hpos) (logDeriv_continuousOn hmodel hmodelpos) hnorm' hnormbar'
  intro t ht
  exact hmain ht

/-! ## 4. Non-vacuity: `k = 2` against the model `K = 1` -/

/-- **Sharp Rauch witness.**  The Jacobi solution with `k = 2` compared against the model
`K = 1` on `(0,1)` satisfies every hypothesis of `rauch_upper_of_jacobi_constCurv`, and the
conclusion `j_2'(t)/j_2(t) ≤ j_1'(t)/j_1(t)` (equivalently `√2·cot(√2 t) ≤ cot t`) is
genuinely nontrivial. -/
theorem rauch_constCurv_witness :
    ∀ t ∈ Ioo (0 : ℝ) 1,
      jacobiDeriv 2 t / jacobiSol 2 t ≤ jacobiDeriv 1 t / jacobiSol 1 t := by
  have hmain := rauch_upper_of_jacobi_constCurv (T := 1) (B := 2) (t₀ := 1 / 4) (K := 1)
    (k := fun _ : ℝ => 2) (u := jacobiSol 2) (du := jacobiDeriv 2)
    (ddu := fun t => -(2 * jacobiSol 2 t))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (jacobiSol_jacobiSolutionOn 2 1)
    (((continuous_const.mul (continuous_jacobiSol 2)).neg).continuousOn)
    (fun t ht => by
      have hb := jacobiSol_second_deriv_bound (K := 2) (T := 1) (by norm_num) t ht
      have hmax : max (1 / Real.sqrt 2) 1 = 1 := by
        rw [max_eq_right]
        rw [div_le_one (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2))]
        exact Real.one_le_sqrt.mpr (by norm_num)
      rw [hmax, mul_one] at hb
      exact hb)
    (jacobiSol_zero 2) (jacobiDeriv_zero 2)
    (fun t ht => jacobiSol_pos_of_nonneg (K := 2) (by norm_num) ht.1
      (Or.inr (by
        have h2 : Real.sqrt 2 < Real.pi := by
          have hlt : Real.sqrt 2 < 2 := by
            rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 2)]
            norm_num
          linarith [Real.pi_gt_three]
        calc Real.sqrt 2 * t ≤ Real.sqrt 2 * 1 :=
              mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg 2)
          _ = Real.sqrt 2 := mul_one _
          _ < Real.pi := h2)))
    (by norm_num) (fun t ht => by norm_num)
    (by norm_num)
    (Or.inr (by
      rw [Real.sqrt_one, one_mul]
      linarith [Real.pi_gt_three]))
  intro t ht
  exact hmain t ht

/-! ## 5. Integrated form: the Jacobi solution is dominated by `j_K` -/

/-- **Integrated Rauch comparison.**  Under the hypotheses of
`rauch_upper_of_jacobi_constCurv`, the Jacobi solution is dominated by the
constant-curvature model: `u t ≤ j_K t` on `(0,T)`.

Proof: the log-derivative comparison makes the ratio `u/j_K` antitone on `(0,T]`
(D12 `areaRatio_antitone_of_logDeriv_le`); the linear bounds `|u s − s| ≤ B s²` and
`|j_K s − s| ≤ B_model s²` give `u s/s → 1` and `j_K s/s → 1` as `s → 0⁺`; passing to the
limit in `u t/j_K t ≤ u s/j_K s` yields `u t/j_K t ≤ 1`. -/
theorem jacobi_le_constCurvModel {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ}
    (hT : 0 < T) (hBnn : 0 ≤ B) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hBt₀ : B * t₀ ≤ 1 / 2)
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B) (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) (hK : 0 ≤ K) (hk : ∀ t ∈ Ioo 0 T, K ≤ k t)
    (hBmodel : (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2)
    (hzero : K = 0 ∨ Real.sqrt K * T < Real.pi) :
    ∀ t ∈ Ioo 0 T, u t ≤ jacobiSol K t := by
  have hmodel := jacobiSol_jacobiSolutionOn K T
  have hmodelpos : ∀ t ∈ Ioc 0 T, 0 < jacobiSol K t := by
    intro t ht
    refine jacobiSol_pos_of_nonneg hK ht.1 ?_
    rcases hzero with h0 | hpi
    · exact Or.inl h0
    · exact Or.inr (lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg K)) hpi)
  have hmodelbound := jacobiSol_second_deriv_bound (K := K) (T := T) hK
  have hBmodelnn : 0 ≤ K * max (1 / Real.sqrt K) T := by
    refine mul_nonneg hK (le_trans ?_ (le_max_left _ _))
    exact div_nonneg zero_le_one (Real.sqrt_nonneg K)
  have hmodelcont : ContinuousOn (fun t => -(K * jacobiSol K t)) (Icc 0 T) :=
    ((continuous_const.mul (continuous_jacobiSol K)).neg).continuousOn
  have hmle := rauch_upper_of_jacobi_constCurv hT hBnn ht₀ ht₀T hBt₀ h hdducont hB hu0
    hdu0 hpos hK hk hBmodel hzero
  have hanti := areaRatio_antitone_of_logDeriv_le (T := T) (A := u) (dA := du)
    (Abar := jacobiSol K) (dAbar := jacobiDeriv K)
    (m := fun t => du t / u t) (mbar := fun t => jacobiDeriv K t / jacobiSol K t) hT
    (fun t ht => h.hasDerivAt_u ht) (fun t ht => hmodel.hasDerivAt_u ht)
    h.continuousOn_u hmodel.continuousOn_u hpos hmodelpos
    (fun t ht => rfl) (fun t ht => rfl) hmle
  -- Limits at `0⁺`.
  have hulim : Tendsto (fun s => u s / s) (𝓝[>] 0) (𝓝 1) := by
    have hdiff : Tendsto (fun s => (u s - s) / s) (𝓝[>] 0) (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (g := fun s => B * s)
        (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
      · filter_upwards [Ioo_mem_nhdsGT hT] with s hs
        have hs2 : |u s - s| ≤ B * s ^ 2 :=
          (jacobi_linear_bounds h hdducont hBnn hB hu0 hdu0).2 s hs
        simp only [norm_div, Real.norm_eq_abs, abs_of_pos hs.1]
        rw [div_le_iff₀ hs.1]
        calc |u s - s| ≤ B * s ^ 2 := hs2
          _ = (B * s) * s := by ring
      · simpa using tendsto_const_nhds.mul
          (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id :
            Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0))
    have h1 : Tendsto (fun s => 1 + (u s - s) / s) (𝓝[>] 0) (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hdiff
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := ne_of_gt hs
    field_simp [hs0]
    ring
  have hjlim : Tendsto (fun s => jacobiSol K s / s) (𝓝[>] 0) (𝓝 1) := by
    have hdiff : Tendsto (fun s => (jacobiSol K s - s) / s) (𝓝[>] 0) (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (g := fun s => (K * max (1 / Real.sqrt K) T) * s)
        (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
      · filter_upwards [Ioo_mem_nhdsGT hT] with s hs
        have hs2 : |jacobiSol K s - s| ≤ (K * max (1 / Real.sqrt K) T) * s ^ 2 :=
          (jacobi_linear_bounds hmodel hmodelcont hBmodelnn hmodelbound
            (jacobiSol_zero K) (jacobiDeriv_zero K)).2 s hs
        simp only [norm_div, Real.norm_eq_abs, abs_of_pos hs.1]
        rw [div_le_iff₀ hs.1]
        calc |jacobiSol K s - s| ≤ (K * max (1 / Real.sqrt K) T) * s ^ 2 := hs2
          _ = ((K * max (1 / Real.sqrt K) T) * s) * s := by ring
      · simpa using tendsto_const_nhds.mul
          (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id :
            Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0))
    have h1 : Tendsto (fun s => 1 + (jacobiSol K s - s) / s) (𝓝[>] 0) (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hdiff
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := ne_of_gt hs
    field_simp [hs0]
    ring
  have hratio : Tendsto (fun s => u s / jacobiSol K s) (𝓝[>] 0) (𝓝 1) := by
    have h := hulim.div hjlim (by norm_num : (1 : ℝ) ≠ 0)
    rw [div_one] at h
    refine h.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hT] with s hs
    have hjs : jacobiSol K s ≠ 0 := ne_of_gt (hmodelpos s ⟨hs.1, hs.2.le⟩)
    have hs0 : s ≠ 0 := ne_of_gt hs.1
    simp only [Pi.div_apply]
    field_simp [hs0, hjs]
  intro t ht
  have htIoc : t ∈ Ioc 0 T := ⟨ht.1, ht.2.le⟩
  have hev : ∀ᶠ s in 𝓝[>] 0, u t / jacobiSol K t ≤ u s / jacobiSol K s := by
    filter_upwards [Ioo_mem_nhdsGT ht.1] with s hs
    have hsIoc : s ∈ Ioc 0 T := ⟨hs.1, le_of_lt (lt_trans hs.2 ht.2)⟩
    exact hanti hsIoc htIoc hs.2.le
  have hlim_le := le_of_tendsto_of_tendsto tendsto_const_nhds hratio hev
  rwa [div_le_one (hmodelpos t htIoc)] at hlim_le

/-- **Integrated-comparison witness.**  The `k = 2` model is dominated by the `K = 1` model on
`(0,1)`: `j_2 t ≤ j_1 t`, i.e. `sin(√2 t)/√2 ≤ sin t`.  This instantiates
`jacobi_le_constCurvModel` with the same data as `rauch_constCurv_witness` and is a strict
inequality on `(0,1)`. -/
theorem jacobiSolTwo_le_model_witness :
    ∀ t ∈ Ioo (0 : ℝ) 1, jacobiSol 2 t ≤ jacobiSol 1 t := by
  have hmain := jacobi_le_constCurvModel (T := 1) (B := 2) (t₀ := 1 / 4) (K := 1)
    (k := fun _ : ℝ => 2) (u := jacobiSol 2) (du := jacobiDeriv 2)
    (ddu := fun t => -(2 * jacobiSol 2 t))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (jacobiSol_jacobiSolutionOn 2 1)
    (((continuous_const.mul (continuous_jacobiSol 2)).neg).continuousOn)
    (fun t ht => by
      have hb := jacobiSol_second_deriv_bound (K := 2) (T := 1) (by norm_num) t ht
      have hmax : max (1 / Real.sqrt 2) 1 = 1 := by
        rw [max_eq_right]
        rw [div_le_one (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2))]
        exact Real.one_le_sqrt.mpr (by norm_num)
      rw [hmax, mul_one] at hb
      exact hb)
    (jacobiSol_zero 2) (jacobiDeriv_zero 2)
    (fun t ht => jacobiSol_pos_of_nonneg (K := 2) (by norm_num) ht.1
      (Or.inr (by
        have h2 : Real.sqrt 2 < Real.pi := by
          have hlt : Real.sqrt 2 < 2 := by
            rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 2)]
            norm_num
          linarith [Real.pi_gt_three]
        calc Real.sqrt 2 * t ≤ Real.sqrt 2 * 1 :=
              mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg 2)
          _ = Real.sqrt 2 := mul_one _
          _ < Real.pi := h2)))
    (by norm_num) (fun t ht => by norm_num)
    (by norm_num)
    (Or.inr (by
      rw [Real.sqrt_one, one_mul]
      linarith [Real.pi_gt_three]))
  intro t ht
  exact hmain t ht


end Poincare.L4.GeodesicComparison
