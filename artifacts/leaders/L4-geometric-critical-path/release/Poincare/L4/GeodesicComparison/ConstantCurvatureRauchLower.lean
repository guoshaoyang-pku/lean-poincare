/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — sharp Rauch II comparison against the constant-curvature model for `K ≤ 0`

`ConstantCurvatureRauch.lean` proves the sharp upper comparison `u'/u ≤ j_K'/j_K` for
`k ≥ K ≥ 0`.  This file proves the mirrored **lower** comparison for nonpositive comparison
curvature:

* `jacobiSol_pos_of_nonpos` — general (proved): `j_K t > 0` for `t > 0`, `K ≤ 0` (the
  hyperbolic model has no zeros).
* `jacobiSol_monotoneOn_of_nonpos` — general (proved): `j_K` is monotone on `[0,T]` for
  `K ≤ 0`, since `j_K' = cosh(√(−K)·) ≥ 0` (and `j_0' = 1`).
* `jacobiSol_second_deriv_bound_nonpos` — general (proved):
  `|j_K''(t)| ≤ |K|·j_K(T)` on `(0,T)` for `K ≤ 0`, by monotonicity and positivity.
* `rauch_lower_of_jacobi_constCurv` — **conditional** (proved): **sharp Rauch II**:
  for `k ≤ K ≤ 0` on `(0,T)`, a positive Jacobi solution with the standard initial data
  satisfies `j_K'(t)/j_K(t) ≤ u'(t)/u(t)` on `(0,T)`.  The proof consumes the constructed
  Euclidean normalizations of both the unknown solution and the model through the *mirrored*
  D12 engine `riccati_ge_of_singular_normalization` with `k̄ = K`.
* `sinh_quarter_le_three`, `sinh_one_le_three` — general (proved): explicit numerical
  bounds used by the witness.
* `rauch_lower_constCurv_witness` — **model** (proved): `k = −2` compared against the model
  `K = −1` on `(0,1/4)`, giving `coth t ≤ √2·coth(√2 t)`.

Semantic class: conditional analytic comparison (scalar ODE), not the manifold-level Rauch
theorem.
-/
import Poincare.L4.GeodesicComparison.ConstantCurvatureRauch

noncomputable section

open Set Filter
open scoped Topology
open MeasureTheory

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-! ## 1. Positivity, monotonicity and the model bound for `K ≤ 0` -/

/-- **Positivity of the model for nonpositive curvature.**  For `K ≤ 0` and `t > 0`,
`jacobiSol K t > 0`: the hyperbolic branch has no zeros. -/
theorem jacobiSol_pos_of_nonpos {K t : ℝ} (hK : K ≤ 0) (ht : 0 < t) :
    0 < jacobiSol K t := by
  rcases eq_or_lt_of_le hK with h | h
  · subst h
    rw [jacobiSol_of_zero]
    exact ht
  · rw [jacobiSol_of_neg h, jacobiSolHyperbolic]
    have hsqrt : 0 < Real.sqrt (-K) := Real.sqrt_pos_of_pos (by linarith)
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hsqrt ht)) hsqrt

/-- **Monotonicity of the model for nonpositive curvature.**  `j_K` is monotone on `[0,T]`
for `K ≤ 0`, because `j_K' = cosh(√(−K)·) ≥ 0` (and `j_0' = 1`). -/
theorem jacobiSol_monotoneOn_of_nonpos {K T : ℝ} (hK : K ≤ 0) :
    MonotoneOn (jacobiSol K) (Icc 0 T) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 T) (continuous_jacobiSol K).continuousOn
    (differentiable_jacobiSol K).differentiableOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [jacobiSol_deriv]
  rcases eq_or_lt_of_le hK with h | h
  · subst h
    rw [jacobiDeriv_of_zero]
    norm_num
  · rw [jacobiDeriv_of_neg h]
    exact (Real.cosh_pos _).le

/-- **Second-derivative bound for the model with `K ≤ 0`.**  `|j_K''(t)| = |K|·j_K(t) ≤
|K|·j_K(T)` on `(0,T)`, by monotonicity and positivity of `j_K`. -/
theorem jacobiSol_second_deriv_bound_nonpos {K T : ℝ} (hK : K ≤ 0) :
    ∀ t ∈ Ioo 0 T, |(-(K * jacobiSol K t))| ≤ |K| * jacobiSol K T := by
  intro t ht
  rcases eq_or_lt_of_le hK with h | h
  · subst h
    simp
  · have htT : t ≤ T := ht.2.le
    have ht0 : 0 ≤ t := ht.1.le
    have hmono := jacobiSol_monotoneOn_of_nonpos (K := K) (T := T) hK
    have hle : jacobiSol K t ≤ jacobiSol K T :=
      hmono ⟨ht0, htT⟩ ⟨le_trans ht0 htT, le_rfl⟩ htT
    have hpos_t : 0 < jacobiSol K t := jacobiSol_pos_of_nonpos hK ht.1
    calc |(-(K * jacobiSol K t))| = (-K) * jacobiSol K t := by
          rw [abs_neg, abs_mul, abs_of_neg h, abs_of_pos hpos_t]
      _ ≤ (-K) * jacobiSol K T := mul_le_mul_of_nonneg_left hle (by linarith)
      _ = |K| * jacobiSol K T := by rw [abs_of_neg h]

/-! ## 2. Sharp Rauch II against `j_K` for `K ≤ 0` -/

/-- **Sharp Rauch II comparison.**  If `k ≤ K ≤ 0` on `(0,T)`, the unknown scalar Jacobi
solution has `u 0 = 0`, `u' 0 = 1`, is positive on `(0,T]`, has `|u''| ≤ B` with
`B t₀ ≤ 1/2`, and the model threshold satisfies `(|K|·j_K(T))·t₀ ≤ 1/2`, then
`j_K'(t)/j_K(t) ≤ u'(t)/u(t)` on `(0,T)`. -/
theorem rauch_lower_of_jacobi_constCurv {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ}
    (hT : 0 < T) (hBnn : 0 ≤ B) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hBt₀ : B * t₀ ≤ 1 / 2)
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B) (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) (hK : K ≤ 0) (hk : ∀ t ∈ Ioo 0 T, k t ≤ K)
    (hBmodel : (|K| * jacobiSol K T) * t₀ ≤ 1 / 2) :
    ∀ t ∈ Ioo 0 T, jacobiDeriv K t / jacobiSol K t ≤ du t / u t := by
  have hmodel := jacobiSol_jacobiSolutionOn K T
  have hmodelpos : ∀ t ∈ Ioc 0 T, 0 < jacobiSol K t :=
    fun t ht => jacobiSol_pos_of_nonpos hK ht.1
  have hmodelbound := jacobiSol_second_deriv_bound_nonpos (K := K) (T := T) hK
  have hBmodelnn : 0 ≤ |K| * jacobiSol K T :=
    mul_nonneg (abs_nonneg K) (le_of_lt (jacobiSol_pos_of_nonpos hK hT))
  have hmodelcont : ContinuousOn (fun t => -(K * jacobiSol K t)) (Icc 0 T) :=
    ((continuous_const.mul (continuous_jacobiSol K)).neg).continuousOn
  have hid := riccati_identity_of_jacobi h hpos
  have hidmodel := riccati_identity_of_jacobi hmodel hmodelpos
  have hnorm := euclideanNormalizedOn_of_jacobi h hdducont hBnn hB hu0 hdu0 ht₀ ht₀T hBt₀
  have hnormbar := euclideanNormalizedOn_of_jacobi (k := fun _ : ℝ => K)
    (u := jacobiSol K) (du := jacobiDeriv K) (ddu := fun t => -(K * jacobiSol K t))
    hmodel hmodelcont hBmodelnn hmodelbound (jacobiSol_zero K) (jacobiDeriv_zero K)
    ht₀ ht₀T hBmodel
  have hnorm' : EuclideanNormalizedOn (fun t => du t / u t) 1
      (max (4 * B) (4 * (|K| * jacobiSol K T))) t₀ :=
    fun t ht => le_trans (hnorm ht) (le_max_left _ _)
  have hnormbar' : EuclideanNormalizedOn (fun t => jacobiDeriv K t / jacobiSol K t) 1
      (max (4 * B) (4 * (|K| * jacobiSol K T))) t₀ :=
    fun t ht => le_trans (hnormbar ht) (le_max_right _ _)
  have hmain := riccati_ge_of_singular_normalization (d := 1) (T := T)
    (C := max (4 * B) (4 * (|K| * jacobiSol K T)))
    (t₀ := t₀) (k := k) (kbar := fun _ : ℝ => K) (m := fun t => du t / u t)
    (dm := fun t => (ddu t * u t - du t ^ 2) / u t ^ 2)
    (mbar := fun t => jacobiDeriv K t / jacobiSol K t)
    (dmbar := fun t => ((-(K * jacobiSol K t)) * jacobiSol K t - jacobiDeriv K t ^ 2) /
      jacobiSol K t ^ 2)
    (by norm_num) hT (by positivity) ht₀ ht₀T
    (fun t ht => le_of_eq (hid.2 t ht).symm)
    (fun t ht => hidmodel.2 t ht)
    (fun t ht => hk t ht)
    (fun t ht => hid.1 t ht)
    (fun t ht => hidmodel.1 t ht)
    (logDeriv_continuousOn h hpos) (logDeriv_continuousOn hmodel hmodelpos) hnorm' hnormbar'
  intro t ht
  exact hmain ht

/-! ## 3. Non-vacuity -/

/-- `sinh (1/4) ≤ 3`, via `sinh < exp` and `exp 1 < 3`. -/
theorem sinh_quarter_le_three : Real.sinh (1 / 4) ≤ 3 := by
  have h1 : Real.sinh (1 / 4) < Real.exp (1 / 4) := by
    rw [Real.sinh_eq]
    have hpos := Real.exp_pos (-(1 / 4))
    have hpos' := Real.exp_pos (1 / 4)
    linarith
  have h2 : Real.exp (1 / 4) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
  linarith [Real.exp_one_lt_three]

/-- `sinh 1 ≤ 3`. -/
theorem sinh_one_le_three : Real.sinh 1 ≤ 3 := by
  have h1 : Real.sinh 1 < Real.exp 1 := by
    rw [Real.sinh_eq]
    have hpos := Real.exp_pos (-1 : ℝ)
    have hpos' := Real.exp_pos (1 : ℝ)
    linarith
  linarith [Real.exp_one_lt_three]

/-- **Rauch II witness.**  The `k = −2` model compared against the `K = −1` model on
`(0,1/4)` satisfies every hypothesis of `rauch_lower_of_jacobi_constCurv` and yields the
genuinely nontrivial inequality `coth t ≤ √2·coth(√2 t)`. -/
theorem rauch_lower_constCurv_witness :
    ∀ t ∈ Ioo (0 : ℝ) (1 / 4),
      jacobiDeriv (-1) t / jacobiSol (-1) t ≤ jacobiDeriv (-2) t / jacobiSol (-2) t := by
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  have hsqrt2_one : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hval2 : jacobiSol (-2) (1 / 4) ≤ 3 := by
    rw [jacobiSol_of_neg (by norm_num : (-2 : ℝ) < 0), jacobiSolHyperbolic]
    simp only [neg_neg]
    have harg : Real.sqrt 2 * (1 / 4) ≤ 1 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2, hsqrt2_pos]
    have hsinh : Real.sinh (Real.sqrt 2 * (1 / 4)) ≤ 3 :=
      le_trans (Real.sinh_le_sinh.mpr harg) sinh_one_le_three
    calc Real.sinh (Real.sqrt 2 * (1 / 4)) / Real.sqrt 2
        ≤ Real.sinh (Real.sqrt 2 * (1 / 4)) / 1 :=
          div_le_div_of_nonneg_left (by positivity) zero_lt_one hsqrt2_one
      _ = Real.sinh (Real.sqrt 2 * (1 / 4)) := div_one _
      _ ≤ 3 := hsinh
  have hval1 : jacobiSol (-1) (1 / 4) ≤ 3 := by
    rw [jacobiSol_of_neg (by norm_num : (-1 : ℝ) < 0), jacobiSolHyperbolic]
    simp only [neg_neg, Real.sqrt_one, one_mul, div_one]
    exact sinh_quarter_le_three
  have hmain := rauch_lower_of_jacobi_constCurv (T := 1 / 4) (B := 6) (t₀ := 1 / 12)
    (K := -1) (k := fun _ : ℝ => -2) (u := jacobiSol (-2)) (du := jacobiDeriv (-2))
    (ddu := fun t => -((-2 : ℝ) * jacobiSol (-2) t))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (jacobiSol_jacobiSolutionOn (-2) (1 / 4))
    (((continuous_const.mul (continuous_jacobiSol (-2))).neg).continuousOn)
    (fun t ht => by
      have hb := jacobiSol_second_deriv_bound_nonpos (K := -2) (T := 1 / 4)
        (by norm_num) t ht
      rw [abs_of_neg (by norm_num : (-2 : ℝ) < 0)] at hb
      linarith)
    (jacobiSol_zero (-2)) (jacobiDeriv_zero (-2))
    (fun t ht => jacobiSol_pos_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0) ht.1)
    (by norm_num) (fun t ht => by norm_num)
    (by
      have h1 : |(-1 : ℝ)| * jacobiSol (-1) (1 / 4) * (1 / 12) ≤ 1 / 2 := by
        rw [abs_neg, abs_one, one_mul]
        linarith
      simpa [mul_assoc] using h1)
  intro t ht
  exact hmain t ht

/-! ## 4. Integrated form: `j_K ≤ u` -/

/-- **Integrated Rauch II comparison.**  Under the hypotheses of
`rauch_lower_of_jacobi_constCurv`, the constant-curvature model is dominated by the Jacobi
solution: `j_K t ≤ u t` on `(0,T)`.  Proof: the log-derivative comparison makes `j_K/u`
antitone (D12 `areaRatio_antitone_of_logDeriv_le`); the linear bounds give `j_K s/s → 1` and
`u s/s → 1` as `s → 0⁺`; passing to the limit in `j_K t/u t ≤ j_K s/u s` gives
`j_K t/u t ≤ 1`. -/
theorem constCurvModel_le_jacobi {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ}
    (hT : 0 < T) (hBnn : 0 ≤ B) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hBt₀ : B * t₀ ≤ 1 / 2)
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B) (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) (hK : K ≤ 0) (hk : ∀ t ∈ Ioo 0 T, k t ≤ K)
    (hBmodel : (|K| * jacobiSol K T) * t₀ ≤ 1 / 2) :
    ∀ t ∈ Ioo 0 T, jacobiSol K t ≤ u t := by
  have hmodel := jacobiSol_jacobiSolutionOn K T
  have hmodelpos : ∀ t ∈ Ioc 0 T, 0 < jacobiSol K t :=
    fun t ht => jacobiSol_pos_of_nonpos hK ht.1
  have hmodelbound := jacobiSol_second_deriv_bound_nonpos (K := K) (T := T) hK
  have hBmodelnn : 0 ≤ |K| * jacobiSol K T :=
    mul_nonneg (abs_nonneg K) (le_of_lt (jacobiSol_pos_of_nonpos hK hT))
  have hmodelcont : ContinuousOn (fun t => -(K * jacobiSol K t)) (Icc 0 T) :=
    ((continuous_const.mul (continuous_jacobiSol K)).neg).continuousOn
  have hmle := rauch_lower_of_jacobi_constCurv hT hBnn ht₀ ht₀T hBt₀ h hdducont hB hu0
    hdu0 hpos hK hk hBmodel
  have hanti := areaRatio_antitone_of_logDeriv_le (T := T) (A := jacobiSol K)
    (dA := jacobiDeriv K) (Abar := u) (dAbar := du)
    (m := fun t => jacobiDeriv K t / jacobiSol K t) (mbar := fun t => du t / u t) hT
    (fun t ht => hmodel.hasDerivAt_u ht) (fun t ht => h.hasDerivAt_u ht)
    hmodel.continuousOn_u h.continuousOn_u hmodelpos hpos
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
      refine squeeze_zero' (g := fun s => (|K| * jacobiSol K T) * s)
        (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
      · filter_upwards [Ioo_mem_nhdsGT hT] with s hs
        have hs2 : |jacobiSol K s - s| ≤ (|K| * jacobiSol K T) * s ^ 2 :=
          (jacobi_linear_bounds hmodel hmodelcont hBmodelnn hmodelbound
            (jacobiSol_zero K) (jacobiDeriv_zero K)).2 s hs
        simp only [norm_div, Real.norm_eq_abs, abs_of_pos hs.1]
        rw [div_le_iff₀ hs.1]
        calc |jacobiSol K s - s| ≤ (|K| * jacobiSol K T) * s ^ 2 := hs2
          _ = ((|K| * jacobiSol K T) * s) * s := by ring
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
  have hratio : Tendsto (fun s => jacobiSol K s / u s) (𝓝[>] 0) (𝓝 1) := by
    have h := hjlim.div hulim (by norm_num : (1 : ℝ) ≠ 0)
    rw [div_one] at h
    refine h.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hT] with s hs
    have hus : u s ≠ 0 := ne_of_gt (hpos s ⟨hs.1, hs.2.le⟩)
    have hs0 : s ≠ 0 := ne_of_gt hs.1
    simp only [Pi.div_apply]
    field_simp [hs0, hus]
  intro t ht
  have htIoc : t ∈ Ioc 0 T := ⟨ht.1, ht.2.le⟩
  have hev : ∀ᶠ s in 𝓝[>] 0, jacobiSol K t / u t ≤ jacobiSol K s / u s := by
    filter_upwards [Ioo_mem_nhdsGT ht.1] with s hs
    have hsIoc : s ∈ Ioc 0 T := ⟨hs.1, le_of_lt (lt_trans hs.2 ht.2)⟩
    exact hanti hsIoc htIoc hs.2.le
  have hlim_le := le_of_tendsto_of_tendsto tendsto_const_nhds hratio hev
  rwa [div_le_one (hpos t htIoc)] at hlim_le

/-- **Integrated lower-comparison witness.**  The `k = −2` model dominates the `K = −1`
model on `(0,1/4)`: `j_{−1} t ≤ j_{−2} t`, i.e. `sinh t ≤ sinh(√2 t)/√2`. -/
theorem constCurvModel_le_jacobi_witness :
    ∀ t ∈ Ioo (0 : ℝ) (1 / 4), jacobiSol (-1) t ≤ jacobiSol (-2) t := by
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  have hsqrt2_one : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hval2 : jacobiSol (-2) (1 / 4) ≤ 3 := by
    rw [jacobiSol_of_neg (by norm_num : (-2 : ℝ) < 0), jacobiSolHyperbolic]
    simp only [neg_neg]
    have harg : Real.sqrt 2 * (1 / 4) ≤ 1 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2, hsqrt2_pos]
    have hsinh : Real.sinh (Real.sqrt 2 * (1 / 4)) ≤ 3 :=
      le_trans (Real.sinh_le_sinh.mpr harg) sinh_one_le_three
    calc Real.sinh (Real.sqrt 2 * (1 / 4)) / Real.sqrt 2
        ≤ Real.sinh (Real.sqrt 2 * (1 / 4)) / 1 :=
          div_le_div_of_nonneg_left (by positivity) zero_lt_one hsqrt2_one
      _ = Real.sinh (Real.sqrt 2 * (1 / 4)) := div_one _
      _ ≤ 3 := hsinh
  have hval1 : jacobiSol (-1) (1 / 4) ≤ 3 := by
    rw [jacobiSol_of_neg (by norm_num : (-1 : ℝ) < 0), jacobiSolHyperbolic]
    simp only [neg_neg, Real.sqrt_one, one_mul, div_one]
    exact sinh_quarter_le_three
  have hmain := constCurvModel_le_jacobi (T := 1 / 4) (B := 6) (t₀ := 1 / 12)
    (K := -1) (k := fun _ : ℝ => -2) (u := jacobiSol (-2)) (du := jacobiDeriv (-2))
    (ddu := fun t => -((-2 : ℝ) * jacobiSol (-2) t))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (jacobiSol_jacobiSolutionOn (-2) (1 / 4))
    (((continuous_const.mul (continuous_jacobiSol (-2))).neg).continuousOn)
    (fun t ht => by
      have hb := jacobiSol_second_deriv_bound_nonpos (K := -2) (T := 1 / 4)
        (by norm_num) t ht
      rw [abs_of_neg (by norm_num : (-2 : ℝ) < 0)] at hb
      linarith)
    (jacobiSol_zero (-2)) (jacobiDeriv_zero (-2))
    (fun t ht => jacobiSol_pos_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0) ht.1)
    (by norm_num) (fun t ht => by norm_num)
    (by
      have h1 : |(-1 : ℝ)| * jacobiSol (-1) (1 / 4) * (1 / 12) ≤ 1 / 2 := by
        rw [abs_neg, abs_one, one_mul]
        linarith
      simpa [mul_assoc] using h1)
  intro t ht
  exact hmain t ht


end Poincare.L4.GeodesicComparison
