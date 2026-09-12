/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — geodesic comparison: from Jacobi initial data to Rauch I and the area-ratio core

This file closes the analytic gap recorded in the D12 `ComparisonGeodesics` result card
(§3, items (i)–(iii) of "what is still missing"): the D12 singular Riccati engine
`riccati_le_of_singular_normalization` consumes the *quantitative Euclidean normalization*
`EuclideanNormalizedOn m d C t₀`, but no lemma produced that normalization from genuine
scalar Jacobi initial data `u 0 = 0`, `u' 0 = 1` with a bounded second derivative.

Contents (all kernel-checked, semantic class marked per declaration):

* `abs_sub_le_of_deriv_bound` — general (proved): a two-sided mean-value/FTC bound for a
  `C¹` function with a bounded derivative on the open interval, stated with only interior
  differentiability and closed-interval continuity (no differentiability at the endpoints).
* `jacobi_linear_bounds` — **conditional** (proved from the explicit Jacobi data): from
  `u 0 = 0`, `du 0 = 1` and `|u''| ≤ B` on `(0,T)` one gets `|u t − t| ≤ B t²` and
  `|du t − 1| ≤ B t` for `t ∈ (0,T)`.
* `jacobi_pos_and_ratio_bound` — **conditional** (proved): consequently `u t ≥ t/2` and
  `|u' t/u t − 1/t| ≤ 4B` whenever `B t ≤ 1/2`.
* `euclideanNormalizedOn_of_jacobi` — **conditional** (proved): the exact
  `EuclideanNormalizedOn (u'/u) 1 (4B) t₀` interface required by the singular comparison.
* `riccati_identity_of_jacobi` — general (proved): for a positive Jacobi solution,
  `m = u'/u` satisfies the Riccati *equality* `m' + m² + k = 0` pointwise on `(0,T)`.
* `rauch_upper_of_jacobi` — **conditional** (proved): **Rauch I upper comparison** for a
  genuine scalar Jacobi solution with `k ≥ 0`: `u' t/u t ≤ 1/t` on `(0,T)`.
* `jacobi_areaRatio_antitone` — **conditional** (proved): the Bishop–Gromov-type consequence
  `u t/t ≤ u s/s` for `0 < s ≤ t < T` (area-ratio antitone), obtained by consuming
  `rauch_upper_of_jacobi` through the D12 theorem `areaRatio_antitone_of_logDeriv_le`.
* `sin_jacobiSolution`, `sin_rauch_witness`, `sin_areaRatio_witness` — **model** (proved): the explicit
  non-vacuous witness `u = sin`, `k = 1`, `B = 1`, `t₀ = 1/2` satisfies every hypothesis and
  yields the genuinely nontrivial inequalities `cos t/sin t ≤ 1/t` and `sin t/t ≤ sin s/s`.

The geometric bridge that identifies `u` with the area density of geodesic spheres (shape
operator Riccati equation, Cauchy–Schwarz) is **not** claimed here; see the result card. The
class of these statements is therefore *conditional analytic comparison*, not the
manifold-level Rauch theorem.
-/
import Poincare.D12.ComparisonGeodesics.ModelEuclidean
import Poincare.D12.ComparisonGeodesics.VolumeRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open Set Filter
open scoped Topology
open MeasureTheory

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics

/-! ## 1. A mean-value bound with interior differentiability only -/

/-- **Mean-value/FTC bound.**  If `f` is continuous on `[a,b]`, `f'` is continuous on
`[a,b]`, `f` has derivative `f' t` at every interior point `t ∈ (a,b)`, and `|f'| ≤ C` on
`(a,b)`, then `|f b − f a| ≤ C (b − a)`.  Stated with interior differentiability only, which
is what the `JacobiSolutionOn` structure provides (it has no differentiability at the
endpoints).  Proof: FTC-2 plus the interval-integral norm bound. -/
theorem abs_sub_le_of_deriv_bound {f f' : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hfcont : ContinuousOn f (Icc a b)) (hf'cont : ContinuousOn f' (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAtR f (f' t) t)
    (hbound : ∀ t ∈ Ioo a b, |f' t| ≤ C) :
    |f b - f a| ≤ C * (b - a) := by
  have hf'cont' : ContinuousOn f' (uIcc a b) := by rwa [uIcc_of_le hab]
  have hFTC : ∫ t in a..b, f' t = f b - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hfcont hderiv
      hf'cont'.intervalIntegrable
  have hnull : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIoc a b → ‖f' t‖ ≤ C := by
    have hb : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hb] with t htb ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    simpa [Real.norm_eq_abs] using hbound t ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩
  have hnorm : ‖∫ t in a..b, f' t‖ ≤ C * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const_ae hnull
  rw [hFTC, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hnorm
  exact hnorm

/-! ## 2. Linear bounds on a Jacobi solution from a second-derivative bound -/

/-- **Jacobi linear bounds.**  For a scalar Jacobi solution `u'' + k u = 0` on `(0,T)` with
`u 0 = 0`, `u' 0 = 1`, continuity of `u`, `u'`, `u''` up to the boundary and `|u''| ≤ B` on
`(0,T)` (with `B ≥ 0`), one has the Euclidean-tangent bounds `|u t − t| ≤ B t²` and
`|u' t − 1| ≤ B t` for every `t ∈ (0,T)`.  This is item (i) of the missing-bridge list in the
D12 card; it is conditional on the second-derivative bound (which is *not* derived here from
a curvature bound — see the result card). -/
theorem jacobi_linear_bounds {k u du ddu : ℝ → ℝ} {T B : ℝ}
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hBnn : 0 ≤ B) (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B)
    (hu0 : u 0 = 0) (hdu0 : du 0 = 1) :
    (∀ t ∈ Ioo 0 T, |du t - 1| ≤ B * t) ∧ (∀ t ∈ Ioo 0 T, |u t - t| ≤ B * t ^ 2) := by
  have hfirst : ∀ t ∈ Ioo 0 T, |du t - 1| ≤ B * t := by
    intro t ht
    have hmain := abs_sub_le_of_deriv_bound (f := fun s => du s - 1) (f' := ddu)
      (a := 0) (b := t) (C := B) ht.1.le
      ((h.continuousOn_du.mono (Icc_subset_Icc_right ht.2.le)).sub continuousOn_const)
      (hdducont.mono (Icc_subset_Icc_right ht.2.le))
      (fun x hx => by
        have hxT : x ∈ Ioo 0 T := ⟨hx.1, lt_trans hx.2 ht.2⟩
        convert (h.hasDerivAt_du hxT).sub (hasDerivAtR_const (1 : ℝ) x) using 1
        · ext s
          simp only [Pi.sub_apply]
        · ring)
      (fun x hx => hB x ⟨hx.1, lt_trans hx.2 ht.2⟩)
    simpa [hdu0] using hmain
  refine ⟨hfirst, ?_⟩
  intro t ht
  have hbound : ∀ x ∈ Ioo 0 t, |du x - 1| ≤ B * t := by
    intro x hx
    have hxT : x ∈ Ioo 0 T := ⟨hx.1, lt_trans hx.2 ht.2⟩
    exact le_trans (hfirst x hxT) (mul_le_mul_of_nonneg_left hx.2.le hBnn)
  have hmain := abs_sub_le_of_deriv_bound (f := fun s => u s - s) (f' := fun s => du s - 1)
    (a := 0) (b := t) (C := B * t) ht.1.le
    ((h.continuousOn_u.mono (Icc_subset_Icc_right ht.2.le)).sub continuousOn_id)
    ((h.continuousOn_du.mono (Icc_subset_Icc_right ht.2.le)).sub continuousOn_const)
    (fun x hx => by
      have hxT : x ∈ Ioo 0 T := ⟨hx.1, lt_trans hx.2 ht.2⟩
      convert (h.hasDerivAt_u hxT).sub (hasDerivAtR_id x) using 1
      ext s
      simp only [Pi.sub_apply])
    hbound
  have hmain' : |u t - t| ≤ B * t * t := by simpa [hu0] using hmain
  calc |u t - t| ≤ B * t * t := hmain'
    _ = B * t ^ 2 := by ring

/-! ## 3. Positivity and the quantitative Euclidean normalization -/

/-- **Positivity and ratio bound.**  Under the hypotheses of `jacobi_linear_bounds`, if in
addition `B t ≤ 1/2` then `u t > 0` and `|u' t/u t − 1/t| ≤ 4B`.  This is the quantitative
Euclidean-tangent normalization in pointwise form. -/
theorem jacobi_pos_and_ratio_bound {k u du ddu : ℝ → ℝ} {T B : ℝ}
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hBnn : 0 ≤ B) (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B)
    (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (hBt : B * t ≤ 1 / 2) :
    0 < u t ∧ |du t / u t - 1 / t| ≤ 4 * B := by
  obtain ⟨hdu, hu⟩ := jacobi_linear_bounds h hdducont hBnn hB hu0 hdu0
  have hdut : |du t - 1| ≤ B * t := hdu t ht
  have hut : |u t - t| ≤ B * t ^ 2 := hu t ht
  have htpos : 0 < t := ht.1
  have htne : t ≠ 0 := ne_of_gt htpos
  have hu_lower : t / 2 ≤ u t := by
    have h₁ : -(B * t ^ 2) ≤ u t - t := (abs_le.mp hut).1
    have h₂ : B * t * t ≤ t / 2 := by nlinarith
    linarith
  have hu_pos : 0 < u t := lt_of_lt_of_le (half_pos htpos) hu_lower
  have hune : u t ≠ 0 := ne_of_gt hu_pos
  have hcross : |t * du t - u t| ≤ 2 * B * t ^ 2 := by
    have hsplit : t * du t - u t = t * (du t - 1) - (u t - t) := by ring
    rw [hsplit]
    calc |t * (du t - 1) - (u t - t)|
        ≤ |t * (du t - 1)| + |u t - t| := abs_sub _ _
      _ = t * |du t - 1| + |u t - t| := by rw [abs_mul, abs_of_pos htpos]
      _ ≤ t * (B * t) + B * t ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left hdut htpos.le) hut
      _ = 2 * B * t ^ 2 := by ring
  have hratio : |du t / u t - 1 / t| ≤ 4 * B := by
    have hrewrite : du t / u t - 1 / t = (t * du t - u t) / (t * u t) := by
      field_simp [hune, htne]
    rw [hrewrite, abs_div, abs_of_pos (mul_pos htpos hu_pos)]
    have hb0 : 0 ≤ 2 * B * t ^ 2 := by positivity
    have htd : t * (t / 2) ≤ t * u t := mul_le_mul_of_nonneg_left hu_lower htpos.le
    have htdpos : 0 < t * (t / 2) := by positivity
    calc |t * du t - u t| / (t * u t)
        ≤ (2 * B * t ^ 2) / (t * u t) :=
          div_le_div_of_nonneg_right hcross (mul_pos htpos hu_pos).le
      _ ≤ (2 * B * t ^ 2) / (t * (t / 2)) :=
          div_le_div_of_nonneg_left hb0 htdpos htd
      _ = 4 * B := by field_simp; ring
  exact ⟨hu_pos, hratio⟩

/-- **The quantitative Euclidean normalization from Jacobi initial data.**  If the
second-derivative bound `|u''| ≤ B` holds on `(0,T)` and `B t₀ ≤ 1/2`, then
`EuclideanNormalizedOn (u'/u) 1 (4B) t₀`, i.e. `|u' t/u t − 1/t| ≤ 4B` for every
`t ∈ (0,t₀)`.  This is the exact interface consumed by
`riccati_le_of_singular_normalization`. -/
theorem euclideanNormalizedOn_of_jacobi {k u du ddu : ℝ → ℝ} {T B t₀ : ℝ}
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hBnn : 0 ≤ B) (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B)
    (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    (_ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hBt₀ : B * t₀ ≤ 1 / 2) :
    EuclideanNormalizedOn (fun t => du t / u t) 1 (4 * B) t₀ := by
  intro t ht
  have htT : t ∈ Ioo 0 T := ⟨ht.1, lt_of_lt_of_le ht.2 ht₀T⟩
  have hBt : B * t ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left ht.2.le hBnn
    linarith
  exact (jacobi_pos_and_ratio_bound h hdducont hBnn hB hu0 hdu0 htT hBt).2

/-! ## 4. The Riccati equation for the logarithmic derivative -/

/-- **The Riccati identity for a positive Jacobi solution.**  If `u > 0` on `(0,T]` and
`u'' + k u = 0`, then `m = u'/u` satisfies `m' = (u'' u − (u')²)/u²` and the Riccati equality
`m' + m²/1 + k = 0` on `(0,T)`.  The positivity on `(0,T]` is what permits the quotient and
also supplies the continuity hypothesis of the singular comparison. -/
theorem riccati_identity_of_jacobi {k u du ddu : ℝ → ℝ} {T : ℝ}
    (h : JacobiSolutionOn k u du ddu 0 T) (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) :
    (∀ t ∈ Ioo 0 T, HasDerivAtR (fun s => du s / u s)
        ((ddu t * u t - du t ^ 2) / u t ^ 2) t) ∧
    (∀ t ∈ Ioo 0 T, (ddu t * u t - du t ^ 2) / u t ^ 2 + (du t / u t) ^ 2 / 1 + k t = 0) := by
  constructor
  · intro t ht
    have hune : u t ≠ 0 := ne_of_gt (hpos t ⟨ht.1, ht.2.le⟩)
    have hd : HasDerivAtR (fun s => du s / u s) ((ddu t * u t - du t * du t) / u t ^ 2) t :=
      (h.hasDerivAt_du ht).div (h.hasDerivAt_u ht) hune
    have h₂ : (ddu t * u t - du t * du t) / u t ^ 2
        = (ddu t * u t - du t ^ 2) / u t ^ 2 := by ring
    simpa only [h₂] using hd
  · intro t ht
    have hune : u t ≠ 0 := ne_of_gt (hpos t ⟨ht.1, ht.2.le⟩)
    rw [h.eq_secondDeriv ht]
    field_simp [hune]
    ring

/-! ## 5. Rauch I upper comparison and its Bishop–Gromov consequence -/

/-- **Rauch I (upper) comparison for a scalar Jacobi solution.**  If `k ≥ 0` on `(0,T)`,
`u'' + k u = 0`, `u > 0` on `(0,T]`, `u 0 = 0`, `u' 0 = 1`, `|u''| ≤ B` on `(0,T)` with
`B ≥ 0`, and `0 < t₀ ≤ T` with `B t₀ ≤ 1/2`, then `u' t/u t ≤ 1/t` for every `t ∈ (0,T)`.
This is the statement obtained by feeding the constructed normalization
(`euclideanNormalizedOn_of_jacobi`) and the constructed Riccati identity
(`riccati_identity_of_jacobi`) into the D12 singular Riccati engine; the Euclidean model
`m̄ = 1/t` is the comparison solution. -/
theorem rauch_upper_of_jacobi {k u du ddu : ℝ → ℝ} {T B t₀ : ℝ}
    (hT : 0 < T) (hBnn : 0 ≤ B) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hBt₀ : B * t₀ ≤ 1 / 2)
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B) (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) (hk : ∀ t ∈ Ioo 0 T, 0 ≤ k t) :
    ∀ t ∈ Ioo 0 T, du t / u t ≤ 1 / t := by
  have hid := riccati_identity_of_jacobi h hpos
  have hnorm := euclideanNormalizedOn_of_jacobi h hdducont hBnn hB hu0 hdu0 ht₀ ht₀T hBt₀
  have hmcont : ContinuousOn (fun t => du t / u t) (Ioc 0 T) := by
    have hdu' : ContinuousOn du (Ioc 0 T) :=
      h.continuousOn_du.mono (fun x hx => ⟨hx.1.le, hx.2⟩)
    have hu' : ContinuousOn u (Ioc 0 T) :=
      h.continuousOn_u.mono (fun x hx => ⟨hx.1.le, hx.2⟩)
    exact hdu'.div hu' (fun x hx => ne_of_gt (hpos x hx))
  have hmain := riccati_le_of_singular_normalization (d := 1) (T := T) (C := 4 * B)
    (t₀ := t₀) (k := k) (kbar := fun _ => 0) (m := fun t => du t / u t)
    (dm := fun t => (ddu t * u t - du t ^ 2) / u t ^ 2)
    (mbar := euclidModelM 1) (dmbar := euclidModelDm 1)
    (by norm_num) hT (by positivity) ht₀ ht₀T
    (fun t ht => le_of_eq (hid.2 t ht))
    (fun t ht => by
      simpa using euclidModelM_riccati (d := 1) (ne_of_gt ht.1)
        (by norm_num : ((1 : ℕ) : ℝ) ≠ 0))
    (fun t ht => hk t ht)
    (fun t ht => hid.1 t ht)
    (fun t ht => euclidModelM_hasDerivAt (d := 1) (ne_of_gt ht.1))
    hmcont euclidModelM_contOn hnorm
    (by simpa using euclidModelM_normalized (d := 1) (C := 4 * B) (t₀ := t₀) (by positivity))
  intro t ht
  have := hmain ht
  simpa [euclidModelM] using this

/-- **Area-ratio antitone (Bishop–Gromov core) for a genuine Jacobi solution.**  With the
hypotheses of `rauch_upper_of_jacobi`, the density ratio `u t/t` is antitone on `(0,T]`:
`u t/t ≤ u s/s` for `0 < s ≤ t ≤ T`.  This is the downstream checked use of the new Rauch
bound, through the D12 theorem `areaRatio_antitone_of_logDeriv_le`; the geometric
identification of `u` with a geodesic-sphere area density is not claimed. -/
theorem jacobi_areaRatio_antitone {k u du ddu : ℝ → ℝ} {T B t₀ : ℝ}
    (hT : 0 < T) (hBnn : 0 ≤ B) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hBt₀ : B * t₀ ≤ 1 / 2)
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B) (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) (hk : ∀ t ∈ Ioo 0 T, 0 ≤ k t) :
    ∀ ⦃s : ℝ⦄, s ∈ Ioc 0 T → ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → s ≤ t →
      u t / t ≤ u s / s := by
  have hle := rauch_upper_of_jacobi hT hBnn ht₀ ht₀T hBt₀ h hdducont hB hu0 hdu0 hpos hk
  have hanti := areaRatio_antitone_of_logDeriv_le (T := T) (A := u) (dA := du)
    (Abar := euclidModelA 1) (dAbar := fun _ => 1)
    (m := fun t => du t / u t) (mbar := euclidModelM 1) hT
    (fun t ht => h.hasDerivAt_u ht)
    (fun t ht => by
      simpa using euclidModelA_hasDerivAt (d := 1) t)
    h.continuousOn_u euclidModelA_contOn hpos
    (fun t ht => euclidModelA_pos ht)
    (fun t ht => rfl)
    (fun t ht => by simp [euclidModelM, euclidModelA])
    (fun t ht => by simpa [euclidModelM] using hle t ht)
  intro s hs t ht hst
  simpa [euclidModelA] using hanti hs ht hst

/-! ## 6. Non-vacuity: the explicit sine model -/

/-- The sine solution `u = sin`, `k = 1` is a Jacobi solution on `(0, 1/2)` with
`u 0 = 0`, `u' 0 = 1` and `|u''| ≤ 1`. -/
theorem sin_jacobiSolution : JacobiSolutionOn (fun _ : ℝ => 1) Real.sin Real.cos
    (fun t => -Real.sin t) 0 (1 / 2) where
  hasDerivAt_u := by
    intro t ht
    simpa using Real.hasDerivAt_sin t
  hasDerivAt_du := by
    intro t ht
    simpa using Real.hasDerivAt_cos t
  eq_secondDeriv := by
    intro t ht
    simp
  continuousOn_u := Real.continuous_sin.continuousOn
  continuousOn_du := Real.continuous_cos.continuousOn

/-- **Rauch I witness.**  The sine model satisfies every hypothesis of
`rauch_upper_of_jacobi` with `B = 1`, `t₀ = 1/2`, and the conclusion is the genuinely
nontrivial inequality `cos t/sin t ≤ 1/t` on `(0,1/2)` (equivalently `t ≤ tan t`). -/
theorem sin_rauch_witness : ∀ t ∈ Ioo (0 : ℝ) (1 / 2), Real.cos t / Real.sin t ≤ 1 / t := by
  have hmain := rauch_upper_of_jacobi (T := 1 / 2) (B := 1) (t₀ := 1 / 2)
    (k := fun _ : ℝ => 1) (u := Real.sin) (du := Real.cos) (ddu := fun t => -Real.sin t)
    (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)
    sin_jacobiSolution
    (by fun_prop)
    (fun t ht => by simpa using Real.abs_sin_le_one (x := t))
    (by simp) (by simp)
    (fun t ht => Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_gt_three]))
    (fun t ht => by norm_num)
  intro t ht
  simpa using hmain t ht

/-- **Area-ratio witness.**  The sine model also satisfies the hypotheses of
`jacobi_areaRatio_antitone`, giving `sin t/t ≤ sin s/s` for `0 < s ≤ t ≤ 1/2`. -/
theorem sin_areaRatio_witness :
    ∀ ⦃s : ℝ⦄, s ∈ Ioc 0 (1 / 2) → ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 (1 / 2) → s ≤ t →
      Real.sin t / t ≤ Real.sin s / s := by
  have hmain := jacobi_areaRatio_antitone (T := 1 / 2) (B := 1) (t₀ := 1 / 2)
    (k := fun _ : ℝ => 1) (u := Real.sin) (du := Real.cos) (ddu := fun t => -Real.sin t)
    (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)
    sin_jacobiSolution
    (by fun_prop)
    (fun t ht => by simpa using Real.abs_sin_le_one (x := t))
    (by simp) (by simp)
    (fun t ht => Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_gt_three]))
    (fun t ht => by norm_num)
  intro s hs t ht hst
  exact hmain hs ht hst

/-! ## 7. Propagation-regime witnesses (`t₀ < T`)

The shipped witnesses above take `t₀ = T = 1/2`, so they exercise only the ε → 0 stage of
`riccati_le_of_singular_normalization`.  The following variants take `T = 3/2 > t₀ = 1/2`
and therefore also exercise the second stage (propagation from `t₀` to `T`), with the same
sine data (`sin > 0` on `(0,3/2]` because `3/2 < π`). -/

/-- The sine solution on the longer interval `(0,3/2)`. -/
theorem sin_jacobiSolution_threeHalves :
    JacobiSolutionOn (fun _ : ℝ => 1) Real.sin Real.cos (fun t => -Real.sin t) 0 (3 / 2) where
  hasDerivAt_u := by
    intro t ht
    simpa using Real.hasDerivAt_sin t
  hasDerivAt_du := by
    intro t ht
    simpa using Real.hasDerivAt_cos t
  eq_secondDeriv := by
    intro t ht
    simp
  continuousOn_u := Real.continuous_sin.continuousOn
  continuousOn_du := Real.continuous_cos.continuousOn

/-- **Rauch I witness, propagation regime.**  With `T = 3/2`, `t₀ = 1/2`, the conclusion
`cos t/sin t ≤ 1/t` holds on the whole interval `(0,3/2)`, so the engine's propagation
stage is exercised by a kernel-checked instance. -/
theorem sin_rauch_witness_long :
    ∀ t ∈ Ioo (0 : ℝ) (3 / 2), Real.cos t / Real.sin t ≤ 1 / t := by
  have hmain := rauch_upper_of_jacobi (T := 3 / 2) (B := 1) (t₀ := 1 / 2)
    (k := fun _ : ℝ => 1) (u := Real.sin) (du := Real.cos) (ddu := fun t => -Real.sin t)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sin_jacobiSolution_threeHalves
    (by fun_prop)
    (fun t ht => by simpa using Real.abs_sin_le_one (x := t))
    (by simp) (by simp)
    (fun t ht => Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_gt_three]))
    (fun t ht => by norm_num)
  intro t ht
  simpa using hmain t ht

/-- **Area-ratio witness, propagation regime.**  With `T = 3/2`, `t₀ = 1/2`,
`sin t/t ≤ sin s/s` for `0 < s ≤ t ≤ 3/2`. -/
theorem sin_areaRatio_witness_long :
    ∀ ⦃s : ℝ⦄, s ∈ Ioc 0 (3 / 2) → ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 (3 / 2) → s ≤ t →
      Real.sin t / t ≤ Real.sin s / s := by
  have hmain := jacobi_areaRatio_antitone (T := 3 / 2) (B := 1) (t₀ := 1 / 2)
    (k := fun _ : ℝ => 1) (u := Real.sin) (du := Real.cos) (ddu := fun t => -Real.sin t)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sin_jacobiSolution_threeHalves
    (by fun_prop)
    (fun t ht => by simpa using Real.abs_sin_le_one (x := t))
    (by simp) (by simp)
    (fun t ht => Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_gt_three]))
    (fun t ht => by norm_num)
  intro s hs t ht hst
  exact hmain hs ht hst

end Poincare.L4.GeodesicComparison
