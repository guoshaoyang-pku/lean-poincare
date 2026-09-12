/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D12 — the volume-ratio (Bishop–Gromov) analytic core

This file separates the **ODE comparison** (already proved in `SturmComparison`,
`RiccatiComparison`, `SingularRiccati`) from the **volume-ratio consequence**, and proves
the latter under fully expanded analytic hypotheses on two "radial area" functions
`A, Ā : ℝ → ℝ` together with their logarithmic derivatives `m = A'/A`, `m̄ = Ā'/Ā`:

1. `areaRatio_antitone_of_logDeriv_le` — if `m ≤ m̄` on `(0,T)` and `A, Ā > 0` on
   `(0,T]`, then `A/Ā` is antitone on `(0,T]` (the quotient rule applied pairwise).
2. `radialVolume_pos_of_pos` — if `Ā` is continuous on `[0,T]` and positive on `(0,T]`,
   then `V̄ r = ∫₀ʳ Ā > 0` for every `r ∈ (0,T]` (compactness: the minimum of `Ā` on
   `[r/2, r]` is positive).
3. `volumeRatio_antitone` — **the Bishop–Gromov volume-ratio monotonicity**: if `A/Ā` is
   antitone on `(0,T]`, `Ā > 0` on `(0,T]` and `A 0 = Ā 0 = 0`, then `V/V̄` is antitone on
   `(0,T]`, where `V r = radialVolume A r = ∫₀ʳ A`.  The proof differentiates the ratio:
   `(V/V̄)'(r) = (A r·V̄ r − V r·Ā r)/V̄ r²` and the numerator is the integral
   `∫₀ʳ (A r·Ā s − A s·Ā r) ds ≤ 0` of a pointwise nonpositive integrand (the ratio
   antitone gives `A r·Ā s ≤ A s·Ā r` on `(0,r)`, and at `s = 0, r` the integrand
   vanishes because `A 0 = Ā 0 = 0`).
4. `bishopGromovVolumeRatio` — the full chain from the **singular Riccati comparison**:
   `m' + m²/d + k ≤ 0` for `m = A'/A`, model equality `m̄' + m̄²/d + k̄ = 0` for `m̄ = Ā'/Ā`,
   `k̄ ≤ k` on `(0,T)`, the quantitative Euclidean normalizations, and the area-level
   hypotheses, imply the volume-ratio comparison

       V R / V̄ R ≤ V r / V̄ r    for every  0 < r ≤ R ≤ T.

Everything is analytic: `A, Ā` are *densities* (the areas of geodesic spheres in the
geometric picture).  The geometric construction that identifies these densities with
actual Riemannian areas/volumes is **not** part of this file and is recorded in the
result card under "missing geometric construction" — in particular the matrix Riccati
equation `S' + S² + R_γ = 0` of the shape operator, the Cauchy–Schwarz step
`tr S² ≥ (tr S)²/(n−1)`, and the identification of metric balls with `[0,t] ×` tangent
sphere (see the header of `Definitions.lean`).
-/
import Poincare.D12.ComparisonGeodesics.Definitions
import Poincare.D12.ComparisonGeodesics.SingularRiccati
import Poincare.D12.ComparisonGeodesics.SturmComparison
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Order.Compact

noncomputable section

open Set Filter
open scoped Topology
open MeasureTheory

namespace Poincare.D12.ComparisonGeodesics

/-! ## 1. The area ratio `A/Ā` -/

/-- The quotient rule for `A/Ā` in terms of the logarithmic derivatives `m = A'/A`,
`m̄ = Ā'/Ā`: `(A/Ā)' = (A/Ā)·(m − m̄)`. -/
theorem areaRatio_hasDerivAt {A dA Abar dAbar m mbar : ℝ → ℝ} {t : ℝ}
    (hA : HasDerivAtR A (dA t) t) (hAbar : HasDerivAtR Abar (dAbar t) t)
    (hA0 : A t ≠ 0) (hAbar0 : Abar t ≠ 0)
    (hm : m t = dA t / A t) (hmbar : mbar t = dAbar t / Abar t) :
    HasDerivAtR (fun s => A s / Abar s) ((A t / Abar t) * (m t - mbar t)) t := by
  have hdiv : HasDerivAtR (fun s => A s / Abar s)
      ((dA t * Abar t - A t * dAbar t) / Abar t ^ 2) t :=
    hA.div hAbar hAbar0
  have hfact : (dA t * Abar t - A t * dAbar t) / Abar t ^ 2
      = (A t / Abar t) * (m t - mbar t) := by
    rw [hm, hmbar]
    field_simp [hA0, hAbar0]
  simpa [hfact] using hdiv

/-- **Area-ratio antitone.**  If `m = A'/A ≤ m̄ = Ā'/Ā` on `(0,T)` and `A, Ā > 0` on
`(0,T]`, then `A/Ā` is antitone on `(0,T]`: for `s ≤ t` in `(0,T]`,
`A t/Ā t ≤ A s/Ā s`.  The proof is pairwise: on each `[s,t]` the derivative
`(A/Ā)·(m − m̄) ≤ 0` is nonpositive, so `antitoneOn_of_deriv_nonpos` applies (the set
`(0,T]` itself is not convex, which is why the conclusion is stated pairwise). -/
theorem areaRatio_antitone_of_logDeriv_le {T : ℝ} {A dA Abar dAbar m mbar : ℝ → ℝ}
    (_hT : 0 < T)
    (hA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR A (dA t) t)
    (hAbar : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR Abar (dAbar t) t)
    (hAcont : ContinuousOn A (Icc 0 T)) (hAbarcont : ContinuousOn Abar (Icc 0 T))
    (hApos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < A t)
    (hAbarpos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < Abar t)
    (hmA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → m t = dA t / A t)
    (hmAbar : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → mbar t = dAbar t / Abar t)
    (hmle : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → m t ≤ mbar t) :
    ∀ ⦃s : ℝ⦄, s ∈ Ioc 0 T → ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → s ≤ t → A t / Abar t ≤ A s / Abar s := by
  intro s hs t ht hst
  have hcont_ratio : ContinuousOn (fun x => A x / Abar x) (Icc s t) := by
    exact (hAcont.mono (by intro x hx; exact ⟨le_trans hs.1.le hx.1, le_trans hx.2 ht.2⟩)).div
      (hAbarcont.mono (by intro x hx; exact ⟨le_trans hs.1.le hx.1, le_trans hx.2 ht.2⟩))
      (by intro x hx; exact ne_of_gt (hAbarpos ⟨lt_of_lt_of_le hs.1 hx.1, le_trans hx.2 ht.2⟩))
  have hdiff : DifferentiableOn ℝ (fun x => A x / Abar x) (Ioo s t) := by
    intro x hx
    have hx0 : x ∈ Ioo 0 T := Ioo_subset_Ioo (le_of_lt hs.1) ht.2 hx
    have hxIoc : x ∈ Ioc 0 T := ⟨lt_trans hs.1 hx.1, le_trans (le_of_lt hx.2) ht.2⟩
    exact (areaRatio_hasDerivAt (hA hx0) (hAbar hx0)
      (ne_of_gt (hApos hxIoc)) (ne_of_gt (hAbarpos hxIoc))
      (hmA hx0) (hmAbar hx0)).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn (fun x => A x / Abar x) (Icc s t) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc s t) hcont_ratio ?_ ?_
    · simpa [interior_Icc] using hdiff
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : x ∈ Ioo 0 T := Ioo_subset_Ioo (le_of_lt hs.1) ht.2 hx
      have hxIoc : x ∈ Ioc 0 T := ⟨lt_trans hs.1 hx.1, le_trans (le_of_lt hx.2) ht.2⟩
      have hderiv : HasDerivAtR (fun y => A y / Abar y)
          ((A x / Abar x) * (m x - mbar x)) x :=
        areaRatio_hasDerivAt (hA hx0) (hAbar hx0)
          (ne_of_gt (hApos hxIoc)) (ne_of_gt (hAbarpos hxIoc))
          (hmA hx0) (hmAbar hx0)
      rw [hderiv.deriv]
      exact mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (le_of_lt (hApos hxIoc)) (le_of_lt (hAbarpos hxIoc)))
        (sub_nonpos.mpr (hmle hx0))
  exact hanti (Set.left_mem_Icc.mpr hst) (Set.right_mem_Icc.mpr hst) hst

/-! ## 2. Positivity of the model volume -/

/-- If `Ā` is continuous on `[0,T]` and positive on `(0,T]`, then the cumulative volume
`V̄ r = ∫₀ʳ Ā` is positive for every `r ∈ (0,T]`.  The minimum of `Ā` on `[r/2, r]` is
positive (compactness), so `∫_{r/2}ʳ Ā ≥ (r/2)·Ā s₀ > 0`; and `∫₀^{r/2} Ā ≥ 0` because
`Ā ≥ 0` on `[0,r]` (positivity on `(0,r]` plus continuity at `0`). -/
theorem radialVolume_pos_of_pos {A : ℝ → ℝ} {T : ℝ} (_hT : 0 < T)
    (hcont : ContinuousOn A (Icc 0 T)) (hpos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < A t) :
    ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < radialVolume A t := by
  intro t ht
  have htpos : 0 < t := ht.1
  have htT : t ≤ T := ht.2
  -- A 0 ≥ 0 via the reflection argument (positivity on (0,t] + continuity at 0).
  have hnonneg0 : 0 ≤ A 0 := by
    have hcont' : ContinuousOn (fun y => A (t - y)) (Icc 0 t) := by
      refine (hcont.comp ((continuousOn_const : ContinuousOn (fun _ : ℝ => t) (Icc 0 t)).sub
        continuousOn_id) ?_)
      intro y hy
      exact ⟨show 0 ≤ t - y from sub_nonneg.mpr hy.2,
        show t - y ≤ T from le_trans (sub_le_self t hy.1) htT⟩
    have hpos' : ∀ ⦃y : ℝ⦄, y ∈ Ioo 0 t → 0 < A (t - y) := by
      intro y hy
      exact hpos ⟨sub_pos.mpr hy.2, le_trans (sub_le_self t (le_of_lt hy.1)) htT⟩
    have hle := nonneg_of_continuousOn_of_posOn_Ioo (u := fun y => A (t - y)) (a := (0 : ℝ)) (b := t)
      htpos hcont' hpos'
    simpa using hle
  -- Ā ≥ 0 on [0,t].
  have hnonneg : ∀ ⦃x : ℝ⦄, x ∈ Icc 0 t → 0 ≤ A x := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      exact hnonneg0
    · exact le_of_lt (hpos ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), le_trans hx.2 htT⟩)
  -- ∫₀^{t/2} ≥ 0
  have hnonneg_int1 : 0 ≤ ∫ s in (0:ℝ)..(t/2), A s := by
    refine intervalIntegral.integral_nonneg ?_ ?_
    · exact le_of_lt (half_pos htpos)
    · intro x hx
      exact hnonneg ⟨hx.1, le_trans hx.2 (half_le_self htpos.le)⟩
  -- the minimum of A on [t/2, t] is positive
  have hcomp : IsCompact (Icc (t/2) t) := isCompact_Icc
  have hne : (Icc (t/2) t).Nonempty := ⟨t/2, ⟨le_rfl, half_le_self htpos.le⟩⟩
  have hcont' : ContinuousOn A (Icc (t/2) t) :=
    hcont.mono (by intro x hx; exact ⟨le_trans (half_pos htpos).le hx.1, le_trans hx.2 htT⟩)
  rcases hcomp.exists_isMinOn hne hcont' with ⟨s₀, hs₀, hmin⟩
  have hmin' : ∀ y ∈ Icc (t/2) t, A s₀ ≤ A y := by
    intro y hy
    exact hmin hy
  have hs₀Ioc : s₀ ∈ Ioc 0 T := ⟨lt_of_lt_of_le (half_pos htpos) hs₀.1, le_trans hs₀.2 htT⟩
  have hA₀pos : 0 < A s₀ := hpos hs₀Ioc
  have hintA : IntervalIntegrable A volume (t/2) t :=
    (hcont'.mono (by intro x hx; rw [uIcc_of_le (half_le_self htpos.le)] at hx; exact hx)).intervalIntegrable
  have hintC : IntervalIntegrable (fun _ : ℝ => A s₀) volume (t/2) t :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ => A s₀) (uIcc (t/2) t)).intervalIntegrable
  have hmono : (∫ s in (t/2)..t, (fun _ : ℝ => A s₀) s) ≤ ∫ s in (t/2)..t, A s := by
    refine intervalIntegral.integral_mono_on (half_le_self htpos.le) hintC hintA ?_
    intro x hx
    exact hmin' x hx
  rw [intervalIntegral.integral_const] at hmono
  have hpos2 : 0 < ∫ s in (t/2)..t, A s := by
    have h₁ : 0 < (t - t/2) * A s₀ := mul_pos (sub_pos.mpr (half_lt_self htpos)) hA₀pos
    exact lt_of_lt_of_le h₁ hmono
  -- ∫₀ᵗ = ∫₀^{t/2} + ∫_{t/2}ᵗ > 0
  have hint1 : IntervalIntegrable A volume 0 (t/2) :=
    (hcont.mono (by intro x hx; rw [uIcc_of_le (a := (0:ℝ)) (b := t/2) (le_of_lt (half_pos htpos))] at hx; exact ⟨hx.1, le_trans hx.2 (le_trans (half_le_self htpos.le) htT)⟩)).intervalIntegrable
  have hsum : radialVolume A t = (∫ s in (0:ℝ)..(t/2), A s) + ∫ s in (t/2)..t, A s := by
    unfold radialVolume
    exact (intervalIntegral.integral_add_adjacent_intervals hint1 hintA).symm
  rw [hsum]
  linarith

/-! ## 3. The volume ratio `V/V̄` -/

/-- The derivative of the cumulative volume `V r = ∫₀ʳ A` is `A r` (for continuous `A`). -/
theorem radialVolume_hasDerivAt {A : ℝ → ℝ} {T : ℝ} (_hT : 0 < T)
    (hcont : ContinuousOn A (Icc 0 T)) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAtR (radialVolume A) (A t) t := by
  have hint : IntervalIntegrable A volume 0 t :=
    (hcont.mono (by intro x hx; rw [uIcc_of_le (a := (0:ℝ)) (b := t) (le_of_lt ht.1)] at hx; exact ⟨hx.1, le_trans hx.2 (le_of_lt ht.2)⟩)).intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter A (𝓝 t) :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hcont.mono Ioo_subset_Icc_self) t ht
  have hb : ContinuousAt A t :=
    hcont.continuousAt
      (mem_of_superset (show Ioo 0 T ∈ 𝓝 t from isOpen_Ioo.mem_nhds ht) Ioo_subset_Icc_self)
  unfold radialVolume
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hb

/-- The numerator of `(V/V̄)'`: `A x·V̄ x − V x·Ā x = ∫₀ˣ (A x·Ā s − A s·Ā x) ds ≤ 0`,
pointwise from the ratio antitone of `A/Ā` (the integrand vanishes at `s = 0` because
`A 0 = Ā 0 = 0`). -/
theorem radialVolume_numerator_le_zero {T x : ℝ} {A Abar : ℝ → ℝ}
    (_hT : 0 < T) (hx : x ∈ Ioc 0 T)
    (hAcont : ContinuousOn A (Icc 0 T)) (hAbarcont : ContinuousOn Abar (Icc 0 T))
    (hA0 : A 0 = 0) (hAbar0 : Abar 0 = 0)
    (hAbarpos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < Abar t)
    (hratio : ∀ ⦃s : ℝ⦄, s ∈ Ioc 0 T → ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → s ≤ t → A t / Abar t ≤ A s / Abar s) :
    A x * radialVolume Abar x - radialVolume A x * Abar x ≤ 0 := by
  have hxpos : 0 < x := hx.1
  have hxT : x ≤ T := hx.2
  -- The pointwise bound for the integrand on Icc 0 x.
  have hG : ∀ s ∈ Icc 0 x, A x * Abar s - A s * Abar x ≤ 0 := by
    intro s hs
    rcases lt_trichotomy s 0 with hneg | hzero | hpos
    · exact False.elim (not_lt.mpr hs.1 hneg)
    · subst hzero
      simp [hAbar0, hA0]
    · have hsx : s ≤ x := hs.2
      have hsIoc : s ∈ Ioc 0 T := ⟨hpos, le_trans hs.2 hxT⟩
      have hratio_sx : A x / Abar x ≤ A s / Abar s := hratio ⟨hpos, le_trans hs.2 hxT⟩ hx hsx
      have hposprod : 0 < Abar x * Abar s := mul_pos (hAbarpos hx) (hAbarpos hsIoc)
      have hmul := mul_le_mul_of_nonneg_right hratio_sx hposprod.le
      have h₁ : (A x / Abar x) * (Abar x * Abar s) = A x * Abar s := by
        field_simp [ne_of_gt (hAbarpos hx)]
      have h₂ : (A s / Abar s) * (Abar x * Abar s) = A s * Abar x := by
        field_simp [ne_of_gt (hAbarpos hsIoc)]
      rw [h₁, h₂] at hmul
      linarith
  -- Continuity of the integrand on [0,x] ⊆ [0,T].
  have hGcont : ContinuousOn (fun s => A x * Abar s - A s * Abar x) (Icc 0 x) := by
    exact (continuousOn_const.mul
      (hAbarcont.mono (by intro y hy; exact ⟨hy.1, le_trans hy.2 hxT⟩))).sub
      ((hAcont.mono (by intro y hy; exact ⟨hy.1, le_trans hy.2 hxT⟩)).mul_const (Abar x))
  have hGint : IntervalIntegrable (fun s => A x * Abar s - A s * Abar x) volume 0 x :=
    (hGcont.mono (by intro y hy; rw [uIcc_of_le hxpos.le] at hy; exact hy)).intervalIntegrable
  have hzeroInt : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 x :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (uIcc 0 x)).intervalIntegrable
  have hGle : ∫ s in (0:ℝ)..x, (A x * Abar s - A s * Abar x) ≤ 0 := by
    have hmono := intervalIntegral.integral_mono_on hxpos.le hGint hzeroInt (by intro s hs; simpa using hG s hs)
    simpa using hmono
  -- The numerator equals that integral.
  have hmain : ∫ s in (0:ℝ)..x, (A x * Abar s - A s * Abar x)
      = A x * radialVolume Abar x - radialVolume A x * Abar x := by
    change ∫ s in (0:ℝ)..x, (A x * Abar s - A s * Abar x)
      = A x * (∫ s in (0:ℝ)..x, Abar s) - (∫ s in (0:ℝ)..x, A s) * Abar x
    have hAint : IntervalIntegrable (fun s : ℝ => A x * Abar s) volume 0 x :=
      (continuousOn_const.mul
        (hAbarcont.mono (by intro y hy; rw [uIcc_of_le (a := (0:ℝ)) (b := x) hxpos.le] at hy; exact ⟨hy.1, le_trans hy.2 hxT⟩))).intervalIntegrable
    have hBint : IntervalIntegrable (fun s : ℝ => A s * Abar x) volume 0 x :=
      ((hAcont.mono (by intro y hy; rw [uIcc_of_le (a := (0:ℝ)) (b := x) hxpos.le] at hy; exact ⟨hy.1, le_trans hy.2 hxT⟩)).mul_const (Abar x)).intervalIntegrable
    rw [intervalIntegral.integral_sub hAint hBint]
    congr 1
    · rw [intervalIntegral.integral_const_mul]
    · rw [intervalIntegral.integral_mul_const]
  linarith

/-- **Bishop–Gromov volume-ratio monotonicity (analytic core).**  If `A/Ā` is antitone on
`(0,T]`, `Ā > 0` on `(0,T]`, both are continuous on `[0,T]` and vanish at `0`, then
`V/V̄` is antitone on `(0,T]`: for `r ≤ R` in `(0,T]`,

    V R / V̄ R ≤ V r / V̄ r   where   V r = ∫₀ʳ A,  V̄ r = ∫₀ʳ Ā.

The proof: on each `[r,R]` the derivative `(V/V̄)' = (A·V̄ − V·Ā)/V̄²` is nonpositive by
`radialVolume_numerator_le_zero` and the positivity of `V̄`. -/
theorem volumeRatio_antitone {T : ℝ} {A Abar : ℝ → ℝ} (hT : 0 < T)
    (hAcont : ContinuousOn A (Icc 0 T)) (hAbarcont : ContinuousOn Abar (Icc 0 T))
    (hA0 : A 0 = 0) (hAbar0 : Abar 0 = 0)
    (hAbarpos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < Abar t)
    (hratio : ∀ ⦃s : ℝ⦄, s ∈ Ioc 0 T → ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → s ≤ t → A t / Abar t ≤ A s / Abar s) :
    ∀ ⦃r : ℝ⦄, r ∈ Ioc 0 T → ∀ ⦃R : ℝ⦄, R ∈ Ioc 0 T → r ≤ R →
      radialVolume A R / radialVolume Abar R ≤ radialVolume A r / radialVolume Abar r := by
  intro r hr R hR hrR
  have hVpos : ∀ ⦃x : ℝ⦄, x ∈ Ioc 0 T → 0 < radialVolume Abar x :=
    radialVolume_pos_of_pos hT hAbarcont hAbarpos
  have hVcont : ContinuousOn (fun x => radialVolume A x) (Icc r R) := by
    have hint : IntervalIntegrable A volume 0 R :=
      (hAcont.mono (by intro y hy; rw [uIcc_of_le (a := (0:ℝ)) (b := R) hR.1.le] at hy; exact ⟨hy.1, le_trans hy.2 hR.2⟩)).intervalIntegrable
    have hprim : ContinuousOn (fun b => ∫ x in (0:ℝ)..b, A x) (uIcc 0 R) :=
      intervalIntegral.continuousOn_primitive_interval' hint Set.left_mem_uIcc
    unfold radialVolume
    exact hprim.mono (by intro y hy; rw [uIcc_of_le (a := (0:ℝ)) (b := R) hR.1.le]; exact ⟨le_trans hr.1.le hy.1, hy.2⟩)
  have hVbarcont : ContinuousOn (fun x => radialVolume Abar x) (Icc r R) := by
    have hint : IntervalIntegrable Abar volume 0 R :=
      (hAbarcont.mono (by intro y hy; rw [uIcc_of_le (a := (0:ℝ)) (b := R) hR.1.le] at hy; exact ⟨hy.1, le_trans hy.2 hR.2⟩)).intervalIntegrable
    have hprim : ContinuousOn (fun b => ∫ x in (0:ℝ)..b, Abar x) (uIcc 0 R) :=
      intervalIntegral.continuousOn_primitive_interval' hint Set.left_mem_uIcc
    unfold radialVolume
    exact hprim.mono (by intro y hy; rw [uIcc_of_le (a := (0:ℝ)) (b := R) hR.1.le]; exact ⟨le_trans hr.1.le hy.1, hy.2⟩)
  have hcontV : ContinuousOn (fun x => radialVolume A x / radialVolume Abar x) (Icc r R) := by
    exact hVcont.div hVbarcont (by intro x hx; exact ne_of_gt (hVpos ⟨lt_of_lt_of_le hr.1 hx.1, le_trans hx.2 hR.2⟩))
  have hdiff : DifferentiableOn ℝ (fun x => radialVolume A x / radialVolume Abar x) (Ioo r R) := by
    intro x hx
    have hxIoo : x ∈ Ioo 0 T := Ioo_subset_Ioo (le_of_lt hr.1) hR.2 hx
    have hV : HasDerivAtR (radialVolume A) (A x) x := radialVolume_hasDerivAt hT hAcont hxIoo
    have hVbar : HasDerivAtR (radialVolume Abar) (Abar x) x := radialVolume_hasDerivAt hT hAbarcont hxIoo
    have hne : radialVolume Abar x ≠ 0 :=
      ne_of_gt (hVpos ⟨lt_trans hr.1 hx.1, le_trans (le_of_lt hx.2) hR.2⟩)
    exact (hV.div hVbar hne).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn (fun x => radialVolume A x / radialVolume Abar x) (Icc r R) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc r R) hcontV ?_ ?_
    · simpa [interior_Icc] using hdiff
    · intro x hx
      rw [interior_Icc] at hx
      have hxIoo : x ∈ Ioo 0 T := Ioo_subset_Ioo (le_of_lt hr.1) hR.2 hx
      have hxIoc : x ∈ Ioc 0 T := ⟨lt_trans hr.1 hx.1, le_trans (le_of_lt hx.2) hR.2⟩
      have hV : HasDerivAtR (radialVolume A) (A x) x := radialVolume_hasDerivAt hT hAcont hxIoo
      have hVbar : HasDerivAtR (radialVolume Abar) (Abar x) x := radialVolume_hasDerivAt hT hAbarcont hxIoo
      have hVbarpos : 0 < radialVolume Abar x := hVpos hxIoc
      have hdiv : HasDerivAt (fun y => radialVolume A y / radialVolume Abar y)
          ((A x * radialVolume Abar x - radialVolume A x * Abar x) / (radialVolume Abar x) ^ 2) x :=
        hV.div hVbar (ne_of_gt hVbarpos)
      rw [hdiv.deriv]
      exact div_nonpos_of_nonpos_of_nonneg
        (radialVolume_numerator_le_zero hT hxIoc hAcont hAbarcont hA0 hAbar0 hAbarpos hratio)
        (sq_nonneg (radialVolume Abar x))
  exact hanti (Set.left_mem_Icc.mpr hrR) (Set.right_mem_Icc.mpr hrR) hrR

/-! ## 4. The full chain from the singular Riccati comparison -/

/-- **Bishop–Gromov volume-ratio comparison under fully expanded analytic hypotheses.**

Assumptions (all analytic; the geometric identification is recorded separately):

* `d > 0` (the dimension parameter `d = n − 1`), `T > 0`, `0 < t₀ ≤ T`, `C ≥ 0`;
* actual Riccati inequality `m' + m²/d + k ≤ 0` and model Riccati equality
  `m̄' + m̄²/d + k̄ = 0` on `(0,T)`, with `k̄ ≤ k` on `(0,T)` and derivative data `dm, dm̄`;
* `m, m̄` continuous on `(0,T]` and Euclidean-normalized: `|m t − d/t| ≤ C`,
  `|m̄ t − d/t| ≤ C` on `(0,t₀]`;
* the area functions `A, Ā` are `C¹` on `(0,T)` with logarithmic derivatives
  `m = A'/A`, `m̄ = Ā'/Ā`; `A, Ā > 0` on `(0,T]`; `A, Ā` continuous on `[0,T]` and
  `A 0 = Ā 0 = 0`.

Conclusion: for every `0 < r ≤ R ≤ T`,

    V R / V̄ R ≤ V r / V̄ r   where   V r = ∫₀ʳ A,  V̄ r = ∫₀ʳ Ā.

The proof is the chain: singular Riccati comparison (`m ≤ m̄` on `(0,T)`) →
`areaRatio_antitone_of_logDeriv_le` → `volumeRatio_antitone`.  No division at zero is
performed anywhere: denominators are `d > 0`, `t, s ≥ ε > 0`, the positive areas on
`(0,T]`, or the positive volumes `V̄ r > 0`. -/
theorem bishopGromovVolumeRatio {d : ℝ} {T C t₀ : ℝ} {k kbar m dm mbar dmbar : ℝ → ℝ}
    {A dA Abar dAbar : ℝ → ℝ}
    (hdpos : 0 < d) (hT : 0 < T) (hC : 0 ≤ C) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (hineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → dm t + m t ^ 2 / d + k t ≤ 0)
    (heq : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → dmbar t + mbar t ^ 2 / d + kbar t = 0)
    (hkk : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → kbar t ≤ k t)
    (hm : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR m (dm t) t)
    (hmbar : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR mbar (dmbar t) t)
    (hmcont : ContinuousOn m (Ioc 0 T)) (hmbarcont : ContinuousOn mbar (Ioc 0 T))
    (hnorm : EuclideanNormalizedOn m d C t₀) (hnormbar : EuclideanNormalizedOn mbar d C t₀)
    (hA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR A (dA t) t)
    (hAbar : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR Abar (dAbar t) t)
    (hAcont : ContinuousOn A (Icc 0 T)) (hAbarcont : ContinuousOn Abar (Icc 0 T))
    (hApos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < A t)
    (hAbarpos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < Abar t)
    (hA0 : A 0 = 0) (hAbar0 : Abar 0 = 0)
    (hmA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → m t = dA t / A t)
    (hmAbar : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → mbar t = dAbar t / Abar t) :
    ∀ ⦃r : ℝ⦄, r ∈ Ioc 0 T → ∀ ⦃R : ℝ⦄, R ∈ Ioc 0 T → r ≤ R →
      radialVolume A R / radialVolume Abar R ≤ radialVolume A r / radialVolume Abar r := by
  have hmle : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → m t ≤ mbar t :=
    riccati_le_of_singular_normalization hdpos hT hC ht₀ ht₀T hineq heq hkk hm hmbar
      hmcont hmbarcont hnorm hnormbar
  have hratio : ∀ ⦃s : ℝ⦄, s ∈ Ioc 0 T → ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → s ≤ t →
      A t / Abar t ≤ A s / Abar s :=
    areaRatio_antitone_of_logDeriv_le hT hA hAbar hAcont hAbarcont hApos hAbarpos
      hmA hmAbar hmle
  exact volumeRatio_antitone hT hAcont hAbarcont hA0 hAbar0 hAbarpos hratio

/-- **Bishop–Gromov inequality, explicit form.**  Under the hypotheses of
`bishopGromovVolumeRatio`, the volume ratio is nonincreasing, so in particular for
`0 < r ≤ R ≤ T` the ball of radius `R` is at most `V̄ R/V̄ r` times the ball of radius `r`
*in the model*, i.e. `V R ≤ (V̄ R/V̄ r)·V r`. -/
theorem bishopGromov_volume_le {d : ℝ} {T C t₀ : ℝ} {k kbar m dm mbar dmbar : ℝ → ℝ}
    {A dA Abar dAbar : ℝ → ℝ}
    (hdpos : 0 < d) (hT : 0 < T) (hC : 0 ≤ C) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (hineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → dm t + m t ^ 2 / d + k t ≤ 0)
    (heq : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → dmbar t + mbar t ^ 2 / d + kbar t = 0)
    (hkk : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → kbar t ≤ k t)
    (hm : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR m (dm t) t)
    (hmbar : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR mbar (dmbar t) t)
    (hmcont : ContinuousOn m (Ioc 0 T)) (hmbarcont : ContinuousOn mbar (Ioc 0 T))
    (hnorm : EuclideanNormalizedOn m d C t₀) (hnormbar : EuclideanNormalizedOn mbar d C t₀)
    (hA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR A (dA t) t)
    (hAbar : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR Abar (dAbar t) t)
    (hAcont : ContinuousOn A (Icc 0 T)) (hAbarcont : ContinuousOn Abar (Icc 0 T))
    (hApos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < A t)
    (hAbarpos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < Abar t)
    (hA0 : A 0 = 0) (hAbar0 : Abar 0 = 0)
    (hmA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → m t = dA t / A t)
    (hmAbar : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → mbar t = dAbar t / Abar t)
    {r R : ℝ} (hr : r ∈ Ioc 0 T) (hR : R ∈ Ioc 0 T) (hrR : r ≤ R) :
    radialVolume A R ≤ (radialVolume Abar R / radialVolume Abar r) * radialVolume A r := by
  have hrat := bishopGromovVolumeRatio hdpos hT hC ht₀ ht₀T hineq heq hkk hm hmbar
    hmcont hmbarcont hnorm hnormbar hA hAbar hAcont hAbarcont hApos hAbarpos hA0 hAbar0
    hmA hmAbar hr hR hrR
  have hVr : 0 < radialVolume Abar r :=
    radialVolume_pos_of_pos hT hAbarcont hAbarpos hr
  have hVR : 0 < radialVolume Abar R :=
    radialVolume_pos_of_pos hT hAbarcont hAbarpos hR
  have hmul := mul_le_mul_of_nonneg_right hrat hVR.le
  have h₁ : (radialVolume A R / radialVolume Abar R) * radialVolume Abar R = radialVolume A R :=
    div_mul_cancel₀ _ (ne_of_gt hVR)
  have h₂ : (radialVolume A r / radialVolume Abar r) * radialVolume Abar R
      = (radialVolume Abar R / radialVolume Abar r) * radialVolume A r := by
    field_simp [ne_of_gt hVr]
  simpa [h₁, h₂] using hmul

end Poincare.D12.ComparisonGeodesics
