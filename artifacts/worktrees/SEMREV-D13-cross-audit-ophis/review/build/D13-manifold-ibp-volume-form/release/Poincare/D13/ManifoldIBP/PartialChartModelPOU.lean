/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (unconditional IBP on the partial half-space atlas)

# An explicit partition of unity and the unconditional IBP on the half-space atlas

`ManifoldIBP.PartialChartModel` constructs the genuinely partial atlas `halfSpaceAtlas`
(identity on `{y 0 < 1}`, dilation by `2` on `{0 < y 0}`) and applies the null-boundary
partial-chart IBP theorem to it, with the partition-of-unity data, the chart identifications
`hD`/`hG` and the integrability of the constructed pieces still as hypotheses.

This module discharges all of them for this model:

* `hsStep` — the smooth step `y ↦ smoothTransition (4 * y 0 - 1)`, equal to `0` for
  `y 0 ≤ 1/4` and to `1` for `1/2 ≤ y 0`, with `tsupport ⊆ {0 < y 0} ∩ {y 0 < 1}`;
* `hsPsi χ` — the two-chart partition of unity `ψ 0 = χ * (1 - step)`, `ψ 1 = χ * step`
  subordinate to the two half-space overlaps, with the sum, support, smoothness and compact
  support lemmas;
* **`halfSpaceAtlas_weightedIBP_unconditional`** — the weighted IBP on the partial atlas with
  **no remaining hypotheses** beyond `C²` data and `tsupport v ⊆ {y 0 < 1}` (so that a bump
  `χ` with `tsupport χ ⊆ {y 0 < 1}` and `χ = 1` on `tsupport v` exists by
  `exists_contDiff_bump`). The POU is constructed from `χ`; the chart identifications `hD`/`hG`
  are the D12 dilation chart-independence lemmas; the integrability of the constructed pieces
  and pairings is discharged by `ManifoldIBP.IntegrableTransfer`;
* `halfSpaceAtlas_dirichletEnergy` — the Dirichlet energy identity `∫ (Δ_F V) V = -∫ |∇V|²`
  as a consumed consequence.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.PartialChartModel
import Poincare.D13.ManifoldIBP.OverlapOperatorCheck
import Poincare.D13.ManifoldIBP.IntegrableTransfer
import Poincare.D13.ManifoldIBP.SmoothPartition
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

open scoped BigOperators ENNReal NNReal Topology Matrix Function ContDiff
open MeasureTheory Set Filter Metric Function

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

namespace OverlapAtlas

variable {n : ℕ}

/-! ## The smooth step in the first coordinate -/

/-- The smooth step `y ↦ smoothTransition (4 * y 0 - 1)`: `0` for `y 0 ≤ 1/4`, `1` for
`1/2 ≤ y 0`, and supported in the slab `1/4 < y 0 < 1/2`. -/
def hsStep (y : Vec (n + 1)) : ℝ := Real.smoothTransition (4 * y 0 - 1)

lemma hsStep_zero {y : Vec (n + 1)} (h : y 0 ≤ 1 / 4) : hsStep (n := n) y = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma hsStep_one {y : Vec (n + 1)} (h : 1 / 2 ≤ y 0) : hsStep (n := n) y = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma contDiff_hsStep : ContDiff ℝ ∞ (hsStep (n := n)) := by
  unfold hsStep
  fun_prop

lemma support_hsStep_subset :
    support (hsStep (n := n)) ⊆ {y : Vec (n + 1) | (1 : ℝ) / 4 < y 0} := by
  intro y hy
  rw [Function.mem_support] at hy
  by_contra h
  exact hy (hsStep_zero (le_of_not_gt h))

lemma tsupport_hsStep_subset :
    tsupport (hsStep (n := n)) ⊆ {y : Vec (n + 1) | (1 : ℝ) / 4 ≤ y 0} :=
  closure_minimal
    (fun (y : Vec (n + 1)) hy =>
      le_of_lt (show (1 : ℝ) / 4 < y 0 from support_hsStep_subset hy))
    (isClosed_le continuous_const (continuous_apply (0 : Fin (n + 1))))

lemma tsupport_hsStep_subset_pos : tsupport (hsStep (n := n)) ⊆ {y : Vec (n + 1) | 0 < y 0} :=
  fun _ hy => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) (tsupport_hsStep_subset hy)

/-! ## The two-chart partition of unity -/

/-- The two-chart partition of unity subordinate to the two half-space charts, cut down by a
bump `χ`: `ψ 0 = χ * (1 - step)` and `ψ 1 = χ * step`. -/
def hsPsi (χ : Vec (n + 1) → ℝ) (j : Fin 2) : Vec (n + 1) → ℝ :=
  if j = 0 then fun y => χ y * (1 - hsStep y) else fun y => χ y * hsStep y

lemma hsPsi_zero (χ : Vec (n + 1) → ℝ) :
    hsPsi χ 0 = fun y => χ y * (1 - hsStep y) := by
  rw [hsPsi, if_pos rfl]

lemma hsPsi_one (χ : Vec (n + 1) → ℝ) : hsPsi χ 1 = fun y => χ y * hsStep y := by
  rw [hsPsi, if_neg (by decide : ¬ ((1 : Fin 2) = 0))]

lemma contDiff_hsPsi {χ : Vec (n + 1) → ℝ} (hχ : ContDiff ℝ ∞ χ) (j : Fin 2) :
    ContDiff ℝ ∞ (hsPsi χ j) := by
  fin_cases j
  · change ContDiff ℝ ∞ (hsPsi χ 0)
    rw [hsPsi_zero]
    exact hχ.mul (contDiff_const.sub contDiff_hsStep)
  · change ContDiff ℝ ∞ (hsPsi χ 1)
    rw [hsPsi_one]
    exact hχ.mul contDiff_hsStep

lemma hsPsi_sum (χ : Vec (n + 1) → ℝ) (y : Vec (n + 1)) :
    hsPsi χ 0 y + hsPsi χ 1 y = χ y := by
  simp only [hsPsi_zero, hsPsi_one]
  ring

lemma support_hsPsi_zero_subset (χ : Vec (n + 1) → ℝ) :
    support (hsPsi χ 0) ⊆ {y : Vec (n + 1) | y 0 < 1 / 2} := by
  intro y hy
  rw [Function.mem_support] at hy
  simp only [hsPsi_zero] at hy
  by_contra h
  have h1 : hsStep y = 1 := hsStep_one (le_of_not_gt h)
  rw [h1] at hy
  exact hy (by ring)

lemma tsupport_hsPsi_zero_subset_le (χ : Vec (n + 1) → ℝ) :
    tsupport (hsPsi χ 0) ⊆ {y : Vec (n + 1) | y 0 ≤ 1 / 2} :=
  closure_minimal
    (fun (y : Vec (n + 1)) hy => le_of_lt (show y 0 < 1 / 2 from support_hsPsi_zero_subset χ hy))
    (isClosed_le (continuous_apply (0 : Fin (n + 1))) continuous_const)

lemma tsupport_hsPsi_zero_subset (χ : Vec (n + 1) → ℝ) :
    tsupport (hsPsi χ 0) ⊆ {y : Vec (n + 1) | y 0 < 1} :=
  fun _ hy => lt_of_le_of_lt (tsupport_hsPsi_zero_subset_le χ hy) (show (1 : ℝ) / 2 < 1 by norm_num)

lemma support_hsPsi_one_subset (χ : Vec (n + 1) → ℝ) :
    support (hsPsi χ 1) ⊆ {y : Vec (n + 1) | (1 : ℝ) / 4 < y 0} := by
  intro y hy
  rw [Function.mem_support] at hy
  simp only [hsPsi_one] at hy
  by_contra h
  have h0 : hsStep y = 0 := hsStep_zero (le_of_not_gt h)
  rw [h0] at hy
  exact hy (by ring)

lemma tsupport_hsPsi_one_subset_ge (χ : Vec (n + 1) → ℝ) :
    tsupport (hsPsi χ 1) ⊆ {y : Vec (n + 1) | (1 : ℝ) / 4 ≤ y 0} :=
  closure_minimal
    (fun (y : Vec (n + 1)) hy => le_of_lt (show (1 : ℝ) / 4 < y 0 from support_hsPsi_one_subset χ hy))
    (isClosed_le continuous_const (continuous_apply (0 : Fin (n + 1))))

lemma tsupport_hsPsi_one_subset (χ : Vec (n + 1) → ℝ) :
    tsupport (hsPsi χ 1) ⊆ {y : Vec (n + 1) | 0 < y 0} :=
  fun _ hy => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) (tsupport_hsPsi_one_subset_ge χ hy)

lemma support_hsPsi_zero_subset_support (χ : Vec (n + 1) → ℝ) :
    support (hsPsi χ 0) ⊆ support χ := by
  intro y hy
  rw [Function.mem_support] at hy ⊢
  simp only [hsPsi_zero] at hy
  exact fun h0 => hy (by rw [h0, zero_mul])

lemma support_hsPsi_one_subset_support (χ : Vec (n + 1) → ℝ) :
    support (hsPsi χ 1) ⊆ support χ := by
  intro y hy
  rw [Function.mem_support] at hy ⊢
  simp only [hsPsi_one] at hy
  exact fun h0 => hy (by rw [h0, zero_mul])

lemma tsupport_hsPsi_zero_subset_tsupport (χ : Vec (n + 1) → ℝ) :
    tsupport (hsPsi χ 0) ⊆ tsupport χ :=
  closure_mono (support_hsPsi_zero_subset_support χ)

lemma tsupport_hsPsi_one_subset_tsupport (χ : Vec (n + 1) → ℝ) :
    tsupport (hsPsi χ 1) ⊆ tsupport χ :=
  closure_mono (support_hsPsi_one_subset_support χ)

lemma hasCompactSupport_hsPsi (χ : Vec (n + 1) → ℝ) (hχ : HasCompactSupport χ) (j : Fin 2) :
    HasCompactSupport (hsPsi χ j) := by
  fin_cases j
  · exact IsCompact.of_isClosed_subset hχ (isClosed_tsupport _)
      (tsupport_hsPsi_zero_subset_tsupport χ)
  · exact IsCompact.of_isClosed_subset hχ (isClosed_tsupport _)
      (tsupport_hsPsi_one_subset_tsupport χ)

/-! ## The unconditional weighted IBP on the half-space atlas -/

/-- **The fully unconditional weighted integration by parts on the partial half-space atlas.**
For `C²` data `f`, `u` and a `C²` compactly supported `v` whose topological support lies in the
base chart source `{y 0 < 1}`, the weighted IBP identity holds on the global Riemannian measure
of the genuinely partial atlas `halfSpaceAtlas` (identity on `{y 0 < 1}`, dilation by `2` on
`{0 < y 0}`). There are no remaining atlas, partition-of-unity or integrability hypotheses: the
partition of unity is constructed from a bump `χ` which exists by `exists_contDiff_bump`, the
chart identifications are the D12 dilation chart-independence lemmas, and the integrability of
the lifted pieces is `integrable_globalMeasure_withDensity_of_supported`. -/
theorem halfSpaceAtlas_weightedIBP_unconditional (G : ChartMetric (n + 1))
    (f u v : Vec (n + 1) → ℝ)
    (hf : ContDiff ℝ 2 f) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hvsupp : tsupport v ⊆ {y : Vec (n + 1) | y 0 < 1}) :
    ∫ m, G.driftLaplacian f u m * v m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight f))
      = -∫ m, G.gradInnerInverse u v m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight f)) := by
  classical
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec (n + 1))).mp hvc.isBounded
  have hU : IsOpen ({y : Vec (n + 1) | y 0 < 1} ∩ ball (0 : Vec (n + 1)) (R + 1)) :=
    (isOpen_lt (continuous_apply (0 : Fin (n + 1))) continuous_const).inter isOpen_ball
  have hKU : tsupport v ⊆ {y : Vec (n + 1) | y 0 < 1} ∩ ball (0 : Vec (n + 1)) (R + 1) :=
    fun y hy => ⟨hvsupp hy, closedBall_subset_ball (by linarith) (hR hy)⟩
  obtain ⟨χ, hχ_sm, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_contDiff_bump (K := tsupport v) (U :=
      {y : Vec (n + 1) | y 0 < 1} ∩ ball (0 : Vec (n + 1)) (R + 1)) hvc hU hKU
  have hχ_tsupp' : tsupport χ ⊆ {y : Vec (n + 1) | y 0 < 1} := fun y hy => (hχ_tsupp hy).1
  have hχ_cc : HasCompactSupport χ :=
    IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Vec (n + 1)) (R + 1))
      (isClosed_tsupport χ) (fun y hy => ball_subset_closedBall (hχ_tsupp hy).2)
  set A : SmoothOverlapAtlas (Vec (n + 1)) (n + 1) := hsAtlas (n := n) G with hA
  -- chart, metric, transition and source normal forms for `A`
  have hchart0 : A.chart 0 = fun y : Vec (n + 1) => (1 : ℝ) • y := hsChart_zero
  have hchart_ne : ∀ {i : ℕ}, i ≠ 0 → A.chart i = fun y : Vec (n + 1) => (2 : ℝ) • y :=
    fun hi => hsChart_ne hi
  have hmetric0 : A.metric 0 = G := hsMetric_zero G
  have hmetric_ne : ∀ {i : ℕ}, i ≠ 0 → A.metric i = dilateMetric G 2 (by norm_num) :=
    fun hi => hsMetric_ne hi G
  have htrans00 : A.transition 0 0 = fun y : Vec (n + 1) => y := dilationTransition_zero_zero 2
  have htrans : ∀ i j y, A.chart j y ∈ A.chart i '' A.source i →
      A.transition i j y ∈ A.source i :=
    halfSpaceAtlas_transition_coherence (n := n) G
  -- smoothness of the chart expressions
  have hfc : ∀ i : ℕ, ContDiff ℝ 2 fun y => f (A.chart i y) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      rw [hchart0]
      simpa [Function.comp_def] using hf.comp (contDiff_const_smul (1 : ℝ))
    · rw [hchart_ne hi]
      simpa [Function.comp_def] using hf.comp (contDiff_const_smul (2 : ℝ))
  have huc : ∀ i : ℕ, ContDiff ℝ 2 fun y => u (A.chart i y) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      rw [hchart0]
      simpa [Function.comp_def] using hu.comp (contDiff_const_smul (1 : ℝ))
    · rw [hchart_ne hi]
      simpa [Function.comp_def] using hu.comp (contDiff_const_smul (2 : ℝ))
  have hvc' : ∀ i : ℕ, ContDiff ℝ 2 fun y => v (A.chart i y) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      rw [hchart0]
      simpa [Function.comp_def] using hv.comp (contDiff_const_smul (1 : ℝ))
    · rw [hchart_ne hi]
      simpa [Function.comp_def] using hv.comp (contDiff_const_smul (2 : ℝ))
  -- the partition-of-unity facts
  have hψ_sm : ∀ j : Fin 2, ContDiff ℝ ∞ (hsPsi χ j) := fun j => contDiff_hsPsi hχ_sm j
  have hψ_supp : ∀ j : Fin 2,
      tsupport (hsPsi χ j) ⊆ overlapOf A.chart A.source ((j : ℕ)) 0 := by
    intro j
    fin_cases j
    · change tsupport (hsPsi χ 0) ⊆ overlapOf A.chart A.source 0 0
      rw [show overlapOf A.chart A.source 0 0 = halfSpaceSource0 (n := n)
        from overlapOf_hs_00]
      exact tsupport_hsPsi_zero_subset χ
    · change tsupport (hsPsi χ 1) ⊆ overlapOf A.chart A.source 1 0
      rw [show overlapOf A.chart A.source 1 0 =
          {y : Vec (n + 1) | 0 < y 0 ∧ y 0 < 1} from overlapOf_hs_i0 (by norm_num)]
      intro y hy
      exact ⟨tsupport_hsPsi_one_subset χ hy,
        hχ_tsupp' (tsupport_hsPsi_one_subset_tsupport χ hy)⟩
  have hψ_supp0 : ∀ j : Fin 2, tsupport (hsPsi χ j) ⊆ overlapOf A.chart A.source 0 0 := by
    intro j
    rw [show overlapOf A.chart A.source 0 0 = halfSpaceSource0 (n := n) from overlapOf_hs_00]
    fin_cases j
    · exact tsupport_hsPsi_zero_subset χ
    · exact (tsupport_hsPsi_one_subset_tsupport χ).trans hχ_tsupp'
  have hψ_sum : ∀ y, v (A.chart 0 y) ≠ 0 → ∑ j : Fin 2, hsPsi χ j y = 1 := by
    intro y hy
    have hy' : v y ≠ 0 := by simpa [hchart0] using hy
    rw [Fin.sum_univ_two, hsPsi_sum χ y,
      hχ_one y (subset_tsupport v (Function.mem_support.mpr hy'))]
  have hψ_cc : ∀ j : Fin 2, HasCompactSupport (hsPsi χ j) :=
    fun j => hasCompactSupport_hsPsi χ hχ_cc j
  -- the piece's own chart expression is compactly supported
  have hpiece_cc : ∀ j : Fin 2,
      HasCompactSupport fun y => A.pouPiece 0 v (hsPsi χ j) (A.chart ((j : ℕ)) y) := by
    intro j
    have hfun : (fun y => A.pouPiece 0 v (hsPsi χ j) (A.chart ((j : ℕ)) y))
        = fun y => hsPsi χ j (A.transition 0 ((j : ℕ)) y) * v (A.chart ((j : ℕ)) y) := by
      funext y
      exact A.pouPiece_chart_of_support htrans (hψ_supp j) y
    rw [hfun]
    refine IsCompact.of_isClosed_subset
      (halfSpaceAtlas_transition_preimage_isCompact (n := n) G 0 ((j : ℕ)) (hψ_cc j))
      (isClosed_tsupport _) ?_
    refine closure_minimal ?_ ((isClosed_tsupport (hsPsi χ j)).preimage
      (A.contDiff_transition 0 ((j : ℕ))).continuous)
    intro y hy
    rw [Function.mem_support] at hy
    exact subset_tsupport _ (Function.mem_support.mpr fun h0 => hy (by rw [h0, zero_mul]))
  -- the piece's own chart expression is supported in the chart's source
  have hpiece_src : ∀ j : Fin 2, ∀ y,
      A.pouPiece 0 v (hsPsi χ j) (A.chart ((j : ℕ)) y) ≠ 0 → y ∈ A.source ((j : ℕ)) := by
    intro j y hy
    rw [A.pouPiece_chart_of_support htrans (hψ_supp j) y] at hy
    have hsupp : A.transition 0 ((j : ℕ)) y ∈ Function.support (hsPsi χ j) :=
      fun h0 => hy (by rw [h0, zero_mul])
    have hmem := hψ_supp j (subset_tsupport _ hsupp)
    obtain ⟨z, hz, hzy⟩ := hmem.2
    rw [A.transition_chart_global 0 ((j : ℕ)) y] at hzy
    rw [← A.inj_chart ((j : ℕ)) hzy]
    exact hz
  -- the chart identifications of the two operators
  have hD : ∀ i y, y ∈ A.source i →
      G.driftLaplacian f u (A.chart i y)
        = (A.metric i).driftLaplacian (fun z => f (A.chart i z))
            (fun z => u (A.chart i z)) y := by
    intro i y _
    by_cases hi : i = 0
    · subst hi
      rw [hchart0, hmetric0]
      simp only [one_smul]
    · rw [hchart_ne hi, hmetric_ne hi]
      exact (dilateMetric_driftLaplacian G 2 (by norm_num) f u hf hu y).symm
  have hG : ∀ i y, y ∈ A.source i →
      G.gradInnerInverse u v (A.chart i y)
        = (A.metric i).gradInnerInverse (fun z => u (A.chart i z))
            (fun z => v (A.chart i z)) y := by
    intro i y _
    by_cases hi : i = 0
    · subst hi
      rw [hchart0, hmetric0]
      simp only [one_smul]
    · rw [hchart_ne hi, hmetric_ne hi]
      exact (dilateMetric_gradInnerInverse G 2 (by norm_num) u v
        (hu.differentiable (by simp)) (hv.differentiable (by simp)) y).symm
  -- support and compact-support facts for the test data
  have hvsupp' : ∀ m, v m ≠ 0 → m ∈ A.chart 0 '' A.source 0 := by
    intro m hm
    refine ⟨m, ?_, by simp [hchart0]⟩
    exact hvsupp (subset_tsupport v (Function.mem_support.mpr hm))
  have hGuvsupp : ∀ m, G.gradInnerInverse u v m ≠ 0 → m ∈ A.chart 0 '' A.source 0 := by
    intro m hm
    refine ⟨m, ?_, by simp [hchart0]⟩
    exact hvsupp (support_gradInnerInverse_subset G u v hm)
  have hvcc : HasCompactSupport fun y => v (A.chart 0 y) := by
    simpa [hchart0] using hvc
  -- integrability of the left-hand pieces
  have hintL : ∀ j : Fin 2, Integrable
      (fun m => G.driftLaplacian f u m * A.pouPiece 0 v (hsPsi χ j) m)
      ((A.globalMeasure volume).withDensity (A.weight f)) := by
    intro j
    refine A.integrable_globalMeasure_withDensity_of_supported volume 0
      hf.continuous.measurable ?_ ?_ ?_
    · exact (G.driftLaplacian_continuous f u hf hu).measurable.mul
        (A.measurable_pouPiece 0 hv.continuous.measurable (hψ_sm j))
    · intro m hm
      have hpiece : A.pouPiece 0 v (hsPsi χ j) m ≠ 0 := fun h0 => hm (by rw [h0, mul_zero])
      obtain ⟨y, hy, hyz⟩ := A.support_lift_subset (b := 0)
        (φ := fun y => hsPsi χ j y * v (A.chart 0 y)) hpiece
      have hyψ : y ∈ Function.support (hsPsi χ j) := fun h0 => hy (by simp [h0])
      exact ⟨y, (hψ_supp j (subset_tsupport _ hyψ)).1, hyz⟩
    · have hfun : (fun y => Real.exp (-(f (A.chart 0 y)))
            * (G.driftLaplacian f u (A.chart 0 y)
              * A.pouPiece 0 v (hsPsi χ j) (A.chart 0 y)) * A.density 0 y)
          = fun y => Real.exp (-(f y))
              * (G.driftLaplacian f u y * (hsPsi χ j y * v y)) * G.density y := by
        funext y
        rw [A.pouPiece_chart_of_support htrans (hψ_supp0 j) y]
        simp only [htrans00, hchart0, hmetric0, OverlapAtlas.density, one_smul]
      rw [hfun]
      have hcont : Continuous (fun y : Vec (n + 1) => Real.exp (-(f y))
          * (G.driftLaplacian f u y * (hsPsi χ j y * v y)) * G.density y) :=
        ((Real.continuous_exp.comp hf.continuous.neg).mul
          ((G.driftLaplacian_continuous f u hf hu).mul
            ((hψ_sm j).continuous.mul hv.continuous))).mul G.density_contDiff_one.continuous
      have hcc : HasCompactSupport (fun y : Vec (n + 1) => Real.exp (-(f y))
          * (G.driftLaplacian f u y * (hsPsi χ j y * v y)) * G.density y) := by
        refine IsCompact.of_isClosed_subset (hψ_cc j) (isClosed_tsupport _)
          (closure_minimal ?_ (isClosed_tsupport _))
        intro y hy
        rw [Function.mem_support] at hy
        by_contra hyt
        have hψv : hsPsi χ j y * v y = 0 := by
          by_contra h
          exact hyt (closure_mono (support_mul_subset_left (hsPsi χ j) v)
            (subset_tsupport (fun y => hsPsi χ j y * v y) (Function.mem_support.mpr h)))
        exact hy (by simp [hψv])
      exact hcont.integrable_of_hasCompactSupport hcc
  -- integrability of the right-hand lifted pairings
  have hintR : ∀ j : Fin 2, Integrable
      (fun m => A.pouPairing 0 ((j : ℕ)) u v (hsPsi χ j) m)
      ((A.globalMeasure volume).withDensity (A.weight f)) := by
    intro j
    refine A.integrable_globalMeasure_withDensity_of_supported volume ((j : ℕ))
      hf.continuous.measurable ?_ ?_ ?_
    · exact A.measurable_pouPairing 0 ((j : ℕ)) (huc (j : ℕ)) (hvc' (j : ℕ)) (hψ_sm j)
    · exact A.support_pouPairing_subset_chart 0 ((j : ℕ)) u v (hsPsi χ j)
    · let i : ℕ := (j : ℕ)
      let φ : Vec (n + 1) → ℝ := fun z => hsPsi χ j (A.transition 0 i z) * v (A.chart i z)
      have hφ_eq : ∀ z, A.pouPiece 0 v (hsPsi χ j) (A.chart i z) = φ z :=
        fun z => A.pouPiece_chart_of_support htrans (hψ_supp j) z
      have hφ_src : ∀ z, φ z ≠ 0 → z ∈ A.source i := fun z hz =>
        hpiece_src j z (by rw [hφ_eq z]; exact hz)
      have hle : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
      have hφ_cd : ContDiff ℝ 2 φ :=
        (((hψ_sm j).of_le hle).comp (A.contDiff_transition 0 i)).mul (hvc' i)
      have hφ_cc : HasCompactSupport φ := by
        have h := hpiece_cc j
        rwa [show (fun y => A.pouPiece 0 v (hsPsi χ j) (A.chart i y)) = φ from
          funext fun y => hφ_eq y] at h
      have hpair_cont : Continuous (fun y => (A.metric i).gradInnerInverse
          (fun z => u (A.chart i z)) φ y) :=
        (A.metric i).gradInnerInverse_continuous _ φ (huc i) hφ_cd
      have hpair_cc : HasCompactSupport (fun y => (A.metric i).gradInnerInverse
          (fun z => u (A.chart i z)) φ y) :=
        IsCompact.of_isClosed_subset hφ_cc (isClosed_tsupport _)
          (closure_minimal (support_gradInnerInverse_subset (A.metric i)
            (fun z => u (A.chart i z)) φ) (isClosed_tsupport _))
      have hbase : Integrable (fun y => Real.exp (-(f (A.chart i y)))
          * (A.metric i).gradInnerInverse (fun z => u (A.chart i z)) φ y
          * A.density i y) volume := by
        have hcont : Continuous (fun y => Real.exp (-(f (A.chart i y)))
            * (A.metric i).gradInnerInverse (fun z => u (A.chart i z)) φ y
            * A.density i y) :=
          ((Real.continuous_exp.comp (hfc i).continuous.neg).mul hpair_cont).mul
            (A.metric i).density_contDiff_one.continuous
        have hcc : HasCompactSupport (fun y => Real.exp (-(f (A.chart i y)))
            * (A.metric i).gradInnerInverse (fun z => u (A.chart i z)) φ y
            * A.density i y) := by
          refine IsCompact.of_isClosed_subset hpair_cc (isClosed_tsupport _)
            (closure_minimal ?_ (isClosed_tsupport _))
          intro y hy
          rw [Function.mem_support] at hy
          by_contra hyt
          have h0 : (A.metric i).gradInnerInverse (fun z => u (A.chart i z)) φ y = 0 :=
            Function.notMem_support.mp fun hmem => hyt (subset_tsupport _ hmem)
          exact hy (by simp [h0])
        exact hcont.integrable_of_hasCompactSupport hcc
      refine hbase.congr ?_
      filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
        (halfSpaceAtlas_frontier_volume_zero (n := n) G i)] with y hy
      by_cases hys : y ∈ A.source i
      · rw [A.pouPairing_apply_of_mem 0 i u v (hsPsi χ j) hys]
      · have hzero_pair : A.pouPairing 0 i u v (hsPsi χ j) (A.chart i y) = 0 := by
          by_contra hne
          obtain ⟨z, hz, hzy⟩ :=
            A.support_pouPairing_subset_chart 0 i u v (hsPsi χ j) (A.chart i y) hne
          exact hys (by rw [← A.inj_chart i hzy]; exact hz)
        have hcl : y ∉ closure (A.source i) := by
          intro hc
          exact hy (by rw [frontier_eq_closure_inter_closure]; exact ⟨hc, subset_closure hys⟩)
        have hφ0 : φ =ᶠ[𝓝 y] 0 := by
          filter_upwards [(isClosed_closure.isOpen_compl).mem_nhds hcl] with z hz
          by_contra hne
          exact hz (subset_closure (hφ_src z hne))
        have hzero_base : (A.metric i).gradInnerInverse (fun z => u (A.chart i z)) φ y = 0 :=
          A.gradInnerInverse_eq_zero_of_eventuallyEq_zero (u := fun z => u (A.chart i z))
            (φ := φ) hφ0
        rw [hzero_pair, hzero_base]
  refine SmoothOverlapAtlas.globalWeightedIBP_of_pou_partial_ae (A := A) htrans 0
    (fun j : Fin 2 => (j : ℕ)) (hsPsi χ) f u v (G.driftLaplacian f u) (G.gradInnerInverse u v)
    hf.continuous.measurable hv.continuous.measurable
    (G.driftLaplacian_continuous f u hf hu).measurable
    (G.gradInnerInverse_continuous u v hu hv).measurable
    hψ_sm hψ_supp hψ_sum hvsupp' hfc huc hvc' hvcc hD hG hGuvsupp hψ_cc
    (fun i j K hK => halfSpaceAtlas_transition_preimage_isCompact (n := n) G i j hK)
    (halfSpaceAtlas_frontier_volume_zero (n := n) G) hintL hintR

/-- **The Dirichlet energy identity on the partial half-space atlas** (the consumed
consequence of the unconditional IBP with `u = v`): `∫ (Δ_F V) · V = -∫ |∇V|²_{G⁻¹}` on the
global Riemannian measure of `halfSpaceAtlas`. -/
theorem halfSpaceAtlas_dirichletEnergy (G : ChartMetric (n + 1)) (F V : Vec (n + 1) → ℝ)
    (hF : ContDiff ℝ 2 F) (hV : ContDiff ℝ 2 V) (hVc : HasCompactSupport V)
    (hVsupp : tsupport V ⊆ {y : Vec (n + 1) | y 0 < 1}) :
    ∫ m, G.driftLaplacian F V m * V m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight F))
      = -∫ m, G.gradInnerInverse V V m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight F)) :=
  halfSpaceAtlas_weightedIBP_unconditional (n := n) G F V V hF hV hV hVc hVsupp

/-- **The Green identity on the partial half-space atlas**: the weighted IBP applied twice
exchanges `Δ_F U` and `Δ_F V` (`⟨∇U,∇V⟩` is symmetric). Both sides are integrals of *integrable*
functions by `halfSpaceAtlas_integrable_dirichlet`, so the identity is not vacuous. -/
theorem halfSpaceAtlas_greenIdentity (G : ChartMetric (n + 1)) (F U V : Vec (n + 1) → ℝ)
    (hF : ContDiff ℝ 2 F) (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V)
    (hUc : HasCompactSupport U) (hVc : HasCompactSupport V)
    (hUsupp : tsupport U ⊆ {y : Vec (n + 1) | y 0 < 1})
    (hVsupp : tsupport V ⊆ {y : Vec (n + 1) | y 0 < 1}) :
    ∫ m, G.driftLaplacian F U m * V m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight F))
      = ∫ m, U m * G.driftLaplacian F V m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight F)) := by
  have h1 := halfSpaceAtlas_weightedIBP_unconditional (n := n) G F U V hF hU hV hVc hVsupp
  have h2 := halfSpaceAtlas_weightedIBP_unconditional (n := n) G F V U hF hV hU hUc hUsupp
  rw [h1, show (∫ m, U m * G.driftLaplacian F V m
      ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity
        ((hsAtlas (n := n) G).weight F)))
      = ∫ m, G.driftLaplacian F V m * U m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight F)) from
    integral_congr_ae (ae_of_all _ fun m => mul_comm _ _), h2]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun m => ChartMetric.gradInnerInverse_comm G U V m)

/-- **Non-vacuity of the Dirichlet energy identity**: both integrands are integrable for the
weighted global measure of the partial atlas (their chart expressions are continuous with
compact support, and `integrable_globalMeasure_withDensity_of_supported` transfers this to the
glued measure). -/
theorem halfSpaceAtlas_integrable_dirichlet (G : ChartMetric (n + 1)) (F V : Vec (n + 1) → ℝ)
    (hF : ContDiff ℝ 2 F) (hV : ContDiff ℝ 2 V) (hVc : HasCompactSupport V)
    (hVsupp : tsupport V ⊆ {y : Vec (n + 1) | y 0 < 1}) :
    Integrable (fun m => G.driftLaplacian F V m * V m)
        (((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight F)) ∧
      Integrable (fun m => G.gradInnerInverse V V m)
        (((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight F)) := by
  have hchart0' : (hsAtlas (n := n) G).chart 0 = fun y : Vec (n + 1) => (1 : ℝ) • y :=
    hsChart_zero
  have hdensity0 : (hsAtlas (n := n) G).density 0 = G.density := rfl
  have hle : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  have hVsupp' : ∀ m, V m ≠ 0 → m ∈ (hsAtlas (n := n) G).chart 0 '' (hsAtlas (n := n) G).source 0 := by
    intro m hm
    exact ⟨m, hVsupp (subset_tsupport V (Function.mem_support.mpr hm)),
      by show (1 : ℝ) • m = m; simp⟩
  have hsuppA : ∀ m, G.driftLaplacian F V m * V m ≠ 0 →
      m ∈ (hsAtlas (n := n) G).chart 0 '' (hsAtlas (n := n) G).source 0 :=
    fun m hm => hVsupp' m fun h0 => hm (by rw [h0, mul_zero])
  have hGuvsupp : ∀ m, G.gradInnerInverse V V m ≠ 0 →
      m ∈ (hsAtlas (n := n) G).chart 0 '' (hsAtlas (n := n) G).source 0 := by
    intro m hm
    exact ⟨m, hVsupp (support_gradInnerInverse_subset G V V hm),
      by show (1 : ℝ) • m = m; simp⟩
  constructor
  · refine (hsAtlas (n := n) G).integrable_globalMeasure_withDensity_of_supported volume 0
      hF.continuous.measurable ?_ hsuppA ?_
    · exact (G.driftLaplacian_continuous F V hF hV).measurable.mul hV.continuous.measurable
    · have hcont : Continuous (fun y : Vec (n + 1) => Real.exp (-(F y))
          * (G.driftLaplacian F V y * V y) * G.density y) :=
        ((Real.continuous_exp.comp hF.continuous.neg).mul
          ((G.driftLaplacian_continuous F V hF hV).mul hV.continuous)).mul
            G.density_contDiff_one.continuous
      have hcc : HasCompactSupport (fun y : Vec (n + 1) => Real.exp (-(F y))
          * (G.driftLaplacian F V y * V y) * G.density y) := by
        refine IsCompact.of_isClosed_subset hVc (isClosed_tsupport _)
          (closure_minimal ?_ (isClosed_tsupport _))
        intro y hy
        rw [Function.mem_support] at hy
        by_contra hyt
        have hV0 : V y = 0 := Function.notMem_support.mp fun hmem => hyt (subset_tsupport _ hmem)
        exact hy (by simp [hV0])
      rw [hchart0', hdensity0]
      simp only [one_smul]
      exact hcont.integrable_of_hasCompactSupport hcc
  · refine (hsAtlas (n := n) G).integrable_globalMeasure_withDensity_of_supported volume 0
      hF.continuous.measurable ?_ hGuvsupp ?_
    · exact (G.gradInnerInverse_continuous V V hV hV).measurable
    · have hcont : Continuous (fun y : Vec (n + 1) => Real.exp (-(F y))
          * G.gradInnerInverse V V y * G.density y) :=
        ((Real.continuous_exp.comp hF.continuous.neg).mul
          (G.gradInnerInverse_continuous V V hV hV)).mul G.density_contDiff_one.continuous
      have hcc : HasCompactSupport (fun y : Vec (n + 1) => Real.exp (-(F y))
          * G.gradInnerInverse V V y * G.density y) := by
        have hpair : HasCompactSupport (fun y : Vec (n + 1) => G.gradInnerInverse V V y) :=
          IsCompact.of_isClosed_subset hVc (isClosed_tsupport _)
            (closure_minimal (support_gradInnerInverse_subset G V V) (isClosed_tsupport _))
        refine IsCompact.of_isClosed_subset hpair (isClosed_tsupport _)
          (closure_minimal ?_ (isClosed_tsupport _))
        intro y hy
        rw [Function.mem_support] at hy
        by_contra hyt
        have h0 : G.gradInnerInverse V V y = 0 := Function.notMem_support.mp fun hmem =>
          hyt (subset_tsupport _ hmem)
        exact hy (by simp [h0])
      rw [hchart0', hdensity0]
      simp only [one_smul]
      exact hcont.integrable_of_hasCompactSupport hcc

/-- **The Laplacian is supported in the topological support of its argument.** This is the
(support-level) locality of `Δ_g = ρ⁻¹ ∑ᵢ ∂ᵢ(ρ · (grad u)ᵢ)`: off the closed set
`tsupport u` the function `u` vanishes on an open neighbourhood, hence so do all its first
partial derivatives, the gradient, the weighted divergence and the Laplacian. -/
theorem support_laplacian_subset (G : ChartMetric (n + 1)) (u : Vec (n + 1) → ℝ) :
    Function.support (fun x => G.laplacian u x) ⊆ tsupport u := by
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxt
  have hV : (tsupport u)ᶜ ∈ 𝓝 x := (isClosed_tsupport u).isOpen_compl.mem_nhds hxt
  obtain ⟨V, hVsub, hVo, hxV⟩ := _root_.mem_nhds_iff.mp hV
  have huV : ∀ y ∈ V, u y = 0 := fun y hy =>
    Function.notMem_support.mp fun hys => hVsub hy (subset_tsupport u hys)
  have hpd : ∀ y ∈ V, ∀ j, ChartMetric.partialDeriv j u y = 0 := by
    intro y hy j
    have h0 : u =ᶠ[𝓝 y] 0 :=
      Filter.eventually_of_mem (hVo.mem_nhds hy) fun z hz => huV z hz
    rw [ChartMetric.partialDeriv, h0.fderiv_eq]
    simp
  have hgrad : ∀ y ∈ V, G.grad u y = 0 := by
    intro y hy
    funext i
    simp only [ChartMetric.grad]
    exact Finset.sum_eq_zero fun j _ => by rw [hpd y hy j, mul_zero]
  have hterm : ∀ y ∈ V, ∀ i,
      fderiv ℝ (fun z => G.density z * G.grad u z i) y (Pi.single i 1) = 0 := by
    intro y hy i
    have h0 : (fun z => G.density z * G.grad u z i) =ᶠ[𝓝 y] 0 := by
      filter_upwards [hVo.mem_nhds hy] with z hz
      simp [hgrad z hz]
    rw [h0.fderiv_eq]
    simp
  have hwd : ∀ y ∈ V, ChartMetric.weightedDivergence G.density (G.grad u) y = 0 := by
    intro y hy
    simp only [ChartMetric.weightedDivergence]
    exact Finset.sum_eq_zero fun i _ => hterm y hy i
  have hdiv : ∀ y ∈ V, G.divergence (G.grad u) y = 0 := by
    intro y hy
    simp only [ChartMetric.divergence, hwd y hy, zero_div]
  have hlap : ∀ y ∈ V, G.laplacian u y = 0 := fun y hy => by
    simp only [ChartMetric.laplacian, hdiv y hy]
  exact hx (hlap x hxV)

/-- **The divergence theorem on the partial half-space atlas**: `∫_M Δ_g V dμ_g = 0` for `C² V`
with topological support in the base chart source. The manifold integral is transferred to the
base chart (`integral_globalMeasure_of_supported` + `integral_chartMeasure_of_supported`), the
chart support reduction uses `support_laplacian_subset`, and the chart identity is D12's
`laplacian_integral_eq_zero`. -/
theorem halfSpaceAtlas_laplacianIntegralZero (G : ChartMetric (n + 1)) (V : Vec (n + 1) → ℝ)
    (hV : ContDiff ℝ 2 V) (hVc : HasCompactSupport V)
    (hVsupp : tsupport V ⊆ {y : Vec (n + 1) | y 0 < 1}) :
    ∫ m, G.laplacian V m ∂((hsAtlas (n := n) G).globalMeasure volume) = 0 := by
  have hsupp : ∀ m, G.laplacian V m ≠ 0 →
      m ∈ (hsAtlas (n := n) G).chart 0 '' (hsAtlas (n := n) G).source 0 := by
    intro m hm
    refine ⟨m, ?_, ?_⟩
    · exact hVsupp (support_laplacian_subset G V hm)
    · show (1 : ℝ) • m = m
      simp
  rw [(hsAtlas (n := n) G).integral_globalMeasure_of_supported volume 0 hsupp]
  rw [(hsAtlas (n := n) G).integral_chartMeasure_of_supported volume 0
    (G.laplacian_continuous V hV).measurable.aestronglyMeasurable hsupp]
  have hfun : (fun y : Vec (n + 1) => G.laplacian V ((hsAtlas (n := n) G).chart 0 y)
        * (hsAtlas (n := n) G).density 0 y)
      = fun y : Vec (n + 1) => G.laplacian V y * G.density y := by
    funext y
    rw [show (hsAtlas (n := n) G).chart 0 = fun y : Vec (n + 1) => (1 : ℝ) • y from hsChart_zero,
      show (hsAtlas (n := n) G).density 0 = G.density from rfl]
    simp
  rw [hfun]
  have hsrc : (hsAtlas (n := n) G).source 0 = {y : Vec (n + 1) | y 0 < 1} := hsSource_zero
  rw [show (fun y : Vec (n + 1) => G.laplacian V y * G.density y)
      = fun y : Vec (n + 1) => G.laplacian V y * G.density y from rfl]
  rw [setIntegral_eq_integral_of_support (s := (hsAtlas (n := n) G).source 0)
    ((isOpen_halfSpaceSource0 (n := n)).measurableSet) ?_ volume]
  · exact G.laplacian_integral_eq_zero V hV hVc
  · intro y hy
    rw [hsrc]
    by_contra hys
    exact hy (by
      have h0 : G.laplacian V y = 0 := Function.notMem_support.mp fun hmem =>
        hys (hVsupp (support_laplacian_subset G V hmem))
      rw [h0, zero_mul])

end OverlapAtlas

end Poincare.D13.ManifoldIBP

/-! ## Axiom audit -/

#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.hsStep
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.hsPsi
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_dirichletEnergy
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_greenIdentity
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_integrable_dirichlet
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.support_laplacian_subset
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_laplacianIntegralZero
