/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license that can be found in the LICENSE file.
Authors: D13-manifold-ibp-volume-form track (constructed partition of unity for the atlas IBP)

# Constructed partition of unity and integrability for the global atlas IBP

`ManifoldIBP.SmoothAtlasPartialAE` proves the global weighted IBP for partial charts with
null-boundary sources, taking the partition-of-unity data (smoothness, supports inside the
overlaps, sum one on the support region, compact support) and the integrability of the
constructed pieces as explicit hypotheses. This module **constructs both** from topological
data:

* the Euclidean partition-of-unity theorem `exists_smooth_partitionOfUnity_subordinate` is
  applied to the finite open cover of `tsupport (v ∘ chart b)` by the (open) base-chart
  overlaps `overlapOf chart source (chartOf j) b`, intersected with a large ball so that the
  partition functions are compactly supported;
* the chart expressions of the lifted pieces and pairings are continuous with compact support
  (the transition preimage of the compact POU support is compact by properness), so
  `integrable_globalMeasure_withDensity_of_supported` transfers integrability to the glued
  weighted measure.

The resulting theorem `SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae` has no
partition-of-unity or integrability hypotheses left: beyond the atlas structure (coherence,
proper transitions, null source boundaries) it assumes only a finite chart cover of the base
chart image, the test data, the operator identifications `hD`/`hG`, and the topological support
of `v ∘ chart b` inside the base chart source.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.SmoothAtlasPartialAE
import Poincare.D13.ManifoldIBP.IntegrableTransfer
import Poincare.D13.ManifoldIBP.SmoothPartition
import Poincare.D13.ManifoldIBP.PartialChartModel
import Poincare.D13.ManifoldIBP.OverlapOperatorCheck

open scoped BigOperators ENNReal NNReal Topology Matrix Function ContDiff
open MeasureTheory Set Filter Metric Function

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

variable {M : Type*} [MeasurableSpace M] {n : ℕ}

namespace SmoothOverlapAtlas

variable {A : SmoothOverlapAtlas M (n + 1)}

/-- **The global weighted IBP for partial charts with constructed partition of unity.** Beyond
the structural atlas hypotheses of `globalWeightedIBP_of_pou_partial_ae` (coherence `htrans`,
proper transitions `hproper`, null-boundary sources `hbd`), the only new geometric input is a
finite chart cover of the base chart image (`hcover`). The partition of unity subordinate to
the base-chart overlaps is constructed by the Euclidean theorem
`exists_smooth_partitionOfUnity_subordinate` (cut down by a large ball so that its pieces are
compactly supported), and the integrability of the lifted pieces and pairings is derived from
`integrable_globalMeasure_withDensity_of_supported`. -/
theorem globalWeightedIBP_of_cover_partial_ae
    (htrans : ∀ i j y, A.chart j y ∈ A.chart i '' A.source i → A.transition i j y ∈ A.source i)
    (b : ℕ) {ι : Type*} [Fintype ι] (chartOf : ι → ℕ)
    (f u v Du Guv : M → ℝ)
    (hf : Measurable f) (hv : Measurable v) (hDu : Measurable Du) (hGuv : Measurable Guv)
    (hvsupp : ∀ m, v m ≠ 0 → m ∈ A.chart b '' A.source b)
    (hfc : ∀ i, ContDiff ℝ 2 fun y => f (A.chart i y))
    (huc : ∀ i, ContDiff ℝ 2 fun y => u (A.chart i y))
    (hvc : ∀ i, ContDiff ℝ 2 fun y => v (A.chart i y))
    (hvcc : HasCompactSupport fun y => v (A.chart b y))
    (htsupp_b : tsupport (fun y => v (A.chart b y)) ⊆ A.source b)
    (hcover : A.chart b '' A.source b ⊆ ⋃ j, A.chart (chartOf j) '' A.source (chartOf j))
    (hD : ∀ i y, y ∈ A.source i →
      Du (A.chart i y) = (A.metric i).driftLaplacian
        (fun z => f (A.chart i z)) (fun z => u (A.chart i z)) y)
    (hG : ∀ i y, y ∈ A.source i →
      Guv (A.chart i y) = (A.metric i).gradInnerInverse
        (fun z => u (A.chart i z)) (fun z => v (A.chart i z)) y)
    (hGuvsupp : ∀ m, Guv m ≠ 0 → m ∈ A.chart b '' A.source b)
    (hproper : ∀ i j, ∀ K : Set (Vec (n + 1)), IsCompact K →
      IsCompact (A.transition i j ⁻¹' K))
    (hbd : ∀ i, volume (frontier (A.source i)) = 0) :
    ∫ m, Du m * v m ∂((A.globalMeasure volume).withDensity (A.weight f))
      = -∫ m, Guv m ∂((A.globalMeasure volume).withDensity (A.weight f)) := by
  classical
  have hle : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  -- a ball containing the compact support of `v ∘ chart b`
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec (n + 1))).mp hvcc.isBounded
  -- the open cover of the support by the base-chart overlaps, cut down by a ball
  set W : ι → Set (Vec (n + 1)) :=
    fun j => overlapOf A.chart A.source (chartOf j) b ∩ ball (0 : Vec (n + 1)) (R + 1) with hW
  have hWo : ∀ j, IsOpen (W j) := fun j =>
    (A.isOpen_overlap (chartOf j) b).inter isOpen_ball
  have hKW : tsupport (fun y => v (A.chart b y)) ⊆ ⋃ j, W j := by
    intro y hy
    have hys : y ∈ A.source b := htsupp_b hy
    have hball : y ∈ ball (0 : Vec (n + 1)) (R + 1) :=
      closedBall_subset_ball (by linarith) (hR hy)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover ⟨y, hys, rfl⟩)
    exact mem_iUnion.mpr ⟨j, ⟨⟨hys, hj⟩, hball⟩⟩
  obtain ⟨ψ, hψ_sm, _hψ_nn, hψ_supp, hψ_sum⟩ :=
    exists_smooth_partitionOfUnity_subordinate W hWo hvcc hKW
  have hψ_supp' : ∀ j, tsupport (ψ j) ⊆ overlapOf A.chart A.source (chartOf j) b :=
    fun j => (hψ_supp j).trans inter_subset_left
  have hψ_cc : ∀ j, HasCompactSupport (ψ j) := fun j =>
    IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Vec (n + 1)) (R + 1))
      (isClosed_tsupport _) fun y hy => ball_subset_closedBall (hψ_supp j hy).2
  have hψ_sum' : ∀ y, v (A.chart b y) ≠ 0 → ∑ j, ψ j y = 1 := fun y hy =>
    hψ_sum y (subset_tsupport _ (Function.mem_support.mpr hy))
  -- the lifted pieces and pairings are measurable
  have hpiece_meas : ∀ j, Measurable (A.pouPiece b v (ψ j)) := fun j =>
    A.measurable_pouPiece b hv (hψ_sm j)
  have hpair_meas : ∀ j, Measurable (A.pouPairing b (chartOf j) u v (ψ j)) := fun j =>
    A.measurable_pouPairing b (chartOf j) (huc (chartOf j)) (hvc (chartOf j)) (hψ_sm j)
  -- integrability of the left-hand pieces: construct the chart expression and transfer
  have hintL : ∀ j, Integrable (fun m => Du m * A.pouPiece b v (ψ j) m)
      ((A.globalMeasure volume).withDensity (A.weight f)) := by
    intro j
    refine A.integrable_globalMeasure_withDensity_of_supported volume b hf
      (hDu.mul (hpiece_meas j)) ?_ ?_
    · intro m hm
      have hpiece : A.pouPiece b v (ψ j) m ≠ 0 := fun h0 => hm (by rw [h0, mul_zero])
      obtain ⟨y, hy, hyz⟩ := A.support_lift_subset (b := b)
        (φ := fun y => ψ j y * v (A.chart b y)) hpiece
      have hyψ : y ∈ Function.support (ψ j) := fun h0 => hy (by simp [h0])
      exact ⟨y, (hψ_supp' j (subset_tsupport _ hyψ)).1, hyz⟩
    · -- the base-chart expression is `Φ * 1_{source b}` for a continuous compactly supported `Φ`
      let Φ : Vec (n + 1) → ℝ := fun y => Real.exp (-(f (A.chart b y)))
        * ((A.metric b).driftLaplacian (fun z => f (A.chart b z))
            (fun z => u (A.chart b z)) y * (ψ j y * v (A.chart b y))) * A.density b y
      have hΦ_cont : Continuous Φ :=
        ((Real.continuous_exp.comp (hfc b).continuous.neg).mul
          (((A.metric b).driftLaplacian_continuous _ _ (hfc b) (huc b)).mul
            ((hψ_sm j).continuous.mul (hvc b).continuous))).mul
              (A.metric b).density_contDiff_one.continuous
      have hΦ_cc : HasCompactSupport Φ := by
        refine IsCompact.of_isClosed_subset (hψ_cc j) (isClosed_tsupport _)
          (closure_minimal ?_ (isClosed_tsupport _))
        intro y hy
        rw [Function.mem_support] at hy
        by_contra hyt
        have hψ0 : ψ j y = 0 := by
          by_contra h
          exact hyt (subset_tsupport _ (Function.mem_support.mpr h))
        exact hy (by simp [Φ, hψ0])
      have hΦ_int : Integrable Φ volume := hΦ_cont.integrable_of_hasCompactSupport hΦ_cc
      have hpt : ∀ y : Vec (n + 1), Real.exp (-(f (A.chart b y)))
            * (Du (A.chart b y) * A.pouPiece b v (ψ j) (A.chart b y)) * A.density b y
          = Φ y * (A.source b).indicator (fun _ => 1) y := by
        intro y
        by_cases hy : y ∈ A.source b
        · rw [A.pouPiece_apply_of_mem b v (ψ j) hy, hD b y hy, Set.indicator_of_mem hy, mul_one]
        · have hmem : A.chart b y ∉ A.chart b '' A.source b := by
            intro hmem
            obtain ⟨z, hz, hzy⟩ := hmem
            exact hy (by rw [← A.inj_chart b hzy]; exact hz)
          have h0 : A.pouPiece b v (ψ j) (A.chart b y) = 0 := by
            simp [pouPiece, lift, hmem]
          simp [h0, Set.indicator_of_notMem hy]
      rw [funext hpt]
      refine hΦ_int.mono ?_ ?_
      · exact hΦ_cont.measurable.aestronglyMeasurable.mul
          (measurable_const.indicator (A.isOpen_source b).measurableSet).aestronglyMeasurable
      · filter_upwards with y
        by_cases hy : y ∈ A.source b
        · simp [Set.indicator_of_mem hy]
        · simp [Set.indicator_of_notMem hy]
  -- integrability of the right-hand lifted pairings
  have hintR : ∀ j, Integrable (fun m => A.pouPairing b (chartOf j) u v (ψ j) m)
      ((A.globalMeasure volume).withDensity (A.weight f)) := by
    intro j
    refine A.integrable_globalMeasure_withDensity_of_supported volume (chartOf j) hf
      (hpair_meas j) (A.support_pouPairing_subset_chart b (chartOf j) u v (ψ j)) ?_
    -- the pairing's chart expression is `Ψ * 1_{source i}`
    let Ψ : Vec (n + 1) → ℝ := fun y => Real.exp (-(f (A.chart (chartOf j) y)))
      * (A.metric (chartOf j)).gradInnerInverse (fun z => u (A.chart (chartOf j) z))
          (fun z => ψ j (A.transition b (chartOf j) z) * v (A.chart (chartOf j) z)) y
      * A.density (chartOf j) y
    have hφ_cont : Continuous (fun z => ψ j (A.transition b (chartOf j) z)
        * v (A.chart (chartOf j) z)) :=
      (((hψ_sm j).of_le hle).comp (A.contDiff_transition b (chartOf j))).continuous.mul
        (hvc (chartOf j)).continuous
    have hφ_cc : HasCompactSupport (fun z => ψ j (A.transition b (chartOf j) z)
        * v (A.chart (chartOf j) z)) := by
      refine IsCompact.of_isClosed_subset
        (hproper b (chartOf j) (tsupport (ψ j)) (hψ_cc j)) (isClosed_tsupport _) ?_
      refine closure_minimal ?_ ((isClosed_tsupport (ψ j)).preimage
        (A.contDiff_transition b (chartOf j)).continuous)
      intro z hz
      rw [Function.mem_support] at hz
      exact subset_tsupport _ (Function.mem_support.mpr fun h0 => hz (by rw [h0, zero_mul]))
    have hpair_cc : HasCompactSupport (fun y => (A.metric (chartOf j)).gradInnerInverse
        (fun z => u (A.chart (chartOf j) z))
        (fun z => ψ j (A.transition b (chartOf j) z) * v (A.chart (chartOf j) z)) y) :=
      IsCompact.of_isClosed_subset hφ_cc (isClosed_tsupport _)
        (closure_minimal (support_gradInnerInverse_subset (A.metric (chartOf j))
          (fun z => u (A.chart (chartOf j) z))
          (fun z => ψ j (A.transition b (chartOf j) z) * v (A.chart (chartOf j) z)))
          (isClosed_tsupport _))
    have hΨ_cont : Continuous Ψ :=
      ((Real.continuous_exp.comp (hfc (chartOf j)).continuous.neg).mul
        ((A.metric (chartOf j)).gradInnerInverse_continuous _ _
          (huc (chartOf j)) (((hψ_sm j).of_le hle).comp
            (A.contDiff_transition b (chartOf j)) |>.mul (hvc (chartOf j))))).mul
        (A.metric (chartOf j)).density_contDiff_one.continuous
    have hΨ_cc : HasCompactSupport Ψ := by
      refine IsCompact.of_isClosed_subset hpair_cc (isClosed_tsupport _)
        (closure_minimal ?_ (isClosed_tsupport _))
      intro y hy
      rw [Function.mem_support] at hy
      by_contra hyt
      have h0 : (A.metric (chartOf j)).gradInnerInverse (fun z => u (A.chart (chartOf j) z))
          (fun z => ψ j (A.transition b (chartOf j) z) * v (A.chart (chartOf j) z)) y = 0 :=
        Function.notMem_support.mp fun hmem => hyt (subset_tsupport _ hmem)
      exact hy (by simp [Ψ, h0])
    have hΨ_int : Integrable Ψ volume := hΨ_cont.integrable_of_hasCompactSupport hΨ_cc
    have hpt : ∀ y : Vec (n + 1), Real.exp (-(f (A.chart (chartOf j) y)))
          * A.pouPairing b (chartOf j) u v (ψ j) (A.chart (chartOf j) y)
          * A.density (chartOf j) y
        = Ψ y * (A.source (chartOf j)).indicator (fun _ => 1) y := by
      intro y
      by_cases hy : y ∈ A.source (chartOf j)
      · rw [A.pouPairing_apply_of_mem b (chartOf j) u v (ψ j) hy,
          Set.indicator_of_mem hy, mul_one]
      · have h0 : A.pouPairing b (chartOf j) u v (ψ j) (A.chart (chartOf j) y) = 0 := by
          by_contra hne
          obtain ⟨z, hz, hzy⟩ :=
            A.support_pouPairing_subset_chart b (chartOf j) u v (ψ j) (A.chart (chartOf j) y) hne
          exact hy (by rw [← A.inj_chart (chartOf j) hzy]; exact hz)
        simp [h0, Set.indicator_of_notMem hy]
    rw [funext hpt]
    refine hΨ_int.mono ?_ ?_
    · exact hΨ_cont.measurable.aestronglyMeasurable.mul
        (measurable_const.indicator (A.isOpen_source (chartOf j)).measurableSet).aestronglyMeasurable
    · filter_upwards with y
      by_cases hy : y ∈ A.source (chartOf j)
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy]
  exact A.globalWeightedIBP_of_pou_partial_ae htrans b chartOf ψ f u v Du Guv hf hv hDu hGuv
    hψ_sm hψ_supp' hψ_sum' hvsupp hfc huc hvc hvcc hD hG hGuvsupp hψ_cc hproper hbd hintL hintR

end SmoothOverlapAtlas

/-! ## The half-space model consumes the constructed-POU theorem -/

namespace OverlapAtlas

/-- **The general cover theorem applied to the half-space model** (base chart `0`, the two-chart
cover). This is a second, independent route to `halfSpaceAtlas_weightedIBP_unconditional`: the
partition of unity and the integrability are produced by `globalWeightedIBP_of_cover_partial_ae`
from the finite cover, rather than supplied by the explicit `hsPsi` construction. -/
theorem halfSpaceAtlas_weightedIBP_of_cover (G : ChartMetric (n + 1))
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
  set A : SmoothOverlapAtlas (Vec (n + 1)) (n + 1) := hsAtlas (n := n) G with hA
  have hchart0 : A.chart 0 = fun y : Vec (n + 1) => (1 : ℝ) • y := hsChart_zero
  have hchart_ne : ∀ {i : ℕ}, i ≠ 0 → A.chart i = fun y : Vec (n + 1) => (2 : ℝ) • y :=
    fun hi => hsChart_ne hi
  have hmetric0 : A.metric 0 = G := hsMetric_zero G
  have hmetric_ne : ∀ {i : ℕ}, i ≠ 0 → A.metric i = dilateMetric G 2 (by norm_num) :=
    fun hi => hsMetric_ne hi G
  have hsource0 : A.source 0 = halfSpaceSource0 (n := n) := hsSource_zero
  have htrans : ∀ i j y, A.chart j y ∈ A.chart i '' A.source i →
      A.transition i j y ∈ A.source i :=
    halfSpaceAtlas_transition_coherence (n := n) G
  have hchart0_fun : (fun y : Vec (n + 1) => v (A.chart 0 y)) = v := by
    funext y
    rw [hchart0]
    simp
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
  have hvsupp' : ∀ m, v m ≠ 0 → m ∈ A.chart 0 '' A.source 0 := by
    intro m hm
    refine ⟨m, ?_, ?_⟩
    · rw [hsource0]
      exact hvsupp (subset_tsupport v (Function.mem_support.mpr hm))
    · rw [hchart0]
      simp
  have hGuvsupp : ∀ m, G.gradInnerInverse u v m ≠ 0 → m ∈ A.chart 0 '' A.source 0 := by
    intro m hm
    refine ⟨m, ?_, ?_⟩
    · rw [hsource0]
      exact hvsupp (support_gradInnerInverse_subset G u v hm)
    · rw [hchart0]
      simp
  have hvcc : HasCompactSupport fun y => v (A.chart 0 y) := by
    rwa [hchart0_fun]
  have htsupp : tsupport (fun y => v (A.chart 0 y)) ⊆ A.source 0 := by
    rw [hchart0_fun, hsource0]
    exact hvsupp
  have hcover : A.chart 0 '' A.source 0 ⊆ ⋃ j : Fin 2, A.chart ((j : ℕ)) '' A.source ((j : ℕ)) :=
    fun y hy => mem_iUnion.mpr ⟨0, hy⟩
  exact A.globalWeightedIBP_of_cover_partial_ae htrans 0 (fun j : Fin 2 => (j : ℕ)) f u v
    (G.driftLaplacian f u) (G.gradInnerInverse u v)
    hf.continuous.measurable hv.continuous.measurable
    (G.driftLaplacian_continuous f u hf hu).measurable
    (G.gradInnerInverse_continuous u v hu hv).measurable
    hvsupp' hfc huc hvc' hvcc htsupp hcover hD hG hGuvsupp
    (fun i j K hK => halfSpaceAtlas_transition_preimage_isCompact (n := n) G i j hK)
    (halfSpaceAtlas_frontier_volume_zero (n := n) G)

/-- **The cover theorem applied with base chart `1`** (the dilation chart). The test function is
now supported in the *second* half-space source `{0 < y 0}`, which the hand-built `hsPsi`
partition of unity (tied to the first source) does not cover: the general cover theorem produces
the partition of unity for this base chart as well. -/
theorem halfSpaceAtlas_weightedIBP_of_cover_chartOne (G : ChartMetric (n + 1))
    (f u v : Vec (n + 1) → ℝ)
    (hf : ContDiff ℝ 2 f) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hvsupp : tsupport v ⊆ {y : Vec (n + 1) | 0 < y 0}) :
    ∫ m, G.driftLaplacian f u m * v m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight f))
      = -∫ m, G.gradInnerInverse u v m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight f)) := by
  classical
  set A : SmoothOverlapAtlas (Vec (n + 1)) (n + 1) := hsAtlas (n := n) G with hA
  have hchart0 : A.chart 0 = fun y : Vec (n + 1) => (1 : ℝ) • y := hsChart_zero
  have hchart1 : A.chart 1 = fun y : Vec (n + 1) => (2 : ℝ) • y :=
    hsChart_ne (i := 1) (by norm_num)
  have hmetric0 : A.metric 0 = G := hsMetric_zero G
  have hmetric_ne : ∀ {i : ℕ}, i ≠ 0 → A.metric i = dilateMetric G 2 (by norm_num) :=
    fun hi => hsMetric_ne hi G
  have hsource1 : A.source 1 = {y : Vec (n + 1) | 0 < y 0} :=
    hsSource_ne (i := 1) (by norm_num)
  have htrans : ∀ i j y, A.chart j y ∈ A.chart i '' A.source i →
      A.transition i j y ∈ A.source i :=
    halfSpaceAtlas_transition_coherence (n := n) G
  have hfc : ∀ i : ℕ, ContDiff ℝ 2 fun y => f (A.chart i y) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      rw [hchart0]
      simpa [Function.comp_def] using hf.comp (contDiff_const_smul (1 : ℝ))
    · rw [show A.chart i = fun y : Vec (n + 1) => (2 : ℝ) • y from hsChart_ne hi]
      simpa [Function.comp_def] using hf.comp (contDiff_const_smul (2 : ℝ))
  have huc : ∀ i : ℕ, ContDiff ℝ 2 fun y => u (A.chart i y) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      rw [hchart0]
      simpa [Function.comp_def] using hu.comp (contDiff_const_smul (1 : ℝ))
    · rw [show A.chart i = fun y : Vec (n + 1) => (2 : ℝ) • y from hsChart_ne hi]
      simpa [Function.comp_def] using hu.comp (contDiff_const_smul (2 : ℝ))
  have hvc' : ∀ i : ℕ, ContDiff ℝ 2 fun y => v (A.chart i y) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      rw [hchart0]
      simpa [Function.comp_def] using hv.comp (contDiff_const_smul (1 : ℝ))
    · rw [show A.chart i = fun y : Vec (n + 1) => (2 : ℝ) • y from hsChart_ne hi]
      simpa [Function.comp_def] using hv.comp (contDiff_const_smul (2 : ℝ))
  have hD : ∀ i y, y ∈ A.source i →
      G.driftLaplacian f u (A.chart i y)
        = (A.metric i).driftLaplacian (fun z => f (A.chart i z))
            (fun z => u (A.chart i z)) y := by
    intro i y _
    by_cases hi : i = 0
    · subst hi
      rw [hchart0, hmetric0]
      simp only [one_smul]
    · rw [show A.chart i = fun y : Vec (n + 1) => (2 : ℝ) • y from hsChart_ne hi,
        hmetric_ne hi]
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
    · rw [show A.chart i = fun y : Vec (n + 1) => (2 : ℝ) • y from hsChart_ne hi,
        hmetric_ne hi]
      exact (dilateMetric_gradInnerInverse G 2 (by norm_num) u v
        (hu.differentiable (by simp)) (hv.differentiable (by simp)) y).symm
  have hmem1 : ∀ m, v m ≠ 0 → m ∈ {y : Vec (n + 1) | 0 < y 0} := fun m hm =>
    hvsupp (subset_tsupport v (Function.mem_support.mpr hm))
  have hsupp1 : ∀ m, m ∈ tsupport v → m ∈ A.chart 1 '' A.source 1 := by
    intro m hm
    have hm1 : 0 < m 0 := hvsupp hm
    refine ⟨(2 : ℝ)⁻¹ • m, ?_, ?_⟩
    · rw [hsource1]
      show 0 < ((2 : ℝ)⁻¹ • m) 0
      simp only [Pi.smul_apply, smul_eq_mul]
      positivity
    · simp [hchart1, smul_smul]
  have hvsupp' : ∀ m, v m ≠ 0 → m ∈ A.chart 1 '' A.source 1 := fun m hm =>
    hsupp1 m (subset_tsupport v (Function.mem_support.mpr hm))
  have hGuvsupp : ∀ m, G.gradInnerInverse u v m ≠ 0 → m ∈ A.chart 1 '' A.source 1 := fun m hm =>
    hsupp1 m (support_gradInnerInverse_subset G u v hm)
  have hvcc : HasCompactSupport fun y => v (A.chart 1 y) := by
    rw [hchart1]
    exact hvc.comp_smul (by norm_num : (2 : ℝ) ≠ 0)
  have htsupp : tsupport (fun y => v (A.chart 1 y)) ⊆ A.source 1 := by
    have hsub : tsupport (fun y : Vec (n + 1) => v ((2 : ℝ) • y)) ⊆
        (fun y : Vec (n + 1) => (2 : ℝ) • y) ⁻¹' tsupport v := by
      refine closure_minimal ?_ ((isClosed_tsupport v).preimage (continuous_const_smul (2 : ℝ)))
      intro y hy
      rw [Function.mem_support] at hy
      exact subset_tsupport v (by simpa using hy)
    intro y hy
    rw [hchart1] at hy
    rw [hsource1]
    have hyv : (2 : ℝ) • y ∈ tsupport v := hsub hy
    have hyv' : 0 < ((2 : ℝ) • y) 0 := hvsupp hyv
    simp only [Pi.smul_apply, smul_eq_mul] at hyv'
    show 0 < y 0
    linarith
  have hcover : A.chart 1 '' A.source 1 ⊆ ⋃ j : Fin 2, A.chart ((j : ℕ)) '' A.source ((j : ℕ)) :=
    fun y hy => mem_iUnion.mpr ⟨1, hy⟩
  exact A.globalWeightedIBP_of_cover_partial_ae htrans 1 (fun j : Fin 2 => (j : ℕ)) f u v
    (G.driftLaplacian f u) (G.gradInnerInverse u v)
    hf.continuous.measurable hv.continuous.measurable
    (G.driftLaplacian_continuous f u hf hu).measurable
    (G.gradInnerInverse_continuous u v hu hv).measurable
    hvsupp' hfc huc hvc' hvcc htsupp hcover hD hG hGuvsupp
    (fun i j K hK => halfSpaceAtlas_transition_preimage_isCompact (n := n) G i j hK)
    (halfSpaceAtlas_frontier_volume_zero (n := n) G)

end OverlapAtlas

end Poincare.D13.ManifoldIBP

/-! ## Axiom audit -/

#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_of_cover
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_of_cover_chartOne
