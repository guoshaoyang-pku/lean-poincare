/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (overlapping-atlas manifold IBP)

# Integration by parts on the overlapping-atlas Riemannian measure

`ManifoldIBP.GlobalMeasure` constructs the Riemannian measure `globalMeasure` of an atlas
whose charts **overlap**, and proves the interface theorem `globalMeasure_apply_chart`
(it computes the measure by the density formula `√(det gᵢⱼ) dx` in *every* chart). This
module **consumes** that measure: it proves the manifold weighted integration-by-parts /
Green identity on the glued measure, by reducing a chart-supported test function to the
D12 chart theorem `ChartMetric.chart_weighted_ibp`.

The reduction is the mathematical content of the atlas layer, and each step is a proved
identity:

* `integral_chartMeasure_of_supported` — the chart measure integral of a function supported
  in one chart image is the density integral `∫ g(c y) · √(det g) ∂μ` over the chart source
  (mathlib `integral_map` + `integral_withDensity_eq_integral_toReal_smul₀`);
* `integral_globalMeasure_of_supported` — the same for the *glued* measure: a function
  supported in a chart image has the same integral against `globalMeasure` and against that
  chart's measure, by `globalMeasure_restrict_eq_chartMeasure`;
* `integral_globalMeasure_withDensity_of_supported` — the same with the entropy weight
  `e^{-f}` inserted as a `withDensity`;
* **`globalWeightedIBP_of_chartSupported`** — the manifold identity
  `∫_M (Δ_f u) v dm = -∫_M ⟨∇u,∇v⟩_{g⁻¹} dm` for the entropy measure `dm = e^{-f} dμ_g`,
  for a test function compactly supported inside a single chart source. The proof is exactly
  the reduction above composed with D12's `chart_weighted_ibp`; no integration by parts is
  assumed on the manifold side.

The test-function scope (support inside one chart) is the honest scope of the chart theorem;
the global case needs a smooth partition of unity subordinate to the atlas, which is a
separate named blocker (`B-D13-SMOOTH-POU`). Within this scope the theorem is unconditional
in the atlas: the overlapping charts enter only through the well-definedness theorem behind
`globalMeasure_restrict_eq_chartMeasure`.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.OverlapModel

open scoped BigOperators ENNReal NNReal Topology Matrix Function
open MeasureTheory Set Filter

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

variable {M : Type*} [MeasurableSpace M] {n : ℕ}

/-! ## Elementary support reductions -/

/-- A function that vanishes off `s` has the same integral against `ν` and against
`ν.restrict s`. -/
lemma integral_eq_restrict_of_support {s : Set M} (hs : MeasurableSet s) {g : M → ℝ}
    (hsupp : ∀ m, g m ≠ 0 → m ∈ s) (ν : Measure M) :
    ∫ m, g m ∂ν = ∫ m, g m ∂(ν.restrict s) := by
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards with m
  by_cases hm : m ∈ s
  · simp only [Set.indicator_of_mem hm]
  · have h0 : g m = 0 := by
      by_contra h
      exact hm (hsupp m h)
    simp only [Set.indicator_of_notMem hm, h0]

/-- A function on the chart domain that vanishes off `s` has the same set integral over `s`
and integral over the whole space. -/
lemma setIntegral_eq_integral_of_support {s : Set (Vec (n + 1))} (hs : MeasurableSet s)
    {f : Vec (n + 1) → ℝ} (hsupp : ∀ y, f y ≠ 0 → y ∈ s) (μ : Measure (Vec (n + 1))) :
    ∫ y in s, f y ∂μ = ∫ y, f y ∂μ := by
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ s
  · simp only [Set.indicator_of_mem hy]
  · have h0 : f y = 0 := by
      by_contra h
      exact hy (hsupp y h)
    simp only [Set.indicator_of_notMem hy, h0]

namespace OverlapAtlas

/-! ## The entropy weight -/

/-- The entropy weight `e^{-f}` of a drift `f`, as an `ℝ≥0∞` density for `withDensity`. -/
def weight (A : OverlapAtlas M (n + 1)) (f : M → ℝ) (m : M) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(f m)))

lemma weight_toReal (A : OverlapAtlas M (n + 1)) (f : M → ℝ) (m : M) :
    (A.weight f m).toReal = Real.exp (-(f m)) :=
  ENNReal.toReal_ofReal (Real.exp_nonneg _)

lemma weight_lt_top (A : OverlapAtlas M (n + 1)) (f : M → ℝ) (m : M) :
    A.weight f m < ∞ :=
  ENNReal.ofReal_lt_top

lemma measurable_weight (A : OverlapAtlas M (n + 1)) {f : M → ℝ} (hf : Measurable f) :
    Measurable (A.weight f) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hf.neg)

/-! ## The chart-measure integral formula -/

/-- **The chart-measure integral formula.** For a measurable function supported in the image
of the `i`-th chart, the integral against that chart's Riemannian measure is the density
integral `∫ g(chartᵢ y) · √(det gᵢ) ∂μ` over the chart source. This is mathlib's
`integral_map` for the pushforward defining `chartMeasure`, composed with the
`withDensity`/`toReal` computation for the density. -/
theorem integral_chartMeasure_of_supported (A : OverlapAtlas M (n + 1))
    (μ : Measure (Vec (n + 1))) (i : ℕ) {g : M → ℝ}
    (hg : AEStronglyMeasurable g (A.chartMeasure μ i))
    (hsupp : ∀ m, g m ≠ 0 → m ∈ A.chart i '' A.source i) :
    ∫ m, g m ∂(A.chartMeasure μ i)
      = ∫ y in A.source i, g (A.chart i y) * A.density i y ∂μ := by
  have hae : AEMeasurable (A.chart i)
      ((μ.restrict (A.source i)).withDensity
        (fun y => ENNReal.ofReal (A.density i y))) :=
    (A.measurable_chart i).aemeasurable
  have hdens : AEMeasurable (fun y => ENNReal.ofReal (A.density i y))
      (μ.restrict (A.source i)) :=
    (ENNReal.measurable_ofReal.comp
      (A.metric i).density_contDiff_one.continuous.measurable).aemeasurable
  rw [chartMeasure, integral_map hae hg,
    integral_withDensity_eq_integral_toReal_smul₀ hdens
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards with y
  rw [ENNReal.toReal_ofReal (A.density_nonneg i y), smul_eq_mul]
  ring

/-- **The glued-measure integral formula.** A measurable function supported in the image of
one chart has the same integral against the global (overlapping-atlas) measure and against
that chart's measure. This is where the chart-independence theorem
(`globalMeasure_restrict_eq_chartMeasure`) is consumed. -/
theorem integral_globalMeasure_of_supported (A : OverlapAtlas M (n + 1))
    (μ : Measure (Vec (n + 1))) [μ.IsAddHaarMeasure]
    (i : ℕ) {g : M → ℝ}
    (hsupp : ∀ m, g m ≠ 0 → m ∈ A.chart i '' A.source i) :
    ∫ m, g m ∂(A.globalMeasure μ) = ∫ m, g m ∂(A.chartMeasure μ i) := by
  have hs : MeasurableSet (A.chart i '' A.source i) := A.measurableSet_image i
  rw [integral_eq_restrict_of_support hs hsupp (A.globalMeasure μ),
    integral_eq_restrict_of_support hs hsupp (A.chartMeasure μ i),
    A.globalMeasure_restrict_eq_chartMeasure μ i]

/-- **The weighted glued-measure integral formula.** With the entropy weight `e^{-f}`
inserted, the integral of a chart-supported function against the weighted global measure is
the chart density integral `∫ e^{-f(chartᵢ y)} g(chartᵢ y) √(det gᵢ) ∂μ`. -/
theorem integral_globalMeasure_withDensity_of_supported (A : OverlapAtlas M (n + 1))
    (μ : Measure (Vec (n + 1))) [μ.IsAddHaarMeasure] (i : ℕ) {f g : M → ℝ}
    (hf : Measurable f) (hg : AEStronglyMeasurable g (A.chartMeasure μ i))
    (hsupp : ∀ m, g m ≠ 0 → m ∈ A.chart i '' A.source i) :
    ∫ m, g m ∂((A.globalMeasure μ).withDensity (A.weight f))
      = ∫ y in A.source i,
          Real.exp (-(f (A.chart i y))) * g (A.chart i y) * A.density i y ∂μ := by
  have hweight : AEMeasurable (A.weight f) (A.globalMeasure μ) :=
    (A.measurable_weight hf).aemeasurable
  rw [integral_withDensity_eq_integral_toReal_smul₀ hweight
      (ae_of_all _ fun m => A.weight_lt_top f m)]
  rw [show (fun m => (A.weight f m).toReal • g m) = fun m => Real.exp (-(f m)) * g m by
    funext m
    rw [A.weight_toReal, smul_eq_mul]]
  have hgm : AEStronglyMeasurable (fun m => Real.exp (-(f m)) * g m) (A.chartMeasure μ i) :=
    ((Real.measurable_exp.comp hf.neg).aemeasurable.aestronglyMeasurable).mul hg
  have hgsupp : ∀ m, Real.exp (-(f m)) * g m ≠ 0 → m ∈ A.chart i '' A.source i :=
    fun m hm => hsupp m (mul_ne_zero_iff.mp hm).2
  rw [A.integral_globalMeasure_of_supported μ i hgsupp,
    A.integral_chartMeasure_of_supported μ i hgm hgsupp]

/-! ## The manifold weighted integration by parts -/

/-- **Manifold weighted integration by parts on the overlapping-atlas measure.** Let `A` be
an atlas whose charts may overlap, `μ` an additive Haar measure on the chart model space,
`f` a drift and `u`, `v` test functions on `M`, with `Δ_f u` and `⟨∇u,∇v⟩_{g⁻¹}` given by
their chart expressions (`hD`, `hG` — the chart-identification interface, exactly as in
`ManifoldAtlasData`). If the test data are supported in the `i`-th chart (hypotheses
`hvsupp`, `hGuvsupp`, `hvsrc`, `hGuvsrc`), then

`∫_M (Δ_f u) · v d(e^{-f} μ_g) = -∫_M ⟨∇u, ∇v⟩_{g⁻¹} d(e^{-f} μ_g)`

for the global Riemannian measure `μ_g = globalMeasure` of the overlapping atlas. The proof
reduces the chart-supported manifold integrals to the chart integrals (the two preceding
theorems) and applies D12's chart theorem `chart_weighted_ibp`. -/
theorem globalWeightedIBP_of_chartSupported (A : OverlapAtlas M (n + 1))
    (i : ℕ) (f u v Du Guv : M → ℝ)
    (hf : Measurable f) (hv : Measurable v) (hDu : Measurable Du) (hGuv : Measurable Guv)
    (hvsupp : ∀ m, v m ≠ 0 → m ∈ A.chart i '' A.source i)
    (hGuvsupp : ∀ m, Guv m ≠ 0 → m ∈ A.chart i '' A.source i)
    (hvsrc : ∀ y, v (A.chart i y) ≠ 0 → y ∈ A.source i)
    (hGuvsrc : ∀ y, (A.metric i).gradInnerInverse (fun z => u (A.chart i z))
        (fun z => v (A.chart i z)) y ≠ 0 → y ∈ A.source i)
    (hfc : ContDiff ℝ 2 fun y => f (A.chart i y))
    (huc : ContDiff ℝ 2 fun y => u (A.chart i y))
    (hvc : ContDiff ℝ 2 fun y => v (A.chart i y))
    (hvcc : HasCompactSupport fun y => v (A.chart i y))
    (hD : ∀ᵐ y ∂volume, y ∈ A.source i →
      Du (A.chart i y)
        = (A.metric i).driftLaplacian (fun z => f (A.chart i z)) (fun z => u (A.chart i z)) y)
    (hG : ∀ᵐ y ∂volume, y ∈ A.source i →
      Guv (A.chart i y)
        = (A.metric i).gradInnerInverse (fun z => u (A.chart i z))
            (fun z => v (A.chart i z)) y) :
    ∫ m, Du m * v m ∂((A.globalMeasure volume).withDensity (A.weight f))
      = -∫ m, Guv m ∂((A.globalMeasure volume).withDensity (A.weight f)) := by
  have hsrc : MeasurableSet (A.source i) := (A.isOpen_source i).measurableSet
  -- left-hand side: reduce to the chart integral, then to the whole-space chart integral
  have hL : ∫ m, Du m * v m ∂((A.globalMeasure volume).withDensity (A.weight f))
      = ∫ y in A.source i,
          Real.exp (-(f (A.chart i y))) * (Du (A.chart i y) * v (A.chart i y))
            * A.density i y ∂volume :=
    A.integral_globalMeasure_withDensity_of_supported volume i hf
      (hDu.mul hv).aestronglyMeasurable
      (fun m hm => hvsupp m (mul_ne_zero_iff.mp hm).2)
  have hL' : ∫ y in A.source i,
        Real.exp (-(f (A.chart i y))) * (Du (A.chart i y) * v (A.chart i y))
          * A.density i y ∂volume
      = ∫ y in A.source i,
          ((A.metric i).driftLaplacian (fun z => f (A.chart i z))
            (fun z => u (A.chart i z)) y * v (A.chart i y))
            * Real.exp (-(f (A.chart i y))) * A.density i y ∂volume := by
    refine setIntegral_congr_ae hsrc ?_
    filter_upwards [hD] with y hy hys
    rw [hy hys]
    ring
  have hL'' : ∫ y in A.source i,
        ((A.metric i).driftLaplacian (fun z => f (A.chart i z))
          (fun z => u (A.chart i z)) y * v (A.chart i y))
          * Real.exp (-(f (A.chart i y))) * A.density i y ∂volume
      = ∫ y, (A.metric i).driftLaplacian (fun z => f (A.chart i z))
          (fun z => u (A.chart i z)) y * v (A.chart i y)
          * Real.exp (-(f (A.chart i y))) * A.density i y ∂volume := by
    refine setIntegral_eq_integral_of_support hsrc ?_ volume
    intro y hy
    obtain ⟨h1, -⟩ := mul_ne_zero_iff.mp hy
    obtain ⟨h2, -⟩ := mul_ne_zero_iff.mp h1
    exact hvsrc y (mul_ne_zero_iff.mp h2).2
  -- right-hand side: reduce to the chart integral
  have hR : ∫ m, Guv m ∂((A.globalMeasure volume).withDensity (A.weight f))
      = ∫ y in A.source i,
          Real.exp (-(f (A.chart i y))) * Guv (A.chart i y) * A.density i y ∂volume :=
    A.integral_globalMeasure_withDensity_of_supported volume i hf
      hGuv.aestronglyMeasurable hGuvsupp
  have hR' : ∫ y in A.source i,
        Real.exp (-(f (A.chart i y))) * Guv (A.chart i y) * A.density i y ∂volume
      = ∫ y in A.source i,
          (A.metric i).gradInnerInverse (fun z => u (A.chart i z))
            (fun z => v (A.chart i z)) y * Real.exp (-(f (A.chart i y)))
            * A.density i y ∂volume := by
    refine setIntegral_congr_ae hsrc ?_
    filter_upwards [hG] with y hy hys
    rw [hy hys]
    ring
  have hR'' : ∫ y in A.source i,
        (A.metric i).gradInnerInverse (fun z => u (A.chart i z))
          (fun z => v (A.chart i z)) y * Real.exp (-(f (A.chart i y)))
          * A.density i y ∂volume
      = ∫ y, (A.metric i).gradInnerInverse (fun z => u (A.chart i z))
          (fun z => v (A.chart i z)) y * Real.exp (-(f (A.chart i y)))
          * A.density i y ∂volume := by
    refine setIntegral_eq_integral_of_support hsrc ?_ volume
    intro y hy
    obtain ⟨h1, -⟩ := mul_ne_zero_iff.mp hy
    exact hGuvsrc y (mul_ne_zero_iff.mp h1).1
  rw [hL, hL', hL'', hR, hR', hR'']
  exact (A.metric i).chart_weighted_ibp (fun z => f (A.chart i z))
    (fun z => u (A.chart i z)) (fun z => v (A.chart i z)) hfc huc hvc hvcc


/-- **Normalisation independence of the manifold IBP.** Rescaling the chart reference measure
to `c • volume` (an arbitrary scalar multiple of Lebesgue, i.e. the general form of an
additive Haar measure on the chart model space) leaves the identity unchanged: both the glued
measure (`globalMeasure_smul`) and the Bochner integral scale by the same constant. This is
the IBP counterpart of the upstream `riemannianMeasure_smul`. -/
theorem globalWeightedIBP_of_chartSupported_smul (A : OverlapAtlas M (n + 1)) (c : ℝ≥0∞)
    (i : ℕ) (f u v Du Guv : M → ℝ)
    (hf : Measurable f) (hv : Measurable v) (hDu : Measurable Du) (hGuv : Measurable Guv)
    (hvsupp : ∀ m, v m ≠ 0 → m ∈ A.chart i '' A.source i)
    (hGuvsupp : ∀ m, Guv m ≠ 0 → m ∈ A.chart i '' A.source i)
    (hvsrc : ∀ y, v (A.chart i y) ≠ 0 → y ∈ A.source i)
    (hGuvsrc : ∀ y, (A.metric i).gradInnerInverse (fun z => u (A.chart i z))
        (fun z => v (A.chart i z)) y ≠ 0 → y ∈ A.source i)
    (hfc : ContDiff ℝ 2 fun y => f (A.chart i y))
    (huc : ContDiff ℝ 2 fun y => u (A.chart i y))
    (hvc : ContDiff ℝ 2 fun y => v (A.chart i y))
    (hvcc : HasCompactSupport fun y => v (A.chart i y))
    (hD : ∀ᵐ y ∂volume, y ∈ A.source i →
      Du (A.chart i y)
        = (A.metric i).driftLaplacian (fun z => f (A.chart i z)) (fun z => u (A.chart i z)) y)
    (hG : ∀ᵐ y ∂volume, y ∈ A.source i →
      Guv (A.chart i y)
        = (A.metric i).gradInnerInverse (fun z => u (A.chart i z))
            (fun z => v (A.chart i z)) y) :
    ∫ m, Du m * v m ∂((A.globalMeasure (c • volume)).withDensity (A.weight f))
      = -∫ m, Guv m ∂((A.globalMeasure (c • volume)).withDensity (A.weight f)) := by
  have hbase := A.globalWeightedIBP_of_chartSupported i f u v Du Guv hf hv hDu hGuv
    hvsupp hGuvsupp hvsrc hGuvsrc hfc huc hvc hvcc hD hG
  have hsm : ∀ g : M → ℝ,
      ∫ m, g m ∂(c • ((A.globalMeasure volume).withDensity (A.weight f)))
        = c.toReal • ∫ m, g m ∂((A.globalMeasure volume).withDensity (A.weight f)) :=
    fun g => integral_smul_measure g c
  rw [A.globalMeasure_smul volume c, MeasureTheory.withDensity_smul_measure,
    hsm (fun m => Du m * v m), hsm Guv, hbase, smul_neg]


/-- The entropy weight of the zero drift is identically `1`. -/
lemma weight_zero (A : OverlapAtlas M (n + 1)) :
    A.weight (fun _ : M => 0) = fun _ => 1 := by
  funext m
  simp [weight]

/-- **The manifold unweighted integration by parts (Green identity) on any overlapping
atlas.** For chart-supported test data, with the operators identified with the chart
Laplacian and the chart inverse-metric pairing (`hD`, `hG` with zero drift), the identity
`∫_M (Δu)·v dμ_g = -∫_M ⟨∇u,∇v⟩_{g⁻¹} dμ_g` holds for the glued Riemannian measure of an
arbitrary atlas with overlaps. This is `globalWeightedIBP_of_chartSupported` with zero drift
(the weight `e^0 = 1`). -/
theorem globalIBP_of_chartSupported (A : OverlapAtlas M (n + 1))
    (i : ℕ) (u v Du Guv : M → ℝ)
    (hv : Measurable v) (hDu : Measurable Du) (hGuv : Measurable Guv)
    (hvsupp : ∀ m, v m ≠ 0 → m ∈ A.chart i '' A.source i)
    (hGuvsupp : ∀ m, Guv m ≠ 0 → m ∈ A.chart i '' A.source i)
    (hvsrc : ∀ y, v (A.chart i y) ≠ 0 → y ∈ A.source i)
    (hGuvsrc : ∀ y, (A.metric i).gradInnerInverse (fun z => u (A.chart i z))
        (fun z => v (A.chart i z)) y ≠ 0 → y ∈ A.source i)
    (huc : ContDiff ℝ 2 fun y => u (A.chart i y))
    (hvc : ContDiff ℝ 2 fun y => v (A.chart i y))
    (hvcc : HasCompactSupport fun y => v (A.chart i y))
    (hD : ∀ᵐ y ∂volume, y ∈ A.source i →
      Du (A.chart i y) = (A.metric i).laplacian (fun z => u (A.chart i z)) y)
    (hG : ∀ᵐ y ∂volume, y ∈ A.source i →
      Guv (A.chart i y)
        = (A.metric i).gradInnerInverse (fun z => u (A.chart i z))
            (fun z => v (A.chart i z)) y) :
    ∫ m, Du m * v m ∂(A.globalMeasure volume)
      = -∫ m, Guv m ∂(A.globalMeasure volume) := by
  have h := A.globalWeightedIBP_of_chartSupported i (fun _ => 0) u v Du Guv
    measurable_const hv hDu hGuv hvsupp hGuvsupp hvsrc hGuvsrc
    contDiff_const huc hvc hvcc
    (by
      refine hD.mono fun y hy => ?_
      intro hys
      rw [hy hys]
      simp [ChartMetric.driftLaplacian, ChartMetric.gradInnerInverse,
        ChartMetric.metricInnerInverse, ChartMetric.partialDeriv])
    hG
  have hw : (A.globalMeasure volume).withDensity (A.weight (fun _ => 0))
      = A.globalMeasure volume := by
    rw [A.weight_zero]
    exact withDensity_one
  rwa [hw] at h


/-- **The manifold divergence theorem (Laplacian form) on any overlapping atlas**:
for a manifold function `Dw` whose chart-`i` expression is the metric Laplacian `Δ V` of a
compactly supported `C²` chart function `V`, the integral against the glued Riemannian measure
vanishes: `∫_M Δ_g V dμ_g = 0`. Proved from the chart integral formula and D12's
`ChartMetric.laplacian_integral_eq_zero`; the chart expression of the Laplacian is assumed
supported in the chart source. -/
theorem globalLaplacianIntegralZero_of_chartSupported (A : OverlapAtlas M (n + 1))
    (i : ℕ) (Dw : M → ℝ) (V : Vec (n + 1) → ℝ) (hDwm : Measurable Dw)
    (hDwsupp : ∀ m, Dw m ≠ 0 → m ∈ A.chart i '' A.source i)
    (hV : ContDiff ℝ 2 V) (hVc : HasCompactSupport V)
    (hVsrc : ∀ y, (A.metric i).laplacian V y ≠ 0 → y ∈ A.source i)
    (hD : ∀ᵐ y ∂volume, y ∈ A.source i → Dw (A.chart i y) = (A.metric i).laplacian V y) :
    ∫ m, Dw m ∂(A.globalMeasure volume) = 0 := by
  rw [A.integral_globalMeasure_of_supported volume i hDwsupp,
    A.integral_chartMeasure_of_supported volume i hDwm.aestronglyMeasurable hDwsupp]
  have h1 : ∫ y in A.source i, Dw (A.chart i y) * A.density i y ∂volume
      = ∫ y in A.source i, (A.metric i).laplacian V y * A.density i y ∂volume := by
    refine setIntegral_congr_ae (A.isOpen_source i).measurableSet ?_
    filter_upwards [hD] with y hy hys
    rw [hy hys]
  have h2 : ∫ y in A.source i, (A.metric i).laplacian V y * A.density i y ∂volume
      = ∫ y, (A.metric i).laplacian V y * A.density i y ∂volume := by
    refine setIntegral_eq_integral_of_support (A.isOpen_source i).measurableSet ?_ volume
    intro y hy
    exact hVsrc y (left_ne_zero_of_mul hy)
  rw [h1, h2]
  exact (A.metric i).laplacian_integral_eq_zero V hV hVc

end OverlapAtlas

end Poincare.D13.ManifoldIBP

/-! ## Axiom audit -/

#print axioms Poincare.D13.ManifoldIBP.integral_eq_restrict_of_support
#print axioms Poincare.D13.ManifoldIBP.setIntegral_eq_integral_of_support
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.weight
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.weight_toReal
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.measurable_weight
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.integral_chartMeasure_of_supported
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.integral_globalMeasure_of_supported
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.integral_globalMeasure_withDensity_of_supported
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_of_chartSupported
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.weight_zero
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalIBP_of_chartSupported
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalLaplacianIntegralZero_of_chartSupported
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_of_chartSupported_smul
