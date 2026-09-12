/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — U7: the D13 coherence hypothesis is redundant

The D13 atlas structure `Poincare.D13.ManifoldIBP.SmoothOverlapAtlas` carries globally
injective charts together with the global transition relation
`chart i (transition i j y) = chart j y`.  Nevertheless the D13 headline
`SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae` still takes the *coherence*
hypothesis

`htrans : ∀ i j y, chart j y ∈ chart i '' source i → transition i j y ∈ source i`

as an explicit argument.  This file shows that `htrans` is derivable from the atlas structure
alone (`smoothOverlapAtlas_transition_mem_source`), and then re-derives the headline without it
(`globalWeightedIBP_of_cover_partial_ae'`), so the hypothesis list of the D13 interface is
strictly smaller.  The strengthened theorem is the downstream consumer of the redundancy
lemma; it also independently re-verifies finding F1 of the independent D13 semantic audit
(`L4-child-d13-semantic-audit`), which discovered the same redundancy in a scratch probe.

Non-vacuity: `halfSpaceAtlas_coherence_derived` instantiates the redundancy lemma on the
concrete half-space dilation atlas of `PartialChartModel`, so the derived statement has a
genuine inhabitant.

The strengthened theorem remains a *conditional interface* over `SmoothOverlapAtlas` data
exactly as the original: no manifold measure, smooth partition of unity, Stokes theorem or
oriented volume form is constructed or claimed here beyond what the D13 layer already provides.
-/
import Poincare.D13.ManifoldIBP.POUConstruction

noncomputable section

open scoped BigOperators ENNReal NNReal Topology Matrix Function ContDiff
open MeasureTheory Set Filter Metric Function

namespace Poincare.L4.ManifoldIBP

open Poincare.D13.ManifoldIBP
open Poincare.D12.VolumeIBP

/-- **The coherence hypothesis is derivable.**  For a `SmoothOverlapAtlas`, if `chart j y` lies
in the image of `source i`, then the transition point `transition i j y` lies in `source i`:
the global transition relation identifies `chart i (transition i j y)` with `chart j y`, and
`chart i` is injective. -/
theorem smoothOverlapAtlas_transition_mem_source {M : Type*} [MeasurableSpace M] {n : ℕ}
    (A : SmoothOverlapAtlas M (n + 1)) :
    ∀ i j y, A.chart j y ∈ A.chart i '' A.source i → A.transition i j y ∈ A.source i := by
  rintro i j y ⟨z, hz, hzy⟩
  have h : A.chart i (A.transition i j y) = A.chart i z := by
    rw [A.transition_chart_global, hzy]
  rw [A.inj_chart i h]
  exact hz

/-- **Non-vacuity of the redundancy lemma.**  The concrete half-space dilation atlas satisfies
the derived coherence statement, so the statement is not vacuous. -/
theorem halfSpaceAtlas_coherence_derived (n : ℕ) (G : ChartMetric (n + 1)) :
    ∀ i j y,
      (OverlapAtlas.halfSpaceAtlas G).chart j y ∈
          (OverlapAtlas.halfSpaceAtlas G).chart i '' (OverlapAtlas.halfSpaceAtlas G).source i →
        (OverlapAtlas.halfSpaceAtlas G).transition i j y ∈
          (OverlapAtlas.halfSpaceAtlas G).source i :=
  smoothOverlapAtlas_transition_mem_source (OverlapAtlas.halfSpaceAtlas G)

/-- **Strengthened D13 headline (coherence hypothesis removed).**  The global weighted IBP for
partial charts with constructed partition of unity, with exactly the hypotheses of
`SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae` *except* `htrans`, which is supplied
by `smoothOverlapAtlas_transition_mem_source`.  The conclusion is unchanged. -/
theorem globalWeightedIBP_of_cover_partial_ae' {M : Type*} [MeasurableSpace M] {n : ℕ}
    {A : SmoothOverlapAtlas M (n + 1)}
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
      = -∫ m, Guv m ∂((A.globalMeasure volume).withDensity (A.weight f)) :=
  A.globalWeightedIBP_of_cover_partial_ae (smoothOverlapAtlas_transition_mem_source A)
    b chartOf f u v Du Guv hf hv hDu hGuv hvsupp hfc huc hvc hvcc htsupp_b hcover hD hG hGuvsupp
    hproper hbd

end Poincare.L4.ManifoldIBP
