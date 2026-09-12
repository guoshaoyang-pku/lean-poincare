import Poincare.L4.ManifoldIBP.WeightedSelfAdjointness

open scoped BigOperators ENNReal NNReal Topology Matrix Function ContDiff
open MeasureTheory Set Filter Metric Function

namespace Review4

open Poincare.D12.VolumeIBP Poincare.D13.ManifoldIBP

/-! (a) `halfSpaceAtlas_weightedLaplacian_selfAdjoint` re-derived independently from
D13's `halfSpaceAtlas_greenIdentity`. -/
example {n : ℕ} (G : ChartMetric (n + 1)) (F u v : Vec (n + 1) → ℝ)
    (hF : ContDiff ℝ 2 F) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (huc : HasCompactSupport u) (husupp : tsupport u ⊆ {y : Vec (n + 1) | y 0 < 1})
    (hvc : HasCompactSupport v) (hvsupp : tsupport v ⊆ {y : Vec (n + 1) | y 0 < 1}) :
    ∫ m, G.driftLaplacian F u m * v m
        ∂(((OverlapAtlas.hsAtlas G).globalMeasure volume).withDensity
          ((OverlapAtlas.hsAtlas G).weight F))
      = ∫ m, G.driftLaplacian F v m * u m
        ∂(((OverlapAtlas.hsAtlas G).globalMeasure volume).withDensity
          ((OverlapAtlas.hsAtlas G).weight F)) := by
  rw [OverlapAtlas.halfSpaceAtlas_greenIdentity (n := n) G F u v hF hu hv huc hvc husupp hvsupp]
  exact integral_congr_ae (ae_of_all _ fun m => mul_comm _ _)

/-! (b) the nonneg conjunct of `halfSpaceAtlas_dirichletEnergy_nonneg` holds for
*every* measure, with no hypotheses at all. -/
example {n : ℕ} (G : ChartMetric (n + 1)) (V : Vec (n + 1) → ℝ) (μ : Measure (Vec (n + 1))) :
    0 ≤ ∫ m, G.gradInnerInverse V V m ∂μ :=
  integral_nonneg (fun m => Poincare.L4.ManifoldIBP.gradInnerInverse_self_nonneg G V m)

example {n : ℕ} (G : ChartMetric (n + 1)) (F V : Vec (n + 1) → ℝ) :
    0 ≤ ∫ m, G.gradInnerInverse V V m
        ∂(((OverlapAtlas.hsAtlas G).globalMeasure volume).withDensity
          ((OverlapAtlas.hsAtlas G).weight F)) :=
  integral_nonneg (fun m => Poincare.L4.ManifoldIBP.gradInnerInverse_self_nonneg G V m)

/-! (c) the integrability conjunct of the L4 theorem is literally D13's second conjunct. -/
example {n : ℕ} (G : ChartMetric (n + 1)) (F V : Vec (n + 1) → ℝ)
    (hF : ContDiff ℝ 2 F) (hV : ContDiff ℝ 2 V) (hVc : HasCompactSupport V)
    (hVsupp : tsupport V ⊆ {y : Vec (n + 1) | y 0 < 1}) :
    Integrable (fun m => G.gradInnerInverse V V m)
      (((OverlapAtlas.hsAtlas G).globalMeasure volume).withDensity
        ((OverlapAtlas.hsAtlas G).weight F)) :=
  (OverlapAtlas.halfSpaceAtlas_integrable_dirichlet G F V hF hV hVc hVsupp).2

/-! (d) the L4 theorem's first conjunct is definitionally that same term. -/
example {n : ℕ} (G : ChartMetric (n + 1)) (F V : Vec (n + 1) → ℝ)
    (hF : ContDiff ℝ 2 F) (hV : ContDiff ℝ 2 V) (hVc : HasCompactSupport V)
    (hVsupp : tsupport V ⊆ {y : Vec (n + 1) | y 0 < 1}) :
    (Poincare.L4.ManifoldIBP.halfSpaceAtlas_dirichletEnergy_nonneg G F V hF hV hVc hVsupp).1
      = (OverlapAtlas.halfSpaceAtlas_integrable_dirichlet G F V hF hV hVc hVsupp).2 := rfl

end Review4
