import Poincare.L4.GeodesicComparison.ConstantCurvatureRauch
import Poincare.L4.ManifoldIBP.WeightedSelfAdjointness

open scoped BigOperators ENNReal NNReal Topology Matrix Function ContDiff
open MeasureTheory Set Filter Metric Function

namespace Review2

open Poincare.D12.VolumeIBP Poincare.D13.ManifoldIBP Poincare.D12.ComparisonGeodesics

-- 1. The pre-existing D12 symmetry lemma (same statement as the new L4 one?)
#check @Poincare.D12.VolumeIBP.ChartMetric.gradInnerInverse_comm
#check @Poincare.L4.ManifoldIBP.gradInnerInverse_comm

-- 2. The pre-existing D13 Green identity (same statement as the new L4 self-adjointness?)
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_greenIdentity
#check @Poincare.L4.ManifoldIBP.halfSpaceAtlas_weightedLaplacian_selfAdjoint

-- 3. The D12 engine signature used by rauch_upper_of_jacobi_constCurv
#check @Poincare.D12.ComparisonGeodesics.riccati_le_of_singular_normalization
#check @Poincare.D12.ComparisonGeodesics.EuclideanNormalizedOn

-- 4. Duplication test: the new self-adjointness theorem follows in one step from the
-- pre-existing D13 green identity (without using any L4 declaration).
example {n : ℕ} (G : ChartMetric (n + 1)) (f u v : Vec (n + 1) → ℝ)
    (hf : ContDiff ℝ 2 f) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (huc : HasCompactSupport u) (husupp : tsupport u ⊆ {y : Vec (n + 1) | y 0 < 1})
    (hvc : HasCompactSupport v) (hvsupp : tsupport v ⊆ {y : Vec (n + 1) | y 0 < 1}) :
    ∫ m, G.driftLaplacian f u m * v m
        ∂(((OverlapAtlas.hsAtlas G).globalMeasure volume).withDensity
          ((OverlapAtlas.hsAtlas G).weight f))
      = ∫ m, G.driftLaplacian f v m * u m
        ∂(((OverlapAtlas.hsAtlas G).globalMeasure volume).withDensity
          ((OverlapAtlas.hsAtlas G).weight f)) := by
  have hcomm : ∫ m, G.driftLaplacian f v m * u m
        ∂(((OverlapAtlas.hsAtlas G).globalMeasure volume).withDensity
          ((OverlapAtlas.hsAtlas G).weight f))
      = ∫ m, u m * G.driftLaplacian f v m
        ∂(((OverlapAtlas.hsAtlas G).globalMeasure volume).withDensity
          ((OverlapAtlas.hsAtlas G).weight f)) :=
    integral_congr_ae (ae_of_all _ fun m => mul_comm _ _)
  rw [hcomm]
  exact OverlapAtlas.halfSpaceAtlas_greenIdentity G f u v hf hu hv huc hvc husupp hvsupp

-- 5. Duplication test: the new gradient-pairing symmetry is exactly the D12 lemma.
example {n : ℕ} (G : ChartMetric (n + 1)) (u v : Vec (n + 1) → ℝ) (x : Vec (n + 1)) :
    G.gradInnerInverse u v x = G.gradInnerInverse v u x :=
  ChartMetric.gradInnerInverse_comm G u v x

end Review2
