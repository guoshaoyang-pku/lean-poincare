import Poincare.L4.Compactness.CoveringStability
import Poincare.L4.ManifoldIBP.WeightedSelfAdjointness

open scoped BigOperators ENNReal NNReal Topology Matrix Function ContDiff
open MeasureTheory Set Filter Metric Function

namespace Review3

open Poincare.D12.VolumeIBP Poincare.D13.ManifoldIBP

/-! ## Item 4: independent re-derivation of self-adjointness from D13 greenIdentity -/

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

/-! ## Item 3: the nonneg conjunct needs NO hypotheses at all (not even measurability) -/

example {n : ℕ} (G : ChartMetric (n + 1)) (V : Vec (n + 1) → ℝ) (μ : Measure (Vec (n + 1))) :
    0 ≤ ∫ m, G.gradInnerInverse V V m ∂μ :=
  integral_nonneg (fun m => Poincare.L4.ManifoldIBP.gradInnerInverse_self_nonneg G V m)

/-! ## Item 6: concrete consistency tests for the covering-number bound -/

example : GromovHausdorff.ghDist PUnit PUnit < (1 : ℝ) := by
  simp [GromovHausdorff.ghDist]

example : Metric.coveringNumber (3 : ℝ≥0) (univ : Set PUnit) = 1 := by
  refine le_antisymm ?_ ?_
  · calc Metric.coveringNumber (3 : ℝ≥0) (univ : Set PUnit)
        ≤ (univ : Set PUnit).encard := Metric.coveringNumber_le_encard_self _
      _ = 1 := by simp
  · exact ENat.one_le_iff_ne_zero.mpr
      (ne_of_gt (Metric.coveringNumber_pos_iff.mpr Set.univ_nonempty))

example : Metric.coveringNumber (0 : ℝ≥0) (univ : Set PUnit) = 1 := by
  refine le_antisymm ?_ ?_
  · calc Metric.coveringNumber (0 : ℝ≥0) (univ : Set PUnit)
        ≤ (univ : Set PUnit).encard := Metric.coveringNumber_le_encard_self _
      _ = 1 := by simp
  · exact ENat.one_le_iff_ne_zero.mpr
      (ne_of_gt (Metric.coveringNumber_pos_iff.mpr Set.univ_nonempty))

-- Instantiate the reviewed theorem at a concrete pair: hypotheses are satisfiable and the
-- conclusion holds (1 ≤ 1).
example : Metric.coveringNumber (3 : ℝ≥0) (univ : Set PUnit) ≤
    Metric.coveringNumber (0 : ℝ≥0) (univ : Set PUnit) :=
  Poincare.L4.Compactness.coveringNumber_le_of_ghDist_lt (X := PUnit) (Y := PUnit)
    (r := 1) (by simp [GromovHausdorff.ghDist]) 0 3 (by norm_num)

-- Sanity: the reverse inequality at this instance also happens to hold (1 ≤ 1), so the
-- PUnit instance alone cannot distinguish the directions.
example : Metric.coveringNumber (0 : ℝ≥0) (univ : Set PUnit) ≤
    Metric.coveringNumber (3 : ℝ≥0) (univ : Set PUnit) := le_of_eq (by simp)

-- What metric instances exist on small finite types (for a two-point test)?
#check (inferInstance : MetricSpace (Fin 2))
#check (inferInstance : PseudoMetricSpace (Fin 2))
#check (inferInstance : Dist (Fin 2))
#check (inferInstance : MetricSpace Bool)

end Review3
