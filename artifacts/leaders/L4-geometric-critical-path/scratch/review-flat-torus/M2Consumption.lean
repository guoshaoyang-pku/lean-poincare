/-
REVIEWER SCRATCH — M2-side audit: proof-term consumption of the round-5 chain, and
concrete evaluation of M2's own constants.  Not part of the release tree.
-/
import Poincare.L4.Compactness.FlatTorusGrowth

open scoped Topology ENNReal NNReal
open Set Filter Metric MeasureTheory
open GromovHausdorff
open Poincare.D12.ComparisonGeodesics

/-! ## 1. Proof terms of the downstream consumers (do they consume the chain?) -/

#print Poincare.L4.Compactness.totallyBounded_torus
#print Poincare.L4.Compactness.isCompact_torus
#print Poincare.L4.Compactness.exists_pointed_subseq_torus
#print Poincare.L4.Compactness.totallyBounded_of_uniformRicciBallGrowth
#print Poincare.L4.Compactness.isCompact_of_uniformRicciBallGrowth
#print Poincare.L4.Compactness.exists_pointed_subseq_of_uniformRicciBallGrowth
#print Poincare.L4.Compactness.UniformRicciBallGrowth.toUniformMeasureGrowth
#print Poincare.L4.Compactness.totallyBounded_of_uniformMeasureGrowth
#print Poincare.L4.Compactness.isCompact_of_uniformMeasureGrowth
#print Poincare.L4.Compactness.exists_pointed_subseq_of_uniformMeasureGrowth
#print Poincare.L4.Compactness.UniformMeasureGrowth.coveringNumber_le
#print Poincare.L4.Compactness.coveringNumber_le_of_measure_doubling

namespace ReviewAudit

open Poincare.L4.Compactness

/-! ## 2. M2's own constants, evaluated -/

example : torusA (1 / 4) = 2 := by rw [torusA_of_mem (by norm_num)]; norm_num
example : torusA (1 / 2) = 4 := by rw [torusA_of_mem (by norm_num)]; norm_num
example : torusA 0 = 0 := torusA_zero
example : torusA (3 / 5) = 0 := torusA_of_gt (by norm_num)
example : ¬ (torusA (1 / 2) = 0) := by rw [torusA_half]; norm_num

example : radialVolume torusA (1 / 4) = 1 / 4 := by
  rw [torusRadialVolume_of_le_half (by norm_num) (by norm_num)]; norm_num
example : radialVolume torusA (1 / 3) = 4 / 9 := by
  rw [torusRadialVolume_of_le_half (by norm_num) (by norm_num)]; norm_num
example : radialVolume torusA (1 / 2) = 1 := torusRadialVolume_of_ge_half le_rfl
example : radialVolume torusA (-1) = 0 := torusRadialVolume_of_nonpos (by norm_num)

example : torusMeasure (closedBall torusZero (1 / 4)) = (1 / 4 : ℝ≥0∞) :=
  torusGrowth_measure_varies.1
example : torusMeasure (closedBall torusZero (3 / 4)) = 1 :=
  torusGrowth_measure_varies.2
example : torusMeasure (closedBall torusZero (-1)) = 0 := by
  rw [torusMeasure_closedBall]; norm_num
example : torusMeasure (univ : Set (toGHSpace FlatTorus).Rep) = 1 := torusMeasure_univ

/-! ## 3. The structure fields of `torusRicciBallGrowth` -/

example : torusRicciBallGrowth.d = 1 := rfl
example : torusRicciBallGrowth.T = 1 / 2 := rfl
example : torusRicciBallGrowth.Cn = 0 := rfl
example : torusRicciBallGrowth.t₀ = 1 / 2 := rfl
example : torusRicciBallGrowth.R = 1 / 4 := rfl
example : torusRicciBallGrowth.A = torusA := rfl
example : torusRicciBallGrowth.k (1 / 4) = 0 := rfl
example : torusRicciBallGrowth.dA (1 / 4) = 8 := rfl
example : torusRicciBallGrowth.m (1 / 4) = 4 := by
  change ((1 / 4 : ℝ))⁻¹ = 4
  norm_num
example : torusRicciBallGrowth.dm (1 / 4) = -16 := by
  change (-(((1 / 4 : ℝ)) ^ 2)⁻¹) = -16
  norm_num

/-- The Riccati inequality is an **equality** at `s = 1/4` for M2's own data. -/
example : torusRicciBallGrowth.dm (1 / 4) +
    torusRicciBallGrowth.m (1 / 4) ^ 2 / (torusRicciBallGrowth.d : ℝ) +
    torusRicciBallGrowth.k (1 / 4) = 0 := by
  change (-(((1 / 4 : ℝ)) ^ 2)⁻¹) + ((1 / 4 : ℝ))⁻¹ ^ 2 / ((1 : ℕ) : ℝ) +
    (0 : ℝ) = 0
  norm_num

example : torusRicciBallGrowth.dm (1 / 4) +
    torusRicciBallGrowth.m (1 / 4) ^ 2 / (torusRicciBallGrowth.d : ℝ) +
    torusRicciBallGrowth.k (1 / 4) ≤ 0 :=
  torusRicciBallGrowth.hineq (s := (1 / 4 : ℝ))
    (show (1 / 4 : ℝ) ∈ Ioo 0 (1 / 2) by norm_num)

/-- `m = A'/A` at `s = 1/4` for M2's own data. -/
example : torusRicciBallGrowth.m (1 / 4) =
    torusRicciBallGrowth.dA (1 / 4) / torusRicciBallGrowth.A (1 / 4) :=
  torusRicciBallGrowth.hmA (s := (1 / 4 : ℝ))
    (show (1 / 4 : ℝ) ∈ Ioo 0 (1 / 2) by norm_num)

example : 0 < torusRicciBallGrowth.A (1 / 2) :=
  torusRicciBallGrowth.hApos (s := (1 / 2 : ℝ))
    (show (1 / 2 : ℝ) ∈ Ioc 0 (1 / 2) by norm_num)

example : torusRicciBallGrowth.A 0 = 0 := torusRicciBallGrowth.hA0

example : torusRicciBallGrowth.A (3 / 5) = 0 :=
  torusRicciBallGrowth.A_saturate (s := (3 / 5 : ℝ))
    (show (1 / 2 : ℝ) < 3 / 5 by norm_num)

/-! ## 4. The derived `UniformMeasureGrowth` constants and the exhaustion radius -/

example : torusRicciBallGrowth.toUniformMeasureGrowth.C = 4 := by
  change (2 : ℝ≥0) ^ (1 + 1) = 4
  norm_num

example : torusRicciBallGrowth.toUniformMeasureGrowth.K = 1 := rfl

example : torusRicciBallGrowth.toUniformMeasureGrowth.m (1 / 4) = (1 / 4 : ℝ≥0) := by
  change (radialVolume torusA (1 / 4)).toNNReal = (1 / 4 : ℝ≥0)
  rw [torusRadialVolume_of_le_half (by norm_num) (by norm_num),
    show 4 * ((1 / 4 : ℝ)) ^ 2 = 1 / 4 by norm_num,
    Real.toNNReal_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  rfl

example : torusRicciBallGrowth.toUniformMeasureGrowth.R = 1 / 4 := rfl

/-- The exhaustion radius is *exactly* half the horizon: `2R = T = 1/2`. -/
example : 2 * (torusRicciBallGrowth.R : ℝ) = torusRicciBallGrowth.T := by
  change 2 * ((1 / 4 : ℝ≥0) : ℝ) = 1 / 2
  norm_num

/-- `R = 1/4` exhausts the torus exactly: the whole space is in the ball of radius
`2R = 1/2`, which is the (attained) diameter. -/
example : (univ : Set (GHSpace.Rep (toGHSpace FlatTorus))) ⊆ closedBall torusZero (1 / 2) := by
  intro x _
  rw [mem_closedBall, ← torusEquiv.dist_eq]
  have hz : torusEquiv torusZero = (0, 0) := by simp [torusZero]
  rw [hz]
  exact torus_dist_le_half _ _

/-- The exhaustion radius cannot be decreased: two points are at distance exactly `1/2`. -/
example : dist (torusEquiv.symm ((0 : AddCircle (1 : ℝ)), 0))
    (torusEquiv.symm ((((1 : ℝ) / 2 : ℝ) : AddCircle (1 : ℝ)), 0)) = 1 / 2 :=
  torus_nondegenerate

/-! ## 5. The measure is transported along the canonical isometry (not assumed) -/

example : torusMeasure = Measure.map torusEquiv.symm volume := rfl
example : torusMeasureOf (toGHSpace FlatTorus) = torusMeasure := torusMeasureOf_apply_member

end ReviewAudit
