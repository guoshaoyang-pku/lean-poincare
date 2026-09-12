import Poincare.L4.Compactness.MeasureGrowthCovers
open MeasureTheory Set Metric

#check @Nat.ceil
#check @Nat.le_ceil
#check @Nat.ceil_le
example : FloorSemiring ℝ≥0 := inferInstance
example (q : ℝ≥0) : q ≤ (⌈q⌉₊ : ℝ≥0) := by exact Nat.le_ceil q
#check @ENat.toNat
#check @ENat.natCast_toNat
#check @ENat.floor_ne_top
#check @ENat.floor_lt_top
#check @ENat.coe_le_coe
#check @ENat.coe_toNat
#check @ENNReal.coe_le_coe
