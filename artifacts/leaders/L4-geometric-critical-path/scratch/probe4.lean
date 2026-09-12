import Poincare.L4.Compactness.MeasureGrowthCovers
open MeasureTheory Set Metric
#check (fun (a : ℕ∞) => (a : ℝ≥0∞))
#check @ENat.toENNReal
#check @ENat.coe_toENNReal
#check @ENat.toENNReal_le_toENNReal
#check @ENat.toENNReal_lt_toENNReal
#check @ENat.toENNReal_inj
#check @ENat.toENNReal_top
example (a : ℕ∞) (n : ℕ) (h : (a : ℝ≥0∞) ≤ ((n : ℕ) : ℝ≥0∞)) : a ≤ (n : ℕ∞) := by
  exact ENat.toENNReal_le_toENNReal.mp h
