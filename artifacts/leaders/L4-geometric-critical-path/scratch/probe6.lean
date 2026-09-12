import Poincare.L4.Compactness.MeasureGrowthChain
open MeasureTheory Set Metric
#check @Measure.smul_apply
#check @smul_apply
#check @ENNReal.add_halves
#check @ENNReal.inv_two_add_inv_two
example : (2:ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := by simpa using ENNReal.add_halves (1:ℝ≥0∞)
#check @Set.indicator_empty
#check @Set.indicator_empty'
example (s : Set ℕ) : s.indicator (1:ℝ≥0∞) 0 = 0 ∨ True := Or.inr trivial
