import Poincare.L4.Compactness.MeasureGrowthChain
open MeasureTheory Set Metric
#check @dite_eq_left
#check @dif_pos
#check @ENNReal.mul_inv_cancel
#check @ENNReal.inv_mul_cancel
example : (2:ℝ≥0∞) * 2⁻¹ = 1 := by rw [ENNReal.mul_inv_cancel] <;> norm_num
example : (2:ℝ≥0∞)⁻¹ ≤ 2 * 2⁻¹ := by rw [ENNReal.mul_inv_cancel] <;> norm_num
example : (1:ℝ≥0∞) ≤ 2 * 2⁻¹ := by rw [ENNReal.mul_inv_cancel] <;> norm_num
