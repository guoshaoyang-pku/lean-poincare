import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
#check @ENNReal.ofReal_inv_of_pos
#check @ENNReal.ofReal_div_of_pos
#check @ENNReal.ofReal_inv
example : ENNReal.ofReal ((1:ℝ)/2) = 2⁻¹ := by
  rw [show (1:ℝ)/2 = (2:ℝ)⁻¹ by norm_num]
  rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2)]
  norm_num
