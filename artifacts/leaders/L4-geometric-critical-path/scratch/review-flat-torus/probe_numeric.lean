import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
open scoped Topology ENNReal NNReal
open Set Metric MeasureTheory
noncomputable section
namespace Probe

example : (4 : ℝ≥0∞) * 9⁻¹ = 4 / 9 := rfl
example : ENNReal.ofReal (4 / 9 : ℝ) = 4 / 9 := by
  rw [show (4 / 9 : ℝ) = 4 * (9 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),
    ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 9), ENNReal.ofReal_ofNat]
  rfl
example (x : ℝ) : ENNReal.ofReal (1/2) * ENNReal.ofReal (1/2) = (1/4 : ℝ≥0∞) := by
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2),
      show (1/2:ℝ) * (1/2) = (4:ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 4)]
  norm_num
example : ENNReal.ofReal (2/3 : ℝ) * ENNReal.ofReal (2/3) = (4/9 : ℝ≥0∞) := by
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2/3),
      show (2/3:ℝ) * (2/3) = 4 * (9:ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),
      ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 9), ENNReal.ofReal_ofNat]
  rfl
example (a b : ℝ) : (a ≤ b) ∨ (b < a) := le_or_gt a b
end Probe
