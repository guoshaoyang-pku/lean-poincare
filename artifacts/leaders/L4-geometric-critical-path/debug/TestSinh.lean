import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.ExponentialBounds

example : Real.sinh (1 / 2) ≤ 1 := by
  rw [Real.sinh_eq]
  have hexp2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]
    norm_num
  have hexp2lt : Real.exp (1 / 2) < 2 := by
    nlinarith [Real.exp_pos (1 / 2), Real.exp_one_lt_three, hexp2,
      sq_nonneg (Real.exp (1 / 2) - 2)]
  have hnum : Real.exp (1 / 2) - Real.exp (-(1 / 2)) ≤ Real.exp (1 / 2) := by
    linarith [Real.exp_pos (-(1 / 2))]
  linarith
