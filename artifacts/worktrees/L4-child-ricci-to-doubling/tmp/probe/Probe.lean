import Poincare.L4.Compactness.RicciToDoublingHyperbolic

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace Probe

/-- Recursive explicit antiderivative of `sinh^d`. -/
def J : ℕ → ℝ → ℝ
  | 0, x => x
  | 1, x => Real.cosh x - 1
  | (d + 2), x => ((Real.sinh x) ^ (d + 1) * Real.cosh x - ((d : ℝ) + 1) * J d x) / ((d : ℝ) + 2)
termination_by d _ => d
decreasing_by omega

example (x : ℝ) : J 0 x = x := by simp [J]
example (x : ℝ) : J 1 x = Real.cosh x - 1 := by simp [J]
example (x : ℝ) : J 2 x = ((Real.sinh x) ^ 1 * Real.cosh x - 1 * J 0 x) / 2 := by
  rw [J]

end Probe
