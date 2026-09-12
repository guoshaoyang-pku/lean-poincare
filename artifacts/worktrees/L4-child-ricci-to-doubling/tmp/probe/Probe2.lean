import Poincare.L4.Compactness.RicciToDoublingHyperbolic

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace Probe

def J : ℕ → ℝ → ℝ
  | 0, x => x
  | 1, x => Real.cosh x - 1
  | (d + 2), x => ((Real.sinh x) ^ (d + 1) * Real.cosh x - ((d : ℝ) + 1) * J d x) / ((d : ℝ) + 2)
termination_by d _ => d
decreasing_by omega

#check @J.eq_1
#check @J.eq_2
#check @J.eq_3
#print J.eq_3

example (x : ℝ) : J 2 x = ((Real.sinh x) ^ 1 * Real.cosh x - 1 * J 0 x) / 2 := by
  rw [J.eq_3]

end Probe
