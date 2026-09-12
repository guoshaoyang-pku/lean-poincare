/-
Task `D2-pde-foundation`: consolidated standard-axioms audit for the PDE
foundation.

Every declaration of `Poincare.Longrun.PDE` is printed with `#print axioms`.
The expected output is either "does not depend on any axioms" or the standard
Lean/mathlib triple `[propext, Classical.choice, Quot.sound]`; in particular no
proof placeholder may appear.
-/
import Poincare.Longrun.PDE.HeatGrid
import Poincare.Longrun.PDE.DiscreteMaximumPrinciple
import Poincare.Longrun.PDE.Energy
import Poincare.Longrun.PDE.ContinuousInterface

namespace Poincare.Longrun.PDE

/-! ## `HeatGrid` -/

#print axioms zeroExtend
#print axioms discreteLaplacian
#print axioms heatStep
#print axioms HeatGridEvolution
#print axioms heatStep_eq_discreteLaplacian
#print axioms HeatGridEvolution.step_eq_discreteLaplacian
#print axioms HeatGridEvolution.step_eq_heatStep
#print axioms HeatGridEvolution.step_eq_convex

/-! ## `DiscreteMaximumPrinciple` -/

#print axioms zeroExtend_le
#print axioms heatStep_le
#print axioms HeatGridEvolution.succ_le
#print axioms HeatGridEvolution.le_of_initial_le
#print axioms HeatGridEvolution.le_sup'_initial
#print axioms strict_grid_max_principle_max
#print axioms strict_grid_max_principle

/-! ## `Energy` -/

#print axioms energy
#print axioms convex_combo_sq_le
#print axioms heatStep_sq_le
#print axioms sum_shift_pred
#print axioms sum_shift_succ
#print axioms energy_heatStep_le
#print axioms energy_nonneg
#print axioms energy_step_le
#print axioms HeatGridEvolution.energy_succ_le
#print axioms HeatGridEvolution.energy_nonincreasing

/-! ## `ContinuousInterface` -/

#print axioms ContinuousHeatHypotheses
#print axioms ContinuousHeatMaximumPrincipleInterface
#print axioms continuousHeatHypotheses_zero
#print axioms continuousHeatHypotheses_affine
#print axioms continuousHeatHypotheses_quadratic
#print axioms continuousHeatMaxPrinciple_zero
#print axioms continuousHeatMaxPrinciple_of_timeIndependent
#print axioms continuousHeatMaxPrinciple_affine
#print axioms continuousHeatMaxPrinciple_quadratic

end Poincare.Longrun.PDE
