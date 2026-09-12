/-
Task `D9-parabolic-maximum-principle`: consolidated `#print axioms` audit.

Every declaration of the D9 cluster (`Interface`, `DiscreteComparison`,
`StateOnly`) is printed with `#print axioms`.  The expected output is either
"does not depend on any axioms" or one of the standard Lean/mathlib cones
`{propext}`, `{propext, Quot.sound}`, `{propext, Classical.choice, Quot.sound}`.
In particular no proof placeholder (`sorryAx`), no `axiom`, no `unsafe`, no
`native_decide` and no `proof_wanted` may appear.

The file is a driver only: it declares nothing and adds no mathematical content.
-/
import Poincare.D9.ParabolicMaximumPrinciple.Interface
import Poincare.D9.ParabolicMaximumPrinciple.DiscreteComparison
import Poincare.D9.ParabolicMaximumPrinciple.StateOnly

namespace Poincare.D9.ParabolicMaximumPrinciple

/-! ## `Interface` — scalar heat-type data and the comparison interface -/

#print axioms HeatTypeData
#print axioms HeatTypeData.driftTerm
#print axioms HeatTypeData.op
#print axioms HeatTypeData.op_apply
#print axioms IsSubsolution
#print axioms IsSupersolution
#print axioms IsSolution
#print axioms isSubsolution_of_isSolution
#print axioms isSupersolution_of_isSolution
#print axioms ComparisonPrincipleStatement
#print axioms zeroHeatTypeData
#print axioms zeroHeatTypeData_op
#print axioms isSolution_zeroHeatTypeData
#print axioms isSubsolution_zeroHeatTypeData
#print axioms isSupersolution_zeroHeatTypeData
#print axioms comparisonPrincipleStatement_zeroHeatTypeData

/-! ## `DiscreteComparison` — checked discrete comparison theorem -/

#print axioms MonotoneScheme
#print axioms comparison_of_monotoneScheme
#print axioms comparison_of_monotoneScheme_of_eq
#print axioms fdOperator
#print axioms fdStep
#print axioms fdStep_eq_convex
#print axioms fdStep_mono
#print axioms fdStep_mono_of_le
#print axioms fdMonotoneScheme
#print axioms GridSubsolution
#print axioms GridSupersolution
#print axioms grid_comparison_succ
#print axioms grid_comparison
#print axioms GridSolution
#print axioms gridSubsolution_of_gridSolution
#print axioms gridSupersolution_of_gridSolution
#print axioms grid_comparison_of_solution
#print axioms grid_solution_unique
#print axioms grid_le_of_constant_barrier
#print axioms gridSolution_zero

/-! ## `StateOnly` — named weak/strong/tensor maximum-principle statements -/

#print axioms WeakMaximumPrincipleStatement
#print axioms WeakMaximumPrincipleComparisonStatement
#print axioms StrongMaximumPrincipleStatement
#print axioms tensorQuad
#print axioms InPositiveCone
#print axioms IsNullVector
#print axioms TensorHeatData
#print axioms PositiveConeCondition
#print axioms DiffusionConeCondition
#print axioms HamiltonTensorMaximumPrincipleStatement
#print axioms zero_inPositiveCone
#print axioms DiagonalPositiveConeCondition
#print axioms diagonalPositiveConeCondition_hamilton

end Poincare.D9.ParabolicMaximumPrinciple
