/-
Task `D9-sobolev-parabolic-estimates`: consolidated kernel axiom audit.

Every declaration authored for this task lives in
`Poincare.D9.ParabolicEstimates.{Gronwall, Basic, MatrixModel, Statements}` and is
printed below with `#print axioms`.  The expected axiom cones are exactly

* `[]` (definitional declarations and structures),
* `[propext]`,
* `[propext, Classical.choice, Quot.sound]`.

Any occurrence of `sorryAx`, of a project axiom, of `unsafe`, `native_decide` or
`proof_wanted` would show up here and is forbidden by the task.
-/
import Poincare.D9.ParabolicEstimates.Statements

/-! ## Grönwall -/

#print axioms Poincare.D9.ParabolicEstimates.gronwall_energy_bound

/-! ## Abstract interface (`Basic`) -/

#print axioms Poincare.D9.ParabolicEstimates.energyDensity
#print axioms Poincare.D9.ParabolicEstimates.forcingEnergy
#print axioms Poincare.D9.ParabolicEstimates.EnergyFunctional
#print axioms Poincare.D9.ParabolicEstimates.EnergyFunctional.energy_nonneg
#print axioms Poincare.D9.ParabolicEstimates.EnergyFunctional.energy_eq_integral
#print axioms Poincare.D9.ParabolicEstimates.DirichletForm
#print axioms Poincare.D9.ParabolicEstimates.WeakSolution
#print axioms Poincare.D9.ParabolicEstimates.EnergyIdentityStatement
#print axioms Poincare.D9.ParabolicEstimates.ClassicalSolution
#print axioms Poincare.D9.ParabolicEstimates.ParabolicL2Bound
#print axioms Poincare.D9.ParabolicEstimates.parabolicL2Bound_of_energyIdentity
#print axioms Poincare.D9.ParabolicEstimates.young_integral
#print axioms Poincare.D9.ParabolicEstimates.zeroEnergyFunctional
#print axioms Poincare.D9.ParabolicEstimates.zeroDirichletForm
#print axioms Poincare.D9.ParabolicEstimates.zeroWeakSolution
#print axioms Poincare.D9.ParabolicEstimates.zeroClassicalSolution
#print axioms Poincare.D9.ParabolicEstimates.zero_parabolicL2Bound

/-! ## Semi-discrete matrix model (`MatrixModel`) -/

#print axioms Poincare.D9.ParabolicEstimates.matrixEnergy
#print axioms Poincare.D9.ParabolicEstimates.dirichletForm
#print axioms Poincare.D9.ParabolicEstimates.IsMatrixLaplacian
#print axioms Poincare.D9.ParabolicEstimates.matrixEnergy_nonneg
#print axioms Poincare.D9.ParabolicEstimates.matrixEnergy_eq_sum_sq
#print axioms Poincare.D9.ParabolicEstimates.dirichletForm_nonneg
#print axioms Poincare.D9.ParabolicEstimates.dirichletForm_symm
#print axioms Poincare.D9.ParabolicEstimates.matrixEnergy_young
#print axioms Poincare.D9.ParabolicEstimates.hasDerivAt_matrixEnergy
#print axioms Poincare.D9.ParabolicEstimates.continuous_matrixEnergy
#print axioms Poincare.D9.ParabolicEstimates.continuous_dirichletForm
#print axioms Poincare.D9.ParabolicEstimates.continuous_dotProduct
#print axioms Poincare.D9.ParabolicEstimates.SemiDiscreteHeatFlow
#print axioms Poincare.D9.ParabolicEstimates.SemiDiscreteHeatFlow.energy_identity
#print axioms Poincare.D9.ParabolicEstimates.SemiDiscreteHeatFlow.energy_deriv_le
#print axioms Poincare.D9.ParabolicEstimates.SemiDiscreteHeatFlow.energy_gronwall
#print axioms Poincare.D9.ParabolicEstimates.SemiDiscreteHeatFlow.weak_equation
#print axioms Poincare.D9.ParabolicEstimates.SemiDiscreteHeatFlow.matrixEnergyFunctional
#print axioms Poincare.D9.ParabolicEstimates.SemiDiscreteHeatFlow.matrixDirichletForm
#print axioms Poincare.D9.ParabolicEstimates.SemiDiscreteHeatFlow.matrixWeakSolution
#print axioms Poincare.D9.ParabolicEstimates.SemiDiscreteHeatFlow.matrixEnergyIdentity
#print axioms Poincare.D9.ParabolicEstimates.SemiDiscreteHeatFlow.matrixClassicalSolution
#print axioms Poincare.D9.ParabolicEstimates.forcingEnergy_count
#print axioms Poincare.D9.ParabolicEstimates.matrix_parabolicL2Bound
#print axioms Poincare.D9.ParabolicEstimates.dirichletForm_transpose_mul_self
#print axioms Poincare.D9.ParabolicEstimates.isMatrixLaplacian_transpose_mul_self
#print axioms Poincare.D9.ParabolicEstimates.isMatrixLaplacian_zero
#print axioms Poincare.D9.ParabolicEstimates.zeroHeatFlow

/-! ## State-only statements (`Statements`) -/

#print axioms Poincare.D9.ParabolicEstimates.ParabolicData
#print axioms Poincare.D9.ParabolicEstimates.ManifoldEnergyIdentity
#print axioms Poincare.D9.ParabolicEstimates.manifoldEnergyIdentity_of_data
#print axioms Poincare.D9.ParabolicEstimates.ParabolicL2AprioriEstimate
#print axioms Poincare.D9.ParabolicEstimates.ParabolicEnergyDissipationEstimate
#print axioms Poincare.D9.ParabolicEstimates.parabolicL2AprioriEstimate_iff
#print axioms Poincare.D9.ParabolicEstimates.SobolevScale
#print axioms Poincare.D9.ParabolicEstimates.ParabolicSmoothingEstimate
#print axioms Poincare.D9.ParabolicEstimates.ParabolicL2ToHkSmoothing
#print axioms Poincare.D9.ParabolicEstimates.SobolevEmbeddingStatement
#print axioms Poincare.D9.ParabolicEstimates.SobolevEmbeddingH1ToL6
#print axioms Poincare.D9.ParabolicEstimates.SobolevEmbeddingH2ToContinuous
#print axioms Poincare.D9.ParabolicEstimates.SobolevEmbeddingHkToContinuous
#print axioms Poincare.D9.ParabolicEstimates.RellichKondrachovStatement
#print axioms Poincare.D9.ParabolicEstimates.GagliardoNirenbergInterpolationStatement
#print axioms Poincare.D9.ParabolicEstimates.PoincareInequalityStatement
#print axioms Poincare.D9.ParabolicEstimates.ClosedManifoldParabolicL2AprioriEstimate
#print axioms Poincare.D9.ParabolicEstimates.ClosedManifoldParabolicEnergyDissipationEstimate
#print axioms Poincare.D9.ParabolicEstimates.ClosedManifoldParabolicSmoothingEstimate
#print axioms Poincare.D9.ParabolicEstimates.ClosedManifoldSobolevEmbeddingH1ToL6
#print axioms Poincare.D9.ParabolicEstimates.ClosedManifoldSobolevEmbeddingH2ToContinuous
#print axioms Poincare.D9.ParabolicEstimates.closedManifoldParabolicL2AprioriEstimate_iff
#print axioms Poincare.D9.ParabolicEstimates.closedManifoldParabolicSmoothingEstimate_iff
#print axioms Poincare.D9.ParabolicEstimates.zeroSobolevScale
#print axioms Poincare.D9.ParabolicEstimates.sobolevEmbedding_zero
#print axioms Poincare.D9.ParabolicEstimates.sobolevEmbeddingH1ToL6_zero
#print axioms Poincare.D9.ParabolicEstimates.sobolevEmbeddingH2ToContinuous_zero
#print axioms Poincare.D9.ParabolicEstimates.rellichKondrachov_zero
#print axioms Poincare.D9.ParabolicEstimates.poincare_zero
#print axioms Poincare.D9.ParabolicEstimates.parabolicSmoothingEstimate_zero
#print axioms Poincare.D9.ParabolicEstimates.unitSobolevScale
#print axioms Poincare.D9.ParabolicEstimates.sobolevEmbeddingH1ToL6_unit
#print axioms Poincare.D9.ParabolicEstimates.sobolevEmbeddingH2ToContinuous_unit
#print axioms Poincare.D9.ParabolicEstimates.poincare_unit
#print axioms Poincare.D9.ParabolicEstimates.matrixParabolicData
#print axioms Poincare.D9.ParabolicEstimates.parabolicL2AprioriEstimate_matrix
