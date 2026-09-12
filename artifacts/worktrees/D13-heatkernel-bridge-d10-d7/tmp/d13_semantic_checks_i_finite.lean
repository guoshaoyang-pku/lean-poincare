-- D13 ninth invocation: semantic transcript for the pinned-operator finite existence theorem.
import Poincare.D13.HeatKernelBridge.FiniteSpaceHeat
import Poincare.D7.HeatKernel.FiniteStatus

open MeasureTheory Filter
open scoped Topology

-- the pinned operator class and its structural theorems
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.laplacian
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.laplacian_one
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.laplacian_selfAdjoint
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.laplacian_ne_zero
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.kernel_pos
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_smul_add
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_smul_column_sum
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_smul_mulVec_sum
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_smul_mulVec_nonneg
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_smul_mulVec_abs_sum_le
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.laplacian_dirichlet_identity
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.laplacian_dirichlet_nonneg
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.laplacian_quadraticForm_nonpos

-- the kernel and its interface-level laws
#check @Poincare.D13.HeatKernelBridge.finiteHeatKernel
#check @Poincare.D13.HeatKernelBridge.finiteHeatKernel_pos
#check @Poincare.D13.HeatKernelBridge.finiteHeatKernel_semigroup
#check @Poincare.D13.HeatKernelBridge.finiteHeatKernel_hasDerivAt
#check @Poincare.D13.HeatKernelBridge.finiteHeatKernel_dirac
#check @Poincare.D13.HeatKernelBridge.finiteHeatKernelData
#check @Poincare.D13.HeatKernelBridge.finiteHeatKernelDataV1
#check @Poincare.D13.HeatKernelBridge.finiteHeatSpacetime_isClosedRiemannian
#check @Poincare.D13.HeatKernelBridge.finite_isHeatKernelPDE
#check @Poincare.D13.HeatKernelBridge.FinitePinnedHeatExistenceStatement
#check @Poincare.D13.HeatKernelBridge.finitePinnedHeatExistenceStatement_proved
#check @Poincare.D13.HeatKernelBridge.finite_pinned_scope
#check @Poincare.D13.HeatKernelBridge.completeGraphOperator

-- D7-level consumption
#check @Poincare.D7.HeatKernel.finite_pinned_kernel_exists
#check @Poincare.D7.HeatKernel.finite_pinned_operator_structure
#check @Poincare.D7.HeatKernel.finite_pinned_legacy_datum
#check @Poincare.D7.HeatKernel.finite_pinned_dataV1
#check @Poincare.D7.HeatKernel.finite_pinned_operator_dissipative
#check @Poincare.D7.HeatKernel.finite_pinned_max_principle
#check @Poincare.D7.HeatKernel.finite_pinned_spacetime_closed
#check @Poincare.D7.HeatKernel.finite_pinned_kernel_nondegenerate
#check @Poincare.D7.HeatKernel.finite_heat_status_summary

-- axiom cones of the main declarations
#print axioms Poincare.D13.HeatKernelBridge.finitePinnedHeatExistenceStatement_proved
#print axioms Poincare.D13.HeatKernelBridge.finite_isHeatKernelPDE
#print axioms Poincare.D13.HeatKernelBridge.finiteHeatKernel_semigroup
#print axioms Poincare.D13.HeatKernelBridge.finiteHeatKernel_dirac
#print axioms Poincare.D13.HeatKernelBridge.completeGraphOperator
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.laplacian_quadraticForm_nonpos
#print axioms Poincare.D7.HeatKernel.finite_pinned_operator_dissipative
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_smul_mulVec_nonneg
#print axioms Poincare.D7.HeatKernel.finite_pinned_max_principle
#print axioms Poincare.D7.HeatKernel.finite_heat_status_summary

-- the statement is non-vacuous: it has an explicit model, and the model is non-degenerate
example : Poincare.D13.HeatKernelBridge.FinitePinnedHeatExistenceStatement :=
  Poincare.D13.HeatKernelBridge.finitePinnedHeatExistenceStatement_proved

example (G : Poincare.D13.HeatKernelBridge.FiniteHeatOperator (Fin 2)) :
    ∃ K : Fin 2 → Fin 2 → ℝ → ℝ,
      Poincare.D13.HeatKernelBridge.IsHeatKernelPDE
        (Poincare.D13.HeatKernelBridge.finiteHeatSpacetime G)
        (Poincare.D12.HeatDomain.AdmissibleTestClass.continuousIntegrableClass
          (Measure.count : Measure (Fin 2))) K :=
  Poincare.D7.HeatKernel.finite_pinned_kernel_exists G
