import Poincare.D13.HeatKernelBridge.GeometricRepair

open Poincare.D13.HeatKernelBridge
open MeasureTheory Filter
open scoped Topology

-- Exact types of the geometric-repair companion declarations (semantic transcript).

-- Part 1: the geometric operator condition and its counterexample exclusion.
#check @AnnihilatesConstants
#check @AnnihilatesConstants.laplacian_one
#check @AnnihilatesConstants.laplacian_one_apply
#check @not_isAnnihilatesConstants_refutingSpacetime
#check @exists_isClosedRiemannianManifold_not_isAnnihilatesConstants
#check @punitDiracSpacetime
#check @punitDiracSpacetime_isClosedRiemannianManifold
#check @isAnnihilatesConstants_punitDiracSpacetime
#check @flatHeatSpacetime_laplacian_one

-- Part 2: the Laplacian-only repair is still refuted through the free time derivative.
#check @adversarialTimeDerivativeSpacetime
#check @adversarialTimeDerivativeSpacetime_heatOperator
#check @adversarialTimeDerivativeSpacetime_isClosedRiemannianManifold
#check @isAnnihilatesConstants_adversarialTimeDerivativeSpacetime
#check @not_exists_isHeatKernelV1_adversarialTimeDerivativeSpacetime
#check @not_isHeatKernel_of_laplacian_zero_timeDerivative_id
#check @not_isHeatKernelV1_of_laplacian_zero_timeDerivative_id
#check @not_forall_annihilatesConstants_implies_exists_snapshot_kernel_of_refuting
#check @not_forall_annihilatesConstants_implies_exists_snapshot_kernel

-- Part 3: the time-derivative repair is vacuous; snapshot and PDE predicates are incomparable.
#check @flatSnapshotSpacetime
#check @flatSnapshotSpacetime_heatOperator_eq_zero
#check @flatKernelRescaled
#check @flatKernelRescaled_isHeatKernelV1
#check @flatKernel_laplacian_snapshot_ne_zero_of_pos
#check @flatKernelRescaled_not_isHeatKernelPDE
#check @not_forall_isHeatKernelV1_imp_isHeatKernelPDE
#check @snapshot_pde_predicates_incomparable

-- Part 4: the statement-level repaired interface (stated, not proved) and its consistency checks.
#check @HeatKernelExistenceStatementPDE
#check @HeatKernelDataExistenceStatement
#check @heatKernelDataExistenceStatement_implies_pde
#check @heatKernelDataExistenceStatement_conclusion_punit
#check @not_both_isClosedRiemannianManifold_and_isAnnihilatesConstants_refutingSpacetime

-- The repaired statements are `Prop`s, exactly like the legacy blocked statement.
#check (HeatKernelExistenceStatementPDE : Prop)
#check (HeatKernelDataExistenceStatement : Prop)

-- Axiom cones of the headline declarations.
#print axioms not_isAnnihilatesConstants_refutingSpacetime
#print axioms not_forall_annihilatesConstants_implies_exists_snapshot_kernel
#print axioms flatKernelRescaled_isHeatKernelV1
#print axioms flatKernelRescaled_not_isHeatKernelPDE
#print axioms snapshot_pde_predicates_incomparable
#print axioms heatKernelDataExistenceStatement_implies_pde
#print axioms heatKernelDataExistenceStatement_conclusion_punit

-- The repaired conclusion on the datum that refutes the snapshot statement.
#check @exists_isHeatKernelPDE_of_punit_dirac_zero
#check @heatKernelExistenceStatementPDE_conclusion_punit
#check @heatKernelExistenceStatementPDE_conclusion_adversarial
#check @heatKernelDataExistenceStatement_conclusion_adversarial
#print axioms heatKernelExistenceStatementPDE_conclusion_adversarial
#print axioms heatKernelDataExistenceStatement_conclusion_adversarial
