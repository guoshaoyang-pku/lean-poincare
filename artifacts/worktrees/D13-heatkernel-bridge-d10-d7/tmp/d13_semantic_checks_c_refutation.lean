import Poincare.D13.HeatKernelBridge.StatementRefutation
import Poincare.D7.HeatKernel.StatementStatus

open Poincare.D13.HeatKernelBridge
open Poincare.D7.HeatKernel
open MeasureTheory Filter
open scoped Topology

-- Exact types of the statement-refutation declarations (semantic transcript).
#check @refutingSpacetime
#check @refutingSpacetime_volume
#check @refutingSpacetime_laplacian
#check @refutingSpacetime_laplacian_apply
#check @refutingSpacetime_timeDerivative
#check @refutingSpacetime_timeDerivative_apply
#check @refutingSpacetime_heatOperator
#check @refutingSpacetime_isClosedRiemannianManifold
#check @subsingleton_measurableSpace_punit
#check @not_isHeatKernel_of_laplacian_id_timeDerivative_zero
#check @not_isHeatKernelV1_of_laplacian_id_timeDerivative_zero
#check @not_heatKernelExistenceStatement_of_refuting
#check @not_heatKernelExistenceStatementV1_of_refuting
#check @not_heatKernelExistenceStatement
#check @Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatementV1
#check @Poincare.D7.HeatKernel.not_heatKernelExistenceStatementV1_of_legacy_refutation
#check @Poincare.D7.HeatKernel.not_heatKernelExistenceStatementV1

-- The compact-scope data-level existential equivalence (bridge losslessness, existential form).
#check @exists_v1_iff_exists_legacy

-- The two refuted D7 existence statements, at their exact (universe-polymorphic) types.
#print Poincare.D7.HeatKernel.HeatKernelExistenceStatement
#print Poincare.D7.HeatKernel.HeatKernelExistenceStatementV1

-- Cross-checked consumption: the D13 refutation and the D7-equivalence-transported refutation.
example : ¬ Poincare.D7.HeatKernel.HeatKernelExistenceStatement :=
  Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatement

example : ¬ Poincare.D7.HeatKernel.HeatKernelExistenceStatementV1 :=
  Poincare.D7.HeatKernel.not_heatKernelExistenceStatementV1

example : ¬ Poincare.D7.HeatKernel.HeatKernelExistenceStatementV1 :=
  Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatementV1

-- Axiom transcript for the existential equivalence, the counterexample and both refutation routes.
#print axioms Poincare.D13.HeatKernelBridge.exists_v1_iff_exists_legacy
#print axioms Poincare.D13.HeatKernelBridge.refutingSpacetime
#print axioms Poincare.D13.HeatKernelBridge.refutingSpacetime_isClosedRiemannianManifold
#print axioms Poincare.D13.HeatKernelBridge.not_isHeatKernel_of_laplacian_id_timeDerivative_zero
#print axioms Poincare.D13.HeatKernelBridge.not_isHeatKernelV1_of_laplacian_id_timeDerivative_zero
#print axioms Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatement
#print axioms Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatementV1
#print axioms Poincare.D7.HeatKernel.not_heatKernelExistenceStatementV1_of_legacy_refutation
#print axioms Poincare.D7.HeatKernel.not_heatKernelExistenceStatementV1
