import Poincare.D13.HeatKernelBridge.DataRefutation
import Poincare.D7.HeatKernel.DataStatus

open Poincare.D13.HeatKernelBridge
open MeasureTheory Filter
open scoped Topology ENNReal

-- The two-point refuting model satisfies the repaired hypothesis class ...
#check @twoPointSpacetime
#check @isClosedRiemannianManifold_twoPointSpacetime
#check @isAnnihilatesConstants_twoPointSpacetime
-- ... and admits no PDE kernel and no strictly positive legacy datum.
#check @not_exists_isHeatKernelPDE_twoPointSpacetime
#check @not_exists_heatKernelData_twoPointSpacetime
#check @not_heatKernelExistenceStatementPDE
#check @not_heatKernelDataExistenceStatement
-- The general schemas.
#check @eq_of_hasDerivAt_zero_of_pos
#check @not_exists_isHeatKernelPDE_of_laplacian_eq_zero
#check @not_exists_heatKernelData_of_laplacian_eq_zero
#check @not_heatKernelExistenceStatementPDE_of_refuting
#check @not_heatKernelDataExistenceStatement_of_refuting
-- The exact failure mode: the bare interface is inhabited with C_lo = 0.
#check @twoPointDegenerateData
#check @twoPointDegenerateData_C_lo
#check @twoPointDegenerateData_not_strictly_positive
#check @twoPoint_data_scope
-- The positive counterpart on the honest flat family.
#check @FlatCorrectedDomainExistence
#check @flatCorrectedDomainExistence_proved
#check @correctedDomain_is_exact_scope
-- D7-level consumption.
#check @Poincare.D7.HeatKernel.not_exists_heatKernelData_strictlyPositive_twoPoint
#check @Poincare.D7.HeatKernel.data_interface_inhabited_with_zero_lower_constant
#check @Poincare.D7.HeatKernel.data_level_target_refuted
#check @Poincare.D7.HeatKernel.corrected_domain_flat_statement_survives
#check @Poincare.D7.HeatKernel.data_status_summary
#print axioms not_heatKernelDataExistenceStatement
#print axioms not_heatKernelExistenceStatementPDE
#print axioms twoPointDegenerateData
#print axioms twoPoint_data_scope
#print axioms flatCorrectedDomainExistence_proved
#print axioms Poincare.D7.HeatKernel.data_status_summary
