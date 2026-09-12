import Poincare.D13.HeatKernelBridge.PDERepair

open Poincare.D13.HeatKernelBridge
open MeasureTheory Filter
open scoped Topology

-- Exact types of the PDE-repair companion declarations (semantic transcript).
#check @IsHeatKernelPDE.v2
#check @IsHeatKernelPDE
#check @IsHeatKernelPDE.solvesPDE_hasDerivAt
#check @HeatKernelDataV1.toHeatSpacetime
#check @HeatKernelDataV1.kernel_pos_of_dist_le_one
#check @IsHeatKernelPDE.of_dataV1
#check @IsHeatKernelPDE.of_dataV1_integrableClass
#check @IsHeatKernelPDE.of_dataV1_ccClass
#check @flatHeatSpacetime_eq_toHeatSpacetime
#check @flat_isHeatKernelPDE_integrable
#check @flat_isHeatKernelPDE_cc
#check @flat_pde_repaired_scope
#check @not_forall_isHeatKernelPDE_imp_isHeatKernelV1

-- The legacy snapshot predicate is untouched: the repaired predicate is a new name.
#check @Poincare.D7.HeatKernel.IsHeatKernel
#check @Poincare.D7.HeatKernel.IsHeatKernelV1
