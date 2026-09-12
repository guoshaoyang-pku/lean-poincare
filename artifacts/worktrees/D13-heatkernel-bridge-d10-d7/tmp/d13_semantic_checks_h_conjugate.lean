import Poincare.D13.HeatKernelBridge.ConjugateHeatBridge
import Poincare.D7.ConjugateHeat.Status

open Poincare.D13.HeatKernelBridge
open Poincare.D7.ConjugateHeat
open MeasureTheory Filter
open scoped Topology

-- The schematic conjugate-heat existence statement is refuted by the two-point datum with the
-- identity Laplacian ...
#check @conjugateRefutingSpacetime
#check @isRiemannianConjugateHeatSpacetime_conjugateRefuting
#check @not_exists_isConjugateHeatKernel_conjugateRefuting
#check @Poincare.D13.HeatKernelBridge.not_conjugateHeatKernelExistenceStatement
-- ... through the general schema (injective Laplacian, zero backward time/curvature operators).
#check @conjugateHeat_eq_neg_laplacian
#check @eq_zero_of_conjugateHeat_eq_zero_of_injective
#check @not_exists_isConjugateHeatKernel_of_injective_laplacian
#check @not_conjugateHeatKernelExistenceStatement_of_refuting
-- The time-reversal filter fact and the corrected-domain predicate with the genuine PDE field.
#check @tendsto_const_sub_nhdsLT
#check @IsConjugateHeatKernelPDE.v2
#check @IsConjugateHeatKernelPDE
#check @IsConjugateHeatKernelPDE.solvesPDE_hasDerivAt
-- The bridge transport: any corrected-domain datum, time-reversed, inhabits the repaired
-- predicate.
#check @HeatKernelDataV1.toConjugateHeatSpacetime
#check @IsConjugateHeatKernelPDE.of_dataV1
#check @IsConjugateHeatKernelPDE.of_dataV1_integrableClass
#check @IsConjugateHeatKernelPDE.of_dataV1_ccClass
-- The flat D10 model in every dimension, and the unrepaired predicate refuted there.
#check @flatConjugateHeatSpacetime
#check @flatConjugateKernel
#check @flat_isConjugateHeatKernelPDE_integrableClass
#check @flat_isConjugateHeatKernelPDE_cc
#check @flatConjugate_not_isConjugateHeatKernel
#check @flat_conjugate_repaired_scope
-- Structural consequences: symmetry, unit mass, mass conservation, Chapman-Kolmogorov.
#check @flatConjugateKernel_symm
#check @flatConjugateKernel_mass
#check @flatConjugateKernel_mass_eq
#check @flatConjugateKernel_semigroup
#check @not_forall_isConjugateHeatKernelPDE_imp_isConjugateHeatKernel
-- The positive counterpart and the exact scope.
#check @FlatConjugateCorrectedDomainExistence
#check @flatConjugateCorrectedDomainExistence_proved
#check @conjugateCorrection_is_exact_scope
-- D7-level consumption.
#check @Poincare.D7.ConjugateHeat.not_conjugateHeatKernelExistenceStatement
#check @Poincare.D7.ConjugateHeat.ConjugateHeatKernelCorrectedDomainStatement
#check @Poincare.D7.ConjugateHeat.conjugateHeatKernelCorrectedDomainStatement_proved
#check @Poincare.D7.ConjugateHeat.exists_flatConjugateKernelPDE
#check @Poincare.D7.ConjugateHeat.conjugate_heat_mass_and_symmetry
#check @Poincare.D7.ConjugateHeat.conjugate_heat_chapman_kolmogorov
#check @Poincare.D7.ConjugateHeat.conjugate_heat_snapshot_refuted
#check @Poincare.D7.ConjugateHeat.conjugate_heat_status_summary
#print axioms Poincare.D13.HeatKernelBridge.not_conjugateHeatKernelExistenceStatement
#print axioms conjugateRefutingSpacetime
#print axioms IsConjugateHeatKernelPDE.of_dataV1
#print axioms flat_isConjugateHeatKernelPDE_integrableClass
#print axioms flat_conjugate_repaired_scope
#print axioms conjugateCorrection_is_exact_scope
#print axioms Poincare.D7.ConjugateHeat.conjugate_heat_status_summary
