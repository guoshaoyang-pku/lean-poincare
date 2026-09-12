import Poincare.D13.HeatKernelBridge.DataRefutation
import Poincare.D7.ConjugateHeat.Blocked

open MeasureTheory Filter
open scoped Topology
open Poincare.D7.ConjugateHeat
open Poincare.D13.HeatKernelBridge

#synth BorelSpace Bool
#check @ConjugateHeatKernelExistenceStatement
#check @IsConjugateHeatKernel
#check @ConjugateHeatSpacetime.conjugateHeat
#check @IsRiemannianConjugateHeatSpacetime
#check @Poincare.D7.HeatKernel.IsClosedRiemannianManifold
#check @Poincare.D13.HeatKernelBridge.HeatKernelDataV1.IsIntegrableClassVariant
#check @Poincare.D13.HeatKernelBridge.HeatKernelDataV1.initialConditionFor
#check @Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_integrableClassVariant
#check @Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_kernel
#check @Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_kernel_eq_gaussian
#check @Poincare.D10.HeatKernelEuclidean.gaussianKernel_pos
#check @tendsto_nhdsWithin_iff
#check @Filter.Tendsto.comp
#check @HasDerivAt.comp
#check @HasDerivAt.const_sub
#check @hasDerivAt_id
example : Function.Injective (LinearMap.id : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ)) := fun _ _ h => h
