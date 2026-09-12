/-
SEMREV-L3 independent review — Stage A: instance/type diagnostics.

This file is NOT part of the reviewed package. It is compiled by the reviewer against the
reviewed package's environment (`lake env lean`) and prints the exact types, the resolved
`NormedAddCommGroup` instance for the Pi type used by the D12 obligation, and the topological
reading of the discharged statement.
-/

import Poincare.L3.HeatTimeDeriv.All

open MeasureTheory Real Filter
open scoped Topology InnerProductSpace Laplacian RealInnerProductSpace

namespace SemrevL3

/-! ## 1. What normed structure does the D12 `HasDerivAt` live in? -/

#synth NormedAddCommGroup (EuclideanSpace ℝ (Fin 3) → ℝ)
#synth NormedSpace ℝ (EuclideanSpace ℝ (Fin 3) → ℝ)
#synth TopologicalSpace (EuclideanSpace ℝ (Fin 3) → ℝ)

-- The instance name and its statement (to see whether it is the sup norm or the product
-- topology / a seminorm).
#print Pi.normedAddCommGroup

/-- The resolved instance, at the level of the *name* Lean chose. -/
example : (inferInstance : NormedAddCommGroup (EuclideanSpace ℝ (Fin 3) → ℝ)) =
    inferInstance := rfl

/-! ## 2. Exact types of the cited L3 declarations -/

#check @Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_holds
#check @Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_pointwise
#check @Poincare.L3.HeatTimeDeriv.hasDerivAt_heatOperator
#check @Poincare.L3.HeatTimeDeriv.hasDerivAt_heatOperator_kernelLaplacian
#check @Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_apply
#check @Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_apply_kernelLaplacian
#check @Poincare.L3.HeatTimeDeriv.uniformMildToClassicalBridge_holds
#check @Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_BCF
#check @Poincare.L3.HeatTimeDeriv.timeDerivBCF
#check @Poincare.L3.HeatTimeDeriv.timeDerivBCF_apply
#check @Poincare.L3.HeatTimeDeriv.heatConv_classicalHeatSolution
#check @Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_const
#check @Poincare.L3.HeatTimeDeriv.integral_timeDerivKernel_mul_const
#check @Poincare.L3.HeatTimeDeriv.heatOperator_const

/-! ## 3. Exact statements of the residuals and of the D12 obligation -/

#print Poincare.L3.HeatTimeDeriv.UniformMildToClassicalBridge
#print Poincare.L3.HeatTimeDeriv.SpatialLaplacianBridge
#print Poincare.D12.ParabolicLocal.mildToClassicalBridge
#print Poincare.L3.HeatTimeDeriv.KernelClassicalHeatSolution
#print Poincare.D12.ParabolicLocal.BUCn
#print Poincare.D12.ParabolicLocal.BCFn

end SemrevL3
