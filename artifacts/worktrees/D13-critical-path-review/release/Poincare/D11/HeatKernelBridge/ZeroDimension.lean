/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D11-heat-kernel-manifold-bridge)
-/

import Poincare.D11.HeatKernelBridge.InitialCondition

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D11.HeatKernelBridge.ZeroDimension

**D11 heat-kernel bridge, part 5: a full D7 instantiation in dimension zero.**

In dimension `0` the Euclidean space `EuclideanSpace ℝ (Fin 0)` is a single point and its Lebesgue
measure is the Dirac measure at that point (`volume_euclideanSpace_eq_dirac`). Consequently every
function on it is integrable, the weak initial condition of `InitialCondition.lean` upgrades to the
literal D7 pointwise initial condition, and the explicit D10 kernel yields a *genuine*
`Poincare.D7.HeatKernel.HeatKernelData`:

`flatHeatKernelData_zero = (flatHeatKernelCore 0).toHeatKernelData flatHeatKernelCore_fullInitialCondition_zero`.

This is the exact sense in which the D7 interface is fully instantiated by the D10 kernel: in
positive dimensions the literal pointwise initial condition quantifies over non-integrable
continuous test functions, for which the Bochner integral is definitionally `0`, so the bridge
proves the weak (distributional) form instead and records the literal field as
`HeatKernelCore.FullInitialCondition`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter Real
open scoped Topology InnerProductSpace Laplacian RealInnerProductSpace

namespace Poincare.D11.HeatKernelBridge

open Poincare.D10.HeatKernelEuclidean

/-- Lebesgue measure on the zero-dimensional Euclidean space is the Dirac measure at the origin. -/
theorem volume_euclideanSpace_fin_zero :
    (volume : Measure (EuclideanSpace ℝ (Fin 0))) =
      Measure.dirac (0 : EuclideanSpace ℝ (Fin 0)) :=
  volume_euclideanSpace_eq_dirac (ι := Fin 0)

/-- Every function on the zero-dimensional Euclidean space is integrable for Lebesgue measure. -/
theorem integrable_euclideanSpace_fin_zero (f : EuclideanSpace ℝ (Fin 0) → ℝ) :
    Integrable f volume := by
  rw [volume_euclideanSpace_fin_zero]
  exact integrable_dirac (by simp)

/-- In dimension `0` the weak initial condition is the full D7 pointwise initial condition. -/
theorem flatHeatKernelCore_fullInitialCondition_zero :
    (flatHeatKernelCore 0).FullInitialCondition := by
  intro x f hf
  have hx : x = (0 : EuclideanSpace ℝ (Fin 0)) := Subsingleton.elim x 0
  subst hx
  rw [show (flatHeatKernelCore 0).volume = Measure.dirac (0 : EuclideanSpace ℝ (Fin 0)) from
    volume_euclideanSpace_fin_zero]
  have hfun : (fun t : ℝ => ∫ y, (flatHeatKernelCore 0).kernel 0 y t * f y
        ∂Measure.dirac (0 : EuclideanSpace ℝ (Fin 0)))
      = fun t : ℝ => (flatHeatKernelCore 0).kernel 0 0 t * f 0 := by
    funext t
    rw [integral_dirac]
  rw [hfun]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  show f 0 = flatKernel 0 0 0 t * f 0
  rw [flatKernel_of_pos 0 0 0 ht]
  simp [gaussianKernel]

/-- **The explicit D10 Euclidean heat kernel as a full D7 heat-kernel datum in dimension `0`.** -/
noncomputable def flatHeatKernelData_zero :
    Poincare.D7.HeatKernel.HeatKernelData (EuclideanSpace ℝ (Fin 0)) :=
  (flatHeatKernelCore 0).toHeatKernelData flatHeatKernelCore_fullInitialCondition_zero

@[simp]
theorem flatHeatKernelData_zero_kernel (x y : EuclideanSpace ℝ (Fin 0)) (t : ℝ) :
    flatHeatKernelData_zero.kernel x y t = flatKernel 0 x y t := rfl

@[simp]
theorem flatHeatKernelData_zero_volume :
    flatHeatKernelData_zero.volume = volume := rfl

/-- The dimension-zero full datum forgets back to the bridge core. -/
theorem flatHeatKernelData_zero_toCore :
    flatHeatKernelData_zero.toCore = flatHeatKernelCore 0 := rfl

end Poincare.D11.HeatKernelBridge
