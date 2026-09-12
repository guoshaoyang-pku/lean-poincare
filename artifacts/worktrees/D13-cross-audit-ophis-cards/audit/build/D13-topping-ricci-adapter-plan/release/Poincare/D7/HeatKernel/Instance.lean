/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-heat-kernel-existence)
-/

import Poincare.D7.HeatKernel.Basic

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D7.HeatKernel.Instance

**D7 heat-kernel layer, part 4: a concrete inhabitant of the heat-kernel interface.**

`HeatKernelData` is an interface, and an interface with no inhabitant would be vacuous. This file
provides the simplest possible kernel-checked inhabitant: the one-point space `PUnit`, with the
Dirac measure at its unique point, the zero distance, dimension `0`, constants
`C_up = C_lo = c_up = c_lo = 1`, and the constant kernel `K x y t = 1`.

For the one-point space all four defining analytic properties hold definitionally or by a single
integral evaluation:

* the Gaussian upper and lower bounds are the trivial inequality `1 ≤ 1`;
* the semigroup property is `1 = ∫ z, 1 * 1 ∂δ = 1`;
* normalization is `∫ y, 1 ∂δ = 1`;
* the initial condition is `∫ y, 1 * f y ∂δ = f ()`, independent of `t`;
* the heat equation is the derivative of a constant.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D7.HeatKernel

/-- **The one-point heat kernel datum.** A concrete inhabitant of `HeatKernelData PUnit` with the
Dirac measure at the unique point and the constant kernel `1`. -/
noncomputable def punitHeatKernelData : HeatKernelData PUnit where
  volume := Measure.dirac PUnit.unit
  dist := fun _ _ => 0
  dim := 0
  C_up := 1
  c_up := 1
  C_lo := 1
  c_lo := 1
  kernel := fun _ _ _ => 1
  laplacian := 0
  dist_self := fun _ => rfl
  dist_nonneg := fun _ _ => le_refl 0
  dist_symm := fun _ _ => rfl
  c_up_pos := one_pos
  c_lo_pos := one_pos
  C_up_nonneg := zero_le_one
  C_lo_nonneg := zero_le_one
  kernel_nonneg := fun _ _ _ => zero_le_one
  gaussianUpperBound := by
    intro x y t ht
    simp [Real.rpow_zero]
  gaussianLowerBound := by
    intro x y t ht hxy
    simp [Real.rpow_zero]
  symmetry := fun _ _ _ => rfl
  semigroup := by
    intro x y s t hs ht
    simp
  normalization := by
    intro x t ht
    simp
  initialCondition := by
    intro x f hf
    obtain rfl : x = PUnit.unit := Subsingleton.elim x PUnit.unit
    simpa [integral_dirac] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => f PUnit.unit) (𝓝[>] (0 : ℝ)) (𝓝 (f PUnit.unit)))
  heatEquation := by
    intro x y t ht
    simpa using hasDerivAt_const t (1 : ℝ)

/-- The kernel of the one-point datum is the constant `1`. -/
@[simp]
theorem punitHeatKernelData_kernel (x y : PUnit) (t : ℝ) :
    punitHeatKernelData.kernel x y t = 1 := rfl

/-- The upper constant of the one-point datum is `1`. -/
@[simp]
theorem punitHeatKernelData_C_up : punitHeatKernelData.C_up = 1 := rfl

/-- The lower constant of the one-point datum is `1`. -/
@[simp]
theorem punitHeatKernelData_C_lo : punitHeatKernelData.C_lo = 1 := rfl

/-- The distance of the one-point datum is identically `0`. -/
@[simp]
theorem punitHeatKernelData_dist (x y : PUnit) : punitHeatKernelData.dist x y = 0 := rfl

/-- The one-point datum satisfies its own Gaussian upper bound with `C_up = 1`. -/
theorem punitHeatKernelData_upper (x y : PUnit) {t : ℝ} (ht : 0 < t) :
    punitHeatKernelData.kernel x y t ≤
      punitHeatKernelData.C_up * t ^ (-(punitHeatKernelData.dim / 2)) *
        Real.exp (-(punitHeatKernelData.dist x y) ^ 2 / (punitHeatKernelData.c_up * t)) :=
  punitHeatKernelData.gaussianUpperBound x y t ht

/-- The one-point datum satisfies its own Gaussian lower bound with `C_lo = 1`. -/
theorem punitHeatKernelData_lower (x y : PUnit) {t : ℝ} (ht : 0 < t)
    (hxy : punitHeatKernelData.dist x y ≤ 1) :
    punitHeatKernelData.C_lo * t ^ (-(punitHeatKernelData.dim / 2)) *
        Real.exp (-(punitHeatKernelData.dist x y) ^ 2 / (punitHeatKernelData.c_lo * t)) ≤
      punitHeatKernelData.kernel x y t :=
  punitHeatKernelData.gaussianLowerBound x y t ht hxy

/-- The one-point datum is strictly positive at every point and positive time. -/
theorem punitHeatKernelData_pos (x y : PUnit) {t : ℝ} (ht : 0 < t) :
    0 < punitHeatKernelData.kernel x y t :=
  punitHeatKernelData.kernel_pos_of_lowerBound (by simp) ht (by simp)

end Poincare.D7.HeatKernel
