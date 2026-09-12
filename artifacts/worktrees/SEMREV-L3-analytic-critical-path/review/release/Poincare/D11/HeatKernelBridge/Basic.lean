/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D11-heat-kernel-manifold-bridge)
-/

import Poincare.D7.HeatKernel.Basic

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D11.HeatKernelBridge.Basic

**D11 heat-kernel bridge, part 1: the D7 interface with its pointwise initial condition isolated.**

The D7 interface `Poincare.D7.HeatKernel.HeatKernelData` bundles the Gaussian upper and lower
bounds, symmetry, the semigroup law, mass normalisation, the heat equation, and the initial
condition `∫ y, K x y t * f y → f x` for *every* continuous test function `f`.

For the explicit Euclidean kernel of `Poincare.D10.HeatKernelEuclidean`,
`K x y t = (4 π t) ^ (-n/2) exp (-‖x - y‖² / (4 t))`, two of the D7 fields need care:

* `kernel_nonneg` is stated for *every real* `t`, whereas the explicit formula is manifestly
  nonnegative only for `t ≥ 0` (for `t < 0` the real power `(4 π t) ^ (-n/2)` may be negative).
  The Euclidean bridge therefore instantiates the interface with the kernel truncated at `t ≤ 0`;
  the truncated kernel agrees with the D10 kernel on the whole positive time axis, which is the
  only place where the analytic fields are asserted;
* `initialCondition` quantifies over *all* continuous test functions. The Bochner integral of a
  non-integrable integrand is `0`, so a continuous test function growing faster than every Gaussian
  makes the integral vanish identically although `f x ≠ 0`. The bridge proves the weak
  (distributional) initial condition for integrable continuous test functions
  (`Poincare.D11.HeatKernelBridge.InitialCondition`) and records the literal D7 field as the named
  predicate `HeatKernelCore.FullInitialCondition`, which is what a full D7 instantiation needs.

`HeatKernelCore X` is the D7 interface with `initialCondition` removed, so that all remaining
analytic fields can be instantiated *unconditionally* for the explicit Euclidean kernel in every
dimension. `HeatKernelCore.toHeatKernelData` re-attaches an initial condition and produces a
genuine `Poincare.D7.HeatKernel.HeatKernelData`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D11.HeatKernelBridge

/-- **The D7 heat-kernel interface without the pointwise initial condition.** Every field is a field
of `Poincare.D7.HeatKernel.HeatKernelData` except `initialCondition`, which is isolated because it
is not satisfiable by the explicit Euclidean kernel for arbitrary continuous test functions. -/
structure HeatKernelCore (X : Type*) [TopologicalSpace X] [MeasurableSpace X] where
  /-- The reference measure (Riemannian volume in the intended application). -/
  volume : Measure X
  /-- The distance entering the Gaussian bounds. -/
  dist : X → X → ℝ
  /-- The dimension entering the Gaussian factor `t ^ (-(dim / 2))`. -/
  dim : ℝ
  /-- The constant of the Gaussian upper bound. -/
  C_up : ℝ
  /-- The decay constant of the Gaussian upper bound. -/
  c_up : ℝ
  /-- The constant of the Gaussian lower bound. -/
  C_lo : ℝ
  /-- The decay constant of the Gaussian lower bound. -/
  c_lo : ℝ
  /-- The heat kernel `K x y t`, heat flowing from `y` to `x` in time `t`. -/
  kernel : X → X → ℝ → ℝ
  /-- The Laplace operator appearing in the heat equation. -/
  laplacian : (X → ℝ) →ₗ[ℝ] (X → ℝ)
  /-- The distance is zero on the diagonal. -/
  dist_self : ∀ x : X, dist x x = 0
  /-- The distance is nonnegative. -/
  dist_nonneg : ∀ x y : X, 0 ≤ dist x y
  /-- The distance is symmetric. -/
  dist_symm : ∀ x y : X, dist x y = dist y x
  /-- The upper decay constant is positive. -/
  c_up_pos : 0 < c_up
  /-- The lower decay constant is positive. -/
  c_lo_pos : 0 < c_lo
  /-- The upper constant is nonnegative. -/
  C_up_nonneg : 0 ≤ C_up
  /-- The lower constant is nonnegative. -/
  C_lo_nonneg : 0 ≤ C_lo
  /-- The kernel is nonnegative. -/
  kernel_nonneg : ∀ x y t, 0 ≤ kernel x y t
  /-- **Gaussian upper bound.** -/
  gaussianUpperBound : ∀ x y t, 0 < t →
    kernel x y t ≤ C_up * t ^ (-(dim / 2)) * Real.exp (-(dist x y) ^ 2 / (c_up * t))
  /-- **Gaussian lower bound.** -/
  gaussianLowerBound : ∀ x y t, 0 < t → dist x y ≤ 1 →
    C_lo * t ^ (-(dim / 2)) * Real.exp (-(dist x y) ^ 2 / (c_lo * t)) ≤ kernel x y t
  /-- **Symmetry** of the kernel. -/
  symmetry : ∀ x y t, kernel x y t = kernel y x t
  /-- **Semigroup property** (Chapman–Kolmogorov). -/
  semigroup : ∀ x y s t, 0 < s → 0 < t →
    kernel x y (s + t) = ∫ z, kernel x z s * kernel z y t ∂volume
  /-- **Normalization**: the kernel is a probability kernel for every `t > 0`. -/
  normalization : ∀ x t, 0 < t → ∫ y, kernel x y t ∂volume = 1
  /-- **Heat equation**: `∂_t K x y t = Δ_x K x y t`. -/
  heatEquation : ∀ x y t, 0 < t →
    HasDerivAt (fun s : ℝ => kernel x y s) (laplacian (fun z => kernel z y t) x) t

namespace HeatKernelCore

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- **The literal D7 initial condition** for a core datum: convergence to the Dirac delta against
every continuous test function, with the Bochner integral over the datum's own measure. -/
def FullInitialCondition (D : HeatKernelCore X) : Prop :=
  ∀ (x : X) (f : X → ℝ), Continuous f →
    Tendsto (fun t : ℝ => ∫ y, D.kernel x y t * f y ∂D.volume) (𝓝[>] (0 : ℝ)) (𝓝 (f x))

/-- **The weak (distributional) initial condition**: convergence to the Dirac delta against
continuous *integrable* test functions (in particular against continuous compactly supported test
functions). This is the form that the Euclidean bridge proves for the explicit D10 kernel. -/
def WeakInitialCondition (D : HeatKernelCore X) : Prop :=
  ∀ (x : X) (f : X → ℝ), Continuous f → Integrable f D.volume →
    Tendsto (fun t : ℝ => ∫ y, D.kernel x y t * f y ∂D.volume) (𝓝[>] (0 : ℝ)) (𝓝 (f x))

/-- A full initial condition is in particular a weak one, since integrability is an extra
hypothesis. -/
theorem WeakInitialCondition.of_full {D : HeatKernelCore X} (h : D.FullInitialCondition) :
    D.WeakInitialCondition :=
  fun x f hf _ => h x f hf

/-- **Forget the pointwise initial condition** of a D7 heat-kernel datum. -/
def _root_.Poincare.D7.HeatKernel.HeatKernelData.toCore
    (D : Poincare.D7.HeatKernel.HeatKernelData X) : HeatKernelCore X where
  volume := D.volume
  dist := D.dist
  dim := D.dim
  C_up := D.C_up
  c_up := D.c_up
  C_lo := D.C_lo
  c_lo := D.c_lo
  kernel := D.kernel
  laplacian := D.laplacian
  dist_self := D.dist_self
  dist_nonneg := D.dist_nonneg
  dist_symm := D.dist_symm
  c_up_pos := D.c_up_pos
  c_lo_pos := D.c_lo_pos
  C_up_nonneg := D.C_up_nonneg
  C_lo_nonneg := D.C_lo_nonneg
  kernel_nonneg := D.kernel_nonneg
  gaussianUpperBound := D.gaussianUpperBound
  gaussianLowerBound := D.gaussianLowerBound
  symmetry := D.symmetry
  semigroup := D.semigroup
  normalization := D.normalization
  heatEquation := D.heatEquation

/-- The core of a D7 datum satisfies the full (hence the weak) initial condition. -/
theorem _root_.Poincare.D7.HeatKernel.HeatKernelData.toCore_fullInitialCondition
    (D : Poincare.D7.HeatKernel.HeatKernelData X) : D.toCore.FullInitialCondition :=
  D.initialCondition

/-- **Re-attach an initial condition.** A core datum together with the literal D7 initial condition
is a genuine `Poincare.D7.HeatKernel.HeatKernelData`. Conversely every D7 datum arises this way
from its core, so the bridge loses nothing but the unsatisfiable-in-the-flat-case field. -/
def toHeatKernelData (D : HeatKernelCore X) (h : D.FullInitialCondition) :
    Poincare.D7.HeatKernel.HeatKernelData X where
  volume := D.volume
  dist := D.dist
  dim := D.dim
  C_up := D.C_up
  c_up := D.c_up
  C_lo := D.C_lo
  c_lo := D.c_lo
  kernel := D.kernel
  laplacian := D.laplacian
  dist_self := D.dist_self
  dist_nonneg := D.dist_nonneg
  dist_symm := D.dist_symm
  c_up_pos := D.c_up_pos
  c_lo_pos := D.c_lo_pos
  C_up_nonneg := D.C_up_nonneg
  C_lo_nonneg := D.C_lo_nonneg
  kernel_nonneg := D.kernel_nonneg
  gaussianUpperBound := D.gaussianUpperBound
  gaussianLowerBound := D.gaussianLowerBound
  symmetry := D.symmetry
  semigroup := D.semigroup
  normalization := D.normalization
  initialCondition := h
  heatEquation := D.heatEquation

/-- Adding the initial condition and forgetting it again is the identity on core data. -/
@[simp]
theorem toHeatKernelData_toCore (D : HeatKernelCore X) (h : D.FullInitialCondition) :
    (D.toHeatKernelData h).toCore = D := rfl

/-- Forgetting the initial condition of a D7 datum and re-attaching it is the identity. -/
@[simp]
theorem toCore_toHeatKernelData (D : Poincare.D7.HeatKernel.HeatKernelData X) :
    D.toCore.toHeatKernelData D.toCore_fullInitialCondition = D := rfl

/-- **Tightness of the bridge.** A D7 `HeatKernelData` with a prescribed core exists if and only if
that core satisfies the literal pointwise initial condition. Thus the single field isolated by
`HeatKernelCore` is exactly the difference between the D7 interface and the bridge. -/
theorem exists_toCore_eq_iff (D₀ : HeatKernelCore X) :
    (∃ D : Poincare.D7.HeatKernel.HeatKernelData X, D.toCore = D₀) ↔ D₀.FullInitialCondition := by
  constructor
  · rintro ⟨D, rfl⟩
    exact D.toCore_fullInitialCondition
  · intro h
    exact ⟨D₀.toHeatKernelData h, rfl⟩

/-- The core datum carries the same Gaussian upper bound as its D7 ancestor. -/
theorem toCore_gaussianUpperBound (D : Poincare.D7.HeatKernel.HeatKernelData X) :
    ∀ x y t, 0 < t → D.toCore.kernel x y t ≤
      D.toCore.C_up * t ^ (-(D.toCore.dim / 2)) *
        Real.exp (-(D.toCore.dist x y) ^ 2 / (D.toCore.c_up * t)) :=
  D.toCore.gaussianUpperBound

end HeatKernelCore

end Poincare.D11.HeatKernelBridge
