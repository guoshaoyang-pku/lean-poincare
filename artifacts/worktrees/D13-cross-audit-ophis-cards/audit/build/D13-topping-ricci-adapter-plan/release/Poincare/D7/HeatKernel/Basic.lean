/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-heat-kernel-existence)
-/

import Mathlib

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D7.HeatKernel.Basic

**D7 heat-kernel layer, part 1: the heat-kernel interface `HeatKernelData`.**

This file defines `HeatKernelData X`, a structure that records, as *explicit fields*, the properties
of a heat kernel `K x y t` on a state space `X`:

* the **Gaussian upper bound**
  `K x y t ≤ C_up * t ^ (-(dim / 2)) * exp (-(dist x y)^2 / (c_up * t))`,
* the **Gaussian lower bound**
  `C_lo * t ^ (-(dim / 2)) * exp (-(dist x y)^2 / (c_lo * t)) ≤ K x y t` (for `dist x y ≤ 1`),
* the **semigroup property** (Chapman–Kolmogorov)
  `K x y (s + t) = ∫ z, K x z s * K z y t ∂volume`,
* **normalization** `∫ y, K x y t ∂volume = 1`,
* **symmetry** `K x y t = K y x t`,
* the **heat equation** `∂_t K x y t = Δ_x K x y t`,
* the **initial condition** `∫ y, K x y t * f y → f x` as `t → 0⁺`.

The structure is an interface: it states the analytic properties that a heat kernel must satisfy and
leaves the existence question to `Poincare.D7.HeatKernel.Blocked`. The remaining modules instantiate
the finite-grid (combinatorial) part of the interface, prove the uniqueness of a finite-grid heat
kernel satisfying the stated bounds, and prove the monotonicity of the discrete heat content.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D7.HeatKernel

/-- **A heat-kernel datum.** The fields record the Gaussian upper and lower bounds, the semigroup
(Chapman–Kolmogorov) property, normalization, symmetry, the heat equation, and the initial
(delta) condition of a heat kernel `kernel x y t` on `X`.

The distance `dist`, the dimension `dim`, the constants `C_up, c_up, C_lo, c_lo`, and the measure
`volume` are part of the datum, so that every instance certifies its own bounds. -/
structure HeatKernelData (X : Type*) [TopologicalSpace X] [MeasurableSpace X] where
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
  /-- **Initial condition**: against every continuous test function the kernel converges to the
  Dirac delta as `t → 0⁺`. -/
  initialCondition : ∀ (x : X) (f : X → ℝ), Continuous f →
    Tendsto (fun t : ℝ => ∫ y, kernel x y t * f y ∂volume) (𝓝[>] (0 : ℝ)) (𝓝 (f x))
  /-- **Heat equation**: `∂_t K x y t = Δ_x K x y t`. -/
  heatEquation : ∀ x y t, 0 < t →
    HasDerivAt (fun s : ℝ => kernel x y s) (laplacian (fun z => kernel z y t) x) t

namespace HeatKernelData

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- **Strict positivity from the Gaussian lower bound.** If the lower constant `C_lo` is positive,
the lower bound forces the kernel to be strictly positive at every point at distance `≤ 1`. -/
theorem kernel_pos_of_lowerBound (D : HeatKernelData X) {x y : X} {t : ℝ} (hC : 0 < D.C_lo)
    (ht : 0 < t) (hxy : D.dist x y ≤ 1) : 0 < D.kernel x y t := by
  have h := D.gaussianLowerBound x y t ht hxy
  have hpos : 0 < D.C_lo * t ^ (-(D.dim / 2)) * Real.exp (-(D.dist x y) ^ 2 / (D.c_lo * t)) :=
    mul_pos (mul_pos hC (Real.rpow_pos_of_pos ht _)) (Real.exp_pos _)
  exact lt_of_lt_of_le hpos h

/-- The Gaussian upper bound on the diagonal: `K x x t ≤ C_up * t ^ (-(dim / 2))`. -/
theorem upperBound_self (D : HeatKernelData X) {x : X} {t : ℝ} (ht : 0 < t) :
    D.kernel x x t ≤ D.C_up * t ^ (-(D.dim / 2)) := by
  have h := D.gaussianUpperBound x x t ht
  simpa [D.dist_self x] using h

/-- The semigroup property written with the symmetry of the kernel applied to the second factor. -/
theorem semigroup_symm (D : HeatKernelData X) (x y : X) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    D.kernel x y (s + t) = ∫ z, D.kernel x z s * D.kernel y z t ∂D.volume := by
  rw [D.semigroup x y s t hs ht]
  exact integral_congr_ae (Eventually.of_forall (fun z => by simp only [D.symmetry z y t]))

/-- Normalization written with the order of the arguments exchanged. -/
theorem normalization_symm (D : HeatKernelData X) (x : X) {t : ℝ} (ht : 0 < t) :
    ∫ y, D.kernel y x t ∂D.volume = 1 := by
  rw [← D.normalization x t ht]
  exact integral_congr_ae (Eventually.of_forall (fun y => by simp only [D.symmetry y x t]))

/-- The Gaussian factor is nonnegative whenever `t > 0`. -/
theorem gaussian_factor_nonneg (D : HeatKernelData X) (x y : X) {t : ℝ} (ht : 0 < t) :
    0 ≤ D.C_up * t ^ (-(D.dim / 2)) * Real.exp (-(D.dist x y) ^ 2 / (D.c_up * t)) :=
  mul_nonneg (mul_nonneg D.C_up_nonneg (Real.rpow_nonneg ht.le _)) (Real.exp_nonneg _)

end HeatKernelData

end Poincare.D7.HeatKernel
