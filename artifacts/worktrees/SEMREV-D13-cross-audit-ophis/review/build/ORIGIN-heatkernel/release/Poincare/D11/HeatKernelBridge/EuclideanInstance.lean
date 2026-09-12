/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D11-heat-kernel-manifold-bridge)
-/

import Poincare.D11.HeatKernelBridge.Basic
import Poincare.D11.HeatKernelBridge.EuclideanLaplacian
import Poincare.D10.HeatKernelEuclidean.Semigroup

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D11.HeatKernelBridge.EuclideanInstance

**D11 heat-kernel bridge, part 3: the explicit D10 Euclidean kernel instantiates the D7 interface.**

The bridge datum `flatHeatKernelCore n` on `EuclideanSpace ℝ (Fin n)` is

* measure: Lebesgue measure `volume`;
* distance: `‖x - y‖` (the Euclidean distance);
* dimension: `n` (as a real number);
* constants: `C_up = C_lo = (4 π) ^ (-n/2)`, `c_up = c_lo = 4`;
* kernel: `flatKernel n x y t = if 0 < t then gaussianKernel n t (x - y) else 0`, the D10 kernel
  translated to the two-point form and truncated at nonpositive times;
* Laplacian: `laplacianLinearMap E`, mathlib's `Δ` packaged as a linear map
  (`EuclideanLaplacian.lean`).

Every field is proved from the D10 theorems:

| bridge field | D10 input |
| --- | --- |
| `kernel_nonneg` | `gaussianKernel_nonneg` |
| `gaussianUpperBound` | `gaussianKernel_apply` + `Real.mul_rpow` |
| `gaussianLowerBound` | `gaussianKernel_apply` + `Real.mul_rpow` |
| `symmetry` | `norm_sub_rev` |
| `semigroup` | `gaussianKernel_convolution` + translation invariance |
| `normalization` | `gaussianKernel_integral` + translation invariance |
| `heatEquation` | `hasDerivAt_gaussianKernel`, `laplacian_gaussianKernel`, `laplacian_comp_sub` |

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter Real
open scoped Topology InnerProductSpace Laplacian RealInnerProductSpace

namespace Poincare.D11.HeatKernelBridge

open Poincare.D10.HeatKernelEuclidean

/-- The explicit Euclidean heat kernel in two-point form, truncated at nonpositive times. For
`t > 0` it is the D10 kernel `gaussianKernel n t (x - y)`. -/
noncomputable def flatKernel (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  if 0 < t then gaussianKernel n t (x - y) else 0

/-- On positive times the bridge kernel is the explicit D10 kernel. -/
theorem flatKernel_of_pos (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 < t) :
    flatKernel n x y t = gaussianKernel n t (x - y) := by
  simp [flatKernel, ht]

/-- On nonpositive times the bridge kernel vanishes. -/
theorem flatKernel_of_nonpos (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : t ≤ 0) :
    flatKernel n x y t = 0 := by
  simp [flatKernel, not_lt.mpr ht]

/-- The explicit value of the bridge kernel at positive times, with the prefactor split into its
constant and time parts. This is the form in which both Gaussian bounds are checked. -/
theorem flatKernel_eq (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 < t) :
    flatKernel n x y t =
      (4 * π) ^ (-(n : ℝ) / 2) * t ^ (-((n : ℝ) / 2)) *
        Real.exp (-(‖x - y‖ ^ 2) / (4 * t)) := by
  rw [flatKernel_of_pos n x y ht, gaussianKernel_apply]
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 * π) ht.le,
    show (-(n : ℝ)) / 2 = -((n : ℝ) / 2) by ring]

/-- The bridge kernel is nonnegative. -/
theorem flatKernel_nonneg (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    0 ≤ flatKernel n x y t := by
  rw [flatKernel]
  split_ifs with ht
  · exact gaussianKernel_nonneg n ht.le (x - y)
  · exact le_refl 0

/-- The bridge kernel is strictly positive at positive times. -/
theorem flatKernel_pos (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 < t) :
    0 < flatKernel n x y t := by
  rw [flatKernel_of_pos n x y ht]
  exact gaussianKernel_pos n ht (x - y)

/-- Translated Gaussian kernels are twice continuously differentiable. -/
theorem contDiff_gaussianKernel_translate (n : ℕ) (t : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ 2 (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (z - y)) := by
  have h1 : ContDiff ℝ 2 (fun z : EuclideanSpace ℝ (Fin n) => ‖z - y‖ ^ 2) := by
    simpa only [Function.comp_def, id_eq] using
      (contDiff_norm_sq ℝ (E := EuclideanSpace ℝ (Fin n))).comp
        (contDiff_id.sub contDiff_const)
  have h2 : ContDiff ℝ 2 (fun z : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-‖z - y‖ ^ 2 / (4 * t))) :=
    (h1.neg.div_const (4 * t)).exp
  simpa only [gaussianKernel_apply, smul_eq_mul] using
    h2.const_smul ((4 * π * t) ^ (-(n : ℝ) / 2))

/-- The packaged Laplacian applied to a translated Gaussian kernel, in terms of mathlib's `Δ`. -/
theorem laplacianLinearMap_flatKernel (n : ℕ) {t : ℝ} (ht : 0 < t)
    (y : EuclideanSpace ℝ (Fin n)) :
    laplacianLinearMap (EuclideanSpace ℝ (Fin n)) (fun z => flatKernel n z y t)
      = fun x => Δ (fun z => gaussianKernel n t (z - y)) x := by
  have hfun : (fun z : EuclideanSpace ℝ (Fin n) => flatKernel n z y t)
      = fun z => gaussianKernel n t (z - y) := by
    funext z
    exact flatKernel_of_pos n z y ht
  rw [hfun, laplacianLinearMap_apply_of_contDiff (contDiff_gaussianKernel_translate n t y)]

/-- **The explicit D10 Euclidean heat kernel as a bridge datum.** All fields of the D7 interface
except the pointwise initial condition are proved unconditionally in every dimension. -/
noncomputable def flatHeatKernelCore (n : ℕ) : HeatKernelCore (EuclideanSpace ℝ (Fin n)) where
  volume := volume
  dist := fun x y => ‖x - y‖
  dim := (n : ℝ)
  C_up := (4 * π) ^ (-(n : ℝ) / 2)
  c_up := 4
  C_lo := (4 * π) ^ (-(n : ℝ) / 2)
  c_lo := 4
  kernel := flatKernel n
  laplacian := laplacianLinearMap (EuclideanSpace ℝ (Fin n))
  dist_self := by intro x; simp
  dist_nonneg := by intro x y; positivity
  dist_symm := by intro x y; rw [norm_sub_rev]
  c_up_pos := by norm_num
  c_lo_pos := by norm_num
  C_up_nonneg := Real.rpow_nonneg (by positivity) _
  C_lo_nonneg := Real.rpow_nonneg (by positivity) _
  kernel_nonneg := fun x y t => flatKernel_nonneg n x y t
  gaussianUpperBound := by
    intro x y t ht
    rw [flatKernel_eq n x y ht]
  gaussianLowerBound := by
    intro x y t ht _
    rw [flatKernel_eq n x y ht]
  symmetry := by
    intro x y t
    rw [flatKernel]
    split_ifs with ht
    · rw [flatKernel_of_pos n y x ht, gaussianKernel_apply, gaussianKernel_apply,
        norm_sub_rev y x]
    · simp [flatKernel, ht]
  semigroup := by
    intro x y s t hs ht
    have hst : 0 < s + t := add_pos hs ht
    rw [flatKernel_of_pos n x y hst]
    have hpoint : ∀ z : EuclideanSpace ℝ (Fin n),
        flatKernel n x z s * flatKernel n z y t
          = gaussianKernel n s (x - z) * gaussianKernel n t (z - y) := by
      intro z
      rw [flatKernel_of_pos n x z hs, flatKernel_of_pos n z y ht]
    simp_rw [hpoint]
    rw [← integral_add_right_eq_self
      (fun z : EuclideanSpace ℝ (Fin n) =>
        gaussianKernel n s (x - z) * gaussianKernel n t (z - y)) y]
    have hpoint' : ∀ z : EuclideanSpace ℝ (Fin n),
        gaussianKernel n s (x - (z + y)) * gaussianKernel n t (z + y - y)
          = gaussianKernel n t z * gaussianKernel n s (x - y - z) := by
      intro z
      rw [add_sub_cancel_right, show x - (z + y) = x - y - z by abel]
      ring
    simp_rw [hpoint']
    rw [gaussianKernel_convolution n ht hs (x - y)]
    exact congrArg (fun u => gaussianKernel n u (x - y)) (add_comm s t)
  normalization := by
    intro x t ht
    have hfun : (fun y : EuclideanSpace ℝ (Fin n) => flatKernel n x y t)
        = fun y => gaussianKernel n t (x - y) := by
      funext y
      exact flatKernel_of_pos n x y ht
    rw [hfun, integral_sub_left_eq_self (fun z => gaussianKernel n t z) volume x]
    exact gaussianKernel_integral n ht
  heatEquation := by
    intro x y t ht
    rw [show (laplacianLinearMap (EuclideanSpace ℝ (Fin n))) (fun z => flatKernel n z y t) x
        = Δ (fun z => gaussianKernel n t (z - y)) x from
      congrFun (laplacianLinearMap_flatKernel n ht y) x]
    rw [laplacian_comp_sub (gaussianKernel n t) y x, laplacian_gaussianKernel n ht (x - y)]
    refine (hasDerivAt_gaussianKernel n ht (x - y)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact flatKernel_of_pos n x y hs

@[simp]
theorem flatHeatKernelCore_kernel (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    (flatHeatKernelCore n).kernel x y t = flatKernel n x y t := rfl

@[simp]
theorem flatHeatKernelCore_volume (n : ℕ) :
    (flatHeatKernelCore n).volume = volume := rfl

@[simp]
theorem flatHeatKernelCore_dist (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) :
    (flatHeatKernelCore n).dist x y = ‖x - y‖ := rfl

@[simp]
theorem flatHeatKernelCore_dim (n : ℕ) : (flatHeatKernelCore n).dim = (n : ℝ) := rfl

@[simp]
theorem flatHeatKernelCore_C_up (n : ℕ) :
    (flatHeatKernelCore n).C_up = (4 * π) ^ (-(n : ℝ) / 2) := rfl

@[simp]
theorem flatHeatKernelCore_c_up (n : ℕ) : (flatHeatKernelCore n).c_up = 4 := rfl

@[simp]
theorem flatHeatKernelCore_C_lo (n : ℕ) :
    (flatHeatKernelCore n).C_lo = (4 * π) ^ (-(n : ℝ) / 2) := rfl

@[simp]
theorem flatHeatKernelCore_c_lo (n : ℕ) : (flatHeatKernelCore n).c_lo = 4 := rfl

@[simp]
theorem flatHeatKernelCore_laplacian (n : ℕ) :
    (flatHeatKernelCore n).laplacian = laplacianLinearMap (EuclideanSpace ℝ (Fin n)) := rfl

/-- The bridge datum has total mass one at every positive time (D10 `gaussianKernel_integral`). -/
theorem flatHeatKernelCore_normalization (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) {t : ℝ}
    (ht : 0 < t) : ∫ y, (flatHeatKernelCore n).kernel x y t = 1 :=
  (flatHeatKernelCore n).normalization x t ht

/-- The bridge datum satisfies the Chapman–Kolmogorov semigroup identity (D10
`gaussianKernel_convolution`). -/
theorem flatHeatKernelCore_semigroup (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) :
    (flatHeatKernelCore n).kernel x y (s + t)
      = ∫ z, (flatHeatKernelCore n).kernel x z s * (flatHeatKernelCore n).kernel z y t :=
  (flatHeatKernelCore n).semigroup x y s t hs ht

/-- The bridge kernel solves the heat equation at every positive time (D10
`hasDerivAt_gaussianKernel` and `laplacian_gaussianKernel`). -/
theorem flatHeatKernelCore_heatEquation (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (flatHeatKernelCore n).kernel x y s)
      ((flatHeatKernelCore n).laplacian (fun z => (flatHeatKernelCore n).kernel z y t) x) t :=
  (flatHeatKernelCore n).heatEquation x y t ht

/-- The bridge datum satisfies its own Gaussian upper bound. -/
theorem flatHeatKernelCore_gaussianUpperBound (n : ℕ) (x y : EuclideanSpace ℝ (Fin n))
    {t : ℝ} (ht : 0 < t) :
    (flatHeatKernelCore n).kernel x y t ≤
      (flatHeatKernelCore n).C_up * t ^ (-((flatHeatKernelCore n).dim / 2)) *
        Real.exp (-((flatHeatKernelCore n).dist x y) ^ 2 / ((flatHeatKernelCore n).c_up * t)) :=
  (flatHeatKernelCore n).gaussianUpperBound x y t ht

/-- The bridge datum satisfies its own Gaussian lower bound. -/
theorem flatHeatKernelCore_gaussianLowerBound (n : ℕ) (x y : EuclideanSpace ℝ (Fin n))
    {t : ℝ} (ht : 0 < t) (hxy : (flatHeatKernelCore n).dist x y ≤ 1) :
    (flatHeatKernelCore n).C_lo * t ^ (-((flatHeatKernelCore n).dim / 2)) *
        Real.exp (-((flatHeatKernelCore n).dist x y) ^ 2 / ((flatHeatKernelCore n).c_lo * t)) ≤
      (flatHeatKernelCore n).kernel x y t :=
  (flatHeatKernelCore n).gaussianLowerBound x y t ht hxy

/-- **The flat bridge is exactly the D7 interface minus the pointwise initial condition**: a D7
`HeatKernelData` whose core is `flatHeatKernelCore n` exists if and only if the explicit Euclidean
kernel satisfies the literal D7 initial condition. In dimension `0` this holds
(`ZeroDimension.flatHeatKernelData_zero`); in positive dimensions the weak theorem
`flatKernel_tendsto_integral` is what the bridge proves instead. -/
theorem flat_exists_heatKernelData_iff (n : ℕ) :
    (∃ D : Poincare.D7.HeatKernel.HeatKernelData (EuclideanSpace ℝ (Fin n)),
      D.toCore = flatHeatKernelCore n) ↔ (flatHeatKernelCore n).FullInitialCondition :=
  HeatKernelCore.exists_toCore_eq_iff _

end Poincare.D11.HeatKernelBridge
