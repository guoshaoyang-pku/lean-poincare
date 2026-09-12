/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Euclidean heat kernel: definition and elementary properties

This file defines the explicit heat kernel on `ℝⁿ`, realised as
`EuclideanSpace ℝ (Fin n)`,

`gaussianKernel n t x = (4 * π * t) ^ (-(n : ℝ) / 2) * exp (-‖x‖² / (4 * t))`,

together with its elementary pointwise properties: positivity, measurability,
continuity and the behaviour of the exponent `‖x‖²` in the standard
orthonormal basis.

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs
in this file; every declaration is proved unconditionally.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! ## The kernel -/

@[expose] public section

open MeasureTheory Real
open scoped InnerProductSpace Laplacian RealInnerProductSpace

namespace Poincare.D10.HeatKernelEuclidean

/-- The explicit heat kernel on `ℝⁿ` (viewed as `EuclideanSpace ℝ (Fin n)`):
`K n t x = (4 π t) ^ (-n/2) * exp (-‖x‖² / (4 t))`. -/
noncomputable def gaussianKernel (n : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))

@[simp]
theorem gaussianKernel_apply (n : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    gaussianKernel n t x =
      (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t)) := rfl

theorem gaussianKernel_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ gaussianKernel n t x := by
  have hbase : 0 ≤ 4 * π * t := by positivity
  exact mul_nonneg (Real.rpow_nonneg hbase _) (Real.exp_nonneg _)

theorem gaussianKernel_pos (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) : 0 < gaussianKernel n t x := by
  have hbase : 0 < 4 * π * t := by positivity
  exact mul_pos (Real.rpow_pos_of_pos hbase _) (Real.exp_pos _)

theorem gaussianKernel_ne_zero (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) : gaussianKernel n t x ≠ 0 :=
  ne_of_gt (gaussianKernel_pos n ht x)

/-- The kernel is measurably parametrised by `(t, x)`. -/
theorem measurable_gaussianKernel (n : ℕ) :
    Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin n) => gaussianKernel n p.1 p.2) := by
  unfold gaussianKernel
  fun_prop

/-- For fixed positive time the kernel is a continuous function of the space variable. -/
theorem continuous_gaussianKernel (n : ℕ) {t : ℝ} :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) => gaussianKernel n t x) := by
  unfold gaussianKernel
  fun_prop

/-- The exponent appearing in the kernel, written in terms of the standard orthonormal
basis of `ℝⁿ`. -/
theorem norm_sq_eq_sum_sq (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  simpa using EuclideanSpace.real_norm_sq_eq x

/-- Pairing with a vector of the standard orthonormal basis extracts the corresponding
coordinate. -/
@[simp]
theorem inner_basisFun (n : ℕ) (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪EuclideanSpace.basisFun (Fin n) ℝ i, x⟫_ℝ = x i := by
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  simp

/-- The standard orthonormal basis of `ℝⁿ` is indexed by `Fin n`. -/
theorem finrank_euclideanSpace_fin (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
  rw [finrank_euclideanSpace, Fintype.card_fin]

/-- The real dimension of `ℝⁿ`, as a real number, is `n`. -/
theorem finrank_euclideanSpace_fin_real (n : ℕ) :
    ((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ)) = (n : ℝ) := by
  rw [finrank_euclideanSpace, Fintype.card_fin]

/-- The `(4 π t) ^ (-n/2)` prefactor is nonzero for positive times. -/
theorem rpow_prefactor_ne_zero (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (4 * π * t) ^ (-(n : ℝ) / 2) ≠ 0 := by
  have hbase : 0 < 4 * π * t := by positivity
  exact ne_of_gt (Real.rpow_pos_of_pos hbase _)

end Poincare.D10.HeatKernelEuclidean
