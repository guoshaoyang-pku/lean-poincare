/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Euclidean heat kernel solves the heat equation

For every positive time `t > 0` and every `x : EuclideanSpace ℝ (Fin n)` we prove
`∂ₜ K = Δ K`, i.e.

`deriv (fun s => gaussianKernel n s x) t = Δ (gaussianKernel n t) x`.

Both sides are computed explicitly:

* the time derivative of `(4 π t) ^ (-n/2) exp (-‖x‖² / 4t)` equals
  `K n t x * (‖x‖² / (4 t²) - n / (2 t))`;
* the Laplacian of `x ↦ exp (a ‖x‖²)` with `a = -1/(4t)` equals
  `(2 a n + 4 a² ‖x‖²) exp (a ‖x‖²)`, which gives the same expression after
  multiplying by the prefactor.

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs
in this file; every declaration is proved unconditionally.
-/
module

public import Poincare.D10.HeatKernelEuclidean.GaussianIntegral

@[expose] public section

open MeasureTheory Real
open scoped InnerProductSpace Laplacian RealInnerProductSpace

namespace Poincare.D10.HeatKernelEuclidean

/-! ## The explicit Laplacian of the kernel -/

/-- The Laplacian of the kernel in the space variable:
`Δ (K n t) x = K n t x * (‖x‖² / (4 t²) - n / (2 t))`. -/
theorem laplacian_gaussianKernel (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    Δ (gaussianKernel n t) x =
      gaussianKernel n t x * (‖x‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) := by
  have hnorm : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) x :=
    (contDiff_norm_sq ℝ (E := EuclideanSpace ℝ (Fin n))).contDiffAt
  have hc : ContDiffAt ℝ 2
      (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-‖y‖ ^ 2 / (4 * t))) x := by
    apply ContDiffAt.exp
    have h1 : ContDiffAt ℝ 2
        (fun y : EuclideanSpace ℝ (Fin n) => -(‖y‖ ^ 2 / (4 * t))) x :=
      (hnorm.div_const (4 * t)).neg
    simpa only [neg_div] using h1
  have hsmul : Δ (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n t y) x =
      (4 * π * t) ^ (-(n : ℝ) / 2) *
        Δ (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-‖y‖ ^ 2 / (4 * t))) x := by
    have hfun : (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n t y) =
        (4 * π * t) ^ (-(n : ℝ) / 2) •
          (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-‖y‖ ^ 2 / (4 * t))) := by
      funext y
      rw [Pi.smul_apply, smul_eq_mul, gaussianKernel_apply]
    rw [hfun, InnerProductSpace.laplacian_smul _ hc]
    rfl
  rw [hsmul]
  have hlap : Δ (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-‖y‖ ^ 2 / (4 * t))) x =
      (‖x‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) *
        Real.exp (-‖x‖ ^ 2 / (4 * t)) := by
    have hfun : (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-‖y‖ ^ 2 / (4 * t))) =
        fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-(1 / (4 * t)) * ‖y‖ ^ 2) := by
      funext y
      rw [show -‖y‖ ^ 2 / (4 * t) = -(1 / (4 * t)) * ‖y‖ ^ 2 by ring]
    have h := laplacian_exp_norm_sq (EuclideanSpace.basisFun (Fin n) ℝ) (-(1 / (4 * t))) x
    simp only [Fintype.card_fin] at h
    rw [hfun, h]
    field_simp
    ring
  rw [hlap, gaussianKernel_apply]
  ring

/-! ## The explicit time derivative of the kernel -/

/-- The time derivative of the kernel at a fixed point:
`∂ₜ (K n · x) t = K n t x * (‖x‖² / (4 t²) - n / (2 t))`. -/
theorem hasDerivAt_gaussianKernel (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s : ℝ => gaussianKernel n s x)
      (gaussianKernel n t x * (‖x‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t))) t := by
  have hbase : 0 < 4 * π * t := by positivity
  have hbasene : 4 * π * t ≠ 0 := ne_of_gt hbase
  have h4 : HasDerivAt (fun s : ℝ => 4 * s) (4 : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (4 : ℝ)
  have h4ne : 4 * t ≠ 0 := by positivity
  have hu : HasDerivAt (fun s : ℝ => 4 * π * s) (4 * π) t := by
    simpa using (hasDerivAt_id t).const_mul (4 * π)
  -- derivative of the prefactor `(4 π s) ^ (-n/2)`
  have hc : HasDerivAt (fun s : ℝ => (4 * π * s) ^ (-(n : ℝ) / 2))
      (-((n : ℝ) / (2 * t)) * (4 * π * t) ^ (-(n : ℝ) / 2)) t := by
    have h0 : HasDerivAt (fun s : ℝ => (4 * π * s) ^ (-(n : ℝ) / 2))
        (4 * π * (-(n : ℝ) / 2) * (4 * π * t) ^ (-(n : ℝ) / 2 - 1)) t :=
      hu.rpow_const (Or.inl hbasene)
    have hval : 4 * π * (-(n : ℝ) / 2) * (4 * π * t) ^ (-(n : ℝ) / 2 - 1)
        = -((n : ℝ) / (2 * t)) * (4 * π * t) ^ (-(n : ℝ) / 2) := by
      rw [show -(n : ℝ) / 2 - 1 = -(n : ℝ) / 2 + (-1) by ring, Real.rpow_add hbase,
        Real.rpow_neg (le_of_lt hbase), Real.rpow_one]
      field_simp
    rwa [hval] at h0
  -- derivative of the Gaussian factor
  have hinv : HasDerivAt (fun s : ℝ => -‖x‖ ^ 2 / (4 * s)) (‖x‖ ^ 2 / (4 * t ^ 2)) t := by
    have h0 : HasDerivAt (fun s : ℝ => -‖x‖ ^ 2 / (4 * s))
        ((0 * (4 * t) - -‖x‖ ^ 2 * 4) / (4 * t) ^ 2) t :=
      (hasDerivAt_const (x := t) (-‖x‖ ^ 2)).div h4 h4ne
    have hval : (0 * (4 * t) - -‖x‖ ^ 2 * 4) / (4 * t) ^ 2 = ‖x‖ ^ 2 / (4 * t ^ 2) := by
      field_simp
      ring
    rwa [hval] at h0
  have hg : HasDerivAt (fun s : ℝ => Real.exp (-‖x‖ ^ 2 / (4 * s)))
      (Real.exp (-‖x‖ ^ 2 / (4 * t)) * (‖x‖ ^ 2 / (4 * t ^ 2))) t :=
    hinv.exp
  have hK := hc.mul hg
  have hfun : (fun s : ℝ => gaussianKernel n s x) =
      fun s : ℝ => (4 * π * s) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * s)) := rfl
  have hfun' : (fun s : ℝ => (4 * π * s) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * s))) =
      ((fun s : ℝ => (4 * π * s) ^ (-(n : ℝ) / 2)) *
        fun s : ℝ => Real.exp (-‖x‖ ^ 2 / (4 * s))) := rfl
  have hval : -((n : ℝ) / (2 * t)) * (4 * π * t) ^ (-(n : ℝ) / 2) *
        Real.exp (-‖x‖ ^ 2 / (4 * t)) +
      (4 * π * t) ^ (-(n : ℝ) / 2) *
        (Real.exp (-‖x‖ ^ 2 / (4 * t)) * (‖x‖ ^ 2 / (4 * t ^ 2)))
      = gaussianKernel n t x * (‖x‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) := by
    rw [gaussianKernel_apply]
    ring
  rw [hval] at hK
  rw [hfun, hfun']
  exact hK

/-! ## The heat equation -/

/-- **The Euclidean heat kernel solves the heat equation**, unconditionally and for
every positive time. -/
theorem heat_equation (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    deriv (fun s : ℝ => gaussianKernel n s x) t = Δ (gaussianKernel n t) x := by
  rw [(hasDerivAt_gaussianKernel n ht x).deriv, laplacian_gaussianKernel n ht x]

/-- The time derivative of the kernel as a function of the space variable, i.e. the
`HasDerivAt` statement in the Banach space `EuclideanSpace ℝ (Fin n) → ℝ`. -/
theorem hasDerivAt_gaussianKernel_fun (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => gaussianKernel n s)
      (fun x : EuclideanSpace ℝ (Fin n) =>
        gaussianKernel n t x * (‖x‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t))) t := by
  rw [hasDerivAt_pi]
  intro x
  exact hasDerivAt_gaussianKernel n ht x

/-- **Function-level form of the heat equation**: `∂ₜ K = Δ K` as an identity of functions
`EuclideanSpace ℝ (Fin n) → ℝ`. -/
theorem heat_equation_fun (n : ℕ) {t : ℝ} (ht : 0 < t) :
    deriv (fun s : ℝ => gaussianKernel n s) t = Δ (gaussianKernel n t) := by
  funext x
  rw [deriv_pi (fun x => (hasDerivAt_gaussianKernel n ht x).differentiableAt)]
  exact heat_equation n ht x

end Poincare.D10.HeatKernelEuclidean
