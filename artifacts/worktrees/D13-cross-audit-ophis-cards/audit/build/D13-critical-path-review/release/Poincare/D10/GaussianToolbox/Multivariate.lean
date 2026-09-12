/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D10-gaussian-toolbox builder
-/
module

public import Poincare.D10.GaussianToolbox.Basic
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Poincare.GaussianToolbox.Multivariate

**The `n`-dimensional Gaussian factors as a product of 1D integrals (Fubini), and has total
mass `1`.**

Everything is proved from the one-dimensional results of `Basic.lean` via mathlib's Fubini
theorem for finite products, `MeasureTheory.integral_fintype_prod_eq_prod`.

Main results:

* `integral_gaussianVec_fubini` — **Fubini factorisation**
  `∫ x : Fin n → ℝ, ∏ i, exp (-(x i)²) = ∏ i, ∫ t, exp (-t²)`;
* `integral_gaussianVec` — `∫ x, ∏ i, exp (-(x i)²) = (√π)^n`;
* `integral_gaussianVec_eq_pi_rpow` — the same integral equals `π ^ (n/2)`;
* `integral_gaussianVecNormalized` — **total mass `1`** for the normalised density
  `x ↦ (√π)^{-n} ∏ i, exp (-(x i)²)`;
* `gaussianVec_eq_exp_neg_sum_sq` — `∏ i, exp (-(x i)²) = exp (-∑ i, (x i)²)`;
* `gaussianVec_eq_exp_neg_normSq` — the same identity through the Euclidean norm on `ℝⁿ`;
* `integral_standardGaussianVec` and `integral_standardGaussianDensity` — the standard
  normalisation `exp (-∑ i, (x i)² / 2)` with total mass `1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Filter Topology
open scoped Real Topology

namespace Poincare.GaussianToolbox

/-! ## Definitions -/

/-- The `n`-dimensional Gaussian weight, as a product of one-dimensional Gaussian kernels. -/
def gaussianVec (n : ℕ) (x : Fin n → ℝ) : ℝ := ∏ i, gaussianKernel 1 (x i)

/-- The normalised `n`-dimensional standard Gaussian density (product form), with total mass
`1` by `integral_gaussianVecNormalized`. -/
def gaussianVecNormalized (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  (sqrt π) ^ (-(n : ℝ)) * gaussianVec n x

/-- The standard Gaussian weight `x ↦ ∏ i, exp (-(x i)² / 2)` (variance `1` in each
coordinate). -/
def standardGaussianVec (n : ℕ) (x : Fin n → ℝ) : ℝ := ∏ i, gaussianKernel (1 / 2) (x i)

/-- The normalised `n`-dimensional standard Gaussian density `(2π)^{-n/2} exp (-‖x‖²/2)`,
with total mass `1` by `integral_standardGaussianDensity`. -/
def standardGaussianDensity (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  (2 * π) ^ (-(n : ℝ) / 2) * standardGaussianVec n x

lemma gaussianVec_def (n : ℕ) (x : Fin n → ℝ) :
    gaussianVec n x = ∏ i, gaussianKernel 1 (x i) := rfl

lemma gaussianVecNormalized_def (n : ℕ) (x : Fin n → ℝ) :
    gaussianVecNormalized n x = (sqrt π) ^ (-(n : ℝ)) * gaussianVec n x := rfl

lemma standardGaussianVec_def (n : ℕ) (x : Fin n → ℝ) :
    standardGaussianVec n x = ∏ i, gaussianKernel (1 / 2) (x i) := rfl

lemma standardGaussianDensity_def (n : ℕ) (x : Fin n → ℝ) :
    standardGaussianDensity n x = (2 * π) ^ (-(n : ℝ) / 2) * standardGaussianVec n x := rfl

/-! ## Fubini factorisation and total mass -/

/-- **Fubini**: the `n`-dimensional Gaussian integral is the product of the one-dimensional
Gaussian integrals. -/
theorem integral_gaussianVec_fubini (n : ℕ) :
    ∫ x : Fin n → ℝ, gaussianVec n x = ∏ _i : Fin n, ∫ t : ℝ, gaussianKernel 1 t := by
  simp only [gaussianVec_def]
  rw [MeasureTheory.volume_pi]
  exact MeasureTheory.integral_fintype_prod_eq_prod (fun _ t => gaussianKernel 1 t)

/-- The `n`-dimensional Gaussian integral: `∫ x, ∏ i, exp (-(x i)²) = (√π)^n`. -/
theorem integral_gaussianVec (n : ℕ) :
    ∫ x : Fin n → ℝ, gaussianVec n x = (sqrt π) ^ n := by
  rw [integral_gaussianVec_fubini, integral_moment_zero, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The `n`-dimensional Gaussian integral in exponential form: `π ^ (n/2)`. -/
theorem integral_gaussianVec_eq_pi_rpow (n : ℕ) :
    ∫ x : Fin n → ℝ, gaussianVec n x = π ^ ((n : ℝ) / 2) := by
  rw [integral_gaussianVec, ← Real.rpow_natCast (sqrt π) n, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (le_of_lt pi_pos)]
  congr 1
  ring

/-- **Total mass `1`** of the normalised `n`-dimensional Gaussian density. -/
theorem integral_gaussianVecNormalized (n : ℕ) :
    ∫ x : Fin n → ℝ, gaussianVecNormalized n x = 1 := by
  simp only [gaussianVecNormalized_def]
  rw [integral_const_mul, integral_gaussianVec,
    ← Real.rpow_natCast (sqrt π) n, ← Real.rpow_add (by positivity : (0 : ℝ) < sqrt π),
    neg_add_cancel, Real.rpow_zero]

/-! ## The sum-of-squares and norm forms -/

/-- The product of one-dimensional Gaussian factors is the exponential of minus the sum of
squares. -/
theorem gaussianVec_eq_exp_neg_sum_sq (n : ℕ) (x : Fin n → ℝ) :
    gaussianVec n x = exp (-∑ i, (x i) ^ 2) := by
  simp only [gaussianVec_def, gaussianKernel_def, one_mul]
  rw [← Real.exp_sum, Finset.sum_neg_distrib]

/-- The `n`-dimensional Gaussian weight through the Euclidean norm on `EuclideanSpace ℝ (Fin n)`. -/
theorem gaussianVec_eq_exp_neg_normSq (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    (∏ i, gaussianKernel 1 (x.ofLp i)) = exp (-‖x‖ ^ 2) := by
  rw [← gaussianVec_def, gaussianVec_eq_exp_neg_sum_sq, EuclideanSpace.norm_sq_eq]
  congr 1
  rw [neg_inj]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.norm_eq_abs, sq_abs]

/-! ## The standard normalisation `exp (-∑ xᵢ² / 2)` -/

/-- The one-dimensional integral of the standard Gaussian kernel
`∫ t, exp (-(t²/2)) = √(2π)`. -/
theorem integral_gaussianKernel_half : ∫ t : ℝ, gaussianKernel (1 / 2) t = sqrt (2 * π) := by
  rw [integral_gaussianKernel]
  congr 1
  field_simp

/-- Fubini for the standard Gaussian weight. -/
theorem integral_standardGaussianVec_fubini (n : ℕ) :
    ∫ x : Fin n → ℝ, standardGaussianVec n x
      = ∏ _i : Fin n, ∫ t : ℝ, gaussianKernel (1 / 2) t := by
  simp only [standardGaussianVec_def]
  rw [MeasureTheory.volume_pi]
  exact MeasureTheory.integral_fintype_prod_eq_prod (fun _ t => gaussianKernel (1 / 2) t)

theorem integral_standardGaussianVec (n : ℕ) :
    ∫ x : Fin n → ℝ, standardGaussianVec n x = (sqrt (2 * π)) ^ n := by
  rw [integral_standardGaussianVec_fubini, integral_gaussianKernel_half, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- The standard Gaussian weight is `exp (-∑ i, (x i)² / 2)`. -/
theorem standardGaussianVec_eq_exp_neg_sum_sq (n : ℕ) (x : Fin n → ℝ) :
    standardGaussianVec n x = exp (-(∑ i, (x i) ^ 2) / 2) := by
  simp only [standardGaussianVec_def, gaussianKernel_def]
  rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.mul_sum]
  congr 1
  ring

/-- **Total mass `1`** of the standard normalised `n`-dimensional Gaussian density. -/
theorem integral_standardGaussianDensity (n : ℕ) :
    ∫ x : Fin n → ℝ, standardGaussianDensity n x = 1 := by
  simp only [standardGaussianDensity_def]
  rw [integral_const_mul, integral_standardGaussianVec,
    ← Real.rpow_natCast (sqrt (2 * π)) n, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (le_of_lt (by positivity : (0 : ℝ) < 2 * π))]
  rw [show (1 / 2 : ℝ) * (n : ℝ) = (n : ℝ) / 2 by ring,
    show -(n : ℝ) / 2 = -((n : ℝ) / 2) by ring,
    ← Real.rpow_add (by positivity : (0 : ℝ) < 2 * π), neg_add_cancel, Real.rpow_zero]

end Poincare.GaussianToolbox
