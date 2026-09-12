/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré formalization longrun (D10-bochner-euclidean)

# Compatibility with mathlib's `gradient` and `Laplacian`

The D10 development defines `grad` and `lap` directly from `fderiv`.  This file
records that they agree with mathlib's `gradient` and `InnerProductSpace.laplacian`,
so the Bochner identity below is stated for the standard operators.
-/

import Poincare.D10.BochnerEuclidean.Corollary
import Mathlib.Analysis.Calculus.Gradient.Basic

noncomputable section

open scoped Topology InnerProductSpace
open Finset

namespace Poincare.D10.BochnerEuclidean

variable {n : ℕ}

/-- The standard basis of `ℝⁿ` sums back to the vector. -/
lemma sum_basis (y : E n) : ∑ i, y i • basis i = y := by
  simpa [basis, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
    (OrthonormalBasis.sum_repr (EuclideanSpace.basisFun (Fin n) ℝ) y)

/-- `⟪y, eᵢ⟫ = yᵢ`. -/
lemma inner_basis_right (y : E n) (i : Fin n) : ⟪y, basis i⟫_ℝ = y i := by
  have h : basis i = (EuclideanSpace.basisFun (Fin n) ℝ) i := by
    rw [EuclideanSpace.basisFun_apply]
    rfl
  rw [h, EuclideanSpace.inner_basisFun_real]

/-- Our gradient is mathlib's `gradient`. -/
lemma grad_eq_gradient (u : E n → ℝ) (x : E n) : grad u x = gradient u x := by
  apply ext_inner_left ℝ
  intro y
  rw [real_inner_comm (gradient u x) y, inner_gradient_left]
  have hfderiv : fderiv ℝ u x y = ∑ i, y i * fderiv ℝ u x (basis i) := by
    conv_lhs => rw [← sum_basis y]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [grad, inner_sum, hfderiv]
  simp only [inner_smul_right, inner_basis_right, D_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- Our Laplacian is mathlib's `Laplacian.laplacian`. -/
lemma lap_eq_laplacian (hu : ContDiff ℝ 2 u) (x : E n) : lap u x = Laplacian.laplacian u x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  have h2 : ContDiffAt ℝ 2 u x := hu.contDiffAt
  simp only [lap, iteratedFDeriv_two_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [D_D h2 i i]
  simp [basis, EuclideanSpace.basisFun_apply]

end Poincare.D10.BochnerEuclidean
