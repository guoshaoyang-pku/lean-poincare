/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré formalization longrun (D10-bochner-euclidean)

# The Bochner identity in Euclidean space

For a `C³` function `u : ℝⁿ → ℝ` we prove the Bochner (Weitzenböck) identity

  `Δ ‖∇u‖² = 2 ‖Hess u‖² + 2 ⟨∇u, ∇Δu⟩`,

where `‖Hess u‖²` is the Hilbert–Schmidt (Frobenius) squared norm `∑ᵢⱼ (∂ᵢ∂ⱼu)²`
of the Hessian and `⟨∇u, ∇Δu⟩` is the Euclidean inner product of `∇u` and `∇Δu`.

The proof is a direct componentwise computation: the only ingredients are the
product, power and sum rules for `fderiv`, and Clairaut's theorem on the symmetry
of second derivatives.
-/

import Poincare.D10.BochnerEuclidean.Basic

noncomputable section

open scoped Topology InnerProductSpace
open Finset

namespace Poincare.D10.BochnerEuclidean

variable {n : ℕ} {u : E n → ℝ}

/-!
## The two building blocks of the computation

`D i (gradNormSq u)` and `D i (D i (gradNormSq u))` are computed explicitly.
-/

lemma D_gradNormSq (hu : ContDiff ℝ 3 u) (i : Fin n) :
    D i (gradNormSq u) = fun x => ∑ k, 2 * D k u x * D i (D k u) x := by
  funext x
  have h2 : ∀ k : Fin n, ContDiffAt ℝ 2 (D k u) x :=
    fun k => (D_of_contDiff hu (m' := 2) (by norm_num) k).contDiffAt
  have h1 : ∀ k : Fin n, ContDiffAt ℝ 2 (fun y => (D k u y) ^ 2) x :=
    fun k => (h2 k).pow 2
  change fderiv ℝ (fun y => ∑ k, (D k u y) ^ 2) x (basis i) = _
  rw [fderiv_fun_sum (fun k _ => (h1 k).differentiableAt (by norm_num))]
  rw [_root_.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [fderiv_fun_pow 2 ((h2 k).differentiableAt (by norm_num))]
  rw [show (2 : ℕ) - 1 = 1 from rfl]
  simp only [smul_apply, smul_eq_mul, nsmul_eq_mul, D_apply, pow_one]
  ring

lemma DD_gradNormSq (hu : ContDiff ℝ 3 u) (i : Fin n) :
    D i (D i (gradNormSq u))
      = fun x => ∑ k, (2 * (D i (D k u) x) ^ 2 + 2 * D k u x * D i (D i (D k u)) x) := by
  funext x
  have h2 : ∀ k : Fin n, ContDiffAt ℝ 2 (D k u) x :=
    fun k => (D_of_contDiff hu (m' := 2) (by norm_num) k).contDiffAt
  have h1 : ∀ k : Fin n, ContDiffAt ℝ 1 (D i (D k u)) x :=
    fun k => D_of_contDiffAt (h2 k) (m' := 1) (by norm_num) i
  have hc : ∀ k : Fin n, DifferentiableAt ℝ (fun y => 2 * D k u y) x :=
    fun k => ((h2 k).differentiableAt (by norm_num)).const_mul 2
  have hmul : ∀ k : Fin n, ContDiffAt ℝ 1 (fun y => 2 * D k u y * D i (D k u) y) x := by
    intro k
    have hc' : ContDiffAt ℝ 1 (fun y => 2 * D k u y) x :=
      (contDiffAt_const (c := (2 : ℝ))).mul ((h2 k).of_le (by norm_num))
    exact hc'.mul (h1 k)
  change fderiv ℝ (D i (gradNormSq u)) x (basis i) = _
  rw [D_gradNormSq hu i]
  rw [fderiv_fun_sum (fun k _ => (hmul k).differentiableAt (by norm_num))]
  rw [_root_.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [fderiv_fun_mul (hc k) ((h1 k).differentiableAt (by norm_num))]
  rw [fderiv_const_mul ((h2 k).differentiableAt (by norm_num)) 2]
  simp only [smul_apply, add_apply, D_apply]
  ring

/-!
## The componentwise Bochner identity
-/

theorem bochner_identity_components (hu : ContDiff ℝ 3 u) (x : E n) :
    lap (gradNormSq u) x = 2 * hessNormSq u x + 2 * gradLapDot u x := by
  have hD : ∀ i : Fin n, D i (D i (gradNormSq u)) x =
      ∑ k, (2 * (D i (D k u) x) ^ 2 + 2 * D k u x * D i (D i (D k u)) x) :=
    fun i => congrFun (DD_gradNormSq hu i) x
  have hsum1 : (∑ i : Fin n, ∑ k : Fin n, 2 * (D i (D k u) x) ^ 2)
      = 2 * ∑ i : Fin n, ∑ k : Fin n, (D i (D k u) x) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  have hsum2 : (∑ i : Fin n, ∑ k : Fin n, 2 * D k u x * D i (D i (D k u)) x)
      = 2 * ∑ k : Fin n, D k u x * (∑ i : Fin n, D i (D i (D k u)) x) := by
    have h1 : (∑ i : Fin n, ∑ k : Fin n, 2 * D k u x * D i (D i (D k u)) x)
        = ∑ i : Fin n, ∑ k : Fin n, 2 * (D k u x * D i (D i (D k u)) x) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
      ring
    rw [h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
  calc lap (gradNormSq u) x
      = ∑ i : Fin n, D i (D i (gradNormSq u)) x := rfl
    _ = ∑ i : Fin n, ∑ k : Fin n,
          (2 * (D i (D k u) x) ^ 2 + 2 * D k u x * D i (D i (D k u)) x) :=
        Finset.sum_congr rfl (fun i _ => hD i)
    _ = (∑ i : Fin n, ∑ k : Fin n, 2 * (D i (D k u) x) ^ 2)
        + (∑ i : Fin n, ∑ k : Fin n, 2 * D k u x * D i (D i (D k u)) x) := by
        simp only [Finset.sum_add_distrib]
    _ = 2 * hessNormSq u x + 2 * gradLapDot u x := by
        rw [hsum1, hsum2, gradLapDot]
        have hfun : (fun k : Fin n => D k u x * (∑ i : Fin n, D i (D i (D k u)) x))
            = fun k : Fin n => D k u x * D k (lap u) x := by
          funext k
          rw [D_lap hu k x]
        rw [hfun]
        simp only [hessNormSq]

/-!
## Bridge lemmas: the coordinate expressions are the geometric ones
-/

/-- The coordinates of the gradient are the coordinate derivatives. -/
lemma grad_apply (u : E n → ℝ) (x : E n) (j : Fin n) :
    (grad u x) j = D j u x := by
  simp only [grad, basis, D, Finset.sum_apply, WithLp.ofLp_sum, WithLp.ofLp_smul,
    Pi.smul_apply, PiLp.ofLp_single, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    have hji : ¬ (j = i) := fun h => hi h.symm
    simp [hji]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- `gradNormSq` is the squared Euclidean norm of the gradient. -/
lemma norm_sq_grad (u : E n → ℝ) (x : E n) :
    ‖grad u x‖ ^ 2 = gradNormSq u x := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs, gradNormSq, grad_apply]

/-- `gradLapDot` is the Euclidean inner product `⟨∇u, ∇Δu⟩`. -/
lemma inner_grad_grad_lap (u : E n → ℝ) (x : E n) :
    ⟪grad u x, grad (lap u) x⟫_ℝ = gradLapDot u x := by
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply, gradLapDot, grad_apply]

/-- `hessNormSq` is the sum of squares of the entries of the Hessian matrix. -/
lemma hessNormSq_eq (hu : ContDiff ℝ 3 u) (x : E n) :
    hessNormSq u x = ∑ i : Fin n, ∑ j : Fin n, (hess u x (basis i) (basis j)) ^ 2 := by
  have h2 : ContDiffAt ℝ 2 u x := (hu.of_le (by norm_num)).contDiffAt
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [D_D h2 j i]
  rfl

/-!
## The Bochner identity in geometric form
-/

/-- **Bochner identity.** For a `C³` function `u` on `ℝⁿ`,

`Δ(‖∇u‖²) = 2 ∑ᵢⱼ (∂ᵢ∂ⱼu)² + 2 ⟨∇u, ∇Δu⟩`,

where the first term on the right is the Hilbert–Schmidt squared norm of the Hessian. -/
theorem bochner_identity (hu : ContDiff ℝ 3 u) (x : E n) :
    lap (fun y => ‖grad u y‖ ^ 2) x
      = 2 * hessNormSq u x + 2 * ⟪grad u x, grad (lap u) x⟫_ℝ := by
  have hfun : (fun y => ‖grad u y‖ ^ 2) = gradNormSq u :=
    funext fun y => norm_sq_grad u y
  rw [hfun, bochner_identity_components hu x, inner_grad_grad_lap, gradLapDot]

end Poincare.D10.BochnerEuclidean
