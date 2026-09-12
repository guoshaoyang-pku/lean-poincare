/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré formalization longrun (D10-bochner-euclidean)

# Gradient, Hessian and Laplacian on `ℝⁿ`

This file sets up the basic objects of the D10 Bochner-identity development.
For a scalar function `u : ℝⁿ → ℝ` we define, purely in terms of mathlib's `fderiv`:

* `D i u`      : the `i`-th coordinate derivative `x ↦ D u(x)(eᵢ)`;
* `grad u x`    : the gradient `∑ᵢ ∂ᵢu(x) • eᵢ`;
* `hess u x`    : the Hessian `D²u(x)`, as a continuous bilinear form;
* `lap u x`     : the Laplacian `∑ᵢ ∂ᵢ∂ᵢu(x)`;
* `gradNormSq u`, `hessNormSq u`, `gradLapDot u` : the quantities appearing in the
  Bochner identity, written out in coordinates.

All derivatives are honest `fderiv` derivatives; no identity is assumed.
-/

import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section

open scoped Topology
open Finset

namespace Poincare.D10.BochnerEuclidean

variable {n : ℕ}

/-- `ℝⁿ`, the Euclidean space `EuclideanSpace ℝ (Fin n)`. -/
abbrev E (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The `i`-th standard basis vector `eᵢ` of `ℝⁿ`. -/
def basis (i : Fin n) : E n := EuclideanSpace.single i (1 : ℝ)

@[simp] lemma basis_apply (i j : Fin n) : (basis i : E n) j = if j = i then (1 : ℝ) else 0 := by
  simp [basis]

/-- The `i`-th coordinate derivative `∂ᵢu(x) = Du(x)(eᵢ)`, defined from `fderiv`. -/
noncomputable def D (i : Fin n) (u : E n → ℝ) : E n → ℝ :=
  fun x => fderiv ℝ u x (basis i)

@[simp] lemma D_apply (i : Fin n) (u : E n → ℝ) (x : E n) :
    D i u x = fderiv ℝ u x (basis i) := rfl

/-- The gradient of a scalar function, `∇u(x) = ∑ᵢ ∂ᵢu(x) • eᵢ`. -/
noncomputable def grad (u : E n → ℝ) (x : E n) : E n :=
  ∑ i, D i u x • basis i

/-- `‖∇u(x)‖²`, written out in coordinates. -/
noncomputable def gradNormSq (u : E n → ℝ) (x : E n) : ℝ :=
  ∑ i, (D i u x) ^ 2

/-- The Hessian `D²u(x)`, as a continuous bilinear form. -/
noncomputable def hess (u : E n → ℝ) (x : E n) : E n →L[ℝ] E n →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ u) x

/-- The Hilbert–Schmidt (Frobenius) squared norm of the Hessian, `∑ᵢⱼ (∂ᵢ∂ⱼu(x))²`. -/
noncomputable def hessNormSq (u : E n → ℝ) (x : E n) : ℝ :=
  ∑ i, ∑ j, (D i (D j u) x) ^ 2

/-- The Laplacian `Δu(x) = ∑ᵢ ∂ᵢ∂ᵢu(x)`, the trace of the Hessian. -/
noncomputable def lap (u : E n → ℝ) (x : E n) : ℝ :=
  ∑ i, D i (D i u) x

/-- The pairing `⟨∇u, ∇(Δu)⟩`, written out in coordinates. -/
noncomputable def gradLapDot (u : E n → ℝ) (x : E n) : ℝ :=
  ∑ i, D i u x * D i (lap u) x

/-- A function is harmonic when its Laplacian vanishes identically. -/
def Harmonic (u : E n → ℝ) : Prop := ∀ x, lap u x = 0

/-!
## Elementary calculus of the coordinate derivative `D`

These lemmas are the only place where the product/power/sum rules for `fderiv` are used.
-/

section Calculus

variable {u f g : E n → ℝ} {x : E n}

/-- `D` lowers smoothness by one. -/
lemma D_of_contDiff {m m' : WithTop ℕ∞} (hf : ContDiff ℝ m f) (hm : m' + 1 ≤ m)
    (i : Fin n) : ContDiff ℝ m' (D i f) := by
  have h2 : ContDiff ℝ m' (fun y => (ContinuousLinearMap.apply ℝ ℝ (basis i)) (fderiv ℝ f y)) :=
    (ContinuousLinearMap.apply ℝ ℝ (basis i)).contDiff.comp (hf.fderiv_right hm)
  have h3 : (fun y => (ContinuousLinearMap.apply ℝ ℝ (basis i)) (fderiv ℝ f y)) =
      fun y => fderiv ℝ f y (basis i) := by
    funext y
    exact ContinuousLinearMap.apply_apply (basis i) (fderiv ℝ f y)
  rw [h3] at h2
  exact h2

/-- `D` lowers smoothness by one, pointwise version. -/
lemma D_of_contDiffAt {m m' : WithTop ℕ∞} (hf : ContDiffAt ℝ m f x) (hm : m' + 1 ≤ m)
    (i : Fin n) : ContDiffAt ℝ m' (D i f) x := by
  have h2 : ContDiffAt ℝ m'
      (fun y => (ContinuousLinearMap.apply ℝ ℝ (basis i)) (fderiv ℝ f y)) x :=
    ((ContinuousLinearMap.apply ℝ ℝ (basis i)).contDiff (n := m')).contDiffAt.comp x
      (hf.fderiv_right hm)
  have h3 : (fun y => (ContinuousLinearMap.apply ℝ ℝ (basis i)) (fderiv ℝ f y)) =
      fun y => fderiv ℝ f y (basis i) := by
    funext y
    exact ContinuousLinearMap.apply_apply (basis i) (fderiv ℝ f y)
  rw [h3] at h2
  exact h2

lemma D_add (hf : ContDiffAt ℝ 1 f x) (hg : ContDiffAt ℝ 1 g x) (i : Fin n) :
    D i (fun y => f y + g y) x = D i f x + D i g x := by
  simp only [D]
  rw [fderiv_fun_add (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))]
  simp

lemma D_const (c : ℝ) (i : Fin n) : D i (fun _ : E n => c) = 0 := by
  funext x
  simp [D]

lemma D_mul (hf : ContDiffAt ℝ 1 f x) (hg : ContDiffAt ℝ 1 g x) (i : Fin n) :
    D i (fun y => f y * g y) x = f x * D i g x + g x * D i f x := by
  simp only [D]
  rw [fderiv_fun_mul (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))]
  simp [smul_apply, add_apply]

lemma D_const_mul (hf : ContDiffAt ℝ 1 f x) (c : ℝ) (i : Fin n) :
    D i (fun y => c * f y) x = c * D i f x := by
  simp only [D]
  rw [fderiv_const_mul (hf.differentiableAt (by norm_num)) c]
  simp [smul_apply]

lemma D_pow_two (hf : ContDiffAt ℝ 1 f x) (i : Fin n) :
    D i (fun y => (f y) ^ 2) x = 2 * f x * D i f x := by
  simp only [D]
  rw [fderiv_fun_pow 2 (hf.differentiableAt (by norm_num))]
  simp [smul_apply, nsmul_eq_mul]

lemma D_sum {ι : Type*} (s : Finset ι) (F : ι → E n → ℝ)
    (hF : ∀ k ∈ s, ContDiffAt ℝ 1 (F k) x) (i : Fin n) :
    D i (fun y => ∑ k ∈ s, F k y) x = ∑ k ∈ s, D i (F k) x := by
  simp only [D]
  rw [fderiv_fun_sum (fun k hk => (hF k hk).differentiableAt (by norm_num))]
  exact _root_.sum_apply s (fun k => fderiv ℝ (F k) x) (basis i)

/-- The derivative of `D i f` is the second derivative of `f`, evaluated on `eᵢ`. -/
lemma fderiv_D (hf : ContDiffAt ℝ 2 f x) (i : Fin n) :
    fderiv ℝ (D i f) x
      = (ContinuousLinearMap.apply ℝ ℝ (basis i)).comp (fderiv ℝ (fderiv ℝ f) x) := by
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : HasFDerivAt
      (fun y => (ContinuousLinearMap.apply ℝ ℝ (basis i)) (fderiv ℝ f y))
      ((ContinuousLinearMap.apply ℝ ℝ (basis i)).comp (fderiv ℝ (fderiv ℝ f) x)) x :=
    (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.apply ℝ ℝ (basis i))).comp x
      hdiff.hasFDerivAt
  have h3 : (fun y => (ContinuousLinearMap.apply ℝ ℝ (basis i)) (fderiv ℝ f y)) =
      fun y => fderiv ℝ f y (basis i) := by
    funext y
    exact ContinuousLinearMap.apply_apply (basis i) (fderiv ℝ f y)
  rw [h3] at h2
  exact h2.fderiv

/-- Second coordinate derivatives are the entries of the Hessian. -/
lemma D_D (hf : ContDiffAt ℝ 2 f x) (i j : Fin n) :
    D j (D i f) x = fderiv ℝ (fderiv ℝ f) x (basis j) (basis i) := by
  change fderiv ℝ (D i f) x (basis j) = fderiv ℝ (fderiv ℝ f) x (basis j) (basis i)
  rw [fderiv_D hf i]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]

/-- Clairaut's theorem in coordinates: mixed second derivatives commute. -/
lemma D_comm (hf : ContDiffAt ℝ 2 f x) (i j : Fin n) :
    D j (D i f) x = D i (D j f) x := by
  rw [D_D hf i j, D_D hf j i]
  exact (hf.isSymmSndFDerivAt (by simp)).eq (basis j) (basis i)

/-- Third order mixed derivatives: `∂ᵢ∂ᵢ∂ₖu = ∂ₖ∂ᵢ∂ᵢu` for `C³` functions. -/
lemma DDD_comm (hu : ContDiff ℝ 3 u) (i k : Fin n) (x : E n) :
    D i (D i (D k u)) x = D k (D i (D i u)) x := by
  have h2u : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have h2 : ContDiff ℝ 2 (D i u) := D_of_contDiff hu (m' := 2) (by norm_num) i
  have hkey : D i (D k u) = D k (D i u) := by
    funext y
    exact (D_comm (x := y) h2u.contDiffAt i k).symm
  calc D i (D i (D k u)) x
      = D i (D k (D i u)) x := by rw [hkey]
    _ = D k (D i (D i u)) x := by
        exact (D_comm (x := x) h2.contDiffAt i k).symm

/-- The coordinate derivative of the Laplacian. -/
lemma D_lap (hu : ContDiff ℝ 3 u) (k : Fin n) (x : E n) :
    D k (lap u) x = ∑ i, D i (D i (D k u)) x := by
  have h2 : ∀ i : Fin n, ContDiff ℝ 2 (D i u) :=
    fun i => D_of_contDiff hu (m' := 2) (by norm_num) i
  have h1 : ∀ i : Fin n, ContDiffAt ℝ 1 (D i (D i u)) x := fun i =>
    (D_of_contDiff (h2 i) (m' := 1) (by norm_num) i).contDiffAt
  have hlap : lap u = fun y => ∑ i, D i (D i u) y := rfl
  rw [hlap]
  change fderiv ℝ (fun y => ∑ i, D i (D i u) y) x (basis k)
    = ∑ i, D i (D i (D k u)) x
  rw [fderiv_fun_sum (fun i _ => (h1 i).differentiableAt (by norm_num))]
  rw [_root_.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (DDD_comm hu i k x).symm

end Calculus

end Poincare.D10.BochnerEuclidean
