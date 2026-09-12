/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (Euclidean chart calculus API)

# Euclidean chart calculus: partial derivatives, radial chain rule, Laplacian

This module supplies the missing calculus API on the D12 chart model `Vec d = Fin d → ℝ`
(mathlib pin `7974e751be`):

* `partialDeriv_eq_deriv_update` — the chart partial derivative `∂ᵢf(x) = fderiv f x eᵢ`
  is the one-dimensional derivative of `t ↦ f (x with i := t)` at `x i` (for `f`
  differentiable at `x`); this is what makes explicit chart computations possible;
* the product/sum rules `partialDeriv_mul`, `partialDeriv_add`;
* `partialDeriv_apply_single` — `∂ᵢ (φ ∘ coordᵢ) = φ'` and the vanishing of `∂ᵢ (φ ∘ coordⱼ)`
  for `i ≠ j`;
* `hasFDerivAt_radSq` / `fderiv_radSq_apply` — the derivative of the squared radius
  `S x = ∑ j, x j ^ 2` is `v ↦ ∑ j (2 x j) v j`, so `dS_x(eᵢ) = 2 xᵢ`;
* `partialDeriv_radial` / `partialDeriv_radial_second` — the chain rule for radial
  functions `x ↦ ψ (S x)`: first partial `ψ'(S x) · 2xᵢ`, second partial
  `ψ''(S x) · (2xᵢ)² + ψ'(S x) · 2`;
* `euclidean_density_eq_one`, `euclidean_grad_eq`, `euclidean_laplacian_eq` — for the
  Euclidean chart metric, `√det g = 1`, `grad = (∂ᵢ)` and
  `Δu = ∑ i, ∂ᵢ∂ᵢu`;
* `laplacian_radial` — hence `Δ(ψ ∘ S)(x) = 4 S(x) ψ''(S x) + 2 d ψ'(S x)`.

Every declaration is proved; no `sorry`, `axiom`, `unsafe`, `native_decide` or
`proof_wanted` appears in this file.
-/
import Poincare.D12.VolumeIBP.IBP

open scoped BigOperators

noncomputable section

open MeasureTheory

namespace Poincare.D13.EuclideanChart

open Poincare.D12.VolumeIBP

variable {n : ℕ}

namespace ChartMetric

/-! ## The partial derivative as a one-dimensional derivative -/

/-- **Partial derivative along a coordinate line.** For `f` differentiable at `x`, the D12
chart partial derivative `∂ᵢf(x) = fderiv f x eᵢ` equals the ordinary derivative of
`t ↦ f (Function.update x i t)` at `x i`. -/
lemma partialDeriv_eq_deriv_update (f : Vec (n + 1) → ℝ) (x : Vec (n + 1)) (i : Fin (n + 1))
    (hf : DifferentiableAt ℝ f x) :
    ChartMetric.partialDeriv i f x = deriv (fun t : ℝ => f (Function.update x i t)) (x i) := by
  have hupd : HasFDerivAt (Function.update x i)
      (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) (x i) :=
    hasFDerivAt_update x (x i)
  have hx : Function.update x i (x i) = x := by
    funext j
    by_cases h : j = i
    · subst h; rw [Function.update_self]
    · rw [Function.update_of_ne h]
  have hf' : HasFDerivAt f (fderiv ℝ f x) (Function.update x i (x i)) := by
    simpa [hx] using hf.hasFDerivAt
  have hcomp : HasFDerivAt (f ∘ Function.update x i)
      ((fderiv ℝ f x).comp
        (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ)))) (x i) :=
    HasFDerivAt.comp (x := x i) (f := Function.update x i) (g := f)
      (f' := ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ)))
      (g' := fderiv ℝ f x) hf' hupd
  have h2 : (fderiv ℝ (f ∘ Function.update x i) (x i)) 1 = fderiv ℝ f x (Pi.single i 1) := by
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]
    congr 1
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [ContinuousLinearMap.pi_apply, Pi.single_eq_of_ne h]
  rw [ChartMetric.partialDeriv, ← h2]
  rfl

/-- **Sum rule for the chart partial derivative.** -/
lemma partialDeriv_add (f g : Vec (n + 1) → ℝ) (x : Vec (n + 1)) (i : Fin (n + 1))
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ChartMetric.partialDeriv i (fun y => f y + g y) x =
      ChartMetric.partialDeriv i f x + ChartMetric.partialDeriv i g x := by
  change (fderiv ℝ (f + g) x) (Pi.single i 1) = _
  rw [ChartMetric.partialDeriv, fderiv_add hf hg]
  simp [ChartMetric.partialDeriv]

/-- **Product rule for the chart partial derivative.** -/
lemma partialDeriv_mul (f g : Vec (n + 1) → ℝ) (x : Vec (n + 1)) (i : Fin (n + 1))
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ChartMetric.partialDeriv i (fun y => f y * g y) x =
      ChartMetric.partialDeriv i f x * g x + f x * ChartMetric.partialDeriv i g x := by
  change (fderiv ℝ (f * g) x) (Pi.single i 1) = _
  rw [ChartMetric.partialDeriv, fderiv_mul hf hg]
  simp only [add_apply, smul_apply, ChartMetric.partialDeriv]
  ring

/-- **Partial derivative of a coordinate function.** `∂ᵢ (φ ∘ coordᵢ)(x) = φ'(xᵢ)`. -/
lemma partialDeriv_apply_single (φ : ℝ → ℝ) (x : Vec (n + 1)) (i : Fin (n + 1))
    (hφ : DifferentiableAt ℝ φ (x i)) :
    ChartMetric.partialDeriv i (fun y => φ (y i)) x = deriv φ (x i) := by
  have hf : DifferentiableAt ℝ (fun y : Vec (n + 1) => φ (y i)) x :=
    hφ.comp x (differentiableAt_apply i x)
  rw [partialDeriv_eq_deriv_update _ _ _ hf]
  congr 1
  funext t
  rw [Function.update_self]

/-- **Partial derivative in a different coordinate.** `∂ᵢ (φ ∘ coordⱼ)(x) = 0` for `i ≠ j`. -/
lemma partialDeriv_apply_single_of_ne (φ : ℝ → ℝ) (x : Vec (n + 1)) (i j : Fin (n + 1))
    (hij : i ≠ j) (hφ : DifferentiableAt ℝ φ (x j)) :
    ChartMetric.partialDeriv i (fun y => φ (y j)) x = 0 := by
  have hf : DifferentiableAt ℝ (fun y : Vec (n + 1) => φ (y j)) x :=
    hφ.comp x (differentiableAt_apply j x)
  rw [partialDeriv_eq_deriv_update _ _ _ hf]
  have hconst : (fun t : ℝ => φ ((Function.update x i t) j)) = fun _ : ℝ => φ (x j) := by
    funext t
    rw [Function.update_of_ne (Ne.symm hij)]
  rw [hconst, deriv_const]

/-- **Partial derivative of a constant multiple of a coordinate.** -/
lemma partialDeriv_const_mul_coord (c : ℝ) (x : Vec (n + 1)) (i : Fin (n + 1)) :
    ChartMetric.partialDeriv i (fun y : Vec (n + 1) => c * y i) x = c := by
  have hφ : DifferentiableAt ℝ (fun t : ℝ => c * t) (x i) :=
    differentiableAt_id.const_mul c
  have hid : deriv (fun t : ℝ => c * t) (x i) = c := by
    have h : HasDerivAt (fun t : ℝ => c * t) c (x i) := by
      simpa using (hasDerivAt_id (x i)).const_mul c
    rw [h.deriv]
  rw [show (fun y : Vec (n + 1) => c * y i) = (fun y => (fun t : ℝ => c * t) (y i)) by rfl]
  rw [partialDeriv_apply_single _ _ _ hφ, hid]

/-- The partial derivative of the constant function vanishes. -/
lemma partialDeriv_const (c : ℝ) (x : Vec (n + 1)) (i : Fin (n + 1)) :
    ChartMetric.partialDeriv i (fun _ : Vec (n + 1) => c) x = 0 := by
  rw [ChartMetric.partialDeriv]
  simp

/-! ## The squared radius and radial chain rules -/

/-- The squared radius `S x = ∑ j, x j ^ 2` on the chart. -/
def radSq (x : Vec (n + 1)) : ℝ := ∑ j, x j ^ 2

/-- `radSq` is differentiable everywhere. -/
lemma radSq_differentiableAt (x : Vec (n + 1)) :
    DifferentiableAt ℝ (fun y : Vec (n + 1) => radSq y) x := by
  unfold radSq
  fun_prop

/-- Splitting off the `i`-th coordinate of the squared radius:
`S (x with i := t) = t² + ∑_{j ≠ i} x j²`. -/
lemma radSq_update (x : Vec (n + 1)) (i : Fin (n + 1)) (t : ℝ) :
    radSq (Function.update x i t) = t ^ 2 + ∑ j ∈ Finset.univ.erase i, x j ^ 2 := by
  unfold radSq
  rw [← Finset.sum_erase_add Finset.univ
    (fun j => (Function.update x i t) j ^ 2) (Finset.mem_univ i)]
  rw [Function.update_self, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

/-- Updating a vector at its own coordinate does not change it. -/
lemma update_self_eq (x : Vec (n + 1)) (i : Fin (n + 1)) :
    Function.update x i (x i) = x := by
  funext j
  by_cases h : j = i
  · subst h; rw [Function.update_self]
  · rw [Function.update_of_ne h]

/-- **Radial chain rule, first order.** For `ψ` differentiable at `S x`,
`∂ᵢ (ψ ∘ S)(x) = ψ'(S x) · 2 xᵢ`. -/
lemma partialDeriv_radial (ψ : ℝ → ℝ) (ψ' : ℝ) (x : Vec (n + 1)) (i : Fin (n + 1))
    (hψ : HasDerivAt ψ ψ' (radSq x)) :
    ChartMetric.partialDeriv i (fun y => ψ (radSq y)) x = ψ' * (2 * x i) := by
  have hdiff : DifferentiableAt ℝ (fun y : Vec (n + 1) => ψ (radSq y)) x :=
    hψ.differentiableAt.comp x (radSq_differentiableAt x)
  rw [partialDeriv_eq_deriv_update _ _ _ hdiff]
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x i) (x i) := by
    simpa using hasDerivAt_pow 2 (x i)
  have hmain : HasDerivAt (fun t : ℝ => t ^ 2 + ∑ j ∈ Finset.univ.erase i, x j ^ 2)
      (2 * x i) (x i) :=
    hsq.add_const _
  have hψ' : HasDerivAt ψ ψ' (x i ^ 2 + ∑ j ∈ Finset.univ.erase i, x j ^ 2) := by
    rw [← radSq_update x i (x i), update_self_eq x i]
    exact hψ
  have hcomp := hψ'.comp (x i) hmain
  have hfun : (fun t : ℝ => ψ (radSq (Function.update x i t)))
      = fun t : ℝ => ψ (t ^ 2 + ∑ j ∈ Finset.univ.erase i, x j ^ 2) := by
    funext t
    rw [radSq_update]
  rw [hfun]
  exact hcomp.deriv

/-- **Radial chain rule, second order.** For `ψ` differentiable everywhere with
`(deriv ψ)'(S x)` the second derivative of `ψ` at `S x`,
`∂ᵢ∂ᵢ (ψ ∘ S)(x) = ψ''(S x) · (2 xᵢ)² + ψ'(S x) · 2`. -/
lemma partialDeriv_radial_second (ψ : ℝ → ℝ) (x : Vec (n + 1)) (i : Fin (n + 1))
    (hψ : ∀ s : ℝ, HasDerivAt ψ (deriv ψ s) s)
    (hψ' : HasDerivAt (deriv ψ) (deriv (deriv ψ) (radSq x)) (radSq x)) :
    ChartMetric.partialDeriv i (fun y => ChartMetric.partialDeriv i (fun z => ψ (radSq z)) y) x =
      deriv (deriv ψ) (radSq x) * (2 * x i) ^ 2 + deriv ψ (radSq x) * 2 := by
  have hfun : (fun y => ChartMetric.partialDeriv i (fun z => ψ (radSq z)) y) =
      fun y => deriv ψ (radSq y) * (2 * y i) := by
    funext y
    exact partialDeriv_radial ψ (deriv ψ (radSq y)) y i (hψ (radSq y))
  rw [hfun]
  have hd1 : DifferentiableAt ℝ (fun y => deriv ψ (radSq y)) x :=
    hψ'.differentiableAt.comp x (radSq_differentiableAt x)
  have hd2 : DifferentiableAt ℝ (fun y : Vec (n + 1) => 2 * y i) x := by fun_prop
  rw [partialDeriv_mul _ _ _ _ hd1 hd2]
  rw [partialDeriv_radial (deriv ψ) (deriv (deriv ψ) (radSq x)) x i hψ']
  rw [partialDeriv_const_mul_coord]
  ring

/-! ## The Euclidean chart metric: density, gradient, Laplacian -/

/-- The Riemannian density of the Euclidean chart metric is `1`. -/
lemma euclidean_density_eq_one (x : Vec (n + 1)) :
    (ChartMetric.euclideanChartMetric (n + 1)).density x = 1 := by
  unfold ChartMetric.density
  have hm : (ChartMetric.euclideanChartMetric (n + 1)).matrix x = 1 := by
    ext i j
    simp [ChartMetric.matrix, ChartMetric.euclideanChartMetric, Matrix.one_apply]
  rw [hm, Matrix.det_one, Real.sqrt_one]

/-- The Euclidean chart gradient is the coordinate partial derivative. -/
lemma euclidean_grad_eq (u : Vec (n + 1) → ℝ) (x : Vec (n + 1)) (i : Fin (n + 1)) :
    (ChartMetric.euclideanChartMetric (n + 1)).grad u x i = ChartMetric.partialDeriv i u x := by
  unfold ChartMetric.grad
  have hm : (ChartMetric.euclideanChartMetric (n + 1)).invMatrix x = 1 := by
    unfold ChartMetric.invMatrix
    have hm' : (ChartMetric.euclideanChartMetric (n + 1)).matrix x = 1 := by
      ext i j
      simp [ChartMetric.matrix, ChartMetric.euclideanChartMetric, Matrix.one_apply]
    rw [hm', inv_one]
  rw [hm]
  simp only [Matrix.one_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg hj.symm, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **The Euclidean chart Laplacian is the sum of the second coordinate partials.** -/
lemma euclidean_laplacian_eq (u : Vec (n + 1) → ℝ) (x : Vec (n + 1)) :
    (ChartMetric.euclideanChartMetric (n + 1)).laplacian u x =
      ∑ i, ChartMetric.partialDeriv i (fun y => ChartMetric.partialDeriv i u y) x := by
  unfold ChartMetric.laplacian ChartMetric.divergence ChartMetric.weightedDivergence
  rw [euclidean_density_eq_one]
  rw [div_one]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfun : (fun y => (ChartMetric.euclideanChartMetric (n + 1)).density y *
        (ChartMetric.euclideanChartMetric (n + 1)).grad u y i)
      = fun y => ChartMetric.partialDeriv i u y := by
    funext y
    rw [euclidean_density_eq_one, euclidean_grad_eq]
    ring
  rw [hfun]
  rfl

/-- **Laplacian of a radial function.** For `ψ` differentiable with second derivative at
`S x`, `Δ(ψ ∘ S)(x) = 4 · S(x) · ψ''(S x) + 2 · d · ψ'(S x)`. -/
lemma laplacian_radial (ψ : ℝ → ℝ) (x : Vec (n + 1))
    (hψ : ∀ s : ℝ, HasDerivAt ψ (deriv ψ s) s)
    (hψ' : HasDerivAt (deriv ψ) (deriv (deriv ψ) (radSq x)) (radSq x)) :
    (ChartMetric.euclideanChartMetric (n + 1)).laplacian (fun y => ψ (radSq y)) x =
      4 * radSq x * deriv (deriv ψ) (radSq x) + 2 * (n + 1) * deriv ψ (radSq x) := by
  rw [euclidean_laplacian_eq]
  simp only [partialDeriv_radial_second ψ x _ hψ hψ']
  have hsum1 : (∑ i : Fin (n + 1),
        (deriv (deriv ψ) (radSq x) * (2 * x i) ^ 2 + deriv ψ (radSq x) * 2))
      = deriv (deriv ψ) (radSq x) * (∑ i : Fin (n + 1), (2 * x i) ^ 2)
        + (n + 1) * (deriv ψ (radSq x) * 2) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hsum2 : (∑ i : Fin (n + 1), (2 * x i) ^ 2) = 4 * radSq x := by
    rw [radSq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum1, hsum2]
  ring

end ChartMetric

end Poincare.D13.EuclideanChart

/-! ## Axiom audit -/

#print axioms Poincare.D13.EuclideanChart.ChartMetric.partialDeriv_eq_deriv_update
#print axioms Poincare.D13.EuclideanChart.ChartMetric.partialDeriv_add
#print axioms Poincare.D13.EuclideanChart.ChartMetric.partialDeriv_mul
#print axioms Poincare.D13.EuclideanChart.ChartMetric.partialDeriv_apply_single
#print axioms Poincare.D13.EuclideanChart.ChartMetric.partialDeriv_apply_single_of_ne
#print axioms Poincare.D13.EuclideanChart.ChartMetric.partialDeriv_const_mul_coord
#print axioms Poincare.D13.EuclideanChart.ChartMetric.partialDeriv_const
#print axioms Poincare.D13.EuclideanChart.ChartMetric.radSq
#print axioms Poincare.D13.EuclideanChart.ChartMetric.radSq_differentiableAt
#print axioms Poincare.D13.EuclideanChart.ChartMetric.radSq_update
#print axioms Poincare.D13.EuclideanChart.ChartMetric.partialDeriv_radial
#print axioms Poincare.D13.EuclideanChart.ChartMetric.partialDeriv_radial_second
#print axioms Poincare.D13.EuclideanChart.ChartMetric.euclidean_density_eq_one
#print axioms Poincare.D13.EuclideanChart.ChartMetric.euclidean_grad_eq
#print axioms Poincare.D13.EuclideanChart.ChartMetric.euclidean_laplacian_eq
#print axioms Poincare.D13.EuclideanChart.ChartMetric.laplacian_radial
