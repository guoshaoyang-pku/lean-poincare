/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (pullback invariance of the gradient pairing)

# Invariance of the inverse-metric gradient pairing under a chart transition

`Poincare.D12.VolumeIBP.ChangeOfVariables` proves the **pullback density law**
`ρ_{ψ*G}(x) = ρ_G(ψ x) · |det J(x)|` for the pullback metric `(ψ*G)(x) = J(x)ᵀ g(ψ x) J(x)`.
This module proves the companion first-order statement: the **inverse-metric gradient pairing**
`⟨∇u, ∇v⟩_{g⁻¹} = ∑_{ij} (g⁻¹)^{ij} ∂ᵢu ∂ⱼv` is invariant under the transition,

`⟨∇(u∘ψ), ∇(v∘ψ)⟩_{(ψ*G)⁻¹}(x) = ⟨∇u, ∇v⟩_{g⁻¹}(ψ x)`.

The general form proved here (`gradInnerInverse_congruence`) assumes only the **congruence law**
`g'(y) = J(y)ᵀ · g(τ y) · J(y)` of the metric matrices together with the invertibility of the
Jacobian `J(y) = ∂τ(y)`; the pullback case `gradInnerInverse_pullbackMetric` is the corollary for
`g' = ψ*G`, `τ = ψ`. This is the chart-level well-definedness of `⟨∇u,∇v⟩_{g⁻¹}` (independent of
the chart in which it is computed) and the exact shape of the `OverlapAtlas.metric_transform`
field, so it is the missing ingredient for reassembling the pairings in a partition-of-unity
decomposition of a global test function:

`Σ_j ⟨∇u, ∇(ψ_j v)⟩ = ⟨∇u, ∇(Σ_j ψ_j v)⟩ = ⟨∇u, ∇v⟩`.

The proof is the chain rule (`partialDeriv_comp`) together with the matrix identity
`(Jᵀ g J)⁻¹ = J⁻¹ g⁻¹ (J⁻¹)ᵀ` for an invertible Jacobian `J`.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D12.VolumeIBP.ChangeOfVariables

open scoped BigOperators Matrix
open MeasureTheory Filter

noncomputable section

namespace Poincare.D13.Riemannian

open Poincare.D12.VolumeIBP

variable {n : ℕ}

/-- The inverse-metric pairing as a matrix-vector product:
`∑ᵢⱼ (g⁻¹)ᵢⱼ pᵢ qⱼ = p ⬝ (g⁻¹ · q)`. -/
lemma metricInnerInverse_eq_dotProduct (G : ChartMetric (n + 1)) (x p q : Vec (n + 1)) :
    G.metricInnerInverse x p q = dotProduct p ((G.invMatrix x).mulVec q) := by
  simp only [ChartMetric.metricInnerInverse, dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The dot product of a matrix-vector product on the left:
`(A v) ⬝ w = v ⬝ (Aᵀ w)`. -/
lemma dotProduct_mulVec_transpose {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (v w : Vec d) :
    dotProduct (A.mulVec v) w = dotProduct v (Aᵀ.mulVec w) := by
  rw [Matrix.dotProduct_mulVec v Aᵀ w, Matrix.vecMul_transpose]

/-- **Chain rule for the coordinate partial derivatives.** If `τ` is differentiable at `x` and
`u` at `τ x`, then the partials of `u ∘ τ` at `x` are the partials of `u` at `τ x` contracted
with the Jacobian matrix of `τ`: `∂ⱼ(u∘τ)(x) = ∑ₖ ∂ₖu(τx) · J(x)_{kj}`. -/
lemma partialDeriv_comp (τ : Vec (n + 1) → Vec (n + 1)) (u : Vec (n + 1) → ℝ) (x : Vec (n + 1))
    (hτ : DifferentiableAt ℝ τ x) (hu : DifferentiableAt ℝ u (τ x)) (j : Fin (n + 1)) :
    ChartMetric.partialDeriv j (fun z => u (τ z)) x
      = ∑ k, ChartMetric.partialDeriv k u (τ x) * ChartMetric.jacobianMatrix τ x k j := by
  have hcomp : fderiv ℝ (fun z => u (τ z)) x
      = (fderiv ℝ u (τ x)).comp (fderiv ℝ τ x) := by
    simpa only [Function.comp_def] using fderiv_comp (𝕜 := ℝ) x hu hτ
  rw [ChartMetric.partialDeriv, hcomp, ContinuousLinearMap.comp_apply]
  conv_lhs => rw [← Finset.univ_sum_single (fderiv ℝ τ x (Pi.single j 1))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsingle : (Pi.single k ((fderiv ℝ τ x) (Pi.single j 1) k) : Vec (n + 1))
      = (fderiv ℝ τ x) (Pi.single j 1) k • (Pi.single k (1 : ℝ) : Vec (n + 1)) := by
    ext i
    simp [Pi.single_apply]
  rw [hsingle, ContinuousLinearMap.map_smul]
  simp only [smul_eq_mul, ChartMetric.jacobianMatrix, Matrix.of_apply, ChartMetric.partialDeriv]
  ring

/-- **The Jacobian determinant of an injective derivative is nonzero.** -/
lemma jacobianMatrix_det_ne_zero_of_injective (τ : Vec (n + 1) → Vec (n + 1)) (x : Vec (n + 1))
    (h : Function.Injective (fderiv ℝ τ x)) : (ChartMetric.jacobianMatrix τ x).det ≠ 0 := by
  rw [ChartMetric.jacobianMatrix_det]
  intro hdet
  have hker : (fderiv ℝ τ x).toLinearMap.ker ≠ ⊥ :=
    bot_lt_iff_ne_bot.mp
      (LinearMap.bot_lt_ker_of_det_eq_zero (f := (fderiv ℝ τ x).toLinearMap) hdet)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hvzero : (fderiv ℝ τ x).toLinearMap v = 0 := LinearMap.mem_ker.mp hv
  exact hv0 (h (by rw [show fderiv ℝ τ x v = 0 from hvzero, map_zero]))

/-- **The inverse of a congruent metric matrix**: for an invertible Jacobian `J`,
`(Jᵀ g J)⁻¹ = J⁻¹ g⁻¹ (J⁻¹)ᵀ`. -/
lemma inv_congruence (G : ChartMetric (n + 1)) (y : Vec (n + 1))
    (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hJ : IsUnit J.det) :
    (Jᵀ * G.matrix y * J)⁻¹ = J⁻¹ * (G.matrix y)⁻¹ * (J⁻¹)ᵀ := by
  have hJJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJ
  have hJtJt : Jᵀ * (J⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul J hJ, Matrix.transpose_one]
  have hGG : G.matrix y * (G.matrix y)⁻¹ = 1 := by
    simpa only [ChartMetric.invMatrix] using G.matrix_mul_invMatrix y
  rw [Matrix.inv_eq_right_inv]
  have h1 : (Jᵀ * G.matrix y * J) * (J⁻¹ * (G.matrix y)⁻¹ * (J⁻¹)ᵀ)
      = Jᵀ * G.matrix y * (J * J⁻¹) * ((G.matrix y)⁻¹ * (J⁻¹)ᵀ) := by
    noncomm_ring
  rw [h1, hJJ, Matrix.mul_one]
  have h2 : Jᵀ * G.matrix y * ((G.matrix y)⁻¹ * (J⁻¹)ᵀ)
      = (Jᵀ * (G.matrix y * (G.matrix y)⁻¹)) * (J⁻¹)ᵀ := by
    noncomm_ring
  rw [h2, hGG, Matrix.mul_one, hJtJt]

/-- **The inverse of the pullback matrix**: `(Jᵀ g J)⁻¹ = J⁻¹ g⁻¹ (J⁻¹)ᵀ` for the pullback of a
chart diffeomorphism. -/
lemma inv_pullbackMatrix (G : ChartMetric (n + 1)) (H : ChartDiffeomorphism (n + 1))
    (x : Vec (n + 1)) :
    (G.pullbackMatrix H.ψ x)⁻¹
      = (ChartMetric.jacobianMatrix H.ψ x)⁻¹ * (G.matrix (H.ψ x))⁻¹
          * ((ChartMetric.jacobianMatrix H.ψ x)⁻¹)ᵀ :=
  inv_congruence G (H.ψ x) (ChartMetric.jacobianMatrix H.ψ x)
    (isUnit_iff_ne_zero.mpr (jacobianMatrix_det_ne_zero_of_injective H.ψ x (H.fderiv_injective x)))

/-- **Invariance of the inverse-metric gradient pairing under a congruent change of metric.**
If the metric matrix of `G'` at `y` is the congruence of the metric matrix of `G` at `τ y` by
the Jacobian of `τ` — the exact `(0,2)`-tensor transformation law, as postulated by
`OverlapAtlas.metric_transform` — and the Jacobian is invertible, then the pairing of the
pulled-back functions computed with `G'` at `y` equals the pairing of the functions computed
with `G` at `τ y`. -/
theorem gradInnerInverse_congruence (G G' : ChartMetric (n + 1))
    (τ : Vec (n + 1) → Vec (n + 1)) (y : Vec (n + 1)) (u v : Vec (n + 1) → ℝ)
    (hτ : DifferentiableAt ℝ τ y) (hu : DifferentiableAt ℝ u (τ y))
    (hv : DifferentiableAt ℝ v (τ y))
    (hJdet : (ChartMetric.jacobianMatrix τ y).det ≠ 0)
    (hG : G'.matrix y
      = (ChartMetric.jacobianMatrix τ y)ᵀ * G.matrix (τ y) * ChartMetric.jacobianMatrix τ y) :
    G'.gradInnerInverse (fun z => u (τ z)) (fun z => v (τ z)) y
      = G.gradInnerInverse u v (τ y) := by
  have hchain : ∀ (w : Vec (n + 1) → ℝ), DifferentiableAt ℝ w (τ y) →
      (fun j => ChartMetric.partialDeriv j (fun z => w (τ z)) y)
        = (ChartMetric.jacobianMatrix τ y)ᵀ.mulVec
            (fun k => ChartMetric.partialDeriv k w (τ y)) := by
    intro w hw
    funext j
    rw [partialDeriv_comp τ w y hτ hw j]
    simp only [Matrix.mulVec, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [ChartMetric.gradInnerInverse, ChartMetric.gradInnerInverse,
    metricInnerInverse_eq_dotProduct, metricInnerInverse_eq_dotProduct]
  rw [hchain u hu, hchain v hv]
  have hinv : G'.invMatrix y
      = (ChartMetric.jacobianMatrix τ y)⁻¹ * (G.matrix (τ y))⁻¹
          * ((ChartMetric.jacobianMatrix τ y)⁻¹)ᵀ := by
    rw [ChartMetric.invMatrix, hG]
    exact inv_congruence G (τ y) (ChartMetric.jacobianMatrix τ y)
      (isUnit_iff_ne_zero.mpr hJdet)
  rw [hinv]
  set J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := ChartMetric.jacobianMatrix τ y with hJdef
  have hJ : IsUnit J.det := isUnit_iff_ne_zero.mpr hJdet
  have hJJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJ
  have hJ'J' : (J⁻¹)ᵀ * Jᵀ = 1 := by
    rw [← Matrix.transpose_mul, hJJ, Matrix.transpose_one]
  have hmat : J * ((J⁻¹ * (G.matrix (τ y))⁻¹ * (J⁻¹)ᵀ) * Jᵀ) = (G.matrix (τ y))⁻¹ := by
    have h1 : J * ((J⁻¹ * (G.matrix (τ y))⁻¹ * (J⁻¹)ᵀ) * Jᵀ)
        = (J * J⁻¹) * (G.matrix (τ y))⁻¹ * ((J⁻¹)ᵀ * Jᵀ) := by noncomm_ring
    rw [h1, hJJ, Matrix.one_mul, hJ'J', Matrix.mul_one]
  rw [Matrix.mulVec_mulVec, dotProduct_mulVec_transpose, Matrix.transpose_transpose,
    Matrix.mulVec_mulVec, hmat]
  simp only [ChartMetric.invMatrix]

/-- **Invariance of the inverse-metric gradient pairing under a chart transition.** For the
pullback metric `ψ*G` of a chart diffeomorphism `ψ`, the pairing of the pulled-back functions
computed with `(ψ*G)⁻¹` at `x` equals the pairing of the functions computed with `G⁻¹` at
`ψ x`. This is the chart-level well-definedness of `⟨∇u,∇v⟩_{g⁻¹}` under change of coordinates;
together with the density law `pullbackDensity_eq` it makes the Riemannian IBP integrand
chart-independent. -/
theorem gradInnerInverse_pullbackMetric (G : ChartMetric (n + 1)) (H : ChartDiffeomorphism (n + 1))
    (u v : Vec (n + 1) → ℝ) (x : Vec (n + 1))
    (hu : DifferentiableAt ℝ u (H.ψ x)) (hv : DifferentiableAt ℝ v (H.ψ x)) :
    (G.pullbackMetric H).gradInnerInverse (fun z => u (H.ψ z)) (fun z => v (H.ψ z)) x
      = G.gradInnerInverse u v (H.ψ x) := by
  refine gradInnerInverse_congruence G (G.pullbackMetric H) H.ψ x u v
    ((ContDiff.differentiable H.smooth (by simp)).differentiableAt) hu hv
    (jacobianMatrix_det_ne_zero_of_injective H.ψ x (H.fderiv_injective x)) ?_
  simp only [ChartMetric.pullbackMetric, ChartMetric.matrix, ChartMetric.pullbackMatrix]
  ext i j
  rfl

end Poincare.D13.Riemannian

/-! ## Axiom audit -/

#print axioms Poincare.D13.Riemannian.metricInnerInverse_eq_dotProduct
#print axioms Poincare.D13.Riemannian.dotProduct_mulVec_transpose
#print axioms Poincare.D13.Riemannian.partialDeriv_comp
#print axioms Poincare.D13.Riemannian.jacobianMatrix_det_ne_zero_of_injective
#print axioms Poincare.D13.Riemannian.inv_congruence
#print axioms Poincare.D13.Riemannian.inv_pullbackMatrix
#print axioms Poincare.D13.Riemannian.gradInnerInverse_congruence
#print axioms Poincare.D13.Riemannian.gradInnerInverse_pullbackMetric
