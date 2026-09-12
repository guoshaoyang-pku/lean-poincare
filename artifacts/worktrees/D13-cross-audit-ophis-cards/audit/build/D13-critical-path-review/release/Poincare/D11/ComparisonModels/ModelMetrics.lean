/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D11 — the constant-curvature model metrics in polar form

For every real `K` the simply connected space form of constant sectional curvature `K` is
written in geodesic polar coordinates as

`g = dr² + j_K(r)² · g_{S^{n-1}}`,

where `j_K` is the D10 normalised Jacobi field `Poincare.D10.jacobiSol K` (the explicit
solution `sin (√K r)/√K` for `K > 0`, `r` for `K = 0`, `sinh (√(-K) r)/√(-K)` for `K < 0`)
and `g_{S^{n-1}}` is the round metric of the unit `(n-1)`-sphere, which we represent by the
Euclidean inner product on the tangent space `EuclideanSpace ℝ (Fin (n-1))` of the
`(n-1)`-sphere.

This file

* defines the polar (warped-product) metric form `polarMetric`,
* proves the algebraic *warped-product metric axioms* (symmetry, additivity, ℝ-linearity,
  positive definiteness off the pole),
* packages the analytic axioms of a constant-curvature model into `WarpedProductModel K j`,
* and **reduces** them to the ODE conditions already proved in D10: for each of the three
  branches (and for the glued `jacobiSol K`) the axioms hold because
  `jacobiSol…_hasNormalizedInitial` and `jacobiSol…_solvesJacobiODE` were proved in
  `Poincare/D10/JacobiConstantCurvature`.
-/
import Poincare.D11.ComparisonModels.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

namespace Poincare.D11

open scoped Real

/-- The polar (warped-product) metric form with warping function `j` at radius `r`:

`g_{(r,x)} ((a,v), (b,w)) = a·b + j(r)² · ⟨v, w⟩`,

i.e. the metric `dr² + j(r)² g₀` on the tangent space `ℝ × E` at the point `(r, x)`, where
`E = EuclideanSpace ℝ (Fin (n-1))` is the tangent space of the `(n-1)`-sphere carrying the
round metric `g₀`. -/
def polarMetric (n : ℕ) (j : ℝ → ℝ) (r : ℝ)
    (u v : ℝ × EuclideanSpace ℝ (Fin (n - 1))) : ℝ :=
  u.1 * v.1 + j r ^ 2 * inner ℝ u.2 v.2

/-! ## The algebraic warped-product metric axioms -/

/-- Symmetry: `g(u, v) = g(v, u)`. -/
theorem polarMetric_symm (n : ℕ) (j : ℝ → ℝ) (r : ℝ)
    (u v : ℝ × EuclideanSpace ℝ (Fin (n - 1))) :
    polarMetric n j r u v = polarMetric n j r v u := by
  unfold polarMetric
  rw [real_inner_comm u.2 v.2, mul_comm u.1 v.1]

/-- Additivity in the first slot: `g(u₁ + u₂, v) = g(u₁, v) + g(u₂, v)`. -/
theorem polarMetric_add_left (n : ℕ) (j : ℝ → ℝ) (r : ℝ)
    (u₁ u₂ v : ℝ × EuclideanSpace ℝ (Fin (n - 1))) :
    polarMetric n j r (u₁ + u₂) v = polarMetric n j r u₁ v + polarMetric n j r u₂ v := by
  unfold polarMetric
  have h1 : (u₁ + u₂).1 = u₁.1 + u₂.1 := rfl
  have h2 : (u₁ + u₂).2 = u₁.2 + u₂.2 := rfl
  rw [h1, h2, add_mul, inner_add_left]
  ring

/-- Additivity in the second slot: `g(u, v₁ + v₂) = g(u, v₁) + g(u, v₂)`. -/
theorem polarMetric_add_right (n : ℕ) (j : ℝ → ℝ) (r : ℝ)
    (u v₁ v₂ : ℝ × EuclideanSpace ℝ (Fin (n - 1))) :
    polarMetric n j r u (v₁ + v₂) = polarMetric n j r u v₁ + polarMetric n j r u v₂ := by
  rw [polarMetric_symm n j r u (v₁ + v₂), polarMetric_add_left n j r v₁ v₂ u,
    polarMetric_symm n j r v₁ u, polarMetric_symm n j r v₂ u]

/-- ℝ-linearity in the first slot: `g(a • u, v) = a · g(u, v)`. -/
theorem polarMetric_smul_left (n : ℕ) (j : ℝ → ℝ) (r : ℝ) (a : ℝ)
    (u v : ℝ × EuclideanSpace ℝ (Fin (n - 1))) :
    polarMetric n j r (a • u) v = a * polarMetric n j r u v := by
  unfold polarMetric
  rw [show (a • u).1 = a * u.1 from rfl]
  rw [show (a • u).2 = a • u.2 from rfl]
  rw [inner_smul_left]
  simp only [starRingEnd_apply, star_id_of_comm]
  ring

/-- ℝ-linearity in the second slot: `g(u, a • v) = a · g(u, v)`. -/
theorem polarMetric_smul_right (n : ℕ) (j : ℝ → ℝ) (r : ℝ) (a : ℝ)
    (u v : ℝ × EuclideanSpace ℝ (Fin (n - 1))) :
    polarMetric n j r u (a • v) = a * polarMetric n j r u v := by
  rw [polarMetric_symm n j r u (a • v), polarMetric_smul_left n j r a v u,
    polarMetric_symm n j r v u]

/-- Nonnegativity of the polar metric form (no positivity of `j` is needed). -/
theorem polarMetric_nonneg (n : ℕ) (j : ℝ → ℝ) (r : ℝ)
    (v : ℝ × EuclideanSpace ℝ (Fin (n - 1))) : 0 ≤ polarMetric n j r v v := by
  unfold polarMetric
  exact add_nonneg (mul_self_nonneg v.1)
    (mul_nonneg (sq_nonneg (j r)) (inner_self_nonneg (𝕜 := ℝ) (x := v.2)))

/-- **Positive definiteness off the pole**: if the warping function does not vanish at `r`
then the polar metric form is strictly positive on nonzero tangent vectors. -/
theorem polarMetric_pos_of_pos (n : ℕ) {j : ℝ → ℝ} {r : ℝ} (hj : j r ≠ 0)
    {v : ℝ × EuclideanSpace ℝ (Fin (n - 1))} (hv : v ≠ 0) :
    0 < polarMetric n j r v v := by
  unfold polarMetric
  by_cases h2 : v.2 = 0
  · have hv1 : v.1 ≠ 0 := by
      intro h
      apply hv
      ext i <;> simp [h, h2]
    have hsq : 0 < v.1 ^ 2 := sq_pos_of_ne_zero hv1
    rw [h2, inner_zero_right, mul_zero, add_zero]
    rw [← pow_two]
    exact hsq
  · have hinn : 0 < inner ℝ v.2 v.2 := by
      refine lt_of_le_of_ne (inner_self_nonneg (𝕜 := ℝ) (x := v.2)) ?_
      intro h
      exact ((inner_self_eq_zero (𝕜 := ℝ) (x := v.2)).not.mpr h2) h.symm
    have hsq : 0 < j r ^ 2 := sq_pos_of_ne_zero hj
    have hmul : 0 < j r ^ 2 * inner ℝ v.2 v.2 := mul_pos hsq hinn
    exact add_pos_of_nonneg_of_pos (mul_self_nonneg v.1) hmul

/-! ## The analytic axioms of a constant-curvature model space, and their reduction to D10 -/

/-- The analytic axioms satisfied by the warping function of a simply connected model space of
constant sectional curvature `K`:

1. `j 0 = 0` and `j' 0 = 1` (the polar coordinates extend smoothly across the pole), and
2. the scalar Jacobi ODE `j'' + K·j = 0` (constant sectional curvature `K`).

Both conditions are exactly the D10 predicates `HasNormalizedInitial` and `SolvesJacobiODE`;
the theorem `warpedProductModel_jacobiSol` below reduces the axiom verification for all three
model metrics to the D10 ODE theorems. -/
structure WarpedProductModel (K : ℝ) (j : ℝ → ℝ) : Prop where
  initial : Poincare.D10.HasNormalizedInitial j
  solves_ode : Poincare.D10.SolvesJacobiODE K j

/-- The Jacobi ODE part of the axioms: a warped-product model of curvature `K` has a warping
function solving the scalar Jacobi equation — the constant-curvature condition reduces to the
D10 ODE predicate. -/
theorem WarpedProductModel.jacobi_ode {K : ℝ} {j : ℝ → ℝ} (h : WarpedProductModel K j) :
    Poincare.D10.SolvesJacobiODE K j :=
  h.solves_ode

/-- The regular-extension part of the axioms: the warp vanishes at the pole with derivative
`1`, i.e. the D10 normalised initial conditions. -/
theorem WarpedProductModel.normalized_initial {K : ℝ} {j : ℝ → ℝ} (h : WarpedProductModel K j) :
    Poincare.D10.HasNormalizedInitial j :=
  h.initial

/-- The spherical model metric `dr² + (sin (√K r)/√K)² g_{S^{n-1}}` (`K > 0`) satisfies the
warped-product model axioms: this is literally the D10 theorem `jacobiSolSphere_initial`
together with `jacobiSolSphere_ode`. -/
theorem warpedProductModel_jacobiSolSphere {K : ℝ} (hK : 0 < K) :
    WarpedProductModel K (Poincare.D10.jacobiSolSphere K) :=
  ⟨Poincare.D10.jacobiSolSphere_hasNormalizedInitial hK,
    Poincare.D10.jacobiSolSphere_solvesJacobiODE hK⟩

/-- The Euclidean model metric `dr² + r² g_{S^{n-1}}` satisfies the warped-product model
axioms: literally the D10 theorems `jacobiSolFlat_initial` and `jacobiSolFlat_ode`. -/
theorem warpedProductModel_jacobiSolFlat :
    WarpedProductModel 0 Poincare.D10.jacobiSolFlat :=
  ⟨Poincare.D10.jacobiSolFlat_hasNormalizedInitial, Poincare.D10.jacobiSolFlat_solvesJacobiODE⟩

/-- The hyperbolic model metric `dr² + (sinh (√(-K) r)/√(-K))² g_{S^{n-1}}` (`K < 0`)
satisfies the warped-product model axioms: literally the D10 theorems
`jacobiSolHyperbolic_initial` and `jacobiSolHyperbolic_ode`. -/
theorem warpedProductModel_jacobiSolHyperbolic {K : ℝ} (hK : K < 0) :
    WarpedProductModel K (Poincare.D10.jacobiSolHyperbolic K) :=
  ⟨Poincare.D10.jacobiSolHyperbolic_hasNormalizedInitial hK,
    Poincare.D10.jacobiSolHyperbolic_solvesJacobiODE hK⟩

/-- The polar metric of every constant-curvature model space — spherical (`K > 0`), Euclidean
(`K = 0`) and hyperbolic (`K < 0`) — satisfies the warped-product model axioms, reducing
unconditionally to the D10 theorems `jacobiSol_hasNormalizedInitial` and
`jacobiSol_solvesJacobiODE`. -/
theorem warpedProductModel_jacobiSol (K : ℝ) :
    WarpedProductModel K (Poincare.D10.jacobiSol K) :=
  ⟨Poincare.D10.jacobiSol_hasNormalizedInitial K, Poincare.D10.jacobiSol_solvesJacobiODE K⟩

/-! ## The three constant-curvature model metrics -/

/-- The spherical space form metric in polar form: `dr² + jacobiSolSphere K (r)² g_{S^{n-1}}`,
for `K > 0`. -/
def modelSphereMetric (n : ℕ) (K r : ℝ)
    (u v : ℝ × EuclideanSpace ℝ (Fin (n - 1))) : ℝ :=
  polarMetric n (Poincare.D10.jacobiSolSphere K) r u v

/-- The Euclidean space form metric in polar form: `dr² + r² g_{S^{n-1}}`. -/
def modelFlatMetric (n : ℕ) (r : ℝ)
    (u v : ℝ × EuclideanSpace ℝ (Fin (n - 1))) : ℝ :=
  polarMetric n Poincare.D10.jacobiSolFlat r u v

/-- The hyperbolic space form metric in polar form: `dr² + jacobiSolHyperbolic K (r)²
g_{S^{n-1}}`, for `K < 0`. -/
def modelHyperbolicMetric (n : ℕ) (K r : ℝ)
    (u v : ℝ × EuclideanSpace ℝ (Fin (n - 1))) : ℝ :=
  polarMetric n (Poincare.D10.jacobiSolHyperbolic K) r u v

/-- The three model metrics satisfy the algebraic warped-product axioms (symmetry,
additivity, ℝ-linearity) — these hold for every warping function `j` and every radius. -/
theorem modelSphereMetric_symm (n : ℕ) (K r : ℝ)
    (u v : ℝ × EuclideanSpace ℝ (Fin (n - 1))) :
    modelSphereMetric n K r u v = modelSphereMetric n K r v u :=
  polarMetric_symm n (Poincare.D10.jacobiSolSphere K) r u v

/-- The Euclidean model metric satisfies the algebraic warped-product axioms. -/
theorem modelFlatMetric_symm (n : ℕ) (r : ℝ)
    (u v : ℝ × EuclideanSpace ℝ (Fin (n - 1))) :
    modelFlatMetric n r u v = modelFlatMetric n r v u :=
  polarMetric_symm n Poincare.D10.jacobiSolFlat r u v

/-- The hyperbolic model metric satisfies the algebraic warped-product axioms. -/
theorem modelHyperbolicMetric_symm (n : ℕ) (K r : ℝ)
    (u v : ℝ × EuclideanSpace ℝ (Fin (n - 1))) :
    modelHyperbolicMetric n K r u v = modelHyperbolicMetric n K r v u :=
  polarMetric_symm n (Poincare.D10.jacobiSolHyperbolic K) r u v

/-- **Positive definiteness of the spherical model metric**: for `0 < r < π/√K` the warp
`sin (√K r)/√K` is positive (D10 `jacobiSolSphere_pos`), so the polar metric is strictly
positive on nonzero tangent vectors. -/
theorem modelSphereMetric_posDef {n : ℕ} {K r : ℝ} (hK : 0 < K) (hr : 0 < r)
    (hrlt : r < Real.pi / Real.sqrt K) {v : ℝ × EuclideanSpace ℝ (Fin (n - 1))} (hv : v ≠ 0) :
    0 < modelSphereMetric n K r v v := by
  unfold modelSphereMetric
  exact polarMetric_pos_of_pos n
    (ne_of_gt (Poincare.D10.jacobiSolSphere_pos hK hr
      (by
        have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos_of_pos hK
        have := mul_lt_mul_of_pos_left hrlt hsqrt
        rwa [mul_div_cancel₀ Real.pi hsqrt.ne'] at this)))
    hv

/-- **Positive definiteness of the Euclidean model metric**: for `r > 0` the warp `r` is
positive, so the polar metric is strictly positive on nonzero tangent vectors. -/
theorem modelFlatMetric_posDef {n : ℕ} {r : ℝ} (hr : 0 < r)
    {v : ℝ × EuclideanSpace ℝ (Fin (n - 1))} (hv : v ≠ 0) :
    0 < modelFlatMetric n r v v := by
  unfold modelFlatMetric
  exact polarMetric_pos_of_pos n (ne_of_gt hr) hv

/-- **Positive definiteness of the hyperbolic model metric**: for `r > 0` the warp
`sinh (√(-K) r)/√(-K)` is positive, so the polar metric is strictly positive on nonzero
tangent vectors. -/
theorem modelHyperbolicMetric_posDef {n : ℕ} {K r : ℝ} (hK : K < 0) (hr : 0 < r)
    {v : ℝ × EuclideanSpace ℝ (Fin (n - 1))} (hv : v ≠ 0) :
    0 < modelHyperbolicMetric n K r v v := by
  unfold modelHyperbolicMetric
  have hfun : Poincare.D10.jacobiSolHyperbolic K = Poincare.D10.jacobiSol K := by
    funext s
    exact (Poincare.D10.jacobiSol_of_neg hK s).symm
  rw [hfun]
  exact polarMetric_pos_of_pos n
    (ne_of_gt (jacobiSol_pos (K := K) hr (fun h => absurd h (not_lt.mpr hK.le)))) hv

/-- The polar metric with warping `jacobiSol K` is positive definite at every radius before
the first zero of the corresponding space form. -/
theorem polarMetric_jacobiSol_posDef {K r : ℝ} {m : ℕ} (hr : 0 < r)
    (hdom : 0 < K → r < Real.pi / Real.sqrt K)
    {v : ℝ × EuclideanSpace ℝ (Fin (m - 1))} (hv : v ≠ 0) :
    0 < polarMetric m (Poincare.D10.jacobiSol K) r v v :=
  polarMetric_pos_of_pos m (ne_of_gt (jacobiSol_pos hr hdom)) hv

end Poincare.D11
