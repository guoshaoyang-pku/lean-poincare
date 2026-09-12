/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D11 — the constant-curvature model space and the Bochner–Weitzenböck identity

The model spaces of constant sectional curvature `κ` are the warped products `ℝ ×_s Sⁿ`
whose radial profile `s` is the D10 normalised Jacobi field `jacobiSol κ` — i.e. the explicit
solutions

* `s(r) = sin(√κ·r)/√κ` (`κ > 0`, the sphere),
* `s(r) = r` (`κ = 0`, Euclidean space),
* `s(r) = sinh(√(-κ)·r)/√(-κ)` (`κ < 0`, hyperbolic space),

proved in `Poincare.D10.JacobiConstantCurvature` to satisfy the scalar Jacobi equation
`s'' + κ·s = 0`, `s(0) = 0`, `s'(0) = 1`.  In geodesic normal coordinates around a point the
entire radial geometry of the model is encoded in the mean-curvature profile

  `m_κ(r) := s'(r)/s(r) = jacobiDeriv κ r / jacobiSol κ r`.

This file proves

1. **the Riccati equation** `m' + m² = −κ` (away from the pole `s ≠ 0`), i.e. the Jacobi
   equation for `s` in profile form — this is the curvature term of the Bochner identity;
2. **the radial Ricci curvature** `Ric(∂_r, ∂_r) = −n·s''/s = n·κ`;
3. **the model Bochner–Weitzenböck identity** (`model_bochner_weitzenbock`): for every
   curvature `κ` (spherical, flat or hyperbolic) and radial `u`,

   `Δ(|∇u|²) = 2 |Hess u|² + 2 ⟨∇u, ∇Δu⟩ + 2·n·κ·|∇u|²`,

   i.e. `Δ‖∇u‖² = 2‖Hess u‖² + 2⟨∇u, ∇Δu⟩ + 2 Ric(∇u, ∇u)` with `Ric = n·κ·g` the model
   Ricci tensor.  The proof reduces to the general warped-profile identity of
   `RadialBochner.lean` and the Riccati equation: the curvature term `−n·(m' + m²)·(u')²`
   equals `n·κ·(u')²`.

All proofs are complete; `#print axioms` reports only the standard Lean cone.
-/

import Poincare.D11.BochnerManifold.RadialBochner

noncomputable section

namespace Poincare.D11.BochnerManifold

variable {u : ℝ → ℝ} {r κ : ℝ}

/-! ## The model mean-curvature profile and its Riccati equation -/

/-- **The model mean-curvature profile** `m_κ := s'/s` of the constant-curvature model space
with radial profile `s = jacobiSol κ` (sphere `κ > 0`, flat `κ = 0`, hyperbolic `κ < 0`). -/
noncomputable def jacobiMeanCurvature (κ : ℝ) : ℝ → ℝ :=
  fun r => Poincare.D10.jacobiDeriv κ r / Poincare.D10.jacobiSol κ r

/-- On the spherical branch (`κ > 0`) the profile is explicit:
`m_κ(r) = √κ·cos(√κ·r)/sin(√κ·r)`. -/
theorem jacobiMeanCurvature_of_pos {κ r : ℝ} (hκ : 0 < κ) :
    jacobiMeanCurvature κ r =
      Real.cos (Real.sqrt κ * r) * Real.sqrt κ / Real.sin (Real.sqrt κ * r) := by
  rw [jacobiMeanCurvature, Poincare.D10.jacobiDeriv_of_pos hκ, Poincare.D10.jacobiSol_of_pos hκ]
  unfold Poincare.D10.jacobiSolSphere
  rw [div_div_eq_mul_div]

/-- On the flat branch (`κ = 0`) the profile is `m₀(r) = 1/r` (the mean curvature of the
distance sphere in Euclidean space). -/
theorem jacobiMeanCurvature_of_zero {r : ℝ} (_hr : r ≠ 0) :
    jacobiMeanCurvature 0 r = 1 / r := by
  rw [jacobiMeanCurvature, Poincare.D10.jacobiDeriv_of_zero, Poincare.D10.jacobiSol_of_zero]
  rfl

/-- On the hyperbolic branch (`κ < 0`) the profile is explicit:
`m_κ(r) = √(-κ)·cosh(√(-κ)·r)/sinh(√(-κ)·r)`. -/
theorem jacobiMeanCurvature_of_neg {κ r : ℝ} (hκ : κ < 0) :
    jacobiMeanCurvature κ r =
      Real.cosh (Real.sqrt (-κ) * r) * Real.sqrt (-κ) / Real.sinh (Real.sqrt (-κ) * r) := by
  rw [jacobiMeanCurvature, Poincare.D10.jacobiDeriv_of_neg hκ, Poincare.D10.jacobiSol_of_neg hκ]
  unfold Poincare.D10.jacobiSolHyperbolic
  rw [div_div_eq_mul_div]

/-- The profile is differentiable wherever the radial profile does not vanish (i.e. away
from the pole and, on the sphere, the antipodal cut locus). -/
theorem hasDerivAt_jacobiMeanCurvature {κ r : ℝ} (hne : Poincare.D10.jacobiSol κ r ≠ 0) :
    HasDerivAt (jacobiMeanCurvature κ)
      (((-(κ * Poincare.D10.jacobiSol κ r)) * Poincare.D10.jacobiSol κ r
          - Poincare.D10.jacobiDeriv κ r * Poincare.D10.jacobiDeriv κ r)
        / (Poincare.D10.jacobiSol κ r) ^ 2) r :=
  (Poincare.D10.hasDerivAt_jacobiDeriv κ r).div (Poincare.D10.hasDerivAt_jacobiSol κ r) hne

/-- The derivative of the profile: `m' = −κ − m²`, the Riccati form of the Jacobi equation. -/
theorem jacobiMeanCurvature_deriv_eq {κ r : ℝ} (hne : Poincare.D10.jacobiSol κ r ≠ 0) :
    deriv (jacobiMeanCurvature κ) r = -κ - (jacobiMeanCurvature κ r) ^ 2 := by
  rw [(hasDerivAt_jacobiMeanCurvature hne).deriv]
  unfold jacobiMeanCurvature
  field_simp [hne]

/-- **The Riccati equation of the model spaces:** `m' + m² = −κ`.  This is exactly the
curvature term of the Bochner–Weitzenböck identity. -/
theorem jacobiMeanCurvature_riccati {κ r : ℝ} (hne : Poincare.D10.jacobiSol κ r ≠ 0) :
    deriv (jacobiMeanCurvature κ) r + (jacobiMeanCurvature κ r) ^ 2 = -κ := by
  rw [jacobiMeanCurvature_deriv_eq hne]
  ring

/-- The radial profile satisfies `s''/s = −κ` (the sectional curvature), as a quotient of
`deriv`s — the geometric meaning of the Riccati equation. -/
theorem jacobiSol_second_deriv_div {κ r : ℝ} (hne : Poincare.D10.jacobiSol κ r ≠ 0) :
    deriv (deriv (Poincare.D10.jacobiSol κ)) r / Poincare.D10.jacobiSol κ r = -κ := by
  have hode := Poincare.D10.jacobiSol_ode κ r
  have h1 : deriv (deriv (Poincare.D10.jacobiSol κ)) r = -(κ * Poincare.D10.jacobiSol κ r) := by
    linarith
  rw [h1]
  field_simp [hne]

/-- **The radial Ricci curvature of the model:** `Ric(∂_r, ∂_r) = −n·s''/s = n·κ`, the
constant-curvature value of the model Ricci tensor `Ric = n·κ·g` on the unit radial vector. -/
theorem radial_ricci_of_model (n : ℕ) {κ r : ℝ} (hne : Poincare.D10.jacobiSol κ r ≠ 0) :
    -((n : ℝ) * (deriv (deriv (Poincare.D10.jacobiSol κ)) r / Poincare.D10.jacobiSol κ r))
      = (n : ℝ) * κ := by
  rw [jacobiSol_second_deriv_div hne]
  ring

/-! ## The model operators (constant-curvature specialisation of the warped model) -/

/-- **Model Laplacian** `Δ_κ u = u'' + n·m_κ·u'` of the constant-curvature space form of
sectional curvature `κ`, in normal coordinates, acting on radial functions. -/
noncomputable def modelLap (n : ℕ) (κ : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  lapG n (jacobiMeanCurvature κ) u

/-- **Model squared Hessian norm** `|Hess u|² = (u'')² + n·m_κ²·(u')²`. -/
noncomputable def modelHessSq (n : ℕ) (κ : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  hessSq n (jacobiMeanCurvature κ) u

/-- **Model squared gradient norm** `|∇u|² = (u')²`. -/
noncomputable def modelGradSq (u : ℝ → ℝ) : ℝ → ℝ := gradSq u

/-- **Model gradient pairing** `⟨∇u, ∇f⟩ = u'·f'`. -/
noncomputable def modelGradDot (u f : ℝ → ℝ) : ℝ → ℝ := gradDot u f

/-- **Model Ricci pairing** `Ric(∇u, ∇u) = n·κ·(u')²` for `Ric = n·κ·g`. -/
noncomputable def modelRicciTerm (n : ℕ) (κ : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun r => (n : ℝ) * κ * (deriv u r) ^ 2

/-- The model Ricci pairing is `n·κ` times the squared gradient norm. -/
theorem modelRicciTerm_eq (n : ℕ) {κ : ℝ} (u : ℝ → ℝ) (r : ℝ) :
    modelRicciTerm n κ u r = (n : ℝ) * κ * modelGradSq u r := by
  rfl

/-! ## The model Bochner–Weitzenböck identity -/

/-- **The Bochner–Weitzenböck identity in the constant-curvature model.**

For every curvature `κ` (spherical `κ > 0`, flat `κ = 0`, hyperbolic `κ < 0`), every radial
function `u` and every point `r` with `jacobiSol κ r ≠ 0` (normal coordinates away from the
pole and cut locus),

`Δ(|∇u|²) = 2 |Hess u|² + 2 ⟨∇u, ∇Δu⟩ + 2 Ric(∇u, ∇u)`

with `Ric(∇u, ∇u) = n·κ·(u')²` (the model Ricci tensor `Ric = n·κ·g` contracted against
`∇u = u'∂_r`).  This is the task's target identity
`Δ‖∇u‖² = 2‖Hess u‖² + 2⟨∇u, ∇Δu⟩ + 2 Ric(∇u, ∇u)` in the explicit constant-curvature
model, with the curvature term fully computed. -/
theorem model_bochner_weitzenbock (n : ℕ) (hu2 : Differentiable ℝ (deriv u))
    (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r) (hne : Poincare.D10.jacobiSol κ r ≠ 0) :
    modelLap n κ (modelGradSq u) r
      = 2 * modelHessSq n κ u r + 2 * modelGradDot u (modelLap n κ u) r
        + 2 * modelRicciTerm n κ u r := by
  have hmain := radial_bochner_identity n hu2 hu3
    (m := jacobiMeanCurvature κ) ((hasDerivAt_jacobiMeanCurvature hne).differentiableAt)
  change lapG n (jacobiMeanCurvature κ) (gradSq u) r
    = 2 * hessSq n (jacobiMeanCurvature κ) u r + 2 * gradDot u (lapG n (jacobiMeanCurvature κ) u) r
      + 2 * ((n : ℝ) * κ * (deriv u r) ^ 2)
  rw [hmain]
  congr 1
  unfold ricTerm
  rw [jacobiMeanCurvature_riccati hne]
  ring

/-- The same identity with the model Laplacian/Hessian operators unfolded, matching the
task's notation `Δ‖∇u‖² = 2‖Hess u‖² + 2⟨∇u, ∇Δu⟩ + 2 Ric(∇u, ∇u)` exactly. -/
theorem model_bochner_weitzenbock_unfolded (n : ℕ) (hu2 : Differentiable ℝ (deriv u))
    (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r) (hne : Poincare.D10.jacobiSol κ r ≠ 0) :
    lapG n (jacobiMeanCurvature κ) (gradSq u) r
      = 2 * (hessSq n (jacobiMeanCurvature κ) u r + gradDot u (lapG n (jacobiMeanCurvature κ) u) r
          + (n : ℝ) * κ * (gradSq u r)) := by
  change modelLap n κ (modelGradSq u) r = 2 * (hessSq n (jacobiMeanCurvature κ) u r
    + gradDot u (lapG n (jacobiMeanCurvature κ) u) r + (n : ℝ) * κ * (gradSq u r))
  rw [model_bochner_weitzenbock n hu2 hu3 hne]
  unfold modelHessSq modelGradDot modelRicciTerm modelLap gradSq
  ring

/-- **Flat model.** For `κ = 0` the model is Euclidean space in normal coordinates
(`m₀(r) = 1/r`): the curvature term vanishes and the identity is the radial Euclidean
Bochner identity of D10. -/
theorem model_flat_bochner (n : ℕ) (hu2 : Differentiable ℝ (deriv u))
    (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r) (hr : r ≠ 0) :
    modelLap n 0 (modelGradSq u) r
      = 2 * modelHessSq n 0 u r + 2 * modelGradDot u (modelLap n 0 u) r := by
  have hne : Poincare.D10.jacobiSol 0 r ≠ 0 := by
    simpa [Poincare.D10.jacobiSol_of_zero, Poincare.D10.jacobiSolFlat] using hr
  have hmain := model_bochner_weitzenbock n hu2 hu3 (κ := 0) hne
  simpa [modelRicciTerm] using hmain

end Poincare.D11.BochnerManifold
