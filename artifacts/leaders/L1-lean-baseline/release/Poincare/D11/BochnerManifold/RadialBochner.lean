/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D11 — the radial Bochner–Weitzenböck identity for a general warped profile

For the warped-product model `ℝ ×_s Sⁿ` with mean-curvature profile `m = s'/s`
(`n` = dimension of the sphere factor) we prove, for radial `u`:

  `Δ(|∇u|²) = 2 |Hess u|² + 2 ⟨∇u, ∇Δu⟩ + 2 Ric(∇u, ∇u)`

where the three model quantities are `lapG (gradSq u)`, `hessSq`, `gradDot` and the
curvature term is `ricTerm = −n·(m' + m²)·(u')²` (the radial Ricci pairing, because
`m' + m² = s''/s` and `Ric(∂_r, ∂_r) = −n·s''/s`).  The theorem is `radial_bochner_identity`
and holds for an *arbitrary* profile `m`, with no curvature assumption: the deviation from
the Euclidean (flat) identity is exactly the Riccati term `m' + m²`.

The flat specialisation `euclidean_radial_bochner` (`m ≡ 0`, curvature term `0`) is the
radial form of the D10 Euclidean identity restated in `Basic.lean`.

The proof is the 1-dimensional jet computation carried out with `deriv` product/power/sum
rules (the lemmas of `Basic.lean`), followed by `ring`: on both sides the terms
`2(u'')² + 2u'u''' + 2n·m·u'·u''` cancel, leaving exactly the curvature term.  All proofs
are complete; `#print axioms` reports only the standard Lean cone.
-/

import Poincare.D11.BochnerManifold.Basic

noncomputable section

namespace Poincare.D11.BochnerManifold

variable {u m : ℝ → ℝ} {r : ℝ}

/-- **The radial Bochner–Weitzenböck identity for a general warped profile.**

`Δ(|∇u|²) = 2 |Hess u|² + 2 ⟨∇u, ∇Δu⟩ + 2 Ric(∇u, ∇u)` in the warped-product model
`ℝ ×_s Sⁿ`, with the curvature term `ricTerm n m u r = −n·(m'(r) + m(r)²)·(u'(r))²`.
No curvature assumption is made on `m`; the identity is the honest jet computation. -/
theorem radial_bochner_identity (n : ℕ) (hu2 : Differentiable ℝ (deriv u))
    (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r) (hm : DifferentiableAt ℝ m r) :
    lapG n m (gradSq u) r = 2 * hessSq n m u r + 2 * gradDot u (lapG n m u) r
      + 2 * ricTerm n m u r := by
  change deriv (deriv (gradSq u)) r + (n : ℝ) * (m r * deriv (gradSq u) r)
    = 2 * ((deriv (deriv u) r) ^ 2 + (n : ℝ) * ((m r) ^ 2 * (deriv u r) ^ 2))
      + 2 * (deriv u r * deriv (lapG n m u) r)
      + 2 * (-((n : ℝ) * ((deriv m r + (m r) ^ 2) * (deriv u r) ^ 2)))
  have h1 := deriv_deriv_gradSq hu2 hu3
  have h2 := deriv_gradSq hu2 r
  have h3 := deriv_lapG n hu2.differentiableAt hu3 hm
  rw [h1, h2, h3]
  ring

/-- **Flat case.** With the vanishing profile `m ≡ 0` the curvature term disappears and the
identity is the radial Euclidean Bochner identity (the D10 identity in normal coordinates
around the origin): `Δ(|∇u|²) = 2 |Hess u|² + 2 ⟨∇u, ∇Δu⟩` with `|Hess u|² = (u'')²`. -/
theorem euclidean_radial_bochner (n : ℕ) (hu2 : Differentiable ℝ (deriv u))
    (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r) :
    lapG n 0 (gradSq u) r = 2 * hessSq n 0 u r + 2 * gradDot u (lapG n 0 u) r := by
  have h := radial_bochner_identity n hu2 hu3 (m := (0 : ℝ → ℝ)) (differentiableAt_const (0 : ℝ))
  simpa [ricTerm] using h

/-- The curvature term is the only deviation from the Euclidean identity: the Laplacian of
the energy density minus `2|Hess u|² + 2⟨∇u,∇Δu⟩` equals exactly `2·ricTerm`. -/
theorem radial_bochner_defect (n : ℕ) (hu2 : Differentiable ℝ (deriv u))
    (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r) (hm : DifferentiableAt ℝ m r) :
    lapG n m (gradSq u) r - (2 * hessSq n m u r + 2 * gradDot u (lapG n m u) r)
      = 2 * ricTerm n m u r := by
  rw [radial_bochner_identity n hu2 hu3 hm]
  ring

/-- In `dimension 0` (no sphere factor, `n = 0`) the model operators reduce to the plain
one-dimensional ones: `Δ = d²/dr²`, `|Hess u|² = (u'')²`, and the identity is the classical
one-dimensional Bochner identity. -/
theorem radial_bochner_identity_dim_zero (hu2 : Differentiable ℝ (deriv u))
    (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r) (hm : DifferentiableAt ℝ m r) :
    deriv (deriv (gradSq u)) r = 2 * (deriv (deriv u) r) ^ 2 + 2 * gradDot u (lapG 0 m u) r
      + 2 * ricTerm 0 m u r := by
  simpa [lapG, hessSq, gradSq] using radial_bochner_identity 0 hu2 hu3 hm

end Poincare.D11.BochnerManifold
