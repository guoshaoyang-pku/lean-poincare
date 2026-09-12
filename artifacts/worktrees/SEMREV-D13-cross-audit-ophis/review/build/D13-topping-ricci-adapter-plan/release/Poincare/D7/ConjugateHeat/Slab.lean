/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-conjugate-heat-interface)
-/

import Poincare.D7.ConjugateHeat.Instance
import Poincare.D7.Divergence.Slab

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# Poincare.D7.ConjugateHeat.Slab

**D7 conjugate-heat layer, part 4: a discrete conjugate-heat slab monotonicity toy.**

A **slab** is a finite time window `Fin (n + 1)` of time slices, each slice carrying a field
`u k : V → ℝ` on the finite weighted graph of `Poincare.D7.ConjugateHeat.Laplacian`. The
**conjugate-heat step** with scalar-curvature term is the explicit Euler step for the backward
heat equation `∂_t u = -Δ u + R u`:

`conjugateHeatStep D w m R u = u + R • u - Δ u`.

The **mass-weighted energy** of a slice is `energy m u = ∑_x m x * (u x)^2`. The main results are

* `energy_le_energy_conjugateHeatStep` — **one-step monotonicity**: if the mass is positive, the
  conductances are nonnegative, and the scalar curvature is nonnegative, then the energy is
  nondecreasing along the conjugate-heat step:
  `energy m u ≤ energy m (conjugateHeatStep D w m R u)`;
* `energy_mono_slab` — **slab monotonicity**: for a slab whose successive slices are related by the
  conjugate-heat step, the energy of the first slice is at most the energy of the last slice,
  `energy m (u 0) ≤ energy m (u (Fin.last n))`.

The proof of the one-step monotonicity is the exact algebraic decomposition

`energy m (u + X) - energy m u = 2 * ∑_x m x * u x * X x + ∑_x m x * (X x)^2`,

with `X = R • u - Δ u`. The cross term is
`∑_x m x * R x * (u x)^2 + dirichletForm D w univ u u`, which is nonnegative by the sign
hypotheses and Green's first identity `green_first`, and the square term is nonnegative because the
mass is positive. The slab statement telescopes this inequality with `sum_telescope`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open Finset
open Poincare.D7.Divergence

namespace Poincare.D7.ConjugateHeat

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- **The mass-weighted energy** of a field: `∑_x m x * (u x)^2`. -/
def energy (m : V → ℝ) (u : V → ℝ) : ℝ := ∑ x, m x * u x ^ 2

/-- **The discrete conjugate-heat step with scalar-curvature term** (explicit Euler step for
`∂_t u = -Δ u + R u`): `u⁺ = u + R • u - Δ u`. -/
noncomputable def conjugateHeatStep (D : DivergenceData V E) (w : E → ℝ) (m R : V → ℝ)
    (u : V → ℝ) : V → ℝ :=
  u + scalarMulLM R u - laplaceBeltrami D w m u

/-- The conjugate-heat step is the sum of the field and the generator
`X = R • u - Δ u`. -/
theorem conjugateHeatStep_eq_add_generator (D : DivergenceData V E) (w : E → ℝ) (m R : V → ℝ)
    (u : V → ℝ) :
    conjugateHeatStep D w m R u
      = u + fun x => R x * u x - laplaceBeltrami D w m u x := by
  funext x
  simp only [conjugateHeatStep, Pi.add_apply, Pi.sub_apply, scalarMulLM_apply,
    laplaceBeltrami_apply]
  ring

/-- **One-step energy monotonicity of the discrete conjugate-heat step.** If the mass density is
positive, the conductances are nonnegative, and the scalar curvature is nonnegative, then the
mass-weighted energy does not decrease under `u⁺ = u + R • u - Δ u`. -/
theorem energy_le_energy_conjugateHeatStep (D : DivergenceData V E) (w : E → ℝ) (m R : V → ℝ)
    (hm : ∀ x, 0 < m x) (hw : ∀ e, 0 ≤ w e) (hR : ∀ x, 0 ≤ R x) (u : V → ℝ) :
    energy m u ≤ energy m (conjugateHeatStep D w m R u) := by
  set X : V → ℝ := fun x => R x * u x - laplaceBeltrami D w m u x with hX
  have hstep : conjugateHeatStep D w m R u = u + X := by
    rw [hX]
    exact conjugateHeatStep_eq_add_generator D w m R u
  -- Exact algebraic decomposition of the energy difference.
  have hdecomp : energy m (conjugateHeatStep D w m R u)
      = energy m u + 2 * (∑ x, m x * u x * X x) + ∑ x, m x * X x ^ 2 := by
    rw [hstep]
    have hpt : ∀ x : V, m x * (u x + X x) ^ 2
        = m x * u x ^ 2 + 2 * (m x * u x * X x) + m x * X x ^ 2 := by
      intro x
      ring
    simp only [energy, Pi.add_apply]
    rw [Finset.sum_congr rfl (fun x _ => hpt x)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  -- The cross term is the scalar-curvature pairing plus the Dirichlet energy.
  have hcross : 0 ≤ ∑ x, m x * u x * X x := by
    have hexp : (∑ x, m x * u x * X x)
        = (∑ x, m x * R x * u x ^ 2)
          - ∑ x, m x * u x * laplaceBeltrami D w m u x := by
      simp only [hX]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [hexp]
    have hcurv : 0 ≤ ∑ x, m x * R x * u x ^ 2 := by
      refine Finset.sum_nonneg (fun x _ => ?_)
      have h1 : 0 ≤ m x * R x := mul_nonneg (le_of_lt (hm x)) (hR x)
      calc (0 : ℝ) ≤ (m x * R x) * (u x * u x) := mul_nonneg h1 (mul_self_nonneg _)
        _ = m x * R x * u x ^ 2 := by ring
    have hlap : (∑ x, m x * u x * laplaceBeltrami D w m u x)
        = -dirichletForm D w Finset.univ u u := by
      have hg := green_first D w m (fun x => ne_of_gt (hm x)) Finset.univ u u
      rw [boundaryPair_univ] at hg
      have hsymm : pairingOn m Finset.univ (laplaceBeltrami D w m u) u
          = ∑ x, m x * u x * laplaceBeltrami D w m u x := by
        simp only [pairingOn]
        exact Finset.sum_congr rfl (fun x _ => by ring)
      rw [hsymm] at hg
      linarith
    have hdir : 0 ≤ dirichletForm D w Finset.univ u u :=
      dirichletForm_nonneg D w Finset.univ u hw
    linarith
  -- The square term is nonnegative because the mass is positive.
  have hsquare : 0 ≤ ∑ x, m x * X x ^ 2 :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (le_of_lt (hm x)) (sq_nonneg _))
  linarith

/-- **Slab monotonicity of the discrete conjugate-heat flow.** If the successive slices of a slab
are related by the conjugate-heat step, the mass-weighted energy of the first slice is at most the
energy of the last slice. -/
theorem energy_mono_slab {n : ℕ} (D : DivergenceData V E) (w : E → ℝ) (m R : V → ℝ)
    (hm : ∀ x, 0 < m x) (hw : ∀ e, 0 ≤ w e) (hR : ∀ x, 0 ≤ R x)
    (u : Fin (n + 1) → V → ℝ)
    (hstep : ∀ k : Fin n, u k.succ = conjugateHeatStep D w m R (u k.castSucc)) :
    energy m (u 0) ≤ energy m (u (Fin.last n)) := by
  have htelescope := sum_telescope (fun k : Fin (n + 1) => energy m (u k))
  have hnonneg : 0 ≤ ∑ k : Fin n,
      (energy m (u k.succ) - energy m (u k.castSucc)) := by
    refine Finset.sum_nonneg (fun k _ => ?_)
    rw [hstep k]
    exact sub_nonneg.mpr
      (energy_le_energy_conjugateHeatStep D w m R hm hw hR (u k.castSucc))
  linarith

end Poincare.D7.ConjugateHeat
