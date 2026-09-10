/-
Task `D2-pde-foundation`: finite-grid heat-evolution foundation.

This file is part of the long-run Poincaré formalization.  It consumes the
accepted `D1-pde-api-map` probe (`longrun/results/D1-pde-api-map.md`), which
established that the pinned mathlib has no heat-equation theory and that the
finite-grid layer is the part which can be fully checked today.
-/
import Mathlib

/-!
# `Poincare.Longrun.PDE.HeatGrid`

Finite-grid heat evolution: data structures and basic rewriting lemmas.

## Conventions (explicit)

* Space is the finite path `0, 1, …, N+1`.  The points `0` and `N+1` are the
  Dirichlet boundary and are pinned to `0` for all times.
* Time is discrete: `u t i` is the value at time step `t` and grid point `i`.
* The heat equation is written with the **positive** sign `∂ₜ u = ∂ₓ² u`.  The
  forward-Euler (explicit) scheme is
  `u (t+1) i = u t i + α * (u t (i-1) - 2 * u t i + u t (i+1))`.
* `α ≥ 0` is the time-step/space-step ratio `Δt / Δx²`.  The stability
  (convexity) condition `α ≤ 1/2` is deliberately **not** a field of the
  structure: it is an explicit hypothesis of the maximum principle
  (`Poincare.Longrun.PDE.HeatGridEvolution.le_of_initial_le`) and of the energy
  monotonicity theorem (`Poincare.Longrun.PDE.HeatGridEvolution.energy_nonincreasing`),
  so every use site displays the sign conventions it relies on.
-/

open scoped BigOperators

namespace Poincare.Longrun.PDE

/-- Zero extension of a grid function past the right boundary.

For the grid `0, …, N+1` we extend a configuration by `0` at every index
`j ≥ N+2`.  Together with the convention `0 - 1 = 0` on `ℕ`, this turns the
shifted sums appearing in the energy estimate into sums over the same index set. -/
def zeroExtend (u : ℕ → ℝ) (N : ℕ) : ℕ → ℝ := fun j => if j ≤ N + 1 then u j else 0

/-- The one-dimensional discrete Laplacian `Δw i = w (i-1) + w (i+1) - 2 * w i`.

It is meant to be applied at interior grid points; at `i = 0` the term `i - 1`
saturates to `0` on `ℕ`, which is harmless because boundary values are pinned to
`0` in every evolution considered here. -/
def discreteLaplacian (w : ℕ → ℝ) (i : ℕ) : ℝ := w (i - 1) + w (i + 1) - 2 * w i

/-- One explicit-Euler heat step at grid point `i`:
`α * w (i-1) + (1 - 2α) * w i + α * w (i+1)`.

For `0 ≤ α ≤ 1/2` this is a convex combination of the old values at `i-1`, `i`,
`i+1`; this is exactly the algebraic form used by both the discrete maximum
principle and the energy estimate. -/
def heatStep (α : ℝ) (w : ℕ → ℝ) (i : ℕ) : ℝ :=
  α * w (i - 1) + (1 - 2 * α) * w i + α * w (i + 1)

/-- The explicit heat step is the identity plus `α` times the discrete Laplacian:
`heatStep α w i = w i + α * Δw i`.  This makes the sign convention
`∂ₜ u = + ∂ₓ² u` explicit. -/
theorem heatStep_eq_discreteLaplacian (α : ℝ) (w : ℕ → ℝ) (i : ℕ) :
    heatStep α w i = w i + α * discreteLaplacian w i := by
  simp only [heatStep, discreteLaplacian]
  ring

/-- A finite-grid explicit-Euler heat evolution with zero Dirichlet boundary.

The fields record, in order: the space-time temperature field `u`, the two
boundary conditions `u t 0 = 0` and `u t (N+1) = 0`, and the forward-Euler
update at interior points.  The update is written in the "identity plus `α` times
the discrete Laplacian" form, matching the heat equation `∂ₜ u = ∂ₓ² u`.

The CFL/convexity condition `0 ≤ α ≤ 1/2` is not a field; see the module
documentation. -/
structure HeatGridEvolution (N : ℕ) (α : ℝ) where
  /-- Space-time temperature field: `u t i` is the value at time `t`, point `i`. -/
  u : ℕ → ℕ → ℝ
  /-- Left Dirichlet boundary condition. -/
  boundary_left : ∀ t, u t 0 = 0
  /-- Right Dirichlet boundary condition. -/
  boundary_right : ∀ t, u t (N + 1) = 0
  /-- Forward-Euler heat update at every interior grid point. -/
  step : ∀ t i, 0 < i → i < N + 1 →
    u (t + 1) i = u t i + α * (u t (i - 1) - 2 * u t i + u t (i + 1))

/-- The evolution equation in discrete-Laplacian form. -/
theorem HeatGridEvolution.step_eq_discreteLaplacian {N : ℕ} {α : ℝ}
    (ev : HeatGridEvolution N α) {t i : ℕ} (hi0 : 0 < i) (hiN : i < N + 1) :
    ev.u (t + 1) i = ev.u t i + α * discreteLaplacian (ev.u t) i := by
  rw [ev.step t i hi0 hiN]
  simp only [discreteLaplacian]
  ring

/-- The evolution equation in `heatStep` form, using the zero extension. -/
theorem HeatGridEvolution.step_eq_heatStep {N : ℕ} {α : ℝ}
    (ev : HeatGridEvolution N α) {t i : ℕ} (hi0 : 0 < i) (hiN : i < N + 1) :
    ev.u (t + 1) i = heatStep α (zeroExtend (ev.u t) N) i := by
  rw [ev.step t i hi0 hiN]
  have h1 : i - 1 ≤ N + 1 := by omega
  have h2 : i ≤ N + 1 := by omega
  have h3 : i + 1 ≤ N + 1 := by omega
  simp only [heatStep, zeroExtend]
  rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left h3]
  ring

/-- The evolution equation in convex-combination form, with all boundary
coefficients explicit.  This is the form consumed by the maximum principle. -/
theorem HeatGridEvolution.step_eq_convex {N : ℕ} {α : ℝ}
    (ev : HeatGridEvolution N α) {t i : ℕ} (hi0 : 0 < i) (hiN : i < N + 1) :
    ev.u (t + 1) i
      = α * ev.u t (i - 1) + (1 - 2 * α) * ev.u t i + α * ev.u t (i + 1) := by
  rw [ev.step t i hi0 hiN]
  ring

/-! ## Axiom audit -/

#print axioms zeroExtend
#print axioms discreteLaplacian
#print axioms heatStep
#print axioms HeatGridEvolution
#print axioms heatStep_eq_discreteLaplacian
#print axioms HeatGridEvolution.step_eq_discreteLaplacian
#print axioms HeatGridEvolution.step_eq_heatStep
#print axioms HeatGridEvolution.step_eq_convex

end Poincare.Longrun.PDE
