/-
Task `D9-parabolic-maximum-principle`: kernel-checked discrete comparison lemma.

This file contains the fully checked toy theorem of the D9 task: for an explicit
finite-difference model of the heat-type operator
`Δu + ⟨X, ∇u⟩ + b · u`, a discrete subsolution that starts below a discrete
supersolution stays below it on the whole time grid.

All steps are proved; there is no placeholder of any kind.
-/
import Poincare.Longrun.PDE.HeatGrid

/-!
# `Poincare.D9.ParabolicMaximumPrinciple.DiscreteComparison`

Two layers, both completely proved.

## 1. Abstract one-step comparison

For any type `ι` of grid points, any one-step operator `step` that is monotone
with respect to the pointwise order, a sequence `u` satisfying the discrete
subsolution inequality `u (t+1) ≤ step (u t)` and a sequence `v` satisfying the
discrete supersolution inequality `step (v t) ≤ v (t+1)` compare on the whole
time grid: `u t ≤ v t` for every `t`, provided `u 0 ≤ v 0`.  This is pure order
theory and is proved by induction on `t`, with the monotonicity of `step` as the
only ingredient besides transitivity.

## 2. The explicit finite-difference model

On the path grid `0, 1, …, N+1` with Dirichlet boundary datum `g`, the spatial
operator is discretized as

`L w i = α * Δw i + β * (w (i+1) - w i) + γ * w i`,

with `α` the diffusion coefficient (the discrete Laplacian `Δ` is the one already
present in `Poincare.Longrun.PDE.HeatGrid`), `β` the upwind coefficient of the
drift `⟨X, ∇u⟩` and `γ` the coefficient of the reaction `b · u`.  The
forward-Euler step is `w i + L w i`, i.e.

`α * w (i-1) + (1 - 2α - β + γ) * w i + (α + β) * w (i+1)`.

Under the stability conditions `0 ≤ α`, `0 ≤ β` and `2α + β - γ ≤ 1` all three
coefficients are nonnegative, so the step is monotone; the grid comparison theorem
is then proved by induction on time, with the boundary comparison supplied by the
common Dirichlet datum `g`.  The stability condition is the discrete analogue of
the CFL-type hypothesis needed for the parabolic maximum principle (compare
`Poincare.Longrun.PDE.DiscreteMaximumPrinciple`, which is the pure-heat case
`β = γ = 0`).
-/

namespace Poincare.D9.ParabolicMaximumPrinciple

open Poincare.Longrun.PDE

universe u

/-! ## 1. Abstract one-step comparison for monotone schemes -/

/-- A one-step finite-difference operator that is monotone with respect to the
pointwise order on configurations.  The explicit heat step and every other
monotone (e.g. upwind, positive-coefficient) scheme are instances. -/
structure MonotoneScheme (ι : Type u) where
  /-- The one-step update. -/
  step : (ι → ℝ) → ι → ℝ
  /-- Monotonicity: larger input configurations produce larger output
  configurations, pointwise. -/
  monotone : ∀ {w z : ι → ℝ}, (∀ i, w i ≤ z i) → ∀ i, step w i ≤ step z i

/-- **Abstract discrete comparison lemma (all steps proved).**

If `u` is a discrete subsolution and `v` a discrete supersolution of the same
monotone one-step scheme, and `u` starts below `v`, then `u` stays below `v` on
the whole time grid `t = 0, 1, 2, …`. -/
theorem comparison_of_monotoneScheme {ι : Type u} (S : MonotoneScheme ι)
    {u v : ℕ → ι → ℝ}
    (hu : ∀ t i, u (t + 1) i ≤ S.step (u t) i)
    (hv : ∀ t i, S.step (v t) i ≤ v (t + 1) i)
    (h0 : ∀ i, u 0 i ≤ v 0 i) :
    ∀ t i, u t i ≤ v t i := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
      intro i
      exact le_trans (hu t i) (le_trans (S.monotone ih i) (hv t i))

/-- **Discrete comparison for two exact solutions of a monotone scheme.**  If both
sequences satisfy the one-step recurrence exactly, the same comparison holds. -/
theorem comparison_of_monotoneScheme_of_eq {ι : Type u} (S : MonotoneScheme ι)
    {u v : ℕ → ι → ℝ}
    (hu : ∀ t i, u (t + 1) i = S.step (u t) i)
    (hv : ∀ t i, v (t + 1) i = S.step (v t) i)
    (h0 : ∀ i, u 0 i ≤ v 0 i) :
    ∀ t i, u t i ≤ v t i :=
  comparison_of_monotoneScheme S (fun t i => le_of_eq (hu t i))
    (fun t i => le_of_eq (hv t i).symm) h0

/-! ## 2. The explicit finite-difference model -/

/-- The finite-difference discretization of the spatial heat-type operator
`Δu + ⟨X, ∇u⟩ + b · u` on the path grid:

`α * Δw i + β * (w (i+1) - w i) + γ * w i`,

where `Δ` is the release's `discreteLaplacian`, `β` is the upwind drift
coefficient and `γ` is the reaction coefficient. -/
def fdOperator (α β γ : ℝ) (w : ℕ → ℝ) (i : ℕ) : ℝ :=
  α * discreteLaplacian w i + β * (w (i + 1) - w i) + γ * w i

/-- The explicit forward-Euler step `w + L w` of the finite-difference model. -/
def fdStep (α β γ : ℝ) (w : ℕ → ℝ) (i : ℕ) : ℝ :=
  w i + fdOperator α β γ w i

/-- The explicit step in the three-point convex-combination form used by the
comparison argument. -/
theorem fdStep_eq_convex (α β γ : ℝ) (w : ℕ → ℝ) (i : ℕ) :
    fdStep α β γ w i
      = α * w (i - 1) + (1 - 2 * α - β + γ) * w i + (α + β) * w (i + 1) := by
  simp only [fdStep, fdOperator, discreteLaplacian]
  ring

/-- **Monotonicity of the finite-difference step.**  If `0 ≤ α`, `0 ≤ α + β`
and `0 ≤ 1 - 2α - β + γ` then all three coefficients in the convex-combination
form are nonnegative and the step is monotone in its configuration argument. -/
theorem fdStep_mono {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ α + β)
    (hγ : 0 ≤ 1 - 2 * α - β + γ) {w z : ℕ → ℝ} (h : ∀ i, w i ≤ z i) (i : ℕ) :
    fdStep α β γ w i ≤ fdStep α β γ z i := by
  have h1 : α * w (i - 1) ≤ α * z (i - 1) :=
    mul_le_mul_of_nonneg_left (h (i - 1)) hα
  have h2 : (1 - 2 * α - β + γ) * w i ≤ (1 - 2 * α - β + γ) * z i :=
    mul_le_mul_of_nonneg_left (h i) hγ
  have h3 : (α + β) * w (i + 1) ≤ (α + β) * z (i + 1) :=
    mul_le_mul_of_nonneg_left (h (i + 1)) hβ
  rw [fdStep_eq_convex, fdStep_eq_convex]
  linarith

/-- **Monotonicity on a finite grid.**  Only the values on the grid `0, …, N+1`
are needed to compare the step at an interior point `i < N+1`.  This is the form
consumed by the grid comparison theorem, whose inductive hypothesis only
controls the grid points. -/
theorem fdStep_mono_of_le {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ α + β)
    (hγ : 0 ≤ 1 - 2 * α - β + γ) {N : ℕ} {w z : ℕ → ℝ}
    (h : ∀ j ≤ N + 1, w j ≤ z j) {i : ℕ} (hi : i < N + 1) :
    fdStep α β γ w i ≤ fdStep α β γ z i := by
  have h1 : α * w (i - 1) ≤ α * z (i - 1) :=
    mul_le_mul_of_nonneg_left (h (i - 1) (by omega)) hα
  have h2 : (1 - 2 * α - β + γ) * w i ≤ (1 - 2 * α - β + γ) * z i :=
    mul_le_mul_of_nonneg_left (h i (by omega)) hγ
  have h3 : (α + β) * w (i + 1) ≤ (α + β) * z (i + 1) :=
    mul_le_mul_of_nonneg_left (h (i + 1) (by omega)) hβ
  rw [fdStep_eq_convex, fdStep_eq_convex]
  linarith

/-- The finite-difference model is an instance of the abstract monotone-scheme
comparison layer. -/
def fdMonotoneScheme {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ α + β)
    (hγ : 0 ≤ 1 - 2 * α - β + γ) : MonotoneScheme ℕ where
  step := fdStep α β γ
  monotone := fun h i => fdStep_mono hα hβ hγ h i

/-! ### The grid comparison theorem -/

/-- A discrete **subsolution** on the path grid `0, 1, …, N+1` with Dirichlet
boundary datum `g`: the values at the two boundary points are at most the datum
and the forward-Euler step over-estimates the actual next slice in the interior. -/
structure GridSubsolution (N : ℕ) (α β γ : ℝ) (g : ℕ → ℝ) (u : ℕ → ℕ → ℝ) : Prop where
  /-- Left Dirichlet boundary inequality. -/
  boundary_left : ∀ t, u t 0 ≤ g 0
  /-- Right Dirichlet boundary inequality. -/
  boundary_right : ∀ t, u t (N + 1) ≤ g (N + 1)
  /-- Discrete subsolution inequality at interior points. -/
  step_le : ∀ t i, 0 < i → i < N + 1 → u (t + 1) i ≤ fdStep α β γ (u t) i

/-- A discrete **supersolution** on the path grid with Dirichlet boundary datum
`g`: the datum is at most the values at the two boundary points and the
forward-Euler step under-estimates the actual next slice in the interior. -/
structure GridSupersolution (N : ℕ) (α β γ : ℝ) (g : ℕ → ℝ) (v : ℕ → ℕ → ℝ) : Prop where
  /-- Left Dirichlet boundary inequality. -/
  boundary_left : ∀ t, g 0 ≤ v t 0
  /-- Right Dirichlet boundary inequality. -/
  boundary_right : ∀ t, g (N + 1) ≤ v t (N + 1)
  /-- Discrete supersolution inequality at interior points. -/
  step_ge : ∀ t i, 0 < i → i < N + 1 → fdStep α β γ (v t) i ≤ v (t + 1) i

/-- **One-step grid comparison.**  Under the stability conditions `0 ≤ α`,
`0 ≤ β` and `2α + β - γ ≤ 1`, if the slice at time `t` is pointwise ordered, so
is the slice at time `t+1`: the boundary values are compared through the common
Dirichlet datum and the interior values through the monotone step. -/
theorem grid_comparison_succ {N : ℕ} {α β γ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hstab : 2 * α + β - γ ≤ 1)
    {g : ℕ → ℝ} {u v : ℕ → ℕ → ℝ}
    (hu : GridSubsolution N α β γ g u) (hv : GridSupersolution N α β γ g v) {t : ℕ}
    (ht : ∀ i ≤ N + 1, u t i ≤ v t i) :
    ∀ i ≤ N + 1, u (t + 1) i ≤ v (t + 1) i := by
  intro i hi
  have hβ' : 0 ≤ α + β := by linarith
  have hγ' : 0 ≤ 1 - 2 * α - β + γ := by linarith
  by_cases hi0 : i = 0
  · rw [hi0]
    exact le_trans (hu.boundary_left (t + 1)) (hv.boundary_left (t + 1))
  by_cases hiN : i = N + 1
  · rw [hiN]
    exact le_trans (hu.boundary_right (t + 1)) (hv.boundary_right (t + 1))
  · have hpos : 0 < i := Nat.pos_of_ne_zero hi0
    have hlt : i < N + 1 := lt_of_le_of_ne hi hiN
    exact le_trans (hu.step_le t i hpos hlt)
      (le_trans (fdStep_mono_of_le hα hβ' hγ' ht hlt) (hv.step_ge t i hpos hlt))

/-- **Discrete comparison principle on the whole time grid (all steps proved).**

For the explicit finite-difference model of `Δu + ⟨X, ∇u⟩ + b · u` on the path
grid with Dirichlet boundary datum `g`, under the stability conditions `0 ≤ α`,
`0 ≤ β` and `2α + β - γ ≤ 1`: a discrete subsolution `u` that starts below a
discrete supersolution `v` stays below `v` at every grid point and every time
step. -/
theorem grid_comparison {N : ℕ} {α β γ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hstab : 2 * α + β - γ ≤ 1)
    {g : ℕ → ℝ} {u v : ℕ → ℕ → ℝ}
    (hu : GridSubsolution N α β γ g u) (hv : GridSupersolution N α β γ g v)
    (h0 : ∀ i ≤ N + 1, u 0 i ≤ v 0 i) :
    ∀ t i, i ≤ N + 1 → u t i ≤ v t i := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih => exact grid_comparison_succ hα hβ hstab hu hv ih

/-! ### Corollaries: exact solutions, uniqueness, and the maximum principle -/

/-- A discrete **solution** on the path grid with Dirichlet boundary datum `g`. -/
structure GridSolution (N : ℕ) (α β γ : ℝ) (g : ℕ → ℝ) (u : ℕ → ℕ → ℝ) : Prop where
  /-- Left Dirichlet boundary condition. -/
  boundary_left : ∀ t, u t 0 = g 0
  /-- Right Dirichlet boundary condition. -/
  boundary_right : ∀ t, u t (N + 1) = g (N + 1)
  /-- Exact forward-Euler update at interior points. -/
  step_eq : ∀ t i, 0 < i → i < N + 1 → u (t + 1) i = fdStep α β γ (u t) i

/-- Every grid solution is a grid subsolution of its own Dirichlet datum. -/
theorem gridSubsolution_of_gridSolution {N : ℕ} {α β γ : ℝ} {g : ℕ → ℝ}
    {u : ℕ → ℕ → ℝ} (hu : GridSolution N α β γ g u) :
    GridSubsolution N α β γ g u where
  boundary_left := fun t => le_of_eq (hu.boundary_left t)
  boundary_right := fun t => le_of_eq (hu.boundary_right t)
  step_le := fun t i hpos hlt => le_of_eq (hu.step_eq t i hpos hlt)

/-- Every grid solution is a grid supersolution of its own Dirichlet datum. -/
theorem gridSupersolution_of_gridSolution {N : ℕ} {α β γ : ℝ} {g : ℕ → ℝ}
    {u : ℕ → ℕ → ℝ} (hu : GridSolution N α β γ g u) :
    GridSupersolution N α β γ g u where
  boundary_left := fun t => le_of_eq (hu.boundary_left t).symm
  boundary_right := fun t => le_of_eq (hu.boundary_right t).symm
  step_ge := fun t i hpos hlt => le_of_eq (hu.step_eq t i hpos hlt).symm

/-- **Comparison of two exact solutions.**  Two grid solutions with the same
Dirichlet datum and ordered initial slices stay ordered on the whole time grid. -/
theorem grid_comparison_of_solution {N : ℕ} {α β γ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hstab : 2 * α + β - γ ≤ 1)
    {g : ℕ → ℝ} {u v : ℕ → ℕ → ℝ} (hu : GridSolution N α β γ g u)
    (hv : GridSolution N α β γ g v) (h0 : ∀ i ≤ N + 1, u 0 i ≤ v 0 i) :
    ∀ t i, i ≤ N + 1 → u t i ≤ v t i :=
  grid_comparison hα hβ hstab (gridSubsolution_of_gridSolution hu)
    (gridSupersolution_of_gridSolution hv) h0

/-- **Uniqueness of grid solutions.**  Two grid solutions with the same
Dirichlet datum and the same initial slice agree on the whole time grid. -/
theorem grid_solution_unique {N : ℕ} {α β γ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hstab : 2 * α + β - γ ≤ 1)
    {g : ℕ → ℝ} {u v : ℕ → ℕ → ℝ} (hu : GridSolution N α β γ g u)
    (hv : GridSolution N α β γ g v) (h0 : ∀ i ≤ N + 1, u 0 i = v 0 i) :
    ∀ t i, i ≤ N + 1 → u t i = v t i := by
  intro t i hi
  exact le_antisymm
    (grid_comparison_of_solution hα hβ hstab hu hv (fun i hi => le_of_eq (h0 i hi)) t i hi)
    (grid_comparison_of_solution hα hβ hstab hv hu (fun i hi => le_of_eq (h0 i hi).symm) t i hi)

/-- **The classical maximum principle as a corollary of comparison.**  With zero
Dirichlet datum, a nonpositive reaction coefficient (`γ ≤ 0`) and `M ≥ 0`, the
constant field `M` is a supersolution (the zero datum is at most `M`), so every
grid subsolution starting below `M` is bounded by `M` on the whole time grid. -/
theorem grid_le_of_constant_barrier {N : ℕ} {α β γ M : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hstab : 2 * α + β - γ ≤ 1)
    (hγ : γ ≤ 0) (hM : 0 ≤ M)
    {u : ℕ → ℕ → ℝ} (hu : GridSubsolution N α β γ (fun _ => 0) u)
    (h0 : ∀ i ≤ N + 1, u 0 i ≤ M) :
    ∀ t i, i ≤ N + 1 → u t i ≤ M := by
  have hv : GridSupersolution N α β γ (fun _ => 0) (fun _ _ => M) := by
    refine ⟨?_, ?_, ?_⟩
    · intro t
      exact hM
    · intro t
      exact hM
    · intro t i _ _
      simp only [fdStep_eq_convex]
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hγ hM]
  exact grid_comparison hα hβ hstab hu hv h0

/-- **Non-vacuity witness.**  The zero field is an exact grid solution of the
finite-difference model for the zero Dirichlet datum, for every choice of the
coefficients: the stability hypotheses used by the comparison theorem are
therefore consistent with the solution predicate. -/
theorem gridSolution_zero (N : ℕ) (α β γ : ℝ) :
    GridSolution N α β γ (fun _ => 0) (fun _ _ => 0) where
  boundary_left := fun _ => rfl
  boundary_right := fun _ => rfl
  step_eq := by
    intro t i _ _
    simp [fdStep, fdOperator, discreteLaplacian]

/-! ## Axiom audit -/

#print axioms MonotoneScheme
#print axioms comparison_of_monotoneScheme
#print axioms comparison_of_monotoneScheme_of_eq
#print axioms fdOperator
#print axioms fdStep
#print axioms fdStep_eq_convex
#print axioms fdStep_mono
#print axioms fdStep_mono_of_le
#print axioms fdMonotoneScheme
#print axioms GridSubsolution
#print axioms GridSupersolution
#print axioms grid_comparison_succ
#print axioms grid_comparison
#print axioms GridSolution
#print axioms gridSubsolution_of_gridSolution
#print axioms gridSupersolution_of_gridSolution
#print axioms grid_comparison_of_solution
#print axioms grid_solution_unique
#print axioms grid_le_of_constant_barrier
#print axioms gridSolution_zero

end Poincare.D9.ParabolicMaximumPrinciple
