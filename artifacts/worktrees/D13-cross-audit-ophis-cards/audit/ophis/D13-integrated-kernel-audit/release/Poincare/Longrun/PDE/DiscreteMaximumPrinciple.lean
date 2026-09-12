/-
Task `D2-pde-foundation`: fully checked discrete maximum principles.

This file is part of the long-run Poincaré formalization.  It consumes the
accepted `D1-pde-api-map` probe (`longrun/results/D1-pde-api-map.md`): the
evolutionary maximum principle is new, while the strict static grid principle at
the end is the checked toy lemma from that probe, re-proved here in the
`Poincare.Longrun.PDE` namespace.
-/
import Poincare.Longrun.PDE.HeatGrid

/-!
# `Poincare.Longrun.PDE.DiscreteMaximumPrinciple`

Two fully checked discrete maximum principles.

## 1. Evolutionary (parabolic) maximum principle

For a `HeatGridEvolution N α` with `0 ≤ α ≤ 1/2` and zero Dirichlet boundary,
every value on the space-time grid is bounded above by any `M ≥ 0` that bounds
the initial slice:

`u t i ≤ M` whenever `u 0 j ≤ M` for all grid points `j` and `M ≥ 0`.

The `M ≥ 0` hypothesis is needed because the Dirichlet boundary is pinned to
`0`, so the constant `M` must dominate the boundary.  Equivalently (the
`le_sup'_initial` corollary) the space-time values are bounded by the maximum of
the initial slice and `0`.

## 2. Strict static maximum principle (from the D1 probe)

If `u` is strictly discrete subharmonic at every interior point of the path
`0, …, N`, then every interior value is strictly below the larger endpoint value.
This is `strict_grid_max_principle` below, with the `max`-of-neighbours form
`strict_grid_max_principle_max` as the primitive statement.
-/

open scoped BigOperators

namespace Poincare.Longrun.PDE

/-! ## 1. Evolutionary maximum principle -/

/-- The zero extension of a configuration bounded by `M` is bounded by `M`,
provided `M ≥ 0` (the extension is `0` past the right boundary). -/
theorem zeroExtend_le {u : ℕ → ℝ} {N : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hu : ∀ i ≤ N + 1, u i ≤ M) : ∀ i, zeroExtend u N i ≤ M := by
  intro i
  simp only [zeroExtend]
  split_ifs with hi
  · exact hu i hi
  · exact hM

/-- One heat step preserves the upper bound `M` when `0 ≤ α ≤ 1/2`: the new
value is a convex combination of old values (all `≤ M`) and of the zero
extension, which is `≤ M` because `M ≥ 0`. -/
theorem heatStep_le {N : ℕ} {α M : ℝ} {u : ℕ → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) (hM : 0 ≤ M)
    (hu : ∀ i ≤ N + 1, u i ≤ M) (i : ℕ) :
    heatStep α (zeroExtend u N) i ≤ M := by
  have h1 := zeroExtend_le hM hu (i - 1)
  have h2 := zeroExtend_le hM hu i
  have h3 := zeroExtend_le hM hu (i + 1)
  have hq : 0 ≤ 1 - 2 * α := by linarith
  have hmono : heatStep α (zeroExtend u N) i
      ≤ α * M + (1 - 2 * α) * M + α * M := by
    simp only [heatStep]
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left h1 hα0)
      (mul_le_mul_of_nonneg_left h2 hq)) (mul_le_mul_of_nonneg_left h3 hα0)
  calc heatStep α (zeroExtend u N) i ≤ α * M + (1 - 2 * α) * M + α * M := hmono
    _ = M := by ring

/-- **One-step maximum principle.**  If the whole slice at time `t` is bounded
above by `M ≥ 0`, then so is the slice at time `t+1`. -/
theorem HeatGridEvolution.succ_le {N : ℕ} {α M : ℝ} (ev : HeatGridEvolution N α)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) (hM : 0 ≤ M)
    (ht : ∀ i ≤ N + 1, ev.u t i ≤ M) :
    ∀ i ≤ N + 1, ev.u (t + 1) i ≤ M := by
  intro i hi
  by_cases hi0 : i = 0
  · rw [hi0, ev.boundary_left (t + 1)]
    exact hM
  by_cases hiN : i = N + 1
  · rw [hiN, ev.boundary_right (t + 1)]
    exact hM
  · have hpos : 0 < i := Nat.pos_of_ne_zero hi0
    have hlt : i < N + 1 := lt_of_le_of_ne hi hiN
    rw [ev.step_eq_heatStep hpos hlt]
    exact heatStep_le hα0 hα1 hM ht i

/-- **Discrete parabolic maximum principle (finite grid, explicit scheme).**

If `0 ≤ α ≤ 1/2`, the initial slice is bounded above by `M ≥ 0`, and the two
Dirichlet boundaries are pinned to `0`, then every value on the space-time grid
is bounded above by `M`. -/
theorem HeatGridEvolution.le_of_initial_le {N : ℕ} {α M : ℝ} (ev : HeatGridEvolution N α)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) (hM : 0 ≤ M)
    (hinit : ∀ i ≤ N + 1, ev.u 0 i ≤ M) :
    ∀ t i, i ≤ N + 1 → ev.u t i ≤ M := by
  intro t
  induction t with
  | zero => exact hinit
  | succ t ih => exact ev.succ_le hα0 hα1 hM ih

/-- **Classical form of the discrete maximum principle.**  Every space-time value
is bounded by the larger of `0` (the boundary value) and the maximum of the
initial slice. -/
theorem HeatGridEvolution.le_sup'_initial {N : ℕ} {α : ℝ} (ev : HeatGridEvolution N α)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) (t : ℕ) {i : ℕ} (hi : i ≤ N + 1) :
    ev.u t i
      ≤ max (Finset.sup' (Finset.range (N + 2))
          ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun j => ev.u 0 j)) 0 := by
  have hinit : ∀ j ≤ N + 1,
      ev.u 0 j ≤ max (Finset.sup' (Finset.range (N + 2))
          ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun j => ev.u 0 j)) 0 := by
    intro j hj
    have h1 : ev.u 0 j ≤ Finset.sup' (Finset.range (N + 2))
        ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun j => ev.u 0 j) :=
      Finset.le_sup' (fun j => ev.u 0 j) (Finset.mem_range.mpr (by omega))
    exact h1.trans (le_max_left _ _)
  exact ev.le_of_initial_le hα0 hα1 (le_max_right _ _) hinit t i hi

/-! ## 2. Strict static maximum principle (checked in the D1 probe) -/

/-- **Strict finite-grid maximum principle (`max`-of-neighbours form).**

If `u` is strictly discrete subharmonic in the weak sense that its value at every
interior grid point is strictly below the larger of its two neighbours, then
every interior value is strictly below the larger of the two endpoint values.
The grid is `0, 1, …, N`, so `N` is the last index. -/
theorem strict_grid_max_principle_max {N : ℕ} (u : ℕ → ℝ)
    (hsub : ∀ i, 0 < i → i < N → u i < max (u (i - 1)) (u (i + 1))) :
    ∀ i, 0 < i → i < N → u i < max (u 0) (u N) := by
  classical
  intro i hi0 hiN
  by_contra hnot
  simp only [not_lt] at hnot
  -- an index where the maximum of `u` on the grid is attained
  obtain ⟨k, hk_mem, hkmax⟩ :=
    Finset.exists_max_image (Finset.range (N + 1)) u
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
  have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk_mem)
  have hi_mem : i ∈ Finset.range (N + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (le_of_lt hiN))
  -- the interior value at `i` is strictly below the grid maximum
  have hneigh : u i < u k := by
    have h3 := hsub i hi0 hiN
    have h4 : u (i - 1) ≤ u k :=
      hkmax (i - 1) (Finset.mem_range.mpr (by omega))
    have h5 : u (i + 1) ≤ u k :=
      hkmax (i + 1) (Finset.mem_range.mpr (by omega))
    linarith [max_le h4 h5]
  have hui : u i ≤ u k := hkmax i hi_mem
  -- hence the maximizing index cannot be an endpoint
  have hk0 : k ≠ 0 := by
    intro hk
    rw [hk] at hneigh
    linarith [le_max_left (u 0) (u N), hnot]
  have hkN : k ≠ N := by
    intro hk
    rw [hk] at hneigh
    linarith [le_max_right (u 0) (u N), hnot]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hklt : k < N := lt_of_le_of_ne hk_le hkN
  -- but at an interior maximizer the strict inequality is impossible
  have h1 : u (k - 1) ≤ u k :=
    hkmax (k - 1) (Finset.mem_range.mpr (by omega))
  have h2 : u (k + 1) ≤ u k :=
    hkmax (k + 1) (Finset.mem_range.mpr (by omega))
  have h3 := hsub k hkpos hklt
  linarith [max_le h1 h2]

/-- **Strict finite-grid maximum principle (average form).**

If every interior value is strictly below the average of its two neighbours,
then every interior value is strictly below the larger of the two endpoint
values.  This follows from the `max`-of-neighbours form because an average is at
most the larger summand. -/
theorem strict_grid_max_principle {N : ℕ} (u : ℕ → ℝ)
    (hsub : ∀ i, 0 < i → i < N → u i < (u (i - 1) + u (i + 1)) / 2) :
    ∀ i, 0 < i → i < N → u i < max (u 0) (u N) := by
  refine strict_grid_max_principle_max u (fun i hi0 hiN => ?_)
  have h := hsub i hi0 hiN
  have havg : (u (i - 1) + u (i + 1)) / 2 ≤ max (u (i - 1)) (u (i + 1)) := by
    linarith [le_max_left (u (i - 1)) (u (i + 1)), le_max_right (u (i - 1)) (u (i + 1))]
  linarith

/-! ## Axiom audit -/

#print axioms zeroExtend_le
#print axioms heatStep_le
#print axioms HeatGridEvolution.succ_le
#print axioms HeatGridEvolution.le_of_initial_le
#print axioms HeatGridEvolution.le_sup'_initial
#print axioms strict_grid_max_principle_max
#print axioms strict_grid_max_principle

end Poincare.Longrun.PDE
