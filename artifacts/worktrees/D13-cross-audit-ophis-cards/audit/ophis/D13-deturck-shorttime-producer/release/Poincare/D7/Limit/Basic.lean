/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-discrete-continuous-limit)
-/

import Poincare.Longrun.PDE.DiscreteMaximumPrinciple
import Poincare.Longrun.PDE.ContinuousInterface
import Poincare.Longrun.Evolution.Bridge

/-!
# Poincare.D7.Limit.Basic

**D7 discrete-to-continuous limit, part 1: meshes, refinements and slabs.**

This file sets up the geometric data used by the consistency certificate of
`Poincare.D7.Limit.ErrorRecursion`:

* `GridMesh a b N` — a strictly increasing grid `x 0 = a < x 1 < … < x (N+1) = b`
  with `N+1` cells (so `N+2` nodes, the two extreme ones being the Dirichlet
  boundary);
* `GridMesh.Refines` — the mesh-refinement relation: every node of the coarse
  grid is a node of the fine grid;
* `TimeMesh Δt` — the discrete time grid `t n = n * Δt`;
* `SlabGrid N α` — a finite-difference slab with the explicit-Euler update
  `v (t+1) i = α v t (i-1) + (1-2α) v t i + α v t (i+1)` at interior points and
  **arbitrary** boundary traces.  This generalizes the D2
  `Poincare.Longrun.PDE.HeatGridEvolution`, whose boundary traces are pinned to
  `0`; the zero-boundary case is recovered by `SlabGrid.ofHeatGridEvolution`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted`.
-/

open Filter Set
open Poincare.Longrun.PDE
open scoped BigOperators Topology

namespace Poincare.D7.Limit

/-- The triangle inequality for three real terms. -/
theorem abs_three_le (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  have h1 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h2 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

/-! ## Spatial meshes -/

/-- **A one-dimensional spatial mesh** on `[a,b]` with `N+1` cells and `N+2`
nodes.  The nodes `0` and `N+1` are the Dirichlet boundary points, pinned to
`a` and `b`; the mesh is strictly increasing on the node range. -/
structure GridMesh (a b : ℝ) (N : ℕ) where
  /-- The node positions.  Only the values at `0, …, N+1` are constrained. -/
  x : ℕ → ℝ
  /-- The left boundary node is `a`. -/
  x_zero : x 0 = a
  /-- The right boundary node is `b`. -/
  x_last : x (N + 1) = b
  /-- The mesh is strictly increasing on the node range. -/
  x_strict : ∀ i j, i ≤ N + 1 → j ≤ N + 1 → i < j → x i < x j

namespace GridMesh

variable {a b : ℝ} {N N' : ℕ}

/-- The interval is nondegenerate: `a < b`. -/
theorem a_lt_b (G : GridMesh a b N) : a < b := by
  have h0 : (0 : ℕ) ≤ N + 1 := Nat.zero_le _
  have h1 : (1 : ℕ) ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le N)
  have h01 : G.x 0 < G.x 1 := G.x_strict 0 1 h0 h1 (by norm_num)
  have h1N : G.x 1 ≤ G.x (N + 1) := by
    rcases eq_or_lt_of_le h1 with h | h
    · have hN : N = 0 := by omega
      subst hN
      simp
    · exact (G.x_strict 1 (N + 1) h1 (le_refl _) h).le
  rw [G.x_zero] at h01
  rw [G.x_last] at h1N
  linarith

/-- Every node in range is at least `a`. -/
theorem a_le_x (G : GridMesh a b N) {i : ℕ} (hi : i ≤ N + 1) : a ≤ G.x i := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp [G.x_zero]
  · have h := G.x_strict 0 i (Nat.zero_le _) hi hpos
    simpa [G.x_zero] using h.le

/-- Every node in range is at most `b`. -/
theorem x_le_b (G : GridMesh a b N) {i : ℕ} (hi : i ≤ N + 1) : G.x i ≤ b := by
  rcases eq_or_lt_of_le hi with h | hlt
  · simp [h, G.x_last]
  · have h := G.x_strict i (N + 1) hi (le_refl _) hlt
    simpa [G.x_last] using h.le

/-- Every node in range lies in the closed interval `[a,b]`. -/
theorem mem_Icc (G : GridMesh a b N) {i : ℕ} (hi : i ≤ N + 1) : G.x i ∈ Icc a b :=
  ⟨G.a_le_x hi, G.x_le_b hi⟩

/-- **Mesh refinement.**  `fine` refines `coarse` when every node of `coarse` is
a node of `fine`.  (No relation between the cell counts is imposed; the strict
monotonicity of both meshes makes the coarse nodes a subset of the fine nodes.) -/
def Refines (coarse : GridMesh a b N) (fine : GridMesh a b N') : Prop :=
  ∀ i ≤ N + 1, ∃ j ≤ N' + 1, fine.x j = coarse.x i

/-- Refinement is reflexive. -/
theorem Refines.refl (G : GridMesh a b N) : G.Refines G :=
  fun i hi => ⟨i, hi, rfl⟩

/-- Refinement is transitive. -/
theorem Refines.trans {G₁ : GridMesh a b N} {G₂ : GridMesh a b N'} {G₃ : GridMesh a b N''}
    (h₁₂ : G₁.Refines G₂) (h₂₃ : G₂.Refines G₃) : G₁.Refines G₃ := by
  intro i hi
  obtain ⟨j, hj, hxj⟩ := h₁₂ i hi
  obtain ⟨k, hk, hxk⟩ := h₂₃ j hj
  exact ⟨k, hk, hxk.trans hxj⟩

/-- **The uniform mesh** `x i = a + i * h` with `(N+1) * h = b - a`. -/
def uniform (a b h : ℝ) (N : ℕ) (hh : 0 < h) (hN : ((N + 1 : ℕ) : ℝ) * h = b - a) :
    GridMesh a b N where
  x i := a + (i : ℝ) * h
  x_zero := by simp
  x_last := by
    have hN' : ((N : ℝ) + 1) * h = b - a := by simpa using hN
    linarith
  x_strict := by
    intro i j _ _ hij
    have hji : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    have h := mul_lt_mul_of_pos_right hji hh
    linarith

@[simp]
theorem uniform_x (a b h : ℝ) (N : ℕ) (hh : 0 < h)
    (hN : ((N + 1 : ℕ) : ℝ) * h = b - a) (i : ℕ) :
    (uniform a b h N hh hN).x i = a + (i : ℝ) * h := rfl

end GridMesh

/-! ## Time meshes -/

/-- **A discrete time mesh** with constant step `Δt`: `t n = n * Δt`. -/
structure TimeMesh (Δt : ℝ) where
  /-- The time of step `n`. -/
  time : ℕ → ℝ
  /-- The initial time is `0`. -/
  time_zero : time 0 = 0
  /-- The recursion `t (n+1) = t n + Δt`. -/
  time_step : ∀ n, time (n + 1) = time n + Δt

namespace TimeMesh

variable {Δt : ℝ}

/-- The closed form of the time mesh: `t n = n * Δt`. -/
theorem time_eq (T : TimeMesh Δt) (n : ℕ) : T.time n = (n : ℝ) * Δt := by
  induction n with
  | zero => simp [T.time_zero]
  | succ n ih => rw [T.time_step, ih]; push_cast; ring

/-- The time mesh is monotone for a nonnegative step. -/
theorem monotone (T : TimeMesh Δt) (hΔt : 0 ≤ Δt) : Monotone T.time := by
  intro m n hmn
  rw [T.time_eq m, T.time_eq n]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) hΔt

/-- The time mesh is strictly monotone for a positive step. -/
theorem strictMono (T : TimeMesh Δt) (hΔt : 0 < Δt) : StrictMono T.time := by
  intro m n hmn
  rw [T.time_eq m, T.time_eq n]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hmn) hΔt

end TimeMesh

/-! ## Finite-difference slabs -/

/-- **A finite-difference slab.**  `v t i` is the value at time step `t` and
node `i`; the update at interior nodes `0 < i < N+1` is the explicit-Euler step
in convex-combination form.  Boundary traces are arbitrary: this is the
generalization of the D2 zero-Dirichlet `HeatGridEvolution` needed for the
consistency error analysis. -/
structure SlabGrid (N : ℕ) (α : ℝ) where
  /-- The space-time values. -/
  v : ℕ → ℕ → ℝ
  /-- The explicit-Euler update at interior nodes. -/
  step : ∀ t i, 0 < i → i < N + 1 →
    v (t + 1) i = α * v t (i - 1) + (1 - 2 * α) * v t i + α * v t (i + 1)

namespace SlabGrid

variable {N : ℕ} {α : ℝ}

/-- The update in `heatStep` form. -/
theorem step_heatStep (G : SlabGrid N α) {t i : ℕ} (hi0 : 0 < i) (hiN : i < N + 1) :
    G.v (t + 1) i = heatStep α (G.v t) i := by
  rw [G.step t i hi0 hiN]
  simp only [heatStep]

/-- Every D2 zero-Dirichlet evolution is a finite-difference slab. -/
def ofHeatGridEvolution (ev : HeatGridEvolution N α) : SlabGrid N α where
  v := ev.u
  step := by
    intro t i hi0 hiN
    rw [ev.step t i hi0 hiN]
    ring

@[simp]
theorem ofHeatGridEvolution_v (ev : HeatGridEvolution N α) :
    (ofHeatGridEvolution ev).v = ev.u := rfl

/-- A finite-difference slab whose boundary traces vanish is a D2 zero-Dirichlet
heat evolution.  This is the converse of `ofHeatGridEvolution`. -/
def toHeatGridEvolution (G : SlabGrid N α) (h0 : ∀ n, G.v n 0 = 0)
    (hN : ∀ n, G.v n (N + 1) = 0) : HeatGridEvolution N α where
  u := G.v
  boundary_left := h0
  boundary_right := hN
  step t i hi0 hiN := by
    rw [G.step t i hi0 hiN]
    ring

@[simp]
theorem toHeatGridEvolution_u (G : SlabGrid N α) (h0 : ∀ n, G.v n 0 = 0)
    (hN : ∀ n, G.v n (N + 1) = 0) :
    (toHeatGridEvolution G h0 hN).u = G.v := rfl

end SlabGrid

end Poincare.D7.Limit
