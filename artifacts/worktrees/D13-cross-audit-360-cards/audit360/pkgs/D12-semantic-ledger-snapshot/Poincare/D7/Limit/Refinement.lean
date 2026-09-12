/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-discrete-continuous-limit)
-/

import Poincare.D7.Limit.Stability

/-!
# Poincare.D7.Limit.Refinement

**D7 discrete-to-continuous limit, part 4: the discrete maximum principle is
preserved under mesh refinement.**

The D2 discrete maximum principle bounds the values of a `HeatGridEvolution` by
any `M ≥ 0` bounding the initial slice.  This file proves the two refinements
needed for the discrete-to-continuous bridge:

* `abs_le_of_initial_abs_le` — the two-sided (absolute-value) form, obtained by
  applying the D2 principle to the evolution and to its negation;
* `maxPrinciple_uniform_in_mesh` — for an initial datum sampled from a
  continuous function `f` bounded by `M` on `[a,b]`, the bound `M` holds for
  **every** mesh on `[a,b]`, uniformly in the number of cells.  This is the
  precise sense in which the discrete maximum principle is preserved under
  refinement: refining the mesh cannot increase the bound;
* `RefinesEvolution.sup_initial_le` — under a refinement, the coarse initial
  supremum is at most the fine one (every coarse node is a fine node), so the
  D2 bound `max 0 (sup initial)` is monotone along refinements.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted`.
-/

open Filter Set
open Poincare.Longrun.PDE
open scoped BigOperators Topology

set_option linter.unusedVariables false

namespace Poincare.D7.Limit

/-! ## The two-sided maximum principle -/

/-- **The negation of a heat evolution** is again a heat evolution: the update
is linear and the zero Dirichlet boundary is preserved. -/
def negEvolution {N : ℕ} {α : ℝ} (ev : HeatGridEvolution N α) : HeatGridEvolution N α where
  u t i := -ev.u t i
  boundary_left t := by rw [ev.boundary_left t]; ring
  boundary_right t := by rw [ev.boundary_right t]; ring
  step t i hi0 hiN := by
    rw [ev.step t i hi0 hiN]
    ring

@[simp]
theorem negEvolution_u {N : ℕ} {α : ℝ} (ev : HeatGridEvolution N α) :
    (negEvolution ev).u = fun t i => -ev.u t i := rfl

/-- **Two-sided discrete maximum principle.**  Under the CFL condition
`0 ≤ α ≤ 1/2`, if the initial slice satisfies `|u 0 i| ≤ M` for `M ≥ 0`, then
every space-time value satisfies `|u t i| ≤ M`.  The upper bound is the D2
maximum principle applied to `ev`; the lower bound is the same principle
applied to `negEvolution ev`. -/
theorem abs_le_of_initial_abs_le {N : ℕ} {α M : ℝ} (ev : HeatGridEvolution N α)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) (hM : 0 ≤ M)
    (hinit : ∀ i ≤ N + 1, |ev.u 0 i| ≤ M) :
    ∀ t i, i ≤ N + 1 → |ev.u t i| ≤ M := by
  intro t i hi
  have hup : ev.u t i ≤ M :=
    ev.le_of_initial_le hα0 hα1 hM (fun j hj => (abs_le.mp (hinit j hj)).2) t i hi
  have hlow : -M ≤ ev.u t i := by
    have h := (negEvolution ev).le_of_initial_le hα0 hα1 hM (fun j hj => by
      have hj' := (abs_le.mp (hinit j hj)).1
      show -ev.u 0 j ≤ M
      linarith) t i hi
    have h' : -ev.u t i ≤ M := by simpa [negEvolution] using h
    linarith
  exact abs_le.mpr ⟨hlow, hup⟩

/-- **Nonpositive form of the discrete maximum principle.**  If the initial
slice is nonpositive, every space-time value is nonpositive; this is the
discrete counterpart of the conclusion of the D2
`ContinuousHeatMaximumPrincipleInterface`. -/
theorem le_zero_of_initial_nonpos {N : ℕ} {α : ℝ} (ev : HeatGridEvolution N α)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) (hinit : ∀ i ≤ N + 1, ev.u 0 i ≤ 0) :
    ∀ t i, i ≤ N + 1 → ev.u t i ≤ 0 :=
  fun t i hi => ev.le_of_initial_le hα0 hα1 le_rfl hinit t i hi

/-! ## Refinement of evolutions -/

/-- **Refinement of evolutions.**  The fine evolution reproduces the coarse
initial datum at every coarse node.  This implies the mesh-refinement relation
`GridMesh.Refines` and records the initial-data compatibility. -/
def RefinesEvolution {a b : ℝ} {N N' : ℕ} {α : ℝ} (coarse : GridMesh a b N)
    (fine : GridMesh a b N') (evc : HeatGridEvolution N α) (evf : HeatGridEvolution N' α) : Prop :=
  ∀ i ≤ N + 1, ∃ j ≤ N' + 1, fine.x j = coarse.x i ∧ evf.u 0 j = evc.u 0 i

/-- Evolution refinement implies mesh refinement. -/
theorem RefinesEvolution.toRefines {a b : ℝ} {N N' : ℕ} {α : ℝ} {coarse : GridMesh a b N}
    {fine : GridMesh a b N'} {evc : HeatGridEvolution N α} {evf : HeatGridEvolution N' α}
    (href : RefinesEvolution coarse fine evc evf) : coarse.Refines fine :=
  fun i hi => by
    obtain ⟨j, hj, hxj, _⟩ := href i hi
    exact ⟨j, hj, hxj⟩

/-- **Refinement raises the initial supremum.**  Every coarse node value appears
among the fine node values, so the coarse initial supremum is at most the fine
initial supremum.  Hence the D2 maximum-principle constant `max 0 (sup initial)`
is monotone along a refinement. -/
theorem RefinesEvolution.sup_initial_le {a b : ℝ} {N N' : ℕ} {α : ℝ} {coarse : GridMesh a b N}
    {fine : GridMesh a b N'} {evc : HeatGridEvolution N α} {evf : HeatGridEvolution N' α}
    (href : RefinesEvolution coarse fine evc evf) :
    Finset.sup' (Finset.range (N + 2)) ⟨0, Finset.mem_range.mpr (by omega)⟩
        (fun i => evc.u 0 i)
      ≤ Finset.sup' (Finset.range (N' + 2)) ⟨0, Finset.mem_range.mpr (by omega)⟩
        (fun j => evf.u 0 j) := by
  refine Finset.sup'_le _ _ (fun i hi => ?_)
  have hi' : i ≤ N + 1 := by
    have := Finset.mem_range.mp hi
    omega
  obtain ⟨j, hj, _, hval⟩ := href i hi'
  rw [← hval]
  exact Finset.le_sup' (fun j => evf.u 0 j) (Finset.mem_range.mpr (by omega))

/-! ## Mesh independence and preservation under refinement -/

/-- **Maximum principle uniform in the mesh.**  If the initial slice is sampled
from a continuous function `f` with `|f x| ≤ M` on `[a,b]` (`M ≥ 0`), then for
*every* mesh on `[a,b]` the whole evolution is bounded by `M`, uniformly in the
number of cells.  This is the mesh-independent form of the discrete maximum
principle. -/
theorem maxPrinciple_uniform_in_mesh {a b : ℝ} {N : ℕ} {α M : ℝ} (ev : HeatGridEvolution N α)
    (G : GridMesh a b N) (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) (hM : 0 ≤ M) {f : ℝ → ℝ}
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M) (hinit : ∀ i ≤ N + 1, ev.u 0 i = f (G.x i)) :
    ∀ t i, i ≤ N + 1 → |ev.u t i| ≤ M := by
  refine abs_le_of_initial_abs_le ev hα0 hα1 hM (fun i hi => ?_)
  rw [hinit i hi]
  exact hf (G.x i) (G.mem_Icc hi)

/-- **The discrete maximum principle is preserved under refinement.**  For a
coarse mesh and a refinement, with both initial slices sampled from the same
continuous datum `f` bounded by `M` on `[a,b]`, the bound `M` holds for the
coarse evolution and for the fine evolution.  The refinement hypothesis records
the intended geometric relation; the bound itself is mesh-independent
(`maxPrinciple_uniform_in_mesh`), which is exactly why it is preserved. -/
theorem maxPrinciple_preserved_under_refinement {a b : ℝ} {N N' : ℕ} {coarse : GridMesh a b N}
    {fine : GridMesh a b N'} {α M : ℝ} (evc : HeatGridEvolution N α)
    (evf : HeatGridEvolution N' α) (href : coarse.Refines fine) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1 / 2) (hM : 0 ≤ M) {f : ℝ → ℝ} (hf : ∀ x ∈ Icc a b, |f x| ≤ M)
    (hinitc : ∀ i ≤ N + 1, evc.u 0 i = f (coarse.x i))
    (hinitf : ∀ j ≤ N' + 1, evf.u 0 j = f (fine.x j)) :
    (∀ t i, i ≤ N + 1 → |evc.u t i| ≤ M) ∧ (∀ t j, j ≤ N' + 1 → |evf.u t j| ≤ M) :=
  ⟨maxPrinciple_uniform_in_mesh evc coarse hα0 hα1 hM hf hinitc,
   maxPrinciple_uniform_in_mesh evf fine hα0 hα1 hM hf hinitf⟩

end Poincare.D7.Limit
