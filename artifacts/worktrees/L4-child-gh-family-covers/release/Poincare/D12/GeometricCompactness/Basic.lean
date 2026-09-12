/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D12-geometric-compactness)
-/
import Mathlib.Topology.MetricSpace.GromovHausdorff

/-!
# Poincare.D12.GeometricCompactness.Basic

Transfer lemmas for Gromov–Hausdorff compactness arguments.

This file develops the metric-space backbone of the converse of Gromov's
compactness criterion, stated in mathlib as
`GromovHausdorff.totallyBounded` (uniform diameter bound + uniform
covering-number bound ⟹ totally bounded in `GHSpace`).  The converse needs
the reverse transfer: if a space `Y` can be covered by `ι`-many δ-balls and
another compact space `X` lies within Gromov–Hausdorff distance `r` of `Y`,
then `X` can be covered by `ι`-many `(2r + δ)`-balls.  The same coupling
argument transfers diameter bounds.

All transfer lemmas are proved by coupling `X` and `Y` in a common metric
space `Z` (for the Gromov–Hausdorff step, mathlib's optimal coupling
`GromovHausdorff.OptimalGHCoupling`, which realizes the distance exactly by
`GromovHausdorff.hausdorffDist_optimal`).  No smooth structure, no gauge
choices, and no curvature data appear anywhere in this file: these lemmas
are purely metric.

## Main declarations

* `cover_transfer_of_hausdorffDist_lt`: coupling-level cover transfer.
* `cover_transfer_of_ghDist`: Gromov–Hausdorff cover transfer.
* `cover_transfer_of_isometry`: cover transfer along an isometry.
* `diam_transfer_of_hausdorffDist_lt`: coupling-level diameter transfer.
* `diam_transfer_of_ghDist`: Gromov–Hausdorff diameter transfer.
* `ghDist_congr_left`, `ghDist_congr_right`: `ghDist` is invariant under
  isometries of either argument.
* `toGHSpace_rep_isometryEquiv`: the canonical representative of
  `toGHSpace X` is isometric to `X`.
-/

open scoped Topology ENNReal Cardinal
open Set Filter Metric
open GromovHausdorff

universe u v w

namespace Poincare.D12.GeometricCompactness

/-- If `X` and `Y` are isometrically embedded in a common metric space with Hausdorff distance
`< r`, and `Y` is covered by `ι`-many `δ`-balls, then `X` is covered by `ι`-many `(2r + δ)`-balls.

The centers in `X` are produced with the axiom of choice (permitted: `Classical.choice`);
compactness of `X` and `Y` is used only to guarantee finiteness of the Hausdorff
edistance through boundedness. -/
theorem cover_transfer_of_hausdorffDist_lt {X : Type u} [MetricSpace X] [CompactSpace X]
    [Nonempty X] {Y : Type u} [MetricSpace Y] [CompactSpace Y] [Nonempty Y] {Z : Type w}
    [MetricSpace Z] {Φ : X → Z} {Ψ : Y → Z} (hΦ : Isometry Φ) (hΨ : Isometry Ψ) {ι : Type u}
    [Fintype ι] {c : ι → Y} {δ r ε : ℝ} (hH : hausdorffDist (range Φ) (range Ψ) < r)
    (hcov : ∀ y : Y, ∃ i : ι, dist y (c i) < δ) (hε : 2 * r + δ < ε) :
    ∃ s : Set X, #s ≤ #ι ∧ univ ⊆ ⋃ x ∈ s, ball x ε := by
  classical
  have hfin : hausdorffEDist (range Φ) (range Ψ) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty _) (range_nonempty _)
      (isCompact_range hΦ.continuous).isBounded (isCompact_range hΨ.continuous).isBounded
  -- For each cover center `c i` of `Y`, choose a point `x i` of `X` whose image in `Z` is
  -- within `r` of `Ψ (c i)` (one-sided Hausdorff bound, in the Ψ → Φ direction).
  let x : ι → X := fun i => Classical.choose (show ∃ x' : X, dist (Ψ (c i)) (Φ x') < r by
    have : ∃ y ∈ range Φ, dist (Ψ (c i)) y < r :=
      exists_dist_lt_of_hausdorffDist_lt (s := range Ψ) (t := range Φ) (h := mem_range_self _)
        (by rwa [hausdorffDist_comm]) (by rwa [hausdorffEDist_comm])
    rcases this with ⟨y, hy, hyr⟩
    rcases mem_range.1 hy with ⟨x', rfl⟩
    exact ⟨x', hyr⟩)
  have hxdist : ∀ i : ι, dist (Ψ (c i)) (Φ (x i)) < r := fun i =>
    Classical.choose_spec (show ∃ x' : X, dist (Ψ (c i)) (Φ x') < r by
      have : ∃ y ∈ range Φ, dist (Ψ (c i)) y < r :=
        exists_dist_lt_of_hausdorffDist_lt (s := range Ψ) (t := range Φ) (h := mem_range_self _)
          (by rwa [hausdorffDist_comm]) (by rwa [hausdorffEDist_comm])
      rcases this with ⟨y, hy, hyr⟩
      rcases mem_range.1 hy with ⟨x', rfl⟩
      exact ⟨x', hyr⟩)
  refine ⟨range x, Cardinal.mk_range_le (f := x), ?_⟩
  intro x₀ hx₀
  -- one-sided Hausdorff bound in the Φ → Ψ direction
  have hw : ∃ y ∈ range Ψ, dist (Φ x₀) y < r :=
    exists_dist_lt_of_hausdorffDist_lt (s := range Φ) (t := range Ψ) (h := mem_range_self _) hH hfin
  rcases hw with ⟨y', hy'mem, hy'dist⟩
  rcases mem_range.1 hy'mem with ⟨y, rfl⟩
  rcases hcov y with ⟨i, hiy⟩
  have hclose : dist x₀ (x i) < ε := by
    calc
      dist x₀ (x i) = dist (Φ x₀) (Φ (x i)) := (Isometry.dist_eq hΦ x₀ (x i)).symm
      _ ≤ dist (Φ x₀) (Ψ y) + dist (Ψ y) (Ψ (c i)) + dist (Ψ (c i)) (Φ (x i)) := by
        have h1 : dist (Φ x₀) (Φ (x i)) ≤ dist (Φ x₀) (Ψ y) + dist (Ψ y) (Φ (x i)) :=
          dist_triangle _ _ _
        have h2 : dist (Ψ y) (Φ (x i)) ≤ dist (Ψ y) (Ψ (c i)) + dist (Ψ (c i)) (Φ (x i)) :=
          dist_triangle _ _ _
        linarith
      _ < r + δ + r :=
        (add_lt_add (add_lt_add hy'dist ((Isometry.dist_eq hΨ y (c i)) ▸ hiy)) (hxdist i))
      _ = 2 * r + δ := by ring
      _ < ε := hε
  exact mem_iUnion₂.2 ⟨x i, mem_range_self _, mem_ball'.2 (by simpa [dist_comm] using hclose)⟩

/-- Cover transfer across a Gromov–Hausdorff bound, via the optimal coupling. -/
theorem cover_transfer_of_ghDist {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
    {Y : Type u} [MetricSpace Y] [CompactSpace Y] [Nonempty Y] {ι : Type u} [Fintype ι]
    {c : ι → Y} {δ r ε : ℝ} (hr : ghDist X Y < r) (hcov : ∀ y : Y, ∃ i : ι, dist y (c i) < δ)
    (hε : 2 * r + δ < ε) :
    ∃ s : Set X, #s ≤ #ι ∧ univ ⊆ ⋃ x ∈ s, ball x ε := by
  have hH : hausdorffDist (range (optimalGHInjl X Y)) (range (optimalGHInjr X Y)) < r := by
    rwa [hausdorffDist_optimal]
  exact cover_transfer_of_hausdorffDist_lt (hΦ := isometry_optimalGHInjl X Y)
    (hΨ := isometry_optimalGHInjr X Y) hH hcov hε

/-- Covers transfer through an isometry: if `Y` is covered by `ι`-many `ε`-balls, so is
any isometric copy `X` (with centers pulled back along the isometry). -/
theorem cover_transfer_of_isometry {X : Type u} [MetricSpace X] {Y : Type u} [MetricSpace Y]
    (e : X ≃ᵢ Y) {ι : Type u} [Fintype ι] {c : ι → Y} {ε : ℝ}
    (hcov : ∀ y : Y, ∃ i : ι, dist y (c i) < ε) :
    ∃ s : Set X, #s ≤ #ι ∧ univ ⊆ ⋃ x ∈ s, ball x ε := by
  classical
  refine ⟨range fun i => e.symm (c i), Cardinal.mk_range_le (f := fun i => e.symm (c i)), ?_⟩
  intro x hx
  rcases hcov (e x) with ⟨i, hi⟩
  refine mem_iUnion₂.2 ⟨e.symm (c i), mem_range_self _, mem_ball'.2 ?_⟩
  calc
    dist (e.symm (c i)) x = dist (c i) (e x) := by
      rw [← e.dist_eq, e.apply_symm_apply]
    _ < ε := by simpa [dist_comm] using hi

/-- If `X` and `Y` are isometrically embedded in a common metric space with Hausdorff distance
`< r`, then a diameter bound for `Y` transfers to one for `X` (up to `2r`). -/
theorem diam_transfer_of_hausdorffDist_lt {X : Type u} [MetricSpace X] [CompactSpace X]
    [Nonempty X] {Y : Type u} [MetricSpace Y] [CompactSpace Y] [Nonempty Y] {Z : Type w}
    [MetricSpace Z] {Φ : X → Z} {Ψ : Y → Z} (hΦ : Isometry Φ) (hΨ : Isometry Ψ) {r D : ℝ}
    (hH : hausdorffDist (range Φ) (range Ψ) < r) (hD : diam (univ : Set Y) ≤ D) :
    diam (univ : Set X) ≤ D + 2 * r := by
  classical
  have hfin : hausdorffEDist (range Φ) (range Ψ) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty _) (range_nonempty _)
      (isCompact_range hΦ.continuous).isBounded (isCompact_range hΨ.continuous).isBounded
  have hr0 : 0 ≤ r := le_of_lt (lt_of_le_of_lt hausdorffDist_nonneg hH)
  have hD0 : 0 ≤ D := le_trans diam_nonneg hD
  refine diam_le_of_forall_dist_le (C := D + 2 * r) ?_ ?_
  · linarith [hD0, hr0]
  · intro x₁ hx₁ x₂ hx₂
    have h1 : ∃ y ∈ range Ψ, dist (Φ x₁) y < r :=
      exists_dist_lt_of_hausdorffDist_lt (s := range Φ) (t := range Ψ) (h := mem_range_self _) hH hfin
    have h2 : ∃ y ∈ range Ψ, dist (Φ x₂) y < r :=
      exists_dist_lt_of_hausdorffDist_lt (s := range Φ) (t := range Ψ) (h := mem_range_self _) hH hfin
    rcases h1 with ⟨z₁, hz₁mem, hz₁⟩
    rcases h2 with ⟨z₂, hz₂mem, hz₂⟩
    rcases mem_range.1 hz₁mem with ⟨y₁, rfl⟩
    rcases mem_range.1 hz₂mem with ⟨y₂, rfl⟩
    have hy₁y₂ : dist (Ψ y₁) (Ψ y₂) ≤ D := by
      calc
        dist (Ψ y₁) (Ψ y₂) = dist y₁ y₂ := Isometry.dist_eq hΨ y₁ y₂
        _ ≤ diam (univ : Set Y) :=
          dist_le_diam_of_mem (isCompact_univ.isBounded : Bornology.IsBounded (univ : Set Y))
            (mem_univ _) (mem_univ _)
        _ ≤ D := hD
    calc
      dist x₁ x₂ = dist (Φ x₁) (Φ x₂) := (Isometry.dist_eq hΦ x₁ x₂).symm
      _ ≤ dist (Φ x₁) (Ψ y₁) + dist (Ψ y₁) (Ψ y₂) + dist (Ψ y₂) (Φ x₂) := by
        have h1' : dist (Φ x₁) (Φ x₂) ≤ dist (Φ x₁) (Ψ y₁) + dist (Ψ y₁) (Φ x₂) :=
          dist_triangle _ _ _
        have h2' : dist (Ψ y₁) (Φ x₂) ≤ dist (Ψ y₁) (Ψ y₂) + dist (Ψ y₂) (Φ x₂) :=
          dist_triangle _ _ _
        linarith
      _ ≤ r + D + r :=
        add_le_add (add_le_add (le_of_lt hz₁) hy₁y₂) (le_of_lt (by simpa [dist_comm] using hz₂))
      _ = D + 2 * r := by ring

/-- Diameter transfer across a Gromov–Hausdorff bound, via the optimal coupling. -/
theorem diam_transfer_of_ghDist {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
    {Y : Type u} [MetricSpace Y] [CompactSpace Y] [Nonempty Y] {r D : ℝ} (hr : ghDist X Y < r)
    (hD : diam (univ : Set Y) ≤ D) : diam (univ : Set X) ≤ D + 2 * r := by
  have hH : hausdorffDist (range (optimalGHInjl X Y)) (range (optimalGHInjr X Y)) < r := by
    rwa [hausdorffDist_optimal]
  exact diam_transfer_of_hausdorffDist_lt (hΦ := isometry_optimalGHInjl X Y)
    (hΨ := isometry_optimalGHInjr X Y) hH hD

/-- `ghDist` is invariant under isometries of the first argument. -/
theorem ghDist_congr_left {X X' : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MetricSpace X'] [CompactSpace X'] [Nonempty X'] {Y : Type u} [MetricSpace Y] [CompactSpace Y]
    [Nonempty Y] (e : X' ≃ᵢ X) : ghDist X' Y = ghDist X Y := by
  rw [ghDist, ghDist, toGHSpace_eq_toGHSpace_iff_isometryEquiv.2 ⟨e⟩]

/-- `ghDist` is invariant under isometries of the second argument. -/
theorem ghDist_congr_right {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X] {Y Y' : Type u}
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y] [MetricSpace Y'] [CompactSpace Y'] [Nonempty Y']
    (e : Y' ≃ᵢ Y) : ghDist X Y' = ghDist X Y := by
  rw [ghDist, ghDist, toGHSpace_eq_toGHSpace_iff_isometryEquiv.2 ⟨e⟩]

/-- The canonical representative `(toGHSpace X).Rep` is isometric to `X`. -/
theorem toGHSpace_rep_isometryEquiv (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] :
    Nonempty ((toGHSpace X).Rep ≃ᵢ X) := by
  let p : GHSpace := toGHSpace X
  have hrep : toGHSpace p.Rep = toGHSpace X := by
    simpa [p] using (GHSpace.toGHSpace_rep p)
  exact toGHSpace_eq_toGHSpace_iff_isometryEquiv.1 hrep

/-- The diameter of `(toGHSpace X).Rep` equals the diameter of `X`. -/
theorem diam_rep_of_toGHSpace (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] :
    diam (univ : Set (toGHSpace X).Rep) = diam (univ : Set X) := by
  classical
  rcases toGHSpace_rep_isometryEquiv X with ⟨e⟩
  rw [← e.isometry.diam_image]
  rw [Set.image_univ, e.surjective.range_eq]

end Poincare.D12.GeometricCompactness
