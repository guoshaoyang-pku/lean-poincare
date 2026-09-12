/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — stability of covering numbers under Gromov–Hausdorff perturbation

The D12 `GeometricCompactness` layer proves Gromov's compactness criterion at the level of
*uniform covers* (`uniformCovers_of_totallyBounded`, `gromovCriterion`,
`gh_subseq_of_familyBounds`).  For the interface to be usable with a quantitative
compactness hypothesis (curvature bounds, non-collapsing, doubling) one needs the covering
numbers themselves to be stable under an arbitrarily small Gromov–Hausdorff perturbation.
This file provides that quantitative statement:

* `coveringNumber_le_of_ghDist_lt` — **general** (proved): if `ghDist X Y < r` and
  `2r + δ < ε` (all radii in the appropriate coercions), then
  `coveringNumber ε (univ : Set X) ≤ coveringNumber δ (univ : Set Y)`.
  The proof consumes D12's `cover_transfer_of_ghDist` with the *minimal* `δ`-cover of `Y`
  produced by mathlib's `exists_set_encard_eq_coveringNumber` (so no cover is assumed), and
  converts the resulting open-ball cover into an `IsCover ε` closed-ball cover.

This is a metric-level interface statement (no curvature, no measure); the missing input for
Cheeger–Gromov remains the implication from curvature bounds and non-collapsing to uniform
covering numbers (`curvatureBoundImpliesUniformCovers`, statement-only in D12).
-/
import Poincare.D12.GeometricCompactness.Criterion
import Mathlib.Topology.MetricSpace.CoveringNumbers

set_option linter.style.haveILetI false

noncomputable section

open Set Metric Filter
open scoped Topology ENNReal NNReal

namespace Poincare.L4.Compactness

open Poincare.D12.GeometricCompactness

/-- **Covering numbers are stable under a Gromov–Hausdorff perturbation.**  If
`ghDist X Y < r` and `2r + δ < ε`, then every `ε`-cover of `X` needs no more balls than a
minimal `δ`-cover of `Y`:
`coveringNumber ε univ_X ≤ coveringNumber δ univ_Y`.

The proof takes the minimal finite `δ`-cover `C` of `Y` (mathlib's
`exists_set_encard_eq_coveringNumber`), turns its closed balls into strict balls of radius
`δ' ∈ (δ, ε − 2r)`, transports along the optimal GH coupling with D12's
`cover_transfer_of_ghDist`, and compares `encard`s. -/
theorem coveringNumber_le_of_ghDist_lt {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
    {Y : Type u} [MetricSpace Y] [CompactSpace Y] [Nonempty Y] {r : ℝ}
    (h : GromovHausdorff.ghDist X Y < r) (δ ε : ℝ≥0)
    (hε : 2 * r + (δ : ℝ) < (ε : ℝ)) :
    Metric.coveringNumber ε (univ : Set X) ≤ Metric.coveringNumber δ (univ : Set Y) := by
  by_cases htop : Metric.coveringNumber δ (univ : Set Y) = ⊤
  · rw [htop]
    exact le_top
  · obtain ⟨C, -, hCfin, hCcover, hCcard⟩ :=
      Metric.exists_set_encard_eq_coveringNumber (A := (univ : Set Y)) htop
    set δ' : ℝ := ((δ : ℝ) + (ε : ℝ) - 2 * r) / 2 with hδ'def
    have hδlt : (δ : ℝ) < δ' := by
      rw [hδ'def]; linarith
    have hε' : 2 * r + δ' < (ε : ℝ) := by
      rw [hδ'def]; linarith
    letI := hCfin.fintype
    have hcov : ∀ y : Y, ∃ i : C, dist y (i : Y) < δ' := by
      intro y
      rcases hCcover (mem_univ y) with ⟨c, hcC, hyc⟩
      have hle : dist y c ≤ (δ : ℝ) := by
        have h' : nndist y c ≤ δ := edist_le_coe.mp (by simpa using hyc)
        exact_mod_cast h'
      exact ⟨⟨c, hcC⟩, lt_of_le_of_lt hle hδlt⟩
    obtain ⟨s, hscard, hcover⟩ :=
      cover_transfer_of_ghDist (X := X) (Y := Y) (ι := C) (c := fun i : C => (i : Y))
        (δ := δ') (r := r) (ε := (ε : ℝ)) h hcov hε'
    have hisCover : Metric.IsCover ε (univ : Set X) s := by
      rw [Metric.isCover_iff_subset_iUnion_closedBall]
      intro x _
      rcases mem_iUnion₂.mp (hcover (mem_univ x)) with ⟨y, hys, hxy⟩
      exact mem_iUnion₂.mpr ⟨y, hys, ball_subset_closedBall hxy⟩
    have h1 : Metric.coveringNumber ε (univ : Set X) ≤ s.encard :=
      Metric.IsCover.coveringNumber_le_encard (subset_univ s) hisCover
    have h2 : s.encard ≤ C.encard := by
      show (Cardinal.mk ↑s).toENat ≤ (Cardinal.mk ↑C).toENat
      exact OrderHomClass.monotone Cardinal.toENat hscard
    rw [hCcard] at h2
    exact h1.trans h2

end Poincare.L4.Compactness
