/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-gh-compactness)

**D7 Gromov–Hausdorff compactness, part 2: total-boundedness consequences of the
precompactness certificate.**

This file discharges the metric content of the precompactness certificate of
`Poincare.D7.Compactness.Basic`.  From the certificate fields alone — the uniform finite
`ε`-nets of basepoint balls and completeness of every member — it derives:

* the explicit uniform finite-net statement (`uniform_finite_net`);
* total boundedness of every basepoint ball (`totallyBounded_closedBall`), hence of every
  open ball;
* compactness of every basepoint ball (`isCompact_closedBall`), by completeness plus total
  boundedness;
* compactness of *every* closed ball (`isCompact_closedBall_any`), because a ball about an
  arbitrary centre is contained in a basepoint ball of radius `r + dist x p`, and hence
  `ProperSpace` for every member (`properSpace`);
* total boundedness and compactness of the whole space under an explicit uniform diameter
  bound (`totallyBounded_univ_of_bounded`, `compactSpace_of_bounded`).

These are the "total-boundedness consequences of the certificate fields" required by the
task.  No limit space is constructed here; the extraction of a convergent subsequence from
the certificate is a state-only statement in
`Poincare.D7.Compactness.ManifoldStatements`.

There is no unproved hole, no extra logical postulate, no kernel bypass, no native
evaluation and no statement stub in this file.
-/

import Poincare.D7.Compactness.Basic

open Filter Set Topology
open scoped Topology

namespace Poincare
namespace D7
namespace Compactness

universe u v

noncomputable section

namespace GHPrecompactCertificate

variable {ι : Type v} {X : ι → PointedMetricSpace}

/-- The covering number of the basepoint `R`-ball at scale `ε` supplied by the
certificate. -/
def coveringNumber (C : GHPrecompactCertificate X) (R ε : ℝ) : ℕ :=
  C.netBound R ε

/-- The explicit net obeys the covering-number bound. -/
theorem card_net_le_coveringNumber (C : GHPrecompactCertificate X) (i : ι) (R ε : ℝ) :
    (C.net i R ε).card ≤ C.coveringNumber R ε :=
  C.net_card_le i R ε

/-- Every net is nonempty, because it contains the basepoint. -/
theorem net_nonempty (C : GHPrecompactCertificate X) (i : ι) (R ε : ℝ) :
    (C.net i R ε).Nonempty :=
  ⟨(X i).base, C.base_mem_net i R ε⟩

/-- **Uniform finite-net consequence.**  A single cardinality bound `N` works for all
members of the family: for every `i` there is an `ε`-net of the basepoint `R`-ball of `X i`
with at most `N` points. -/
theorem uniform_finite_net (C : GHPrecompactCertificate X) (R ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ i : ι, ∃ t : Finset (X i), t.card ≤ N ∧
      ∀ x : X i, dist x (X i).base ≤ R → ∃ y ∈ t, dist x y < ε :=
  ⟨C.netBound R ε, fun i =>
    ⟨C.net i R ε, C.net_card_le i R ε, fun x hx => C.net_covers i R ε hε x hx⟩⟩

/-- **Total-boundedness consequence (basepoint balls).**  Every basepoint `R`-ball is
totally bounded, with the explicit finite nets supplied by the certificate. -/
theorem totallyBounded_closedBall (C : GHPrecompactCertificate X) (i : ι) (R : ℝ) :
    TotallyBounded (Metric.closedBall (X i).base R) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  refine ⟨(C.net i R ε : Set (X i)), (C.net i R ε).finite_toSet, ?_⟩
  intro x hx
  rw [Metric.mem_closedBall] at hx
  obtain ⟨y, hy, hxy⟩ := C.net_covers i R ε hε x hx
  exact Set.mem_iUnion₂.mpr ⟨y, hy, by rw [Metric.mem_ball]; exact hxy⟩

/-- **Total-boundedness consequence (open balls).**  Every open basepoint ball is totally
bounded. -/
theorem totallyBounded_ball (C : GHPrecompactCertificate X) (i : ι) (R : ℝ) :
    TotallyBounded (Metric.ball (X i).base R) :=
  (C.totallyBounded_closedBall i R).subset Metric.ball_subset_closedBall

/-- **Compactness consequence (basepoint balls).**  Completeness plus total boundedness of
the basepoint ball makes it compact. -/
theorem isCompact_closedBall (C : GHPrecompactCertificate X) (i : ι) (R : ℝ) :
    IsCompact (Metric.closedBall (X i).base R) := by
  have := C.complete i
  exact isCompact_iff_totallyBounded_isComplete.mpr
    ⟨C.totallyBounded_closedBall i R, Metric.isClosed_closedBall.isComplete⟩

/-- **Compactness consequence (arbitrary closed balls).**  A closed ball about an arbitrary
centre is contained in the basepoint ball of radius `r + dist x p`, hence compact.  This is
the precise reason the certificate yields a proper space rather than only properness at the
basepoint. -/
theorem isCompact_closedBall_any (C : GHPrecompactCertificate X) (i : ι) (x : X i)
    (r : ℝ) : IsCompact (Metric.closedBall x r) := by
  refine IsCompact.of_isClosed_subset (C.isCompact_closedBall i (r + dist x (X i).base))
    Metric.isClosed_closedBall ?_
  intro y hy
  rw [Metric.mem_closedBall] at hy ⊢
  calc dist y (X i).base ≤ dist y x + dist x (X i).base := dist_triangle _ _ _
    _ ≤ r + dist x (X i).base := by linarith

/-- **Properness consequence.**  Every member of a certified family is a proper metric
space: all closed balls are compact. -/
theorem properSpace (C : GHPrecompactCertificate X) (i : ι) : ProperSpace (X i) :=
  ⟨fun x r => C.isCompact_closedBall_any i x r⟩

/-- **Total-boundedness consequence (whole space).**  Under an explicit uniform diameter
bound `D`, the whole space is totally bounded. -/
theorem totallyBounded_univ_of_bounded (C : GHPrecompactCertificate X) {D : ℝ}
    (hD : ∀ i (x : X i), dist x (X i).base ≤ D) (i : ι) :
    TotallyBounded (Set.univ : Set (X i)) :=
  (C.totallyBounded_closedBall i D).subset fun x _ => by
    rw [Metric.mem_closedBall]
    exact hD i x

/-- **Compactness consequence (whole space).**  Under an explicit uniform diameter bound,
every member is a compact metric space. -/
theorem compactSpace_of_bounded (C : GHPrecompactCertificate X) {D : ℝ}
    (hD : ∀ i (x : X i), dist x (X i).base ≤ D) (i : ι) : CompactSpace (X i) := by
  have := C.complete i
  rw [← isCompact_univ_iff]
  exact isCompact_iff_totallyBounded_isComplete.mpr
    ⟨C.totallyBounded_univ_of_bounded hD i, isComplete_univ⟩

/-- Totally bounded basepoint balls are in particular bounded. -/
theorem isBounded_closedBall (C : GHPrecompactCertificate X) (i : ι) (R : ℝ) :
    Bornology.IsBounded (Metric.closedBall (X i).base R) :=
  (C.totallyBounded_closedBall i R).isBounded

end GHPrecompactCertificate

end

end Compactness
end D7
end Poincare
