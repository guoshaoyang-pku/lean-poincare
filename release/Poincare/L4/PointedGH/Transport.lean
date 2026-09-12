/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task L4-child-pointed-gh-transport)
-/
import Poincare.D12.GeometricCompactness.Basic
import Mathlib.Tactic

/-!
# Poincare.L4.PointedGH.Transport

**Point transport across a Gromov–Hausdorff coupling.**

Mathlib's `GromovHausdorff` API is *unpointed*: the Gromov–Hausdorff distance
`ghDist X Y` is the Hausdorff distance of the images of `X` and `Y` in the
optimal coupling `OptimalGHCoupling X Y`, and
`GromovHausdorff.hausdorffDist_optimal` identifies the two.  What the unpointed
API does not provide is the *point-level* content that pointed convergence
needs: given a point `x : X`, a point `y : Y` whose coupled image is close to
that of `x`.

This file supplies exactly that, at the level of arbitrary couplings and at
the level of the optimal coupling:

* `exists_dist_of_hausdorffDist_lt` / `exists_dist_of_hausdorffDist_lt'`:
  coupling-level point transport in both directions (isometric images of two
  compact nonempty metric spaces with Hausdorff distance `< r`).
* `exists_dist_optimalGHInjl_optimalGHInjr_lt`: **the point-transport lemma**
  for the optimal coupling, `∃ y : Y, dist (optimalGHInjl X Y x)
  (optimalGHInjr X Y y) < r` from `ghDist X Y < r`.
* `exists_dist_optimalGHInjr_optimalGHInjl_lt`: the symmetric direction.
* `exists_dist_optimalGHInjl_optimalGHInjr_lt_add`: the `ghDist + ε` form
  (rate form used by the pointed family assembly).
* `exists_dist_optimalGHInjl_optimalGHInjr_le`: the sharp form — the infimum over `y` is
  attained, with the exact bound `ghDist X Y` (no slack).
* `exists_dist_rep_lt_of_dist_lt`: the `GHSpace` form, for the canonical
  representatives `p.Rep`, `q.Rep`.

Everything here is *proved metric-level* content: compact nonempty metric
spaces, no smooth structure, no gauge, no curvature, no pointed convergence
relation assumed anywhere.  The only axioms in the cones are the kernel
trusted `propext`, `Classical.choice`, `Quot.sound`.

## Main declarations

* `exists_dist_of_hausdorffDist_lt`, `exists_dist_of_hausdorffDist_lt'`
* `exists_dist_optimalGHInjl_optimalGHInjr_lt`
* `exists_dist_optimalGHInjr_optimalGHInjl_lt`
* `exists_dist_optimalGHInjl_optimalGHInjr_lt_add`
* `exists_dist_rep_lt_of_dist_lt`
-/

open scoped Topology ENNReal Cardinal
open Set Filter Metric
open GromovHausdorff

universe u v w

namespace Poincare.L4.PointedGH

variable {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
variable {Y : Type v} [MetricSpace Y] [CompactSpace Y] [Nonempty Y]

/-- **Point transport for an arbitrary coupling.**  If isometric copies of the compact nonempty
metric spaces `X` and `Y` in a common metric space `Z` have Hausdorff distance `< r`, then every
point of `X` has a partner in `Y` whose coupled image is within `r`.

This is the point-level refinement of D12's `cover_transfer_of_hausdorffDist_lt`: that lemma
transfers a covering by balls, this one transfers a single point.  It is proved from mathlib's
`exists_dist_lt_of_hausdorffDist_lt`; finiteness of the Hausdorff edistance comes from
compactness of both spaces (`hausdorffEDist_ne_top_of_nonempty_of_bounded`). -/
theorem exists_dist_of_hausdorffDist_lt {Z : Type w} [MetricSpace Z] {Φ : X → Z} {Ψ : Y → Z}
    (hΦ : Isometry Φ) (hΨ : Isometry Ψ) {r : ℝ}
    (hH : hausdorffDist (range Φ) (range Ψ) < r) (x : X) :
    ∃ y : Y, dist (Φ x) (Ψ y) < r := by
  have hfin : hausdorffEDist (range Φ) (range Ψ) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty _) (range_nonempty _)
      (isCompact_range hΦ.continuous).isBounded (isCompact_range hΨ.continuous).isBounded
  rcases exists_dist_lt_of_hausdorffDist_lt (s := range Φ) (t := range Ψ)
      (h := mem_range_self x) hH hfin with ⟨z, hz, hzd⟩
  rcases mem_range.1 hz with ⟨y, rfl⟩
  exact ⟨y, hzd⟩

/-- **Point transport for an arbitrary coupling, other direction.**  Every point of `Y` has a
partner in `X` whose coupled image is within `r`. -/
theorem exists_dist_of_hausdorffDist_lt' {Z : Type w} [MetricSpace Z] {Φ : X → Z} {Ψ : Y → Z}
    (hΦ : Isometry Φ) (hΨ : Isometry Ψ) {r : ℝ}
    (hH : hausdorffDist (range Φ) (range Ψ) < r) (y : Y) :
    ∃ x : X, dist (Φ x) (Ψ y) < r := by
  have hfin : hausdorffEDist (range Φ) (range Ψ) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty _) (range_nonempty _)
      (isCompact_range hΦ.continuous).isBounded (isCompact_range hΨ.continuous).isBounded
  rcases exists_dist_lt_of_hausdorffDist_lt' (s := range Φ) (t := range Ψ)
      (h := mem_range_self y) hH hfin with ⟨z, hz, hzd⟩
  rcases mem_range.1 hz with ⟨x, rfl⟩
  exact ⟨x, hzd⟩

/-- **The coupling-space point-transport lemma.**  For compact nonempty metric spaces `X`, `Y`
with `ghDist X Y < r`, every point `x : X` has a partner `y : Y` whose image under the optimal
coupling is within `r` of the image of `x`:

`∃ y : Y, dist (optimalGHInjl X Y x) (optimalGHInjr X Y y) < r`.

The proof rewrites `ghDist` as the Hausdorff distance of the ranges of the optimal coupling
(`GromovHausdorff.hausdorffDist_optimal`) and applies the coupling-level transport lemma.  This
is the exact metric-level input that pointed Gromov–Hausdorff convergence needs in order to
compare basepoints, and it is *proved* here, not assumed. -/
theorem exists_dist_optimalGHInjl_optimalGHInjr_lt {r : ℝ} (hr : ghDist X Y < r) (x : X) :
    ∃ y : Y, dist (optimalGHInjl X Y x) (optimalGHInjr X Y y) < r := by
  refine exists_dist_of_hausdorffDist_lt (X := X) (Y := Y)
    (isometry_optimalGHInjl X Y) (isometry_optimalGHInjr X Y) ?_ x
  rwa [hausdorffDist_optimal]

/-- **The coupling-space point-transport lemma, other direction.**  For compact nonempty metric
spaces `X`, `Y` with `ghDist X Y < r`, every point `y : Y` has a partner `x : X` whose image
under the optimal coupling is within `r` of the image of `y`. -/
theorem exists_dist_optimalGHInjr_optimalGHInjl_lt {r : ℝ} (hr : ghDist X Y < r) (y : Y) :
    ∃ x : X, dist (optimalGHInjl X Y x) (optimalGHInjr X Y y) < r := by
  refine exists_dist_of_hausdorffDist_lt' (X := X) (Y := Y)
    (isometry_optimalGHInjl X Y) (isometry_optimalGHInjr X Y) ?_ y
  rwa [hausdorffDist_optimal]

/-- **Rate form of the point-transport lemma.**  For every `ε > 0` and every `x : X` there is
`y : Y` with `dist (optimalGHInjl X Y x) (optimalGHInjr X Y y) < ghDist X Y + ε`.  This is the
form used to build the pointed-coupling structure: the transport error is bounded by the
(unpointed) Gromov–Hausdorff rate plus a vanishing slack. -/
theorem exists_dist_optimalGHInjl_optimalGHInjr_lt_add {ε : ℝ} (hε : 0 < ε) (x : X) :
    ∃ y : Y, dist (optimalGHInjl X Y x) (optimalGHInjr X Y y) < ghDist X Y + ε :=
  exists_dist_optimalGHInjl_optimalGHInjr_lt (lt_add_of_pos_right _ hε) x

/-- **Point transport at the level of `GHSpace`.**  If `p q : GHSpace` satisfy `dist p q < r`,
then every point of the canonical representative `p.Rep` has a partner in `q.Rep` whose image in
the optimal coupling of the representatives is within `r`.  This is the form consumed by the
pointed family assembly, where limits are produced by D12's subsequence theorems as abstract
points of `GHSpace`. -/
theorem exists_dist_rep_lt_of_dist_lt {p q : GHSpace} {r : ℝ} (h : dist p q < r) (x : p.Rep) :
    ∃ y : q.Rep, dist (optimalGHInjl p.Rep q.Rep x) (optimalGHInjr p.Rep q.Rep y) < r := by
  refine exists_dist_optimalGHInjl_optimalGHInjr_lt ?_ x
  rwa [← dist_ghDist]

/-- **Point transport at the level of `GHSpace`, other direction.** -/
theorem exists_dist_rep_lt_of_dist_lt' {p q : GHSpace} {r : ℝ} (h : dist p q < r) (y : q.Rep) :
    ∃ x : p.Rep, dist (optimalGHInjl p.Rep q.Rep x) (optimalGHInjr p.Rep q.Rep y) < r := by
  refine exists_dist_optimalGHInjr_optimalGHInjl_lt ?_ y
  rwa [← dist_ghDist]

/-- **Sharp form of the point-transport lemma: the infimum is attained.**  For compact nonempty
metric spaces `X`, `Y` and `x : X` there is `y : Y` whose coupled image is at distance *at most*
`ghDist X Y` from that of `x` (no slack).  The `Y`-dependent infimum implicit in the Hausdorff
distance is attained because `Y` is compact: transport with rates `ghDist X Y + 1/(n+1)`, use
compactness of the range of `optimalGHInjr X Y` to extract a convergent subsequence, and pass to
the limit. -/
theorem exists_dist_optimalGHInjl_optimalGHInjr_le (x : X) :
    ∃ y : Y, dist (optimalGHInjl X Y x) (optimalGHInjr X Y y) ≤ ghDist X Y := by
  classical
  choose y hy using fun n : ℕ =>
    exists_dist_optimalGHInjl_optimalGHInjr_lt (X := X) (Y := Y)
      (r := ghDist X Y + 1 / ((n : ℝ) + 1)) (lt_add_of_pos_right _ (by positivity)) x
  obtain ⟨z, hz, ψ, hψ, hzconv⟩ :=
    IsCompact.tendsto_subseq
      (isCompact_range (isometry_optimalGHInjr X Y).continuous)
      (fun n => mem_range_self (y n))
  rcases mem_range.1 hz with ⟨y₀, rfl⟩
  refine ⟨y₀, ?_⟩
  have hdist : Tendsto (fun k => dist (optimalGHInjl X Y x) (optimalGHInjr X Y (y (ψ k))))
      atTop (𝓝 (dist (optimalGHInjl X Y x) (optimalGHInjr X Y y₀))) :=
    tendsto_const_nhds.dist hzconv
  have hbound : Tendsto (fun k => ghDist X Y + 1 / (((ψ k : ℕ) : ℝ) + 1)) atTop
      (𝓝 (ghDist X Y + 0)) :=
    tendsto_const_nhds.add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hψ.tendsto_atTop)
  have hle : ∀ k, dist (optimalGHInjl X Y x) (optimalGHInjr X Y (y (ψ k))) ≤
      ghDist X Y + 1 / (((ψ k : ℕ) : ℝ) + 1) := fun k => le_of_lt (hy (ψ k))
  have := le_of_tendsto_of_tendsto' hdist hbound hle
  simpa using this

end Poincare.L4.PointedGH
