/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-gh-compactness)

**D7 Gromov–Hausdorff / Cheeger–Gromov compactness, part 1: pointed metric families,
`GHConvergenceData` and the precompactness certificate.**

This file fixes the two interfaces of the task.

* `PointedMetricSpace` is a pointed pseudo-metric space: an underlying type with a
  pseudo-metric and a distinguished basepoint.  Pseudo-metrics are used because none of the
  metric-space results below distinguishes points at distance zero; the intended case is of
  course a genuine metric space.

* `GHConvergenceData l X Y` is **pointed Gromov–Hausdorff convergence data** in the
  ε-approximation form (Gromov 1981; Petersen, *Riemannian Geometry*, §10.3.2): a family of
  maps `approx i : X i → Y` which are almost isometric with distortion `ε i`, almost
  surjective, and move basepoints by at most `ε i`, with `ε i → 0` along the filter `l`.
  The definition is index-generic (`ι` and a filter `l`), so it covers sequences
  (`l = atTop`), nets, and one-step approximations.

* `GHPrecompactCertificate X` is a **precompactness certificate** for a family of pointed
  metric spaces: a uniform, explicitly enumerated finite ε-net of the `R`-ball about the
  basepoint of every member (`net`, `net_card_le`, `base_mem_net`, `net_covers`) together
  with completeness of every member.  These are exactly the two hypotheses of Gromov's
  pointed precompactness theorem; the certificate never asserts that a limit exists.

Checked content of this file: distortion bounds, basepoint convergence, reflexivity,
monotonicity in the approximation scale and in the filter, and composition of two
ε-approximations (the triangle bookkeeping `ε₁ + 2 ε₂`).

The total-boundedness consequences of the certificate fields are in
`Poincare.D7.Compactness.TotalBounded`; the toy compactness theorem for finite families is
in `Poincare.D7.Compactness.ToyCompactness`; the state-only Cheeger–Gromov statements are in
`Poincare.D7.Compactness.ManifoldStatements`.

Every unproved input is an explicit structure field or hypothesis; there is no unproved
hole, no extra logical postulate, no kernel bypass, no native evaluation and no statement
stub in this file.
-/

import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Order.Filter.Ultrafilter.Basic

open Filter Set Topology
open scoped Topology

namespace Poincare
namespace D7
namespace Compactness

universe u v

noncomputable section

/-! ## 1. Pointed metric spaces -/

/-- **A pointed pseudo-metric space.**  The underlying type `M`, a pseudo-metric on it, and a
distinguished basepoint `base`.  The pseudo-metric generality is harmless for the compactness
interface: all statements below concern distances and never identify points. -/
structure PointedMetricSpace where
  /-- The underlying type. -/
  M : Type u
  /-- The pseudo-metric structure. -/
  inst : PseudoMetricSpace M
  /-- The basepoint. -/
  base : M

attribute [instance] PointedMetricSpace.inst

instance : CoeSort PointedMetricSpace (Type u) := ⟨PointedMetricSpace.M⟩

namespace PointedMetricSpace

/-- **The one-point pointed space.**  The basepoint is the unique point of `PUnit`; this is
the non-vacuity model for every structure and theorem of the development.  It is an `abbrev`
so that instance search can see that its underlying type is `PUnit`. -/
abbrev unit : PointedMetricSpace where
  M := PUnit
  inst := inferInstance
  base := PUnit.unit

@[simp]
theorem unit_base : unit.base = PUnit.unit := rfl

end PointedMetricSpace

/-! ## 2. Pointed Gromov–Hausdorff convergence data -/

/-- **Pointed Gromov–Hausdorff convergence data.**  `GHConvergenceData l X Y` records that
the pointed spaces `X i` converge to the pointed space `Y` along the filter `l`, in the
ε-approximation sense:

* `ε i` is the approximation error at index `i`, nonnegative and tending to `0` along `l`;
* `approx i : X i → Y` is an ε-isometry: the distortion
  `|dist (approx i x) (approx i y) - dist x y|` is at most `ε i`;
* `approx i` is `ε i`-surjective onto `Y`;
* `approx i` moves the basepoint by at most `ε i`.

This is the standard definition of pointed GH convergence by ε-isometries.  The fields are
data, not axioms: any use of a datum is an explicit hypothesis of the theorem that consumes
it. -/
structure GHConvergenceData {ι : Type v} (l : Filter ι) (X : ι → PointedMetricSpace)
    (Y : PointedMetricSpace) where
  /-- The approximation error scale. -/
  ε : ι → ℝ
  /-- The error scale is nonnegative. -/
  ε_nonneg : ∀ i, 0 ≤ ε i
  /-- The error scale tends to zero along `l`. -/
  ε_tendsto : Tendsto ε l (𝓝 0)
  /-- The almost isometric approximation maps. -/
  approx : ∀ i, X i → Y
  /-- The distortion bound defining an ε-isometry. -/
  distortion : ∀ i (x y : X i),
    |dist (approx i x) (approx i y) - dist x y| ≤ ε i
  /-- Almost surjectivity of the approximation maps. -/
  surjective : ∀ i (y : Y), ∃ x : X i, dist y (approx i x) ≤ ε i
  /-- The approximation maps move basepoints by at most the error scale. -/
  base_dist : ∀ i, dist (approx i (X i).base) Y.base ≤ ε i

namespace GHConvergenceData

variable {ι : Type v} {l : Filter ι} {X : ι → PointedMetricSpace} {Y : PointedMetricSpace}
variable {Z : PointedMetricSpace}

/-- **Upper distortion bound.**  The distances of images are at most the original distances
plus the error scale. -/
theorem dist_approx_le (D : GHConvergenceData l X Y) (i : ι) (x y : X i) :
    dist (D.approx i x) (D.approx i y) ≤ dist x y + D.ε i := by
  have h := (abs_le.mp (D.distortion i x y)).2
  linarith

/-- **Lower distortion bound.**  The original distances are at most the distances of images
plus the error scale. -/
theorem dist_le_dist_approx (D : GHConvergenceData l X Y) (i : ι) (x y : X i) :
    dist x y ≤ dist (D.approx i x) (D.approx i y) + D.ε i := by
  have h := (abs_le.mp (D.distortion i x y)).1
  linarith

/-- The distortion tends to zero along the filter, uniformly over the family. -/
theorem tendsto_abs_distortion (D : GHConvergenceData l X Y) (x y : ∀ i, X i) :
    Tendsto (fun i => |dist (D.approx i (x i)) (D.approx i (y i)) - dist (x i) (y i)|)
      l (𝓝 0) :=
  squeeze_zero (fun _ => abs_nonneg _) (fun i => D.distortion i (x i) (y i)) D.ε_tendsto

/-- **Basepoint convergence.**  The distances between the approximated basepoints and the
basepoint of the limit tend to zero. -/
theorem tendsto_base_dist (D : GHConvergenceData l X Y) :
    Tendsto (fun i => dist (D.approx i (X i).base) Y.base) l (𝓝 0) :=
  squeeze_zero (fun _ => dist_nonneg) (fun i => D.base_dist i) D.ε_tendsto

/-- **Basepoint convergence, point form.**  The approximated basepoints converge to the
basepoint of the limit. -/
theorem tendsto_approx_base (D : GHConvergenceData l X Y) :
    Tendsto (fun i => D.approx i (X i).base) l (𝓝 Y.base) := by
  rw [tendsto_iff_dist_tendsto_zero]
  exact D.tendsto_base_dist

/-- **Reflexivity.**  Every pointed space GH-converges to itself along any filter, with the
identity approximation maps and zero error.  This is the checked identity case of the toy
compactness theorem. -/
def refl (l : Filter ι) (X : PointedMetricSpace) :
    GHConvergenceData l (fun _ : ι => X) X where
  ε := fun _ => 0
  ε_nonneg := fun _ => le_refl 0
  ε_tendsto := tendsto_const_nhds
  approx := fun _ x => x
  distortion := by
    intro i x y
    simp
  surjective := by
    intro i y
    exact ⟨y, by simp⟩
  base_dist := by
    intro i
    simp

/-- **Monotonicity in the error scale.**  Enlarging the error scale pointwise (while keeping
it nonnegative and convergent to zero) preserves GH convergence data. -/
def mono (D : GHConvergenceData l X Y) (δ : ι → ℝ) (hδ : ∀ i, D.ε i ≤ δ i)
    (hδ0 : ∀ i, 0 ≤ δ i) (hδt : Tendsto δ l (𝓝 0)) : GHConvergenceData l X Y where
  ε := δ
  ε_nonneg := hδ0
  ε_tendsto := hδt
  approx := D.approx
  distortion := fun i x y => le_trans (D.distortion i x y) (hδ i)
  surjective := by
    intro i y
    obtain ⟨x, hx⟩ := D.surjective i y
    exact ⟨x, le_trans hx (hδ i)⟩
  base_dist := fun i => le_trans (D.base_dist i) (hδ i)

/-- **Monotonicity in the filter.**  GH convergence along `l` implies GH convergence along
any coarser filter `l' ≤ l`. -/
def monoFilter {l' : Filter ι} (D : GHConvergenceData l X Y) (h : l' ≤ l) :
    GHConvergenceData l' X Y where
  ε := D.ε
  ε_nonneg := D.ε_nonneg
  ε_tendsto := D.ε_tendsto.mono_left h
  approx := D.approx
  distortion := D.distortion
  surjective := D.surjective
  base_dist := D.base_dist

/-- **Composition of GH convergence data.**  Two ε-approximations compose to an
`(ε₁ + 2 ε₂)`-approximation: the factor `2` accounts for the second distortion bound being
used once for surjectivity and once for the basepoint.  This makes pointed GH convergence
transitive in the limit. -/
def comp (D₂ : GHConvergenceData l (fun _ : ι => Y) Z) (D₁ : GHConvergenceData l X Y) :
    GHConvergenceData l X Z where
  ε := fun i => D₁.ε i + 2 * D₂.ε i
  ε_nonneg := by
    intro i
    have h₁ := D₁.ε_nonneg i
    have h₂ := D₂.ε_nonneg i
    linarith
  ε_tendsto := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    have h₁ : ∀ᶠ i in l, D₁.ε i < δ / 2 := by
      have h := (Metric.tendsto_nhds.mp D₁.ε_tendsto) (δ / 2) (by linarith)
      filter_upwards [h] with i hi
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (D₁.ε_nonneg i)] at hi
    have h₂ : ∀ᶠ i in l, D₂.ε i < δ / 4 := by
      have h := (Metric.tendsto_nhds.mp D₂.ε_tendsto) (δ / 4) (by linarith)
      filter_upwards [h] with i hi
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (D₂.ε_nonneg i)] at hi
    filter_upwards [h₁, h₂] with i hi1 hi2
    have h0 : 0 ≤ D₁.ε i + 2 * D₂.ε i := by
      have := D₁.ε_nonneg i
      have := D₂.ε_nonneg i
      linarith
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
    linarith
  approx := fun i x => D₂.approx i (D₁.approx i x)
  distortion := by
    intro i x y
    have h₁ : dist x y ≤ dist (D₁.approx i x) (D₁.approx i y) + D₁.ε i :=
      D₁.dist_le_dist_approx i x y
    have h₂ : dist (D₁.approx i x) (D₁.approx i y) ≤ dist x y + D₁.ε i :=
      D₁.dist_approx_le i x y
    have h₂' : dist (D₂.approx i (D₁.approx i x)) (D₂.approx i (D₁.approx i y))
        ≤ dist (D₁.approx i x) (D₁.approx i y) + D₂.ε i :=
      D₂.dist_approx_le i _ _
    have h₂'' : dist (D₁.approx i x) (D₁.approx i y)
        ≤ dist (D₂.approx i (D₁.approx i x)) (D₂.approx i (D₁.approx i y)) + D₂.ε i :=
      D₂.dist_le_dist_approx i _ _
    rw [abs_le]
    constructor <;> linarith
  surjective := by
    intro i z
    obtain ⟨y, hy⟩ := D₂.surjective i z
    obtain ⟨x, hx⟩ := D₁.surjective i y
    refine ⟨x, ?_⟩
    have h₂ := D₂.dist_approx_le i y (D₁.approx i x)
    calc dist z (D₂.approx i (D₁.approx i x))
        ≤ dist z (D₂.approx i y) + dist (D₂.approx i y) (D₂.approx i (D₁.approx i x)) :=
          dist_triangle _ _ _
      _ ≤ D₂.ε i + (dist y (D₁.approx i x) + D₂.ε i) := by linarith
      _ ≤ D₂.ε i + (D₁.ε i + D₂.ε i) := by linarith
      _ = D₁.ε i + 2 * D₂.ε i := by ring
  base_dist := by
    intro i
    have h₁ : dist (D₁.approx i (X i).base) Y.base ≤ D₁.ε i := D₁.base_dist i
    have h₂ : dist (D₂.approx i (D₁.approx i (X i).base))
        (D₂.approx i (Y.base)) ≤ dist (D₁.approx i (X i).base) Y.base + D₂.ε i :=
      D₂.dist_approx_le i _ _
    have h₃ : dist (D₂.approx i (Y.base)) Z.base ≤ D₂.ε i := D₂.base_dist i
    calc dist (D₂.approx i (D₁.approx i (X i).base)) Z.base
        ≤ dist (D₂.approx i (D₁.approx i (X i).base)) (D₂.approx i (Y.base))
            + dist (D₂.approx i (Y.base)) Z.base := dist_triangle _ _ _
      _ ≤ (dist (D₁.approx i (X i).base) Y.base + D₂.ε i) + D₂.ε i := by linarith
      _ ≤ (D₁.ε i + D₂.ε i) + D₂.ε i := by linarith
      _ = D₁.ε i + 2 * D₂.ε i := by ring

end GHConvergenceData

/-! ## 3. The precompactness certificate -/

/-- **Pointed GH precompactness certificate.**  A family `X : ι → PointedMetricSpace` is
uniformly totally bounded on basepoint balls, and every member is complete.

* `netBound R ε` is the uniform bound on the cardinality of an `ε`-net of the `R`-ball;
* `net i R ε` is the *explicit* `ε`-net of the `R`-ball about the basepoint of `X i`,
  containing the basepoint;
* `net_covers` is the covering property.

This is the hypothesis side of Gromov's pointed precompactness theorem.  The certificate is
a structure of data and hypotheses, never an assertion that a limit exists; the extraction
of a convergent subsequence from it is a state-only statement in
`Poincare.D7.Compactness.ManifoldStatements`. -/
structure GHPrecompactCertificate {ι : Type v} (X : ι → PointedMetricSpace) where
  /-- The uniform cardinality bound for `ε`-nets of `R`-balls. -/
  netBound : ℝ → ℝ → ℕ
  /-- The explicit `ε`-nets. -/
  net : ∀ i, ℝ → ℝ → Finset (X i)
  /-- The nets obey the uniform cardinality bound. -/
  net_card_le : ∀ i R ε, (net i R ε).card ≤ netBound R ε
  /-- Every net contains the basepoint. -/
  base_mem_net : ∀ i R ε, (X i).base ∈ net i R ε
  /-- The nets cover the basepoint ball. -/
  net_covers : ∀ i R ε, 0 < ε → ∀ x : X i, dist x (X i).base ≤ R →
    ∃ y ∈ net i R ε, dist x y < ε
  /-- Every member of the family is complete. -/
  complete : ∀ i, CompleteSpace (X i)

namespace GHPrecompactCertificate

variable {ι : Type v} {X : ι → PointedMetricSpace}

/-- The certificate packaged as a single explicit finite-net statement. -/
theorem exists_net (C : GHPrecompactCertificate X) (i : ι) (R ε : ℝ) (hε : 0 < ε) :
    ∃ t : Finset (X i), t.card ≤ C.netBound R ε ∧ (X i).base ∈ t ∧
      ∀ x : X i, dist x (X i).base ≤ R → ∃ y ∈ t, dist x y < ε :=
  ⟨C.net i R ε, C.net_card_le i R ε, C.base_mem_net i R ε,
    fun x hx => C.net_covers i R ε hε x hx⟩

/-- **Weakening the cardinality bound.**  A certificate with bound `netBound` yields one with
any pointwise larger bound. -/
def monoBound (C : GHPrecompactCertificate X) (N' : ℝ → ℝ → ℕ)
    (hN : ∀ R ε, C.netBound R ε ≤ N' R ε) : GHPrecompactCertificate X where
  netBound := N'
  net := C.net
  net_card_le := fun i R ε => le_trans (C.net_card_le i R ε) (hN R ε)
  base_mem_net := C.base_mem_net
  net_covers := C.net_covers
  complete := C.complete

/-- **The certificate for a constant family of a finite pointed space.**  The explicit
enumeration is `Finset.univ`, with cardinality bound `Fintype.card`. -/
def const (X : PointedMetricSpace) [Fintype X] (ι : Type v) :
    GHPrecompactCertificate (fun _ : ι => X) where
  netBound := fun _ _ => Fintype.card X
  net := fun _ _ _ => Finset.univ
  net_card_le := fun _ _ _ => le_rfl
  base_mem_net := fun _ _ _ => Finset.mem_univ _
  net_covers := by
    intro i R ε hε x _
    exact ⟨x, Finset.mem_univ x, by simpa using hε⟩
  complete := fun _ => inferInstance

end GHPrecompactCertificate

/-! ## 4. Finite pseudo-metric spaces are complete -/

/-- **Finite uniform spaces are complete.**  Every ultrafilter on a finite type is principal,
and a principal ultrafilter converges to its point; hence every Cauchy ultrafilter converges
and the space is complete.  This instance is what makes the precompactness certificate of a
finite family discharge its completeness field. -/
instance finiteCompleteSpace {α : Type u} [Finite α] [UniformSpace α] : CompleteSpace α := by
  rw [completeSpace_iff_ultrafilter]
  intro l _hl
  obtain ⟨a, rfl⟩ := Ultrafilter.eq_pure_of_finite l
  exact ⟨a, pure_le_nhds a⟩

end

end Compactness
end D7
end Poincare
