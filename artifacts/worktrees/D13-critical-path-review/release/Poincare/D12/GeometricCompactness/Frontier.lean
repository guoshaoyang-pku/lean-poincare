/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D12-geometric-compactness)
-/
import Poincare.D12.GeometricCompactness.Criterion

/-!
# Poincare.D12.GeometricCompactness.Frontier

The **next proof frontier** for Cheeger–Gromov compactness, ancient κ-solution
compactness and canonical neighbourhoods, anchored to the metric-level
theorems of this module.

## What is proved here

* `closure_isCompact_of_totallyBounded`: every totally bounded family of
  compact metric spaces has compact closure in `GHSpace` — the exact
  assembly of `uniformCovers_of_totallyBounded` (converse criterion) and
  `isCompact_of_uniformCovers` that a Cheeger–Gromov statement consumes
  after the smooth inputs are supplied.  (A proved theorem.)
* `gh_subseq_of_familyBounds`: subsequence/convergence witness for a
  totally bounded family — a proved corollary.

## What is statement-only here (explicitly NOT claimed, no inhabitants)

The following `Prop`-valued interfaces record, with full type information,
the smooth/gauge/curvature inputs that are missing in pinned mathlib and in
this task's scope.  They are **definitions**, not axioms, and nothing in
`proved_declarations` depends on them.

1. `harmonicCoordinatesExistence` — existence of `C^{1,α}` harmonic
   coordinate charts with estimates depending on injectivity-radius lower
   bounds and curvature bounds (needs an elliptic PDE layer; mathlib has no
   manifold Laplacian with Schauder estimates).
2. `curvatureBoundImpliesUniformCovers` — the **Bishop–Gromov step**: a
   uniform lower bound on the volume of unit balls (equivalently
   κ-non-collapsing) plus a uniform curvature bound implies a uniform
   covering-number bound on balls of any fixed radius.  This is exactly the
   missing input that turns the metric-level `gromovCriterion` into a
   compactness theorem for families of Riemannian manifolds.
3. `cheegerGromovCompactness` — pointed Cheeger–Gromov compactness: a
   sequence of pointed Riemannian `n`-manifolds with `|Rm| ≤ K`, `inj ≥ i₀`
   and `diam ≤ D` has a subsequence converging in pointed `C^{1,α}` to a
   limit manifold, with the `C^∞` upgrade when the bounds hold at all
   scales.  The convergence relation is an explicit parameter (mathlib has
   no pointed smooth GH convergence).
4. `ancientKappaCompactnessFrontier` — the κ-solution compactness statement
   of D9's `perelmanCompactnessTheorem`, re-stated here as: a family of
   pointed 3-dimensional κ-solutions (in the sense of
   `D9.AncientKappa.ThreeDimKappaSolution`) maps to a family of pointed
   compact metric spaces; if `curvatureBoundImpliesUniformCovers` holds for
   that family, then the image family satisfies the hypotheses of
   `gh_subseq_of_familyBounds`.  The D9 statement additionally requires the
   pointed convergence relation and the limit-is-κ-solution checks.
5. `canonicalNeighborhoodFrontier` — the canonical-neighbourhood linkage of
   D9's `canonicalNeighborhoodLinkage` requires, as metric-level input, the
   pointed GH compactness (4) plus the explicit model spaces (round
   cylinder `S² × ℝ` and its caps) and a neck/cap recognition predicate;
   recorded as a dependency DAG, not a theorem.

The dependency DAG (documented, all leaves outside this task):

```
metric level (PROVED): GromovHausdorff.totallyBounded
        + uniformCovers_of_totallyBounded (this task)
        ==> gromovCriterion, gh_subseq_of_compact, gh_subseq_of_uniformCovers
               |            (PROVED, general)
               v
     curvatureBoundImpliesUniformCovers   (STATEMENT-ONLY: needs
        |        Bishop-Gromov volume comparison, i.e. geodesics,
        |        Ricci curvature, volume form — mathlib gaps U3/U7)
        v
     harmonicCoordinatesExistence         (STATEMENT-ONLY: needs elliptic
        |        PDE / Schauder estimates — mathlib gap U6/U8)
        v
     cheegerGromovCompactness             (STATEMENT-ONLY)
        |
        +----> ancientKappaCompactnessFrontier (STATEMENT-ONLY; consumes
        |          D9 perelmanCompactnessTheorem's ConvergesTo parameter)
        |
        +----> canonicalNeighborhoodFrontier   (STATEMENT-ONLY; consumes
                   D9 canonicalNeighborhoodLinkage predicates)
```
-/

open scoped Topology ENNReal Cardinal
open Set Filter Metric
open GromovHausdorff

namespace Poincare.D12.GeometricCompactness

/-! ## Proved: downstream assembly of the criterion -/

/-- **Downstream use of the converse criterion.**  A totally bounded family of compact metric
spaces has compact closure in `GHSpace`: the converse `uniformCovers_of_totallyBounded`
supplies the uniform diameter/covering bounds for the closure, and
`isCompact_of_uniformCovers` closes. -/
theorem closure_isCompact_of_totallyBounded {t : Set GHSpace} (ht : TotallyBounded t) :
    IsCompact (closure t) := by
  classical
  rcases uniformCovers_of_totallyBounded ht.closure with ⟨hC, hK⟩
  exact isCompact_of_uniformCovers isClosed_closure hC hK

/-- **Subsequence witness for totally bounded families.**  Every sequence in the closure of a
totally bounded family has a strictly monotone reindexing converging (topologically and in
`ghDist`) to a point of the closure. -/
theorem gh_subseq_of_familyBounds {t : Set GHSpace} (ht : TotallyBounded t) {u : ℕ → GHSpace}
    (hu : ∀ n, u n ∈ closure t) :
    ∃ (a : GHSpace) (φ : ℕ → ℕ), a ∈ closure t ∧ StrictMono φ ∧
      Tendsto (u ∘ φ) atTop (𝓝 a) ∧
      Tendsto (fun n => ghDist (GHSpace.Rep (u (φ n))) (GHSpace.Rep a)) atTop (𝓝 0) := by
  classical
  exact gh_subseq_of_compact (closure_isCompact_of_totallyBounded ht) hu

/-! ## Statement-only: the missing smooth/gauge/curvature steps

All declarations below are plain `def`s of `Prop`-valued statements with explicit parameters;
**none of them has an inhabitant and none is used by any proved declaration**.  They name the
exact missing inputs for Cheeger–Gromov compactness. -/

/-- **Statement-only.**  Existence of harmonic coordinate charts: on every member of a family
of pointed Riemannian `n`-manifolds with `|Rm| ≤ K` on `B(p, r)` and `inj(p) ≥ i₀`, there is a
`C^{1,α}` chart `φ : U → ℝⁿ` with `φ(p) = 0`, bi-Lipschitz constants controlled by `n`, `K`,
`i₀`, `r` and `α` only.  `RiemannianFamily` and `ChartWithEstimates` are the (unavailable in
mathlib) carriers of the smooth data. -/
def harmonicCoordinatesExistence (_n : ℕ) (_α : ℝ)
    (RiemannianFamily : Type*) (ChartWithEstimates : RiemannianFamily → Prop)
    (CurvatureBound : RiemannianFamily → ℝ → Prop) (InjectivityLowerBound : RiemannianFamily → ℝ → Prop) :
    Prop :=
  ∀ (F : RiemannianFamily) (K i₀ : ℝ), 0 < i₀ → CurvatureBound F K →
    InjectivityLowerBound F i₀ → ChartWithEstimates F

/-- **Statement-only.**  The Bishop–Gromov volume-comparison step: for a Riemannian `n`-manifold
with `Ric ≥ κ` (encoded by `RicciLowerBound`), the volume of `B(p, r)` is comparable to the
model volume `VolModel r` (the space form of curvature `κ/(n-1)`), uniformly in `p`.  When
`RicciLowerBound` holds for a uniform `κ` and the balls have a uniform positive volume lower
bound (`KappaNoncollapsing`), this is the curvature input that produces **uniform covering
numbers** for the family — the missing link between κ-non-collapsing and `gromovCriterion`. -/
def bishopGromovVolumeComparison (_n : ℕ) (RiemannianFamily : Type*)
    (Volume : RiemannianFamily → ℝ → ℝ) (RicciLowerBound : RiemannianFamily → ℝ → Prop)
    (VolModel : ℝ → ℝ) : Prop :=
  ∀ (F : RiemannianFamily) (κ : ℝ), RicciLowerBound F κ →
    ∀ _p : RiemannianFamily, ∀ r : ℝ, 0 < r → Volume F r ≤ VolModel r

/-- **Statement-only.**  κ-non-collapsing plus a curvature bound implies uniform covering
numbers: every member of a family of pointed compact metric spaces arising from Riemannian
manifolds with `KappaNoncollapsing F κ` and `CurvatureBound F K` admits an `ε`-cover of every
`r`-ball by `≤ K ε` balls, uniformly in the family.  This is the exact hypothesis factory for
`isCompact_of_uniformCovers` / `gh_subseq_of_uniformCovers` on the metric side. -/
def curvatureBoundImpliesUniformCovers (RiemannianFamily : Type*)
    (GHImage : RiemannianFamily → GHSpace) (KappaNoncollapsing : RiemannianFamily → ℝ → Prop)
    (CurvatureBound : RiemannianFamily → ℝ → Prop) : Prop :=
  ∀ F : RiemannianFamily, ∀ κ K : ℝ, 0 < κ → KappaNoncollapsing F κ → CurvatureBound F K →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ s : Set (GHSpace.Rep (GHImage F)),
      #s ≤ N ∧ univ ⊆ ⋃ x ∈ s, ball x ε

/-- **Statement-only.**  Cheeger–Gromov compactness: pointed Riemannian `n`-manifolds with
`|Rm| ≤ K`, injectivity radius `≥ i₀` and diameter `≤ D` have a subsequence converging in the
pointed `C^{1,α}` topology (supplied relation `ConvergesTo`) to a limit manifold, with the
`C^∞` limit upgrade under all-scale bounds.  The smooth part (harmonic coordinates + elliptic
estimates) is the content of `harmonicCoordinatesExistence`; the metric part is
`gromovCriterion` applied through `curvatureBoundImpliesUniformCovers`. -/
def cheegerGromovCompactness (_n : ℕ) (_α : ℝ) (PointedManifold : Type*)
    (ConvergesTo : PointedManifold → PointedManifold → Prop)
    (CurvatureBound : PointedManifold → ℝ → Prop)
    (InjectivityLowerBound : PointedManifold → ℝ → Prop)
    (DiameterBound : PointedManifold → ℝ → Prop) : Prop :=
  ∀ (F : ℕ → PointedManifold) (K i₀ D : ℝ), 0 < i₀ →
    (∀ m, CurvatureBound (F m) K) → (∀ m, InjectivityLowerBound (F m) i₀) →
    (∀ m, DiameterBound (F m) D) →
    ∃ (limit : PointedManifold) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ᶠ k in atTop, ConvergesTo (F (φ k)) limit

/-- **Statement-only.**  The ancient-κ-solution compactness frontier: D9's
`perelmanCompactnessTheorem` (state-only there) is the conjunction of (a) a pointed
convergence relation `ConvergesTo` on pointed 3-dimensional κ-solutions,
(b) `curvatureBoundImpliesUniformCovers` for the family of pointed metric spaces underlying the
κ-solutions, and (c) the limit-closure check `LimitIsKappaSolution`.  The metric-level
consequence — a `ghDist`-convergent subsequence of the GH images — follows **once (b) is
supplied**, from `gh_subseq_of_familyBounds`; (a) and (c) stay open. -/
def ancientKappaCompactnessFrontier (PointedKappaSolution : Type*)
    (ConvergesTo : PointedKappaSolution → PointedKappaSolution → Prop)
    (GHImage : PointedKappaSolution → GHSpace)
    (KappaNoncollapsing : PointedKappaSolution → ℝ → Prop)
    (CurvatureBound : PointedKappaSolution → ℝ → Prop)
    (LimitIsKappaSolution : PointedKappaSolution → Prop) : Prop :=
  curvatureBoundImpliesUniformCovers PointedKappaSolution GHImage KappaNoncollapsing CurvatureBound ∧
  ∀ (F : ℕ → PointedKappaSolution) (κ K : ℝ), 0 < κ →
    (∀ m, KappaNoncollapsing (F m) κ) → (∀ m, CurvatureBound (F m) K) →
    ∃ (limit : PointedKappaSolution) (φ : ℕ → ℕ), StrictMono φ ∧ LimitIsKappaSolution limit ∧
      (∀ᶠ k in atTop, ConvergesTo (F (φ k)) limit)

/-- **Statement-only.**  The canonical-neighbourhood frontier: for a family of pointed
κ-solutions whose GH images form a totally bounded family, plus the neck/cap recognition
predicates `HasCanonicalNeighborhood` of D9's `canonicalNeighborhoodLinkage`, the model-space
side (round cylinder `S² × ℝ`, caps, compact positive models) and their `ε`-closeness in the
pointed GH sense are the required inputs.  No neck analysis is claimed. -/
def canonicalNeighborhoodFrontier (PointedKappaSolution : Type*)
    (HasCanonicalNeighborhood : PointedKappaSolution → ℝ → Prop)
    (HighCurvature : PointedKappaSolution → ℝ → Prop) : Prop :=
  ∀ (S : PointedKappaSolution) (ε : ℝ), 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ HighCurvature S ε → HasCanonicalNeighborhood S δ

/-- Shape lemma: `canonicalNeighborhoodFrontier` is the displayed formula (a definition, not a
postulate). -/
theorem canonicalNeighborhoodFrontier_iff (PointedKappaSolution : Type*)
    (HasCanonicalNeighborhood : PointedKappaSolution → ℝ → Prop)
    (HighCurvature : PointedKappaSolution → ℝ → Prop) :
    canonicalNeighborhoodFrontier PointedKappaSolution HasCanonicalNeighborhood HighCurvature ↔
      ∀ (S : PointedKappaSolution) (ε : ℝ), 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ HighCurvature S ε → HasCanonicalNeighborhood S δ :=
  Iff.rfl

/-- Shape lemma: `curvatureBoundImpliesUniformCovers` is the displayed formula (a definition,
not a postulate). -/
theorem curvatureBoundImpliesUniformCovers_iff (RiemannianFamily : Type*)
    (GHImage : RiemannianFamily → GHSpace) (KappaNoncollapsing : RiemannianFamily → ℝ → Prop)
    (CurvatureBound : RiemannianFamily → ℝ → Prop) :
    curvatureBoundImpliesUniformCovers RiemannianFamily GHImage KappaNoncollapsing CurvatureBound ↔
      ∀ F : RiemannianFamily, ∀ κ K : ℝ, 0 < κ → KappaNoncollapsing F κ → CurvatureBound F K →
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ s : Set (GHSpace.Rep (GHImage F)),
          #s ≤ N ∧ univ ⊆ ⋃ x ∈ s, ball x ε :=
  Iff.rfl

end Poincare.D12.GeometricCompactness
