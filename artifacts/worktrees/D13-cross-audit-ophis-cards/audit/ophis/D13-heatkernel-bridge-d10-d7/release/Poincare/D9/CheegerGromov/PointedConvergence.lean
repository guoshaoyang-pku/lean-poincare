import Mathlib
import Poincare.Stage1.RiemannAdapter

/-!
# Poincare.D9.CheegerGromov.PointedConvergence

**D9 / Cheeger–Gromov compactness: the pointed `C^k` convergence interface.**

This module is part of the `D9-cheeger-gromov-compactness` task and consumes the accepted release
manifold layer `Poincare.Stage1.RiemannAdapter` (the `PointwiseCurvature` /
`RiemannianCurvatureData` interface) without modifying it.

## What this file provides

* `PointedManifold E H I` — a pointed Riemannian manifold over the release's manifold layer: a type
  `M` with a `ChartedSpace H M`, a `C^∞` manifold structure, a `ContMDiffRiemannianMetric`
  (mathlib's smooth metric bundle API, as used by the D6 release), a basepoint, and the associated
  *intrinsic distance* `dist` (an explicit interface field: the pinned mathlib revision
  `7974e751bece493b6ff508039423ca9fa2452fa8` constructs no Riemannian distance function, so it is
  carried as data with the metric axioms, exactly in the release's "explicit interface" style).
* `PointedManifold.metricBall`, `PointedManifold.HasCompactMetricBalls`,
  `PointedManifold.IsCompleteMetric` — the pointed metric neighbourhoods used by pointed
  convergence, and the completeness / compact-ball hypotheses that Cheeger–Gromov compactness needs.
* `CompactExhaustion X` — an exhaustion of `X` by compact sets `K n` with
  `K n ⊆ interior (K (n+1))` and `⋃ n, K n = univ`, plus the checked lemma
  `CompactExhaustion.exists_subset`: **every compact subset of `X` is contained in
  some exhaustion stage** (finite-subcover argument, fully proved).
* `pullbackMetric X Y φ` — the pullback of the metric of `Y` along `φ`, as a family of continuous
  bilinear forms on the model space, and `PointedManifold.metricDiffCoeff`, its coordinate
  difference with the metric of `X` in a chart.
* `PointedManifold.CkCloseOnChart k e K ε g'` — `C^k`-closeness, in a chart `e`, of a bilinear-form
  family `g'` to the metric of `X` on `K`: all chart-coordinate derivatives of order `≤ k` of the
  component difference are bounded by `ε` (through `iteratedFDerivWithin`).
* `CkCloseAtScale k R ε X Y` — the pointed `C^k`-closeness datum at scale `R`: a smooth pointed
  embedding `φ : X.M → Y.M` (smooth, a topological embedding, an immersion) sending basepoints to
  basepoints, together with `C^{k+1}`-closeness of the pulled-back metric `φ^* g_Y` to `g_X` on the
  pointed ball of radius `R` in `X`.
* `CkConvergence k X Y` — the interface for a sequence `X : ℕ → PointedManifold E H I` converging to
  a pointed limit `Y` in the pointed `C^k` sense: a compact exhaustion of the limit, smooth
  embeddings `φ n : Y.M → (X n).M` of the limit into the approximants (basepoint preserving), and
  `C^{k+1}`-closeness of the pulled-back metrics on the exhausted compact pieces with tolerances
  `ε n → 0`.
* `CkConvergesTo k X Y` — the `Prop`-valued version over **real** scales (`∀ R ≥ 0, ∀ ε > 0`,
  eventually `ε`-close at scale `R`), its natural-scale companion `CkConvergesToNat` and the checked
  equivalence `ckConvergesTo_nat_iff` (integral scales suffice, by monotonicity of pointed closeness
  in the scale), and the checked implication `CkConvergence.convergesTo` showing the interface
  refines the `Prop` (under the compact-ball hypothesis on the limit).
* `ckCloseAtScale_self`, `ckCloseAtScaleProp_self`, `ckConvergesTo_const` — **non-vacuity witnesses**:
  the identity embedding is `0`-close at every scale on which the pointed ball lies in the basepoint
  chart, and the constant sequence `X, X, …` converges to `X` in the pointed `C^k` sense.

## Honest boundary

Nothing here asserts the Cheeger–Gromov compactness theorem: the geometric bounds are hypotheses of
the *state-only* Props in `Poincare.D9.CheegerGromov.CheegerGromov`.  The `dist` data is an honest
interface field; the four metric axioms (diagonal, symmetry, nonnegativity, triangle inequality) are
required, but nothing here requires `dist` to be positive-definite or to induce the manifold
topology, and no theorem of this file claims that `dist` is the Riemannian distance (that
construction is absent from the pinned mathlib revision).  All proofs are complete: no `sorry`,
`axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open Bundle Filter
open scoped Manifold ContDiff Topology Bundle

namespace Poincare
namespace D9
namespace CheegerGromov

universe uE uH uM

noncomputable section

set_option synthInstance.maxHeartbeats 400000

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- **Pointed Riemannian manifold** over the release's manifold layer: a smooth manifold `M`
modelled on `(E, H, I)` carrying a `C^∞` Riemannian metric `metric`, a basepoint, and an explicit
intrinsic distance `dist` (an interface field with the metric axioms). -/
structure PointedManifold (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) where
  /-- The underlying manifold. -/
  M : Type uM
  [topologicalSpace : TopologicalSpace M]
  [chartedSpace : ChartedSpace H M]
  [isManifold : IsManifold I ∞ M]
  /-- The smooth Riemannian metric (mathlib's `ContMDiffRiemannianMetric`). -/
  metric : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type uE)
  /-- The pointed basepoint. -/
  basepoint : M
  /-- The intrinsic distance, as an explicit interface field.  In the intended model this is the
  Riemannian distance; the pinned mathlib revision constructs no such function, so the field is
  data, constrained by the metric axioms below. -/
  dist : M → M → ℝ
  /-- The distance is zero on the diagonal. -/
  dist_self : ∀ x, dist x x = 0
  /-- The distance is symmetric. -/
  dist_comm : ∀ x y, dist x y = dist y x
  /-- The distance is nonnegative. -/
  dist_nonneg : ∀ x y, 0 ≤ dist x y
  /-- The triangle inequality. -/
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z

attribute [instance] PointedManifold.topologicalSpace PointedManifold.chartedSpace
  PointedManifold.isManifold

namespace PointedManifold

variable (X : PointedManifold E H I)

/-- The closed pointed ball of radius `R` around the basepoint, defined through the intrinsic
distance field. -/
def metricBall (R : ℝ) : Set X.M := {y | X.dist X.basepoint y ≤ R}

/-- The basepoint lies in every ball of nonnegative radius. -/
theorem basepoint_mem_metricBall {R : ℝ} (hR : 0 ≤ R) : X.basepoint ∈ X.metricBall R := by
  simpa [metricBall, X.dist_self] using hR

/-- Balls are monotone in the radius. -/
theorem metricBall_mono {R R' : ℝ} (h : R ≤ R') : X.metricBall R ⊆ X.metricBall R' :=
  fun _ hy => le_trans hy h

/-- **Compact balls**: every pointed ball is compact.  For a complete Riemannian manifold this is
Hopf–Rinow; here it is an explicit hypothesis, as in the state-only compactness Props. -/
def HasCompactMetricBalls : Prop := ∀ R : ℝ, IsCompact (X.metricBall R)

/-- **Metric completeness** of the intrinsic distance: every Cauchy sequence (in the `ε`-`N`
formulation) converges to a point, expressed through `dist`. -/
def IsCompleteMetric : Prop :=
  ∀ u : ℕ → X.M, (∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, X.dist (u m) (u n) ≤ ε) →
    ∃ x : X.M, Tendsto (fun n => X.dist (u n) x) atTop (𝓝 0)

end PointedManifold

/-- **Exhaustion by compact sets**: a sequence of compact sets `K n` with `K n ⊆ interior (K (n+1))`
whose union is everything.  This is the exhaustion used in the pointed convergence interface. -/
structure CompactExhaustion (X : PointedManifold E H I) where
  /-- The compact pieces. -/
  K : ℕ → Set X.M
  /-- Each piece is compact. -/
  isCompact_K : ∀ n, IsCompact (K n)
  /-- Each piece contains the basepoint. -/
  basepoint_mem : ∀ n, X.basepoint ∈ K n
  /-- The exhaustion is monotone. -/
  monotone_K : Monotone K
  /-- Each piece is contained in the interior of the next. -/
  subset_interior_succ : ∀ n, K n ⊆ interior (K (n + 1))
  /-- The pieces exhaust the manifold. -/
  iUnion_K : (⋃ n, K n) = Set.univ

namespace CompactExhaustion

variable {X : PointedManifold E H I} (E : CompactExhaustion X)

/-- Consecutive exhaustion stages. -/
theorem subset_succ (n : ℕ) : E.K n ⊆ E.K (n + 1) :=
  E.monotone_K (Nat.le_succ n)

/-- Every exhaustion stage is contained in all later stages. -/
theorem subset_of_le {m n : ℕ} (h : m ≤ n) : E.K m ⊆ E.K n :=
  E.monotone_K h

/-- **Every compact subset of `X` is contained in some exhaustion stage.**  The interiors of the
exhaustion stages cover `X` (by `K n ⊆ interior (K (n+1))` and `⋃ n, K n = univ`), hence cover the
compact set `s`; a finite subcover and monotonicity of the exhaustion bound the finitely many
indices by their supremum. -/
theorem exists_subset {s : Set X.M} (hs : IsCompact s) : ∃ n : ℕ, s ⊆ E.K n := by
  classical
  have hcover : s ⊆ ⋃ n : ℕ, interior (E.K (n + 1)) := by
    intro x hx
    have hx' : x ∈ ⋃ n : ℕ, E.K n := by
      rw [E.iUnion_K]
      trivial
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx'
    exact Set.mem_iUnion.mpr ⟨n, E.subset_interior_succ n hn⟩
  obtain ⟨t, ht⟩ :=
    hs.elim_finite_subcover (fun n : ℕ => interior (E.K (n + 1)))
      (fun n => isOpen_interior) hcover
  refine ⟨t.sup (fun n => n + 1), fun x hx => ?_⟩
  obtain ⟨n, hnt, hn⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact E.monotone_K (Finset.le_sup hnt) (interior_subset hn)

end CompactExhaustion

/-! ## Pullback metrics and `C^k`-closeness in a chart -/

/-- The pullback of the metric of `Y` along `φ : X.M → Y.M`, as a family of continuous bilinear
forms on the model space `E`: `x ↦ (v, w) ↦ ⟨dφ_x v, dφ_x w⟩_{Y, φ x}`. -/
noncomputable def pullbackMetric (X : PointedManifold E H I) (Y : PointedManifold E H I)
    (φ : X.M → Y.M) : X.M → E →L[ℝ] E →L[ℝ] ℝ :=
  fun x => ((Y.metric.inner (φ x)).comp (mfderiv I I φ x)).comp (mfderiv I I φ x)

/-- The pullback of the metric along the identity is the metric itself (the composite of the
metric's inner product with `mfderiv I I id x` is the inner product). -/
theorem pullbackMetric_id (X : PointedManifold E H I) :
    pullbackMetric X X id = X.metric.inner := by
  funext x
  ext v w
  simp only [pullbackMetric, mfderiv_id]
  rfl

namespace PointedManifold

variable (X : PointedManifold E H I)

/-- The coordinate components, in a chart `e : PartialEquiv X.M E`, of the difference between a
bilinear-form family `g'` and the metric of `X`. -/
noncomputable def metricDiffCoeff (e : PartialEquiv X.M E)
    (g' : X.M → E →L[ℝ] E →L[ℝ] ℝ) (v w : E) : E → ℝ :=
  fun z => g' (e.symm z) v w - X.metric.inner (e.symm z) v w

/-- The metric difference of the pulled-back metric along the identity vanishes identically: the
component functions are `g - g = 0`.  This is the checked content of the non-vacuity witness
`ckCloseAtScale_self` below. -/
theorem metricDiffCoeff_id (e : PartialEquiv X.M E) (v w : E) :
    X.metricDiffCoeff e (pullbackMetric X X id) v w = fun _ => (0 : ℝ) := by
  funext z
  simp only [metricDiffCoeff, pullbackMetric_id]
  exact sub_self _

/-- **`C^k`-closeness in a chart.**  The bilinear-form family `g'` is `ε`-close to the metric of `X`
in `C^k` on `K` with respect to the chart `e`: for every order `i ≤ k`, every pair of model vectors
`v w`, and every chart point `y` in the image of `K`, the `i`-th iterated derivative (within the
chart target) of the component difference is bounded by `ε` in operator norm. -/
def CkCloseOnChart (k : ℕ) (e : PartialEquiv X.M E) (K : Set X.M) (ε : ℝ)
    (g' : X.M → E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  ∀ i ≤ k, ∀ v w : E, ∀ y ∈ e.target ∩ e '' K,
    ‖iteratedFDerivWithin ℝ i (X.metricDiffCoeff e g' v w) e.target y‖ ≤ ε

/-- `C^k`-closeness in a chart is monotone in the tolerance. -/
theorem CkCloseOnChart.mono {k : ℕ} {e : PartialEquiv X.M E} {K : Set X.M} {ε ε' : ℝ}
    {g' : X.M → E →L[ℝ] E →L[ℝ] ℝ} (hε : ε ≤ ε') (h : X.CkCloseOnChart k e K ε g') :
    X.CkCloseOnChart k e K ε' g' :=
  fun i hi v w y hy => le_trans (h i hi v w y hy) hε

/-- `C^k`-closeness in a chart is monotone in the order. -/
theorem CkCloseOnChart.mono_order {k k' : ℕ} {e : PartialEquiv X.M E} {K : Set X.M} {ε : ℝ}
    {g' : X.M → E →L[ℝ] E →L[ℝ] ℝ} (hk : k' ≤ k) (h : X.CkCloseOnChart k e K ε g') :
    X.CkCloseOnChart k' e K ε g' :=
  fun i hi v w y hy => h i (le_trans hi hk) v w y hy

/-- `C^k`-closeness in a chart is monotone in the set. -/
theorem CkCloseOnChart.mono_set {k : ℕ} {e : PartialEquiv X.M E} {K K' : Set X.M} {ε : ℝ}
    {g' : X.M → E →L[ℝ] E →L[ℝ] ℝ} (hKK' : K' ⊆ K) (h : X.CkCloseOnChart k e K ε g') :
    X.CkCloseOnChart k e K' ε g' :=
  fun i hi v w y hy => h i hi v w y ⟨hy.1, Set.image_mono hKK' hy.2⟩

end PointedManifold

/-! ## The pointed `C^k`-closeness datum at scale `R` -/

/-- **Pointed `C^k`-closeness at scale `R`.**  A pointed smooth embedding `emb : X.M → Y.M` (smooth,
a topological embedding, an immersion) sending the basepoint of `X` to the basepoint of `Y`, whose
pulled-back metric `emb^* g_Y` is `C^{k+1}`-close to `g_X` with tolerance `ε` on the pointed ball of
radius `R` in `X`, measured in the extended chart at the basepoint.

The `C^{k+1}` order is the task's requirement: the metric tensor is compared through order `k+1`,
which is the standard amount of control needed for the geometry to converge through order `k`
(curvature is of second order in the metric). -/
structure CkCloseAtScale (k : ℕ) (R ε : ℝ) (X Y : PointedManifold E H I) where
  /-- The pointed ball of radius `R` is contained in the chart at the basepoint. -/
  ball_subset_chart : X.metricBall R ⊆ (extChartAt I X.basepoint).source
  /-- The pointed embedding, from the model manifold into the approximant. -/
  emb : X.M → Y.M
  /-- Smoothness of the embedding. -/
  contMDiff_emb : ContMDiff I I ∞ emb
  /-- The embedding is a topological embedding. -/
  isEmbedding_emb : Topology.IsEmbedding emb
  /-- The embedding is an immersion at every point. -/
  isImmersion_emb : ∀ x : X.M, Manifold.IsImmersionAt I I ∞ emb x
  /-- The embedding preserves basepoints. -/
  maps_basepoint : emb X.basepoint = Y.basepoint
  /-- `C^{k+1}`-closeness of the pulled-back metric to the metric of `X` on the pointed ball. -/
  metric_close : X.CkCloseOnChart (k + 1) (extChartAt I X.basepoint) (X.metricBall R) ε
    (pullbackMetric X Y emb)

namespace CkCloseAtScale

variable {k : ℕ} {R R' ε ε' : ℝ} {X Y : PointedManifold E H I}

/-- Pointed closeness at scale is monotone in the tolerance. -/
def mono (hε : ε ≤ ε') (h : CkCloseAtScale k R ε X Y) :
    CkCloseAtScale k R ε' X Y where
  ball_subset_chart := h.ball_subset_chart
  emb := h.emb
  contMDiff_emb := h.contMDiff_emb
  isEmbedding_emb := h.isEmbedding_emb
  isImmersion_emb := h.isImmersion_emb
  maps_basepoint := h.maps_basepoint
  metric_close := PointedManifold.CkCloseOnChart.mono X hε h.metric_close

/-- Pointed closeness at scale is monotone in the scale. -/
def mono_scale (hR : R' ≤ R) (h : CkCloseAtScale k R ε X Y) :
    CkCloseAtScale k R' ε X Y where
  ball_subset_chart := fun _ hy =>
    h.ball_subset_chart (PointedManifold.metricBall_mono X hR hy)
  emb := h.emb
  contMDiff_emb := h.contMDiff_emb
  isEmbedding_emb := h.isEmbedding_emb
  isImmersion_emb := h.isImmersion_emb
  maps_basepoint := h.maps_basepoint
  metric_close := PointedManifold.CkCloseOnChart.mono_set X
    (PointedManifold.metricBall_mono X hR) h.metric_close

/-- Pointed closeness at scale is monotone in the convergence order. -/
def mono_order {k k' : ℕ} (hk : k' ≤ k) (h : CkCloseAtScale k R ε X Y) :
    CkCloseAtScale k' R ε X Y where
  ball_subset_chart := h.ball_subset_chart
  emb := h.emb
  contMDiff_emb := h.contMDiff_emb
  isEmbedding_emb := h.isEmbedding_emb
  isImmersion_emb := h.isImmersion_emb
  maps_basepoint := h.maps_basepoint
  metric_close := PointedManifold.CkCloseOnChart.mono_order X (Nat.succ_le_succ hk) h.metric_close

end CkCloseAtScale

/-- The `Prop`-valued pointed `C^k`-closeness at scale. -/
def CkCloseAtScaleProp (k : ℕ) (R ε : ℝ) (X Y : PointedManifold E H I) : Prop :=
  Nonempty (CkCloseAtScale k R ε X Y)

/-- **Non-vacuity witness for pointed closeness.**  If the pointed ball of radius `R` lies in the
chart at the basepoint of `X`, then `X` is `0`-close to itself at scale `R` through the identity
embedding: the pulled-back metric is the metric itself (`metricDiffCoeff_id`).  So the
`CkCloseAtScale` interface is satisfiable (it is not a vacuous structure). -/
noncomputable def ckCloseAtScale_self (k : ℕ) (X : PointedManifold E H I) {R : ℝ}
    (hball : X.metricBall R ⊆ (extChartAt I X.basepoint).source) :
    CkCloseAtScale k R 0 X X where
  ball_subset_chart := hball
  emb := id
  contMDiff_emb := contMDiff_id
  isEmbedding_emb := Topology.IsEmbedding.id
  isImmersion_emb := fun x =>
    ⟨PUnit, inferInstance, inferInstance,
      Manifold.IsImmersionOfComplement.id (I := I) (n := ∞) (M := X.M) x⟩
  maps_basepoint := rfl
  metric_close := by
    intro i _hi v w _y _hy
    have hzero : X.metricDiffCoeff (extChartAt I X.basepoint) (pullbackMetric X X id) v w
        = fun _ => (0 : ℝ) := PointedManifold.metricDiffCoeff_id X _ v w
    rw [hzero]
    rcases i with _ | i
    · simp
    · simp [iteratedFDerivWithin_const_of_ne (Nat.succ_ne_zero i)]

/-- The `Prop`-valued form of the self-closeness witness. -/
theorem ckCloseAtScaleProp_self (k : ℕ) (X : PointedManifold E H I) {R : ℝ}
    (hball : X.metricBall R ⊆ (extChartAt I X.basepoint).source) :
    CkCloseAtScaleProp k R 0 X X :=
  ⟨ckCloseAtScale_self k X hball⟩

/-- **Pointed `C^k` convergence to a limit** (the `Prop`-valued form).  For every scale `R ≥ 0` and
every tolerance `ε > 0`, the *limit* `Y` is eventually `ε`-close at scale `R` to the approximants
`X n`: eventually there is a pointed smooth embedding `Y.M → (X n).M` whose pulled-back metric is
`C^{k+1}`-close to `g_Y` on the pointed ball of radius `R` in `Y`. -/
def CkConvergesTo (k : ℕ) (X : ℕ → PointedManifold E H I) (Y : PointedManifold E H I) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, CkCloseAtScaleProp k R ε Y (X n)

/-- The natural-scale form of pointed `C^k` convergence: it suffices to test the integral scales
`R = 0, 1, 2, …`.  `CkConvergesTo.toNat` and `CkConvergesToNat.toReal` below show that the two forms
are equivalent, so the choice of scale indexing is immaterial. -/
def CkConvergesToNat (k : ℕ) (X : ℕ → PointedManifold E H I) (Y : PointedManifold E H I) : Prop :=
  ∀ R : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, CkCloseAtScaleProp k (R : ℝ) ε Y (X n)

/-- The real-scale form implies the natural-scale form. -/
theorem CkConvergesTo.toNat {k : ℕ} {X : ℕ → PointedManifold E H I} {Y : PointedManifold E H I}
    (h : CkConvergesTo k X Y) : CkConvergesToNat k X Y :=
  fun R ε hε => h R (Nat.cast_nonneg R) ε hε

/-- The natural-scale form implies the real-scale form: test the integral scale `⌈R⌉ ≥ R`
(`Nat.le_ceil`) and use monotonicity of pointed closeness in the scale (`CkCloseAtScale.mono_scale`).
So quantifying over integral scales loses nothing. -/
theorem CkConvergesToNat.toReal {k : ℕ} {X : ℕ → PointedManifold E H I}
    {Y : PointedManifold E H I} (h : CkConvergesToNat k X Y) : CkConvergesTo k X Y := by
  intro R _hR ε hε
  obtain ⟨N, hN⟩ := h (Nat.ceil R) ε hε
  exact ⟨N, fun n hn => (hN n hn).elim fun c => ⟨c.mono_scale (Nat.le_ceil R)⟩⟩

/-- **The real-scale and natural-scale forms of pointed `C^k` convergence agree.** -/
theorem ckConvergesTo_nat_iff {k : ℕ} {X : ℕ → PointedManifold E H I}
    {Y : PointedManifold E H I} : CkConvergesTo k X Y ↔ CkConvergesToNat k X Y :=
  ⟨CkConvergesTo.toNat, CkConvergesToNat.toReal⟩

/-- **Non-vacuity witness for pointed convergence.**  If every pointed ball of `X` lies in the
chart at its basepoint, then the constant sequence `X, X, X, …` converges to `X` in the pointed
`C^k` sense for every `k`: the identity embedding is `0`-close at every scale
(`ckCloseAtScale_self`), hence `ε`-close for every `ε > 0`.  This shows the convergence relation is
inhabited (it is not a vacuous `Prop`). -/
theorem ckConvergesTo_const (k : ℕ) (X : PointedManifold E H I)
    (hball : ∀ R : ℝ, 0 ≤ R → X.metricBall R ⊆ (extChartAt I X.basepoint).source) :
    CkConvergesTo k (fun _ => X) X := by
  intro R hR ε hε
  exact ⟨0, fun _ _ => ⟨(ckCloseAtScale_self k X (hball R hR)).mono (le_of_lt hε)⟩⟩

/-! ## The pointed `C^k` convergence interface

The interface bundles all the task's ingredients: an exhaustion by compact sets of the limit, smooth
basepoint-preserving embeddings of the limit into the approximants, and `C^{k+1}`-closeness of the
pulled-back metrics on the exhausted pieces with tolerances tending to zero. -/

/-- **Pointed `C^k` convergence interface.**  A sequence `X : ℕ → PointedManifold E H I` converges
to the pointed limit `Y` in the pointed `C^k` sense if:

* `Y` carries a compact exhaustion `exhaustion`;
* there are smooth basepoint-preserving embeddings `emb n : Y.M → (X n).M` of the limit into the
  approximants (each a topological embedding and an immersion);
* the pulled-back metric `(emb n)^* g_{X n}` is `C^{k+1}`-close to `g_Y` on the `n`-th compact
  exhaustion piece with tolerance `ε n`, where `ε n → 0`.

The embeddings go from the limit into the approximants, which is the standard Cheeger–Gromov
convention. -/
structure CkConvergence (k : ℕ) (X : ℕ → PointedManifold E H I) (Y : PointedManifold E H I) where
  /-- Exhaustion of the limit by compact sets. -/
  exhaustion : CompactExhaustion Y
  /-- The pointed embeddings of the limit into the approximants. -/
  emb : ∀ n : ℕ, Y.M → (X n).M
  /-- Smoothness of each embedding. -/
  contMDiff_emb : ∀ n : ℕ, ContMDiff I I ∞ (emb n)
  /-- Each embedding is a topological embedding. -/
  isEmbedding_emb : ∀ n : ℕ, Topology.IsEmbedding (emb n)
  /-- Each embedding is an immersion at every point. -/
  isImmersion_emb : ∀ n : ℕ, ∀ x : Y.M, Manifold.IsImmersionAt I I ∞ (emb n) x
  /-- Each embedding preserves basepoints. -/
  maps_basepoint : ∀ n : ℕ, emb n Y.basepoint = (X n).basepoint
  /-- The pointed balls of the limit are contained in the chart at its basepoint. -/
  ball_subset_chart : ∀ n : ℕ, Y.metricBall (n : ℝ) ⊆ (extChartAt I Y.basepoint).source
  /-- The tolerances. -/
  ε : ℕ → ℝ
  /-- The tolerances are positive. -/
  eps_pos : ∀ n : ℕ, 0 < ε n
  /-- The tolerances tend to zero. -/
  eps_tendsto_zero : Tendsto ε atTop (𝓝 0)
  /-- `C^{k+1}`-closeness of the pulled-back metrics on the exhaustion pieces. -/
  metric_close : ∀ n : ℕ,
    Y.CkCloseOnChart (k + 1) (extChartAt I Y.basepoint) (exhaustion.K n) (ε n)
      (pullbackMetric Y (X n) (emb n))

namespace CkConvergence

variable {k : ℕ} {X : ℕ → PointedManifold E H I} {Y : PointedManifold E H I}

/-- **The interface refines the `Prop`.**  If `X` converges to `Y` in the pointed `C^k` interface
sense and the limit has compact pointed balls, then `X` converges to `Y` in the `Prop`-valued
pointed `C^k` sense.  The compact-ball hypothesis places the pointed ball of real radius `R` inside
an exhaustion stage; the tolerance is then the exhaustion-indexed tolerance `ε m`, which is
eventually below the requested `ε`. -/
theorem convergesTo (h : CkConvergence k X Y) (hball : Y.HasCompactMetricBalls) :
    CkConvergesTo k X Y := by
  intro R _hR ε hε
  obtain ⟨n, hn⟩ := h.exhaustion.exists_subset (hball R)
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp h.eps_tendsto_zero) ε hε
  have hMle : ∀ m ≥ M, h.ε m ≤ ε := by
    intro m hm
    have hm' := hM m hm
    rw [Real.dist_eq, sub_zero] at hm'
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) hm')
  refine ⟨max (max n (Nat.ceil R)) M, fun m hm => ?_⟩
  have hnm : n ≤ m :=
    le_trans (le_max_left n (Nat.ceil R)) (le_trans (le_max_left (max n (Nat.ceil R)) M) hm)
  have hceil : Nat.ceil R ≤ m :=
    le_trans (le_max_right n (Nat.ceil R)) (le_trans (le_max_left (max n (Nat.ceil R)) M) hm)
  have hmM : M ≤ m := le_trans (le_max_right (max n (Nat.ceil R)) M) hm
  have hRm : R ≤ (m : ℝ) := le_trans (Nat.le_ceil R) (by exact_mod_cast hceil)
  refine ⟨?_⟩
  exact
    { ball_subset_chart := fun _ hy =>
        h.ball_subset_chart m (PointedManifold.metricBall_mono Y hRm hy)
      emb := h.emb m
      contMDiff_emb := h.contMDiff_emb m
      isEmbedding_emb := h.isEmbedding_emb m
      isImmersion_emb := h.isImmersion_emb m
      maps_basepoint := h.maps_basepoint m
      metric_close :=
        PointedManifold.CkCloseOnChart.mono Y (hMle m hmM)
          (PointedManifold.CkCloseOnChart.mono_set Y
            (fun _ hy => h.exhaustion.monotone_K hnm (hn hy)) (h.metric_close m)) }

end CkConvergence

end

end CheegerGromov
end D9
end Poincare
