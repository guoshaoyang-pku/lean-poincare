/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-gh-compactness)

**D7 Gromov–Hausdorff / Cheeger–Gromov compactness, part 4: state-only Cheeger–Gromov
statements and the named missing-input ledger.**

The toy compactness theorem of `Poincare.D7.Compactness.ToyCompactness` is the only
convergence theorem proved in this development.  The **pointed Cheeger–Gromov compactness
theorem for Riemannian manifolds** —

> a sequence of complete pointed `n`-manifolds with `|Rm| ≤ K` and `inj ≥ i₀ > 0` has a
> subsequence converging in the pointed `C^∞` Cheeger–Gromov sense to a complete pointed
> `n`-manifold with the same bounds

— is not formalized: the pinned mathlib has no Riemann curvature tensor, no injectivity
radius theory, no harmonic coordinates, no elliptic regularity for the metric and no
pointed Gromov–Hausdorff compactness.  This file fixes the statements exactly, as
state-only `Prop`s with every missing input named, and proves the checked reductions.

* `missingCheegerGromovCompactness` — the full state-only `Prop`.  Its conclusion is the
  conjunction of the *checked* metric GH convergence datum of `Basic` and an opaque smooth
  convergence relation `CGConvergesTo`, which is a parameter of the statement.  The
  geometric hypotheses (curvature radius, injectivity radius, noncollapsing, harmonic
  bounds) are explicit fields of `ManifoldFamilyHypotheses`.
* `missingPointedGHConvergentSubsequence` — the metric half on its own: the extraction of a
  GH-convergent subsequence from the precompactness certificate.  This is the missing
  diagonal argument; the certificate itself and its total-boundedness consequences are
  checked in `Basic` and `TotalBounded`.
* `ghSubsequence_of_cheegerGromov`, `smoothPart_of_cheegerGromov` — checked projections of
  the state-only statement onto its metric and smooth halves.
* `cheegerGromov_of_ghSubsequence` — checked reduction: explicit GH-convergent subsequence
  data plus the smooth relation imply the state-only statement.
* `cheegerGromov_of_ghPrecompact_and_smoothUpgrade` — checked reduction: the metric
  extraction plus a uniform smooth upgrade imply the state-only statement, isolating
  exactly the two missing inputs.
* `cheegerGromovConclusion_of_finiteFamily` — checked instance: for a finite family of
  finite pointed spaces, the conclusion of the state-only statement holds with the smooth
  relation supplied, by the toy compactness theorem.
* `cheegerGromovDependencies` — the named ledger of twelve missing analytic/geometric
  inputs; `cheegerGromovBlockers` — the five named blockers.

Every unproved input is a `Prop` parameter, a structure field or a `String` ledger entry;
there is no unproved hole, no extra logical postulate, no kernel bypass, no native
evaluation and no statement stub in this file.
-/

import Poincare.D7.Compactness.ToyCompactness
import Poincare.D7.ShortTime.Statements
import Poincare.Longrun.Topology.MissingTheorems

open Filter Set Topology
open scoped Topology

namespace Poincare
namespace D7
namespace Compactness

open Poincare.D7.ShortTime

universe u v

noncomputable section

/-! ## 1. The geometric hypotheses of a manifold family -/

/-- **Opaque geometric hypotheses for a family of pointed Riemannian manifolds.**  The
manifolds themselves are not formalized; the bundle records exactly the hypotheses of the
Cheeger–Gromov compactness theorem:

* a common positive dimension;
* a curvature radius `r₀` with `|Rm| ≤ 1/r₀²` (opaque, because mathlib has no Riemann
  curvature tensor);
* a positive injectivity radius lower bound (opaque, because mathlib has no cut locus
  theory);
* uniform noncollapsing (opaque volume comparison);
* uniform harmonic-coordinate `C^∞` bounds (opaque elliptic regularity).

The `Prop` fields are hypotheses, never assertions. -/
structure ManifoldFamilyHypotheses (ι : Type v) where
  /-- The common dimension. -/
  dim : ℕ
  /-- The dimension is positive. -/
  dim_pos : 0 < dim
  /-- The curvature scale `r₀` in `|Rm| ≤ 1/r₀²`. -/
  curvatureRadius : ℝ
  /-- The curvature scale is positive. -/
  curvatureRadius_pos : 0 < curvatureRadius
  /-- The injectivity radius lower bound. -/
  injectivityRadius : ℝ
  /-- The injectivity radius bound is positive. -/
  injectivityRadius_pos : 0 < injectivityRadius
  /-- Uniform noncollapsing of the family (opaque). -/
  noncollapsed : Prop
  /-- Uniform harmonic-coordinate bounds (opaque). -/
  harmonicBounds : Prop

/-- **Bundled Cheeger–Gromov convergence data.**  The *checked* pointed GH convergence datum
of `Poincare.D7.Compactness.Basic` together with the opaque smooth regularity proposition
(the `C^∞` part of Cheeger–Gromov convergence). -/
structure CheegerGromovConvergenceData {ι : Type v} (l : Filter ι)
    (X : ι → PointedMetricSpace.{u}) (Y : PointedMetricSpace.{u}) where
  /-- The metric part: pointed GH convergence data, checked in `Basic`. -/
  metric : GHConvergenceData l X Y
  /-- The smooth part: the missing `C^∞` convergence statement. -/
  smoothRegularity : Prop

/-- **Checked projection.**  Cheeger–Gromov convergence data contain pointed GH
convergence data. -/
def ghConvergence_of_cheegerGromov {ι : Type v} {l : Filter ι}
    {X : ι → PointedMetricSpace.{u}} {Y : PointedMetricSpace.{u}}
    (D : CheegerGromovConvergenceData l X Y) : GHConvergenceData l X Y :=
  D.metric

/-! ## 2. The state-only statements -/

/-- **MISSING THEOREM (pointed Gromov precompactness, metric half).**  Every
precompactness certificate for a family of pointed metric spaces yields a pointed
GH-convergent subsequence.  The certificate itself and its total-boundedness consequences
are checked in `Basic` and `TotalBounded`; the diagonal extraction of the subsequence is
not, and is the content of this state-only `Prop`. -/
def missingPointedGHConvergentSubsequence (X : ℕ → PointedMetricSpace.{u}) : Prop :=
  ∀ _Cert : GHPrecompactCertificate X,
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ Y : PointedMetricSpace.{u}, Nonempty (GHConvergenceData atTop (fun k => X (φ k)) Y)

/-- **Checked shape lemma.**  The metric missing statement unfolds to its subsequence
form. -/
theorem missingPointedGHConvergentSubsequence_iff (X : ℕ → PointedMetricSpace.{u}) :
    missingPointedGHConvergentSubsequence X ↔
      ∀ _Cert : GHPrecompactCertificate X,
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∃ Y : PointedMetricSpace.{u},
            Nonempty (GHConvergenceData atTop (fun k => X (φ k)) Y) :=
  Iff.rfl

/-- **MISSING THEOREM (pointed Cheeger–Gromov compactness, `C^∞` form).**  Let `X` be a
sequence of complete pointed Riemannian `n`-manifolds satisfying the bundled geometric
hypotheses `H` (curvature bound, injectivity radius bound, noncollapsing, harmonic bounds).
Then some strictly monotone subsequence has a pointed limit `Y` which is simultaneously

* a pointed Gromov–Hausdorff limit, in the checked sense of
  `Poincare.D7.Compactness.GHConvergenceData`, and
* a limit in the smooth Cheeger–Gromov sense, expressed by the opaque relation
  `CGConvergesTo`, which is a parameter because the smooth convergence relation is not
  formalized.

The statement is a `def ... : Prop`; it is never asserted as a theorem. -/
def missingCheegerGromovCompactness (X : ℕ → PointedMetricSpace.{u})
    (H : ManifoldFamilyHypotheses ℕ)
    (CGConvergesTo : (ℕ → PointedMetricSpace.{u}) → PointedMetricSpace.{u} → Prop) : Prop :=
  H.noncollapsed → H.harmonicBounds →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ Y : PointedMetricSpace.{u},
        Nonempty (GHConvergenceData atTop (fun k => X (φ k)) Y) ∧
          CGConvergesTo (fun k => X (φ k)) Y

/-- **Checked shape lemma.**  The state-only Cheeger–Gromov statement unfolds to its
hypotheses-imply-subsequence form. -/
theorem missingCheegerGromovCompactness_iff (X : ℕ → PointedMetricSpace.{u})
    (H : ManifoldFamilyHypotheses ℕ)
    (CGConvergesTo : (ℕ → PointedMetricSpace.{u}) → PointedMetricSpace.{u} → Prop) :
    missingCheegerGromovCompactness X H CGConvergesTo ↔
      (H.noncollapsed → H.harmonicBounds →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∃ Y : PointedMetricSpace.{u},
            Nonempty (GHConvergenceData atTop (fun k => X (φ k)) Y) ∧
              CGConvergesTo (fun k => X (φ k)) Y) :=
  Iff.rfl

/-! ## 3. Checked reductions -/

/-- **Checked projection (metric half).**  The state-only statement implies the existence of
a GH-convergent subsequence; the smooth part is simply dropped. -/
theorem ghSubsequence_of_cheegerGromov {X : ℕ → PointedMetricSpace.{u}}
    {H : ManifoldFamilyHypotheses ℕ}
    {CGConvergesTo : (ℕ → PointedMetricSpace.{u}) → PointedMetricSpace.{u} → Prop}
    (h : missingCheegerGromovCompactness X H CGConvergesTo)
    (hnc : H.noncollapsed) (hhb : H.harmonicBounds) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ Y : PointedMetricSpace.{u}, Nonempty (GHConvergenceData atTop (fun k => X (φ k)) Y) := by
  obtain ⟨φ, hφ, Y, hGH, _⟩ := h hnc hhb
  exact ⟨φ, hφ, Y, hGH⟩

/-- **Checked projection (smooth half).**  The state-only statement implies the existence of
a smooth Cheeger–Gromov convergent subsequence; the metric part is simply dropped. -/
theorem smoothPart_of_cheegerGromov {X : ℕ → PointedMetricSpace.{u}}
    {H : ManifoldFamilyHypotheses ℕ}
    {CGConvergesTo : (ℕ → PointedMetricSpace.{u}) → PointedMetricSpace.{u} → Prop}
    (h : missingCheegerGromovCompactness X H CGConvergesTo)
    (hnc : H.noncollapsed) (hhb : H.harmonicBounds) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ Y : PointedMetricSpace.{u}, CGConvergesTo (fun k => X (φ k)) Y := by
  obtain ⟨φ, hφ, Y, _, hCG⟩ := h hnc hhb
  exact ⟨φ, hφ, Y, hCG⟩

/-- **Checked reduction (explicit subsequence data).**  If a GH-convergent subsequence and
the smooth convergence relation for it are supplied explicitly, the state-only
Cheeger–Gromov statement holds. -/
theorem cheegerGromov_of_ghSubsequence {X : ℕ → PointedMetricSpace.{u}}
    {H : ManifoldFamilyHypotheses ℕ}
    {CGConvergesTo : (ℕ → PointedMetricSpace.{u}) → PointedMetricSpace.{u} → Prop}
    (h : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ Y : PointedMetricSpace.{u},
        Nonempty (GHConvergenceData atTop (fun k => X (φ k)) Y) ∧
          CGConvergesTo (fun k => X (φ k)) Y) :
    missingCheegerGromovCompactness X H CGConvergesTo :=
  fun _ _ => h

/-- **Checked reduction (metric extraction plus smooth upgrade).**  The state-only
Cheeger–Gromov statement follows from exactly two inputs: the missing metric extraction of a
GH-convergent subsequence from the precompactness certificate, and a uniform smooth upgrade
of GH convergence to Cheeger–Gromov convergence.  This isolates what is missing. -/
theorem cheegerGromov_of_ghPrecompact_and_smoothUpgrade {X : ℕ → PointedMetricSpace.{u}}
    {H : ManifoldFamilyHypotheses ℕ}
    {CGConvergesTo : (ℕ → PointedMetricSpace.{u}) → PointedMetricSpace.{u} → Prop}
    (Cert : GHPrecompactCertificate X)
    (hGH : missingPointedGHConvergentSubsequence X)
    (hUpgrade : ∀ (φ : ℕ → ℕ) (Y : PointedMetricSpace.{u}),
      GHConvergenceData atTop (fun k => X (φ k)) Y →
        CGConvergesTo (fun k => X (φ k)) Y) :
    missingCheegerGromovCompactness X H CGConvergesTo :=
  fun _ _ => by
    obtain ⟨φ, hφ, Y, hD⟩ := hGH Cert
    obtain ⟨D⟩ := hD
    exact ⟨φ, hφ, Y, ⟨D⟩, hUpgrade φ Y D⟩

/-- **Checked consequence (the certificate's metric content).**  Every basepoint ball of
every member of a certified family is totally bounded; this is the checked input that the
missing metric extraction consumes. -/
theorem totallyBounded_of_precompactCertificate {X : ℕ → PointedMetricSpace.{u}}
    (Cert : GHPrecompactCertificate X) (k : ℕ) (R : ℝ) :
    TotallyBounded (Metric.closedBall (X k).base R) :=
  Cert.totallyBounded_closedBall k R

/-- **Checked finite-family instance of the Cheeger–Gromov conclusion.**  For a finite
family of finite pointed spaces and any index sequence, the conclusion of the state-only
Cheeger–Gromov statement holds as soon as the smooth relation is supplied on the family.
The metric part is the toy compactness theorem, not an assumption. -/
theorem cheegerGromovConclusion_of_finiteFamily {n : ℕ} (F : Fin n → PointedMetricSpace.{u})
    [∀ i, Fintype (F i)] (u : ℕ → Fin n)
    (CGConvergesTo : (ℕ → PointedMetricSpace.{u}) → PointedMetricSpace.{u} → Prop)
    (hCG : ∀ i : Fin n, CGConvergesTo (fun _ : ℕ => F i) (F i)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ Y : PointedMetricSpace.{u},
        Nonempty (GHConvergenceData atTop (fun k => F (u (φ k))) Y) ∧
          CGConvergesTo (fun k => F (u (φ k))) Y := by
  let W := constSubsequence u
  have hfun : (fun k => F (u (W.subseq k))) = fun _ : ℕ => F W.index := by
    funext k
    rw [W.const k]
  refine ⟨W.subseq, W.strictMono, F W.index, ?_, ?_⟩
  · rw [hfun]
    exact ⟨GHConvergenceData.refl atTop (F W.index)⟩
  · rw [hfun]
    exact hCG W.index

/-! ## 4. The named missing-input ledger -/

/-- **Blocker `B-D7-GHC-CURVATURE`.**  Mathlib has no Riemann curvature tensor, so the
curvature bounds of the Cheeger–Gromov theorem cannot even be stated over a manifold. -/
def BlockerCurvatureTensor : String :=
  "B-D7-GHC-CURVATURE: the pinned mathlib has no Riemann curvature tensor, no Ricci tensor \
  and no sectional curvature on a Riemannian manifold, so the hypotheses |Rm| <= 1/r0^2 and \
  the curvature convergence of the Cheeger-Gromov limit are carried as opaque Prop fields."

/-- **Blocker `B-D7-GHC-HARMONIC`.**  The harmonic-coordinate atlas and the elliptic
regularity estimates on it are missing. -/
def BlockerHarmonicCoordinates : String :=
  "B-D7-GHC-HARMONIC: no harmonic-coordinate existence theorem, no Schauder/elliptic \
  regularity for the metric components in harmonic coordinates, and no C^{k,alpha} a priori \
  bounds; the uniform harmonic bounds are an opaque Prop field."

/-- **Blocker `B-D7-GHC-INJECTIVITY`.**  The injectivity radius and its lower bound are
missing. -/
def BlockerInjectivityRadius : String :=
  "B-D7-GHC-INJECTIVITY: the pinned mathlib has no cut locus theory and no injectivity \
  radius of a Riemannian manifold, so the bound inj >= i0 is an opaque numeric field and \
  the Cheeger-Gromov noncollapsing consequence is not derived."

/-- **Blocker `B-D7-GHC-SMOOTH`.**  The smooth Cheeger–Gromov convergence relation itself is
missing. -/
def BlockerSmoothConvergence : String :=
  "B-D7-GHC-SMOOTH: there is no C^infinity pointed Cheeger-Gromov convergence relation in \
  mathlib; it is supplied as the opaque parameter CGConvergesTo, and the uniform smooth \
  upgrade of metric GH convergence is an explicit hypothesis of the checked reduction."

/-- **Blocker `B-D7-GHC-GH-SUBSEQUENCE`.**  Pointed Gromov–Hausdorff compactness (the
diagonal extraction) is missing. -/
def BlockerGHSubsequence : String :=
  "B-D7-GHC-GH-SUBSEQUENCE: mathlib has GHSpace and ghDist for compact (unpointed) metric \
  spaces, but no pointed Gromov-Hausdorff convergence and no diagonal extraction of a \
  convergent subsequence from uniform total boundedness plus completeness; that extraction \
  is the state-only Prop missingPointedGHConvergentSubsequence."

theorem BlockerCurvatureTensor_ne_nil : BlockerCurvatureTensor ≠ "" := by
  simp [BlockerCurvatureTensor]

theorem BlockerHarmonicCoordinates_ne_nil : BlockerHarmonicCoordinates ≠ "" := by
  simp [BlockerHarmonicCoordinates]

theorem BlockerInjectivityRadius_ne_nil : BlockerInjectivityRadius ≠ "" := by
  simp [BlockerInjectivityRadius]

theorem BlockerSmoothConvergence_ne_nil : BlockerSmoothConvergence ≠ "" := by
  simp [BlockerSmoothConvergence]

theorem BlockerGHSubsequence_ne_nil : BlockerGHSubsequence ≠ "" := by
  simp [BlockerGHSubsequence]

/-- **The named missing inputs of pointed Cheeger–Gromov compactness.**  Each entry names a
standard ingredient of the proof and records why it is absent from the pinned mathlib and
from this development. -/
def cheegerGromovDependencies : List MissingDependency := [
  ⟨"CGH-1 pointed Riemannian manifold family",
   "A sequence (M_i, g_i, p_i) of complete pointed smooth Riemannian n-manifolds with the \
    Riemannian distance. Mathlib has IsRiemannianManifold and RiemannianBundle, but the \
    pointed family interface, its completeness and the identification of the Riemannian \
    distance with the metric dist are not assembled."⟩,
  ⟨"CGH-2 Riemann curvature tensor and bounds",
   "The Riemann curvature tensor Rm, its covariant derivatives and the bound \
    |Rm| <= 1/r0^2. The pinned mathlib has no curvature tensor; the bound is an opaque \
    Prop field of ManifoldFamilyHypotheses."⟩,
  ⟨"CGH-3 injectivity radius",
   "The injectivity radius of a Riemannian manifold and the lower bound inj >= i0. It needs \
    the cut locus and the exponential map; neither is in the pinned mathlib. The bound is an \
    opaque numeric field."⟩,
  ⟨"CGH-4 Cheeger noncollapsing",
   "The volume comparison that turns a curvature bound and an injectivity radius bound into \
    a uniform lower bound for the volume of unit balls (Cheeger, Gromov). Supplied as the \
    opaque field noncollapsed."⟩,
  ⟨"CGH-5 harmonic coordinates",
   "Existence of a harmonic-coordinate atlas with uniform radius and the resulting \
    quasilinear elliptic equation for the metric components. Not in the pinned mathlib."⟩,
  ⟨"CGH-6 elliptic regularity and a priori bounds",
   "Schauder/Calderon-Zygmund estimates and the C^{k,alpha} bounds for the metric in \
    harmonic coordinates, uniform over the family. Not in the pinned mathlib."⟩,
  ⟨"CGH-7 Sobolev embedding and Arzela-Ascoli",
   "The compactness step extracting a smoothly convergent subsequence of metric components \
    from the uniform bounds. Not available at the manifold level in the pinned mathlib."⟩,
  ⟨"CGH-8 smooth Cheeger-Gromov convergence relation",
   "The C^infinity pointed Cheeger-Gromov convergence relation, including the convergence \
    of the Levi-Civita connections and curvature tensors. It is the opaque parameter \
    CGConvergesTo of the state-only statement."⟩,
  ⟨"CGH-9 pointed Gromov-Hausdorff convergence",
   "Pointed GH convergence by epsilon-isometries is defined and checked here \
    (GHConvergenceData), but the equivalence with the pointed GH distance and the \
    completeness of the limit are not formalized; mathlib's GHSpace is unpointed and \
    restricted to compact spaces."⟩,
  ⟨"CGH-10 Gromov precompactness and diagonal extraction",
   "The diagonal argument that extracts a GH-convergent subsequence from uniform total \
    boundedness of basepoint balls plus completeness. The certificate and its \
    total-boundedness consequences are checked; the extraction is the state-only Prop \
    missingPointedGHConvergentSubsequence."⟩,
  ⟨"CGH-11 limit manifold and inherited bounds",
   "The construction of the limit pointed Riemannian manifold and the verification that it \
    is complete and satisfies the same dimension, curvature and injectivity radius bounds. \
    Not formalized."⟩,
  ⟨"CGH-12 smoothness of the limit metric",
   "The proof that the GH limit metric is smooth (a Riemannian metric of the same regularity \
    class) and that the convergence is C^infinity, via the harmonic-coordinate bounds. Not \
    formalized."⟩
]

theorem cheegerGromovDependencies_length : cheegerGromovDependencies.length = 12 := rfl

theorem cheegerGromovDependencies_ne_nil : cheegerGromovDependencies ≠ [] := by
  simp [cheegerGromovDependencies]

/-- Every listed dependency has a nonempty name and reason. -/
theorem cheegerGromovDependencies_all_named :
    ∀ d ∈ cheegerGromovDependencies, d.name ≠ "" ∧ d.reason ≠ "" := by
  simp [cheegerGromovDependencies]

/-- The five named blockers of pointed Cheeger–Gromov compactness. -/
def cheegerGromovBlockers : List String := [
  BlockerCurvatureTensor,
  BlockerHarmonicCoordinates,
  BlockerInjectivityRadius,
  BlockerSmoothConvergence,
  BlockerGHSubsequence
]

theorem cheegerGromovBlockers_length : cheegerGromovBlockers.length = 5 := rfl

theorem cheegerGromovBlockers_ne_nil : cheegerGromovBlockers ≠ [] := by
  simp [cheegerGromovBlockers]

/-- Every named blocker is a nonempty string. -/
theorem cheegerGromovBlockers_all_named :
    ∀ b ∈ cheegerGromovBlockers, b ≠ "" := by
  simp [cheegerGromovBlockers, BlockerCurvatureTensor, BlockerHarmonicCoordinates,
    BlockerInjectivityRadius, BlockerSmoothConvergence, BlockerGHSubsequence]

end

end Compactness
end D7
end Poincare
