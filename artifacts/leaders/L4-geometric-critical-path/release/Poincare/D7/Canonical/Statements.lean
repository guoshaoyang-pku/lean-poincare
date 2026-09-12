/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-canonical-neighborhood)

**D7 canonical-neighborhood interface, part 5: the state-only Perelman canonical neighborhood
theorem and the named missing-input ledger.**

Perelman's canonical neighborhood theorem (Perelman, *Ricci flow with surgery on
three-manifolds*, §3; Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Theorem 12.1)
states, in the form used by the surgery argument:

> For every `ε > 0` and `κ > 0` there is `r₀ = r₀(ε, κ) > 0` such that if `(M³, g(t))` is a
> complete Ricci flow with `Rm ≥ -r₀⁻²` and with `κ`-noncollapsing at scale `r₀`, and if
> `R(x₀, t₀) ≥ r₀⁻²`, then the parabolic neighborhood of `(x₀, t₀)` at scale `r₀` is a
> canonical neighborhood: an `ε`-neck, an `ε`-cap, or a compact positively curved model.

The checked interface of `Poincare.D7.Canonical.Basic`–`Classification` supplies the
classification datum (`CanonicalNeighborhoodCertificate`) and the model instance checks; the
manifold-level theorem itself is not formalized, because the pinned mathlib has no Riemannian
curvature, no Ricci flow, no κ-noncollapsing and no ancient-solution theory.

This module fixes the statement exactly as a state-only `Prop`, never asserted as a theorem:

* `CanonicalNeighborhoodHypotheses X`: the bundled geometric hypotheses over the pointed
  region `X` — dimension three, a curvature scale `r₀`, a noncollapsing constant `κ`, and the
  opaque propositions recording the curvature lower bound, the scalar curvature lower bound,
  κ-noncollapsing, the ancient κ-solution structure and the uniform derivative bounds;
* `missingPerelmanCanonicalNeighborhood X H ε`: the state-only `Prop`.  Its conclusion is the
  existence of an admissible scale `r ≤ r₀`, a curvature normalization at scale `r`, and a
  `CanonicalNeighborhoodCertificate ε H.kappa r X`;
* checked reductions isolating the certificate extraction, the scale extraction and the
  certificate-supplies-the-statement direction;
* `perelmanCanonicalNeighborhoodDependencies` (12 named missing inputs) and
  `perelmanCanonicalNeighborhoodBlockers` (6 named blockers).

Every unproved input is a `Prop` parameter, a structure field or a `String` ledger entry;
there is no unproved hole, no extra logical postulate, no kernel bypass, no native evaluation
and no statement stub in this file.
-/

import Poincare.D7.Canonical.Classification
import Poincare.D7.ShortTime.Statements

set_option autoImplicit false

set_option linter.unusedVariables false

open Filter Set Topology
open scoped Topology

namespace Poincare
namespace D7
namespace Canonical

universe u

open Poincare.D7.Compactness
open Poincare.D7.ShortTime

noncomputable section

/-! ## 1. The geometric hypotheses -/

/-- **The bundled geometric hypotheses of Perelman's canonical neighborhood theorem.**  The
region `X` is the pointed parabolic neighborhood of the point where the scalar curvature is
large (the manifold itself is not formalized).  The numeric fields are explicit; the geometric
content that mathlib cannot currently state — the curvature lower bound, the scalar curvature
lower bound, κ-noncollapsing, the ancient κ-solution structure and the uniform curvature
derivative bounds — is carried by `Prop` fields, never asserted. -/
structure CanonicalNeighborhoodHypotheses (X : PointedMetricSpace.{u}) where
  /-- The dimension of the manifold. -/
  dim : ℕ
  /-- The dimension is three. -/
  dim_eq_three : dim = 3
  /-- The curvature scale `r₀` in `Rm ≥ -r₀⁻²` and `R ≥ r₀⁻²`. -/
  curvatureRadius : ℝ
  /-- The curvature scale is positive. -/
  curvatureRadius_pos : 0 < curvatureRadius
  /-- The noncollapsing constant `κ`. -/
  kappa : ℝ
  /-- The noncollapsing constant is positive. -/
  kappa_pos : 0 < kappa
  /-- Opaque: the curvature lower bound `Rm ≥ -r₀⁻²` (missing manifold curvature). -/
  curvatureLowerBound : Prop
  /-- Opaque: the scalar curvature lower bound `R(base) ≥ r₀⁻²`. -/
  scalarCurvatureLarge : Prop
  /-- Opaque: κ-noncollapsing at scale `r₀` (missing volume comparison). -/
  noncollapsed : Prop
  /-- Opaque: the ancient κ-solution structure used by the blow-up argument. -/
  ancientKappaSolution : Prop
  /-- Opaque: the uniform bounds on the curvature derivatives. -/
  boundedCurvatureDerivatives : Prop

/-! ## 2. The state-only statement -/

/-- **MISSING THEOREM (Perelman's canonical neighborhood theorem, state-only form).**  For
every `ε > 0` and every `κ > 0` there is an admissible scale `r > 0` with `r ≤ r₀` such that
the geometric hypotheses of `H` imply that the region `X` carries a
`CanonicalNeighborhoodCertificate ε κ r X`.

The scale is existentially quantified in the conclusion (the theorem's content is the
existence of a scale depending only on `ε` and `κ`, with `r ≤ r₀`).  The statement is a
`def ... : Prop`; it is never asserted as a theorem. -/
def missingPerelmanCanonicalNeighborhood (X : PointedMetricSpace.{u})
    (H : CanonicalNeighborhoodHypotheses X) (ε : ℝ) : Prop :=
  0 < ε → H.curvatureLowerBound → H.scalarCurvatureLarge → H.noncollapsed →
    ∃ r : ℝ, 0 < r ∧ r ≤ H.curvatureRadius ∧
      ∃ curvature : CurvatureScaleDatum.{u, u} r,
        Nonempty (CanonicalNeighborhoodCertificate ε H.kappa r X)

/-- **Checked shape lemma.**  The state-only statement unfolds to its hypotheses-imply-data
form. -/
theorem missingPerelmanCanonicalNeighborhood_iff (X : PointedMetricSpace.{u})
    (H : CanonicalNeighborhoodHypotheses X) (ε : ℝ) :
    missingPerelmanCanonicalNeighborhood X H ε ↔
      0 < ε → H.curvatureLowerBound → H.scalarCurvatureLarge → H.noncollapsed →
        ∃ r : ℝ, 0 < r ∧ r ≤ H.curvatureRadius ∧
          ∃ curvature : CurvatureScaleDatum.{u, u} r,
            Nonempty (CanonicalNeighborhoodCertificate ε H.kappa r X) :=
  Iff.rfl

/-! ## 3. Checked reductions -/

/-- **Certificate extraction.**  The state-only statement, applied to the hypotheses, yields
an admissible scale and a canonical-neighborhood certificate. -/
theorem certificate_of_missingPerelmanCanonicalNeighborhood {X : PointedMetricSpace.{u}}
    {H : CanonicalNeighborhoodHypotheses X} {ε : ℝ}
    (h : missingPerelmanCanonicalNeighborhood X H ε) (hε : 0 < ε)
    (hcurv : H.curvatureLowerBound) (hscalar : H.scalarCurvatureLarge)
    (hnc : H.noncollapsed) :
    ∃ r : ℝ, 0 < r ∧ r ≤ H.curvatureRadius ∧
      ∃ curvature : CurvatureScaleDatum.{u, u} r,
        Nonempty (CanonicalNeighborhoodCertificate ε H.kappa r X) :=
  h hε hcurv hscalar hnc

/-- **Scale extraction.**  The scale produced by the state-only statement is positive and at
most the curvature scale `r₀`; this is the quantitative content `r = r₀(ε, κ) ≤ r₀`. -/
theorem exists_admissible_scale_of_missingPerelmanCanonicalNeighborhood
    {X : PointedMetricSpace.{u}} {H : CanonicalNeighborhoodHypotheses X} {ε : ℝ}
    (h : missingPerelmanCanonicalNeighborhood X H ε) (hε : 0 < ε)
    (hcurv : H.curvatureLowerBound) (hscalar : H.scalarCurvatureLarge)
    (hnc : H.noncollapsed) :
    ∃ r : ℝ, 0 < r ∧ r ≤ H.curvatureRadius := by
  obtain ⟨r, hr, hrle, _⟩ := h hε hcurv hscalar hnc
  exact ⟨r, hr, hrle⟩

/-- **A scale below the curvature radius exists**, because `r₀ > 0`.  This is the trivial
quantitative input used by the checked reduction above. -/
theorem exists_scale_below_curvatureRadius {X : PointedMetricSpace.{u}}
    (H : CanonicalNeighborhoodHypotheses X) :
    ∃ r : ℝ, 0 < r ∧ r ≤ H.curvatureRadius :=
  ⟨H.curvatureRadius, H.curvatureRadius_pos, le_rfl⟩

/-- **Checked reduction (certificate supplies the statement).**  If every admissible data
tuple is supplied with a certificate, then the state-only statement holds.  This isolates the
theorem's mathematical content as the existence of the certificate. -/
theorem missingPerelmanCanonicalNeighborhood_of_certificate {X : PointedMetricSpace.{u}}
    {H : CanonicalNeighborhoodHypotheses X} {ε : ℝ}
    (hcert : ∀ r : ℝ, 0 < r → r ≤ H.curvatureRadius →
      ∃ curvature : CurvatureScaleDatum.{u, u} r,
        Nonempty (CanonicalNeighborhoodCertificate ε H.kappa r X)) :
    missingPerelmanCanonicalNeighborhood X H ε :=
  fun _ _ _ _ => by
    obtain ⟨r, hr, hrle⟩ :=
      exists_scale_below_curvatureRadius H
    obtain ⟨curvature, hcert'⟩ := hcert r hr hrle
    exact ⟨r, hr, hrle, curvature, hcert'⟩

/-- **The collapsed model is excluded by the conclusion.**  If the state-only statement's
conclusion held for the collapsed region and the admissible scale satisfied `2 ε < r`, then
`Classification.degenerateModel_not_certificate` would be contradicted; hence the conclusion
can only hold for the collapsed region at scales `r ≤ 2 ε`.  This is the classification
consistency check of the state-only statement with the checked toy. -/
theorem scale_le_two_mul_of_missingPerelman_conclusion
    {H : CanonicalNeighborhoodHypotheses degenerateModel} {ε r : ℝ}
    (hcert : Nonempty (CanonicalNeighborhoodCertificate ε H.kappa r degenerateModel)) :
    r ≤ 2 * ε := by
  obtain ⟨C⟩ := hcert
  exact scale_le_two_mul_of_subsingleton C

/-- **The checked toy is incompatible with a large admissible scale on the collapsed model.**
For `2 ε < r` the state-only statement cannot conclude with scale `r` on the collapsed
region. -/
theorem not_conclusion_scale_of_two_mul_lt
    {H : CanonicalNeighborhoodHypotheses degenerateModel} {ε r : ℝ} (h : 2 * ε < r) :
    ¬ Nonempty (CanonicalNeighborhoodCertificate ε H.kappa r degenerateModel) :=
  degenerateModel_not_certificate h

/-! ## 4. The named missing-input ledger -/

/-- **Blocker `B-D7-CN-MANIFOLD`.**  The smooth Riemannian 3-manifold and its parabolic
neighborhood are not formalized. -/
def BlockerManifold : String :=
  "B-D7-CN-MANIFOLD: the pinned mathlib has no smooth Riemannian 3-manifold with a \
  Riemannian distance assembled from a metric tensor, no parabolic neighborhood of a \
  space-time point, and no identification of the metric-space region with a metric ball; the \
  region is an abstract pointed metric space in this interface."

/-- **Blocker `B-D7-CN-CURVATURE`.**  Manifold-level curvature bounds are not available. -/
def BlockerCurvature : String :=
  "B-D7-CN-CURVATURE: there is no Riemann curvature tensor, no Ricci tensor and no scalar \
  curvature on a Riemannian manifold in the pinned mathlib; the bounds Rm >= -r0^{-2} and \
  R >= r0^{-2} are opaque Prop fields, and the curvature normalization of the certificate is \
  an algebraic RiemannCurvatureData of the D7 curvature layer."

/-- **Blocker `B-D7-CN-NONCOLLAPSING`.**  κ-noncollapsing is not available. -/
def BlockerNoncollapsing : String :=
  "B-D7-CN-NONCOLLAPSING: the volume comparison theorem turning a curvature bound into a \
  uniform lower bound for the volume of balls is not formalized; the certificate carries only \
  the checkable metric shadow MetricNoncollapsing."

/-- **Blocker `B-D7-CN-ANCIENT`.**  The ancient κ-solution classification is not available. -/
def BlockerAncient : String :=
  "B-D7-CN-ANCIENT: the classification of ancient κ-solutions in dimension three (the \
  spherical and cylindrical alternatives) and the blow-up argument producing them are not \
  formalized; they are the analytic heart of Perelman's theorem."

/-- **Blocker `B-D7-CN-SMOOTH-CLOSENESS`.**  Smooth closeness to the round models is not
available. -/
def BlockerSmoothCloseness : String :=
  "B-D7-CN-SMOOTH-CLOSENESS: the epsilon-neck and epsilon-cap conditions are smooth \
  C^{infinity} closeness to the round cylinder and cap, with derivative bounds; the checked \
  interfaces capture only the metric-shadow features (distances, diameters and scalar \
  curvature normalizations) in the pointed Gromov-Hausdorff epsilon-isometry sense."

/-- **Blocker `B-D7-CN-QUANTITATIVE`.**  The quantitative dependence `r₀ = r₀(ε, κ)` is not
available. -/
def BlockerQuantitative : String :=
  "B-D7-CN-QUANTITATIVE: the explicit dependence r0 = r0(epsilon, kappa) and the uniform \
  constant in the compactness blow-up are not formalized; the state-only statement \
  existentially quantifies the admissible scale."

theorem BlockerManifold_ne_nil : BlockerManifold ≠ "" := by simp [BlockerManifold]

theorem BlockerCurvature_ne_nil : BlockerCurvature ≠ "" := by simp [BlockerCurvature]

theorem BlockerNoncollapsing_ne_nil : BlockerNoncollapsing ≠ "" := by
  simp [BlockerNoncollapsing]

theorem BlockerAncient_ne_nil : BlockerAncient ≠ "" := by simp [BlockerAncient]

theorem BlockerSmoothCloseness_ne_nil : BlockerSmoothCloseness ≠ "" := by
  simp [BlockerSmoothCloseness]

theorem BlockerQuantitative_ne_nil : BlockerQuantitative ≠ "" := by
  simp [BlockerQuantitative]

/-- **The named missing inputs of Perelman's canonical neighborhood theorem.**  Each entry
names a standard ingredient of the proof and records why it is absent from the pinned mathlib
and from this development. -/
def perelmanCanonicalNeighborhoodDependencies : List MissingDependency := [
  ⟨"PCN-1 smooth Riemannian 3-manifold",
   "A complete smooth Riemannian 3-manifold with its Riemannian distance and the parabolic \
    neighborhood of a space-time point. Mathlib has RiemannianBundle and IsRiemannianManifold \
    but the pointed family interface, completeness and the distance comparison are not \
    assembled."⟩,
  ⟨"PCN-2 Ricci flow and the parabolic neighborhood",
   "A Ricci flow g(t) on a time interval, its space-time parabolic neighborhoods, and the \
    notion of a point with large scalar curvature. Not formalized; only the D7 matrix model of \
    the short-time layer exists."⟩,
  ⟨"PCN-3 curvature lower bound Rm >= -r0^{-2}",
   "The Riemann curvature tensor and its two-sided lower bound at scale r0. The pinned mathlib \
    has no curvature tensor; the bound is an opaque Prop field."⟩,
  ⟨"PCN-4 scalar curvature lower bound R >= r0^{-2}",
   "The scalar curvature of the marked point and the largeness hypothesis. The D7 RicciScalar \
    layer has an algebraic scalar curvature, not a manifold-level one; the bound is an opaque \
    Prop field."⟩,
  ⟨"PCN-5 kappa-noncollapsing at scale r0",
   "The volume comparison and the resulting uniform lower bound vol B(x, r0) >= kappa r0^3. \
    The D7 kappa layer is conditional and measure-theoretic; the certificate carries the \
    metric shadow MetricNoncollapsing."⟩,
  ⟨"PCN-6 ancient kappa-solution classification",
   "The classification of three-dimensional ancient kappa-solutions into the spherical and \
    cylindrical alternatives. Not formalized; it is the analytic heart of the theorem."⟩,
  ⟨"PCN-7 epsilon-neck condition",
   "Smooth C^{infinity} closeness of the region to the round cylinder S^2(r) x R, with \
    derivative bounds. The checked interface records the metric-shadow features (cross-section \
    antipodal distance pi r and the scalar curvature normalization 2/r^2)."⟩,
  ⟨"PCN-8 epsilon-cap condition",
   "Smooth C^{infinity} closeness to a round cap with a boundary collar that is an epsilon-neck. \
    The checked interface records the boundary distance r, the diameter bound pi r and the \
    scalar curvature normalization 6/r^2."⟩,
  ⟨"PCN-9 compact positively curved models",
   "The compact alternative: a closed 3-manifold of positive curvature, diffeomorphic to S^3 \
    or a quotient by a finite free isometric group action. The checked interface records the \
    round-sphere metric shadow; the diffeomorphism classification is not formalized."⟩,
  ⟨"PCN-10 blow-up and pointed Gromov-Hausdorff compactness",
   "The blow-up argument at a point of large scalar curvature, producing a pointed limit of \
    rescaled solutions. The D7 Compactness layer supplies the metric GH data and its \
    precompactness certificate; the manifold-level extraction and the smooth upgrade are \
    missing (see the Cheeger-Gromov blockers)."⟩,
  ⟨"PCN-11 quantitative scale r0(epsilon, kappa)",
   "The explicit positive function r0(epsilon, kappa) and the uniform constants of the \
    compactness argument. The state-only statement existentially quantifies the admissible \
    scale with r <= r0."⟩,
  ⟨"PCN-12 surgery-scale consistency",
   "The compatibility of the canonical neighborhood scale with the surgery parameters used \
    later in the program (the neck and cap alternatives are the ones cut and capped). Not \
    formalized; the surgery layer is statement-only."⟩
]

theorem perelmanCanonicalNeighborhoodDependencies_length :
    perelmanCanonicalNeighborhoodDependencies.length = 12 := rfl

theorem perelmanCanonicalNeighborhoodDependencies_ne_nil :
    perelmanCanonicalNeighborhoodDependencies ≠ [] := by
  simp [perelmanCanonicalNeighborhoodDependencies]

/-- Every listed dependency has a nonempty name and reason. -/
theorem perelmanCanonicalNeighborhoodDependencies_all_named :
    ∀ d ∈ perelmanCanonicalNeighborhoodDependencies, d.name ≠ "" ∧ d.reason ≠ "" := by
  simp [perelmanCanonicalNeighborhoodDependencies]

/-- **The six named blockers of Perelman's canonical neighborhood theorem.** -/
def perelmanCanonicalNeighborhoodBlockers : List String := [
  BlockerManifold,
  BlockerCurvature,
  BlockerNoncollapsing,
  BlockerAncient,
  BlockerSmoothCloseness,
  BlockerQuantitative
]

theorem perelmanCanonicalNeighborhoodBlockers_length :
    perelmanCanonicalNeighborhoodBlockers.length = 6 := rfl

theorem perelmanCanonicalNeighborhoodBlockers_ne_nil :
    perelmanCanonicalNeighborhoodBlockers ≠ [] := by
  simp [perelmanCanonicalNeighborhoodBlockers]

/-- Every named blocker is a nonempty string. -/
theorem perelmanCanonicalNeighborhoodBlockers_all_named :
    ∀ b ∈ perelmanCanonicalNeighborhoodBlockers, b ≠ "" := by
  simp [perelmanCanonicalNeighborhoodBlockers, BlockerManifold, BlockerCurvature,
    BlockerNoncollapsing, BlockerAncient, BlockerSmoothCloseness, BlockerQuantitative]

end

end Canonical
end D7
end Poincare
