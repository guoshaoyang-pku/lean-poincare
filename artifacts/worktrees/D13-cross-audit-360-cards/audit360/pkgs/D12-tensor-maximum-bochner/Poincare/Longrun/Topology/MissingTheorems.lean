/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D3-kappa-ledger)
-/
import Poincare.Longrun.Topology.Stage6Bridge

/-!
# Poincare.Longrun.Topology.MissingTheorems

**Statement-only ledger of the exact missing theorems** behind

* κ-non-collapsing (Perelman's no-local-collapsing theorem and its analytic inputs), and
* sphere recognition (the Poincaré conjecture and the missing `π₁(𝕊³) = 0` input).

Every declaration named `missing...` is a `def ... : Prop` (or a `def` with parameters
ending in `Prop`).  It is **not** a theorem and **not** a postulate or statement stub; it only fixes the
statement so that the remaining work is measurable.
Each missing statement is accompanied below by a checked shape lemma and, for the main
ones, by a checked consequence that consumes the missing theorem.

The statements are phrased over the interfaces of this layer
(`KappaNoncollapsingCertificate`, `NormalizedBallVolumeLowerBound`) and over the shared
Stage6 statement-only targets.  The mathematical content (which hypotheses a real proof
needs) is recorded in the result card, together with the exact analytic/algebraic-topology
theorems that are absent from mathlib.

No declaration in this file uses any forbidden construct: no unproved holes, no extra
logical postulates, no kernel bypasses, no native evaluation, no statement stubs.
-/

open scoped Manifold ContDiff Topology ENNReal
open MeasureTheory

namespace Poincare

namespace Longrun

namespace Topology

/-! ## 1. Missing theorems for κ-non-collapsing -/

/-- **MISSING THEOREM (κ-non-collapsing, Perelman 2002 §4, Theorem 4.1).**

Under the normalized Ricci-flow hypotheses `FlowHypotheses`, a κ-non-collapsing certificate
exists: there are `κ > 0` and `r₀ > 0` such that every ball of radius `r ≤ r₀` on which the
curvature is bounded by `r⁻²` has volume at least `κ r³`.

The hypotheses are an opaque `Prop` parameter because the flow itself is not formalized;
the conclusion is the certificate of `Poincare.Longrun.Topology.Noncollapsing`. -/
def missingKappaNoncollapsing {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M) (FlowHypotheses : Prop) : Prop :=
  FlowHypotheses → ∃ κ r₀ : ℝ, KappaNoncollapsingCertificate M μ K κ r₀

/-- **MISSING THEOREM (normalized-volume form of κ-non-collapsing).**

The same theorem with the conclusion in normalized-volume form
`κ ≤ μ(B(x,r))/r³`; by `kappaNoncollapsingCertificate_iff_normalizedBallVolumeLowerBound`
this is *equivalent* to `missingKappaNoncollapsing`, which is checked below. -/
def missingNormalizedNoLocalCollapsing {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M) (FlowHypotheses : Prop) : Prop :=
  FlowHypotheses → ∃ κ r₀ : ℝ, NormalizedBallVolumeLowerBound M μ K κ r₀

/-- **MISSING THEOREM (entropy route to non-collapsing).**

Perelman's derivation of non-collapsing from the monotonicity of `μ` (equivalently `W`)
along the flow, together with the normalization of the initial metric.  `MuMonotone`
records the entropy-monotonicity hypothesis abstractly. -/
def missingKappaNoncollapsingOfMuMonotonicity {M : Type*} [PseudoEMetricSpace M]
    [MeasurableSpace M] (μ : Measure M) (K : CurvatureBoundedOn M)
    (MuMonotone : Prop) (FlowHypotheses : Prop) : Prop :=
  MuMonotone → FlowHypotheses → ∃ κ r₀ : ℝ, KappaNoncollapsingCertificate M μ K κ r₀

/-- **MISSING THEOREM (reduced-volume monotonicity, Perelman 2002 §7).**

Perelman's reduced volume `Ṽ(τ)` is non-increasing along the flow.  The construction of
`Ṽ` (reduced length, its minimizers, and the Jacobian comparison) is itself missing; this
statement fixes only the monotonicity half, over a supplied function `V`. -/
def missingReducedVolumeMonotonicity (V : ℝ → ℝ) (T : Set ℝ) : Prop :=
  AntitoneOn V T

/-- **MISSING THEOREM (conjugate heat kernel, Perelman 2002 §6–7).**

Existence of the conjugate heat kernel used to define `W`, the reduced length and the
reduced volume: a measurable family `u τ` of unit total mass.  The parabolic regularity
and the conjugate heat equation are *not* asserted here; they are part of the missing
analytic content recorded in the result card. -/
def missingConjugateHeatKernel {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (FlowHypotheses : Prop) : Prop :=
  FlowHypotheses → ∃ u : ℝ → M → ℝ,
    (∀ τ : ℝ, 0 < τ → Measurable (u τ)) ∧
      (∀ τ : ℝ, 0 < τ → ∫ x, u τ x ∂μ = 1)

/-- **MISSING THEOREM (persistence of κ under surgery, Perelman 2003 §4).**

A manifold that is κ-non-collapsing before a surgery remains non-collapsing (possibly with
a smaller constant and scale) after the surgery, under the surgery hypotheses. -/
def missingKappaPersistenceUnderSurgery {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M) (SurgeryHypotheses : Prop) (κ r₀ : ℝ) : Prop :=
  SurgeryHypotheses → KappaNoncollapsingCertificate M μ K κ r₀ →
    ∃ κ' r₀' : ℝ, KappaNoncollapsingCertificate M μ K κ' r₀'

/-- **MISSING THEOREM (canonical neighbourhood theorem, Perelman 2003 §3).**

Every point of sufficiently high curvature in a three-dimensional κ-solution is
ε-close (after scaling) to a model geometry.  The statement needs a pointed
Gromov–Hausdorff/ε-close-to-model predicate that mathlib does not have, so only the
existence of a canonical-neighbourhood predicate is fixed here. -/
def missingCanonicalNeighborhoodTheorem (M : Type*) (Canonical : M → Prop)
    (HighCurvature : M → Prop) : Prop :=
  ∀ x : M, HighCurvature x → Canonical x

/-! ### Checked companions for the κ statements -/

/-- **Checked shape lemma.** `missingKappaNoncollapsing` unfolds to its interface form. -/
theorem missingKappaNoncollapsing_iff {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M) (FlowHypotheses : Prop) :
    missingKappaNoncollapsing μ K FlowHypotheses ↔
      (FlowHypotheses → ∃ κ r₀ : ℝ, KappaNoncollapsingCertificate M μ K κ r₀) :=
  Iff.rfl

/-- **Checked shape lemma.** The normalized form unfolds to its interface form. -/
theorem missingNormalizedNoLocalCollapsing_iff {M : Type*} [PseudoEMetricSpace M]
    [MeasurableSpace M] (μ : Measure M) (K : CurvatureBoundedOn M) (FlowHypotheses : Prop) :
    missingNormalizedNoLocalCollapsing μ K FlowHypotheses ↔
      (FlowHypotheses → ∃ κ r₀ : ℝ, NormalizedBallVolumeLowerBound M μ K κ r₀) :=
  Iff.rfl

/-- **Checked consequence.** The absolute and normalized statements of the missing
non-collapsing theorem are equivalent, by the interface equivalence proved in
`Poincare.Longrun.Topology.NormalizedVolume`. -/
theorem missingKappaNoncollapsing_iff_missingNormalizedNoLocalCollapsing
    {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M) (FlowHypotheses : Prop) :
    missingKappaNoncollapsing μ K FlowHypotheses ↔
      missingNormalizedNoLocalCollapsing μ K FlowHypotheses := by
  constructor
  · intro h hFlow
    obtain ⟨κ, r₀, hcert⟩ := h hFlow
    exact ⟨κ, r₀, hcert.toNormalizedBallVolumeLowerBound⟩
  · intro h hFlow
    obtain ⟨κ, r₀, hnv⟩ := h hFlow
    exact ⟨κ, r₀, hnv.toKappaNoncollapsingCertificate⟩

/-- **Checked consequence.** The missing theorem, once proved, produces the certificate
interface for any flow satisfying the flow hypotheses. -/
theorem kappaCertificate_of_missingKappaNoncollapsing {M : Type*} [PseudoEMetricSpace M]
    [MeasurableSpace M] {μ : Measure M} {K : CurvatureBoundedOn M} {FlowHypotheses : Prop}
    (h : missingKappaNoncollapsing μ K FlowHypotheses) (hFlow : FlowHypotheses) :
    ∃ κ r₀ : ℝ, KappaNoncollapsingCertificate M μ K κ r₀ :=
  h hFlow

/-- **Checked consequence.** The missing theorem, once proved, yields a certificate whose
constant bounds every unit ball below as soon as the certificate's scale is at least `1`. -/
theorem unit_ball_lower_bound_of_missingKappaNoncollapsing
    {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    {μ : Measure M} {K : CurvatureBoundedOn M} {FlowHypotheses : Prop}
    (h : missingKappaNoncollapsing μ K FlowHypotheses) (hFlow : FlowHypotheses)
    (hK : ∀ x : M, K x 1) :
    ∃ κ r₀ : ℝ, KappaNoncollapsingCertificate M μ K κ r₀ ∧
      ((1 : ℝ) ≤ r₀ → ∀ x : M, ENNReal.ofReal κ ≤ μ (Metric.eball x 1)) := by
  obtain ⟨κ, r₀, hcert⟩ := h hFlow
  exact ⟨κ, r₀, hcert, fun hr₀ x => hcert.volume_unit_ball_lower hr₀ (hK x)⟩

/-! ## 2. Missing theorems for sphere recognition -/

-- The uniform missing statements below are stated at universe level `0` (`Type`), which
-- is where all concrete model spaces of this development live.  Per-manifold forms can
-- be stated at any universe level through the parameterized definitions.

/-- **MISSING THEOREM.** The unit `3`-sphere is simply connected.  This is the missing
input that certifies `𝕊³` itself as a member of the class recognized by the Poincaré
theorem; it is also the `n = 3` case of the missing computation `π₁(𝕊ⁿ) = 0` for `n ≥ 2`. -/
def missingSphereThreeSimplyConnected : Prop :=
  SimplyConnectedSpace SphereThree

/-- **MISSING THEOREM.** `π₁(𝕊³) = 0`, in pointwise form; equivalent to
`missingSphereThreeSimplyConnected` by the shared Stage6 reduction. -/
def missingSphereThreePiOneTrivial : Prop :=
  ∀ x : SphereThree, Subsingleton (π_ 1 SphereThree x)

/-- **MISSING THEOREM (Poincaré conjecture, topological form).**

Every compact `3`-manifold that is simply connected is homeomorphic to `𝕊³`.  This is the
uniform version of the shared Stage6 statement-only target
`Poincare.Stage6.poincareConjectureTopologicalThree`. -/
def missingPoincareConjectureTopologicalThree : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M]
    [SimplyConnectedSpace M] [CompactSpace M],
    Poincare.Stage6.poincareConjectureTopologicalThree M

/-- **MISSING THEOREM (Poincaré conjecture, smooth form).** The same statement with a
`C^∞` structure and the conclusion that the homeomorphism can be chosen a diffeomorphism;
uniform version of `Poincare.Stage6.poincareConjectureSmoothThree`. -/
def missingPoincareConjectureSmoothThree : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M]
    [IsManifold ThreeManifoldModel ∞ M] [SimplyConnectedSpace M] [CompactSpace M],
    Poincare.Stage6.poincareConjectureSmoothThree M

/-- **MISSING THEOREM (sphere recognition algorithm, Rubinstein–Thompson).**

There is a decision procedure that, for every compact `3`-manifold, decides whether it is
homeomorphic to `𝕊³`.  Stated as `Nonempty (Decidable _)` so that it is a proposition. -/
def missingSphereRecognitionAlgorithm : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M]
    [CompactSpace M], Nonempty (Decidable (Nonempty (M ≃ₜ SphereThree)))

/-! ### Checked companions for the sphere-recognition statements -/

/-- **Checked shape lemma.** The missing `𝕊³` simple-connectivity theorem is exactly the
Stage6 statement-only target `Poincare.Stage6.sphereThreeSimplyConnected`. -/
theorem missingSphereThreeSimplyConnected_iff_stage6 :
    missingSphereThreeSimplyConnected ↔ Poincare.Stage6.sphereThreeSimplyConnected :=
  Iff.rfl

/-- **Checked shape lemma.** The missing `π₁(𝕊³) = 0` theorem is exactly the Stage6
statement-only target `Poincare.Stage6.sphereThreePiOneTrivial`. -/
theorem missingSphereThreePiOneTrivial_iff_stage6 :
    missingSphereThreePiOneTrivial ↔ Poincare.Stage6.sphereThreePiOneTrivial :=
  Iff.rfl

/-- **Checked shape lemma.** The uniform Poincaré statement unfolds to the Stage6 alias
under the same typeclass hypotheses. -/
theorem missingPoincareConjectureTopologicalThree_iff :
    missingPoincareConjectureTopologicalThree ↔
      ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M]
        [SimplyConnectedSpace M] [CompactSpace M],
        Poincare.Stage6.poincareConjectureTopologicalThree M :=
  Iff.rfl

/-- **Checked consequence.** The missing uniform Poincaré theorem, once proved, discharges
the shared Stage6 statement-only target for every admissible `M`. -/
theorem stage6Target_of_missingPoincareConjectureTopologicalThree
    (h : missingPoincareConjectureTopologicalThree) {M : Type} [TopologicalSpace M]
    [T2Space M] [ChartedSpace EuclideanThree M] [SimplyConnectedSpace M] [CompactSpace M] :
    Poincare.Stage6.poincareConjectureTopologicalThree M :=
  h M

/-- **Checked consequence.** The missing sphere-recognition algorithm would in particular
decide the conclusion of the Poincaré theorem for every compact `3`-manifold. -/
theorem decidableSphereRecognition_of_missingSphereRecognitionAlgorithm
    (h : missingSphereRecognitionAlgorithm) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [CompactSpace M] :
    Nonempty (Decidable (Nonempty (M ≃ₜ SphereThree))) :=
  h M

/-- **Checked consequence.** The missing `𝕊³` simple-connectivity theorem, together with
the checked Stage6 reduction, reduces to path connectivity (already proved in Stage6) and
trivial fundamental groups (still missing). -/
theorem missingSphereThreeSimplyConnected_iff_pathConnected_and_fundamentalGroup :
    missingSphereThreeSimplyConnected ↔
      PathConnectedSpace SphereThree ∧
        ∀ x : SphereThree, Subsingleton (FundamentalGroup SphereThree x) :=
  Poincare.Stage6.simplyConnectedSpace_iff_pathConnectedSpace_and_subsingleton_fundamentalGroup
    (X := SphereThree)

/-- **Checked consequence.** The missing `𝕊³` simple-connectivity and `π₁(𝕊³) = 0`
statements are equivalent. -/
theorem missingSphereThreeSimplyConnected_iff_piOneTrivial :
    missingSphereThreeSimplyConnected ↔ missingSphereThreePiOneTrivial :=
  Poincare.Stage6.sphereThreePiOneTrivial_iff_simplyConnected.symm

end Topology

end Longrun

end Poincare
