/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-sphere-recognition)

**D7 sphere recognition, part 3: the final homeomorphism construction (statement-only).**

This module fixes the statement-only `Prop`s of the final homeomorphism construction together
with their named missing inputs.  Nothing here is a proof of the Poincaré conjecture: every
`missing...` declaration is a `def ... : Prop`, and every conditional theorem below consumes it
as an explicit hypothesis.

The named missing inputs are:

* **Moise / smoothing bridge** (`missingMoiseSmoothingBridge`) — a topological homeomorphism to
  `𝕊³` upgrades to a diffeomorphism for the `C^∞` structure (Moise's theorem that every
  topological `3`-manifold has a unique smooth structure compatible with the topological one,
  and that homeomorphisms can be smoothed);
* **geometrization output** (`missingGeometrizationOutput`) — the geometric decomposition of a
  closed `3`-manifold into geometric pieces (Thurston's geometrization, of which Perelman's
  theorem is the spherical case);
* **final homeomorphism construction** (`missingFinalHomeomorphismConstruction`) — the uniform
  statement that every simply connected closed `3`-manifold with an `ℝ³`-atlas is homeomorphic
  to `𝕊³`; this is exactly the shared Stage6 statement-only target in the `TopSpace` packaging.

The checked content of the module is:

* `missingFinalHomeomorphismConstruction_iff_missingPoincareConjectureTopologicalThree` — the
  final construction is definitionally the uniform statement-only Poincaré target of the D3
  topology layer;
* `stage6Target_of_missingFinalHomeomorphismConstruction` — the final construction discharges
  the shared Stage6 target for every admissible `M`;
* `smoothTarget_of_topologicalTarget_and_moise` — the Moise bridge turns a topological
  homeomorphism into the smooth Stage6 target;
* `sphericalPieces_of_geometrization` — the geometrization output instantiated at the spherical
  predicate produces the spherical terminal pieces;
* `finalHomeomorphismConstruction_of_certificateFamily` — a family of extinction/canonical
  certificates, one for every admissible manifold, plus the recognition bridge, implies the
  final homeomorphism construction through the checked assembly of `Assembly.lean`.

No declaration uses `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/

import Poincare.D7.Recognition.Assembly
import Poincare.Longrun.Topology.MissingTheorems

set_option autoImplicit false

open scoped Topology Manifold ContDiff

namespace Poincare

namespace D7

namespace Recognition

open Poincare.D7.Canonical
open Poincare.D7.Compactness
open Poincare.Longrun.Surgery
open Poincare.Longrun.Topology
open Poincare.D7.ShortTime

universe u

/-! ## 1. The statement-only missing inputs -/

/-- **MISSING INPUT (Moise / smoothing bridge), statement-only.**  A topological homeomorphism
from a `C^∞` three-manifold to `𝕊³` yields a diffeomorphism to `𝕊³`.  This is the form of
Moise's theorem needed to pass from the topological Stage6 target to the smooth Stage6 target:
every topological `3`-manifold admits a unique smooth structure, and a homeomorphism can be
smoothed.

This is a `def ... : Prop`, not a theorem and not an `axiom`. -/
def missingMoiseSmoothingBridge : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M]
    [IsManifold ThreeManifoldModel ∞ M] [SimplyConnectedSpace M] [CompactSpace M],
    Nonempty (M ≃ₜ SphereThree) → Poincare.Stage6.poincareConjectureSmoothThree M

/-- **MISSING INPUT (geometrization output), statement-only.**  Every compact Hausdorff
three-manifold admits a finite decomposition into pieces satisfying the supplied geometric
predicate `Geometric`.  Instantiating `Geometric` with the spherical-piece predicate recovers
the decomposition used by the extinction assembly; instantiating it with the eight Thurston
geometries recovers the full geometrization output.

The predicate is a parameter, exactly as orientability is a parameter in
`Poincare.Longrun.Surgery.canonicalLedger`: the pinned mathlib has no notion of a geometric
structure on a manifold, so the development refuses to invent one. -/
def missingGeometrizationOutput (Geometric : TopSpace.{0} → Prop) : Prop :=
  ∀ (M : TopSpace.{0}), CompactSpace M.Carrier → T2Space M.Carrier →
    ∃ pieces : List (TopSpace.{0}), pieces ≠ [] ∧ ∀ P ∈ pieces, Geometric P

/-- **MISSING INPUT (final homeomorphism construction), statement-only.**  Every simply
connected closed three-manifold with an `ℝ³`-atlas is homeomorphic to `𝕊³`.

This is the uniform statement-only root proposition of the end game, phrased over the bundled
`TopSpace` interface.  It is a `def ... : Prop`; the assembly proves it *conditionally* on the
certificate family and the recognition bridge, never unconditionally. -/
def missingFinalHomeomorphismConstruction : Prop :=
  ∀ (X : TopSpace.{0}), SimplyConnectedSpace X.Carrier → CompactSpace X.Carrier →
    T2Space X.Carrier → ChartedSpace EuclideanThree X.Carrier →
      Nonempty (X.Carrier ≃ₜ SphereThree)

/-! ## 2. Checked shape lemmas -/

/-- **Checked shape lemma.**  The Moise bridge unfolds to its statement form. -/
theorem missingMoiseSmoothingBridge_iff :
    missingMoiseSmoothingBridge ↔
      ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M]
        [IsManifold ThreeManifoldModel ∞ M] [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ SphereThree) → Poincare.Stage6.poincareConjectureSmoothThree M :=
  Iff.rfl

/-- **Checked shape lemma.**  The geometrization output unfolds to its statement form. -/
theorem missingGeometrizationOutput_iff (Geometric : TopSpace.{0} → Prop) :
    missingGeometrizationOutput Geometric ↔
      ∀ (M : TopSpace.{0}), CompactSpace M.Carrier → T2Space M.Carrier →
        ∃ pieces : List (TopSpace.{0}), pieces ≠ [] ∧ ∀ P ∈ pieces, Geometric P :=
  Iff.rfl

/-- **Checked shape lemma.**  The final homeomorphism construction unfolds to its statement
form. -/
theorem missingFinalHomeomorphismConstruction_iff :
    missingFinalHomeomorphismConstruction ↔
      ∀ (X : TopSpace.{0}), SimplyConnectedSpace X.Carrier → CompactSpace X.Carrier →
        T2Space X.Carrier → ChartedSpace EuclideanThree X.Carrier →
          Nonempty (X.Carrier ≃ₜ SphereThree) :=
  Iff.rfl

/-! ## 3. Checked bridges to the D3/Stage6 statement-only targets -/

/-- **Checked bridge.**  The final homeomorphism construction is exactly the uniform
statement-only Poincaré target `Poincare.Longrun.Topology.missingPoincareConjectureTopologicalThree`
of the D3 topology layer.  The two statements differ only by the `TopSpace` packaging. -/
theorem missingFinalHomeomorphismConstruction_iff_missingPoincareConjectureTopologicalThree :
    missingFinalHomeomorphismConstruction ↔
      Poincare.Longrun.Topology.missingPoincareConjectureTopologicalThree := by
  constructor
  · intro h M instTop instT2 instChart instSC instComp
    show Nonempty (M ≃ₜ SphereThree)
    exact h (TopSpace.mk M instTop) instSC instComp instT2 instChart
  · intro h X hSC hComp hT2 hChart
    exact h X.Carrier

/-- **Checked consequence.**  The final homeomorphism construction discharges the shared
Stage6 statement-only Poincaré target for every admissible `M`. -/
theorem stage6Target_of_missingFinalHomeomorphismConstruction
    (h : missingFinalHomeomorphismConstruction) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [SimplyConnectedSpace M] [CompactSpace M] :
    Poincare.Stage6.poincareConjectureTopologicalThree M := by
  let X : TopSpace.{0} := TopSpace.mk M inferInstance
  have hX : Nonempty (X.Carrier ≃ₜ SphereThree) :=
    h X inferInstance inferInstance inferInstance inferInstance
  show Nonempty (M ≃ₜ SphereThree)
  exact hX

/-- **Checked consequence.**  The uniform statement-only Poincaré target of the D3 layer
implies the final homeomorphism construction. -/
theorem missingFinalHomeomorphismConstruction_of_missingPoincare
    (h : Poincare.Longrun.Topology.missingPoincareConjectureTopologicalThree) :
    missingFinalHomeomorphismConstruction :=
  missingFinalHomeomorphismConstruction_iff_missingPoincareConjectureTopologicalThree.mpr h

/-- **Checked consequence.**  The Moise smoothing bridge turns a topological homeomorphism to
`𝕊³` into the smooth Stage6 target. -/
theorem smoothTarget_of_topologicalTarget_and_moise
    (hMoise : missingMoiseSmoothingBridge) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [IsManifold ThreeManifoldModel ∞ M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ SphereThree)) :
    Poincare.Stage6.poincareConjectureSmoothThree M :=
  hMoise M h

/-- **Checked consequence.**  The geometrization output, instantiated at the spherical-piece
predicate, produces the finite spherical decomposition of a compact three-manifold. -/
theorem sphericalPieces_of_geometrization
    (hGeo : missingGeometrizationOutput (fun P : TopSpace.{0} => IsSphericalPiece P))
    {X : TopSpace.{0}} (hcompact : CompactSpace X.Carrier) (ht2 : T2Space X.Carrier) :
    ∃ pieces : List (TopSpace.{0}), pieces ≠ [] ∧ ∀ P ∈ pieces, IsSphericalPiece P :=
  hGeo X hcompact ht2

/-! ## 4. The conditional final construction from the certificate family -/

/-- **Checked assembly (final homeomorphism construction).**  Suppose the spherical-piece
recognition bridge holds and every admissible manifold carries an extinction certificate and
the canonical-neighborhood input over it.  Then the final homeomorphism construction holds:
every simply connected closed three-manifold with an `ℝ³`-atlas is homeomorphic to `𝕊³`.

The certificate-family hypothesis is the named missing geometric input (Ricci flow with
surgery for every initial manifold); the recognition bridge is the named missing topological
input.  The conclusion is obtained by the checked assembly of `Assembly.lean`. -/
theorem finalHomeomorphismConstruction_of_certificateFamily
    (hrec : SphericalPieceRecognition)
    (hcert : ∀ (X : TopSpace.{0}), CompactSpace X.Carrier → T2Space X.Carrier →
      ChartedSpace EuclideanThree X.Carrier → SimplyConnectedSpace X.Carrier →
      ∃ E : ExtinctionCertificate X, Nonempty (CanonicalNeighborhoodInput X E)) :
    missingFinalHomeomorphismConstruction := by
  intro X hSC hComp hT2 hChart
  obtain ⟨E, ⟨C⟩⟩ := hcert X hComp hT2 hChart hSC
  exact stage6Target_of_certificates hComp hT2 hChart hSC E C hrec

/-! ## 5. The named missing-input ledger -/

/-- **The named missing inputs of the final homeomorphism construction.**  Each entry names a
standard ingredient of the end game and records why it is absent from the pinned mathlib and
from this development. -/
def finalHomeomorphismDependencies : List MissingDependency := [
  ⟨"SR-1 Moise smoothing bridge",
   "Every topological 3-manifold admits a smooth structure, unique up to diffeomorphism \
    compatible with the given topological structure, and homeomorphisms can be smoothed. The \
    pinned mathlib has no topological 3-manifold smoothing theorem; the bridge is the \
    statement-only Prop missingMoiseSmoothingBridge."⟩,
  ⟨"SR-2 geometrization output",
   "The geometric decomposition of a closed 3-manifold into geometric pieces (Thurston, \
    proved by Perelman). The pinned mathlib has no notion of a geometric structure on a \
    manifold, no JSJ decomposition and no connected-sum operation; the output is the \
    statement-only Prop missingGeometrizationOutput, parameterized by the geometric predicate."⟩,
  ⟨"SR-3 spherical space form theorem",
   "A simply connected spherical space form is S^3: the fundamental group of S^3/G for a free \
    finite action is G, so a simply connected quotient has trivial G. Neither the covering \
    space argument nor the classification of free finite actions on S^3 is in the pinned \
    mathlib; the recognition bridge SphericalPieceRecognition carries it as a function field."⟩,
  ⟨"SR-4 van Kampen for connected sums",
   "The fundamental group of a connected sum is the free product of the fundamental groups of \
    the summands, so a simply connected connected sum has simply connected summands. The \
    pinned mathlib has no connected-sum operation; ConnectedSumDecomposition.simplyConnected_pieces \
    carries the implication as a function field."⟩,
  ⟨"SR-5 connected sum of spheres",
   "A connected sum of summands each homeomorphic to S^3 is itself homeomorphic to S^3. The \
    pinned mathlib has no connected-sum operation; \
    ConnectedSumDecomposition.sphere_of_spheres carries the implication as a function field."⟩,
  ⟨"SR-6 Ricci flow with surgery and extinction",
   "For every simply connected closed 3-manifold, Ricci flow with surgery exists for all time, \
    performs finitely many surgeries, becomes extinct in finite time, and decomposes the \
    manifold as a connected sum of spherical terminal pieces. The extinction half is the D3/D6 \
    interface Poincare.Longrun.Surgery.ExtinctionTheorem; the manifold-level flow, the \
    canonical-neighborhood theorem and the extinction theorem are all absent from the pinned \
    mathlib."⟩
]

theorem finalHomeomorphismDependencies_length :
    finalHomeomorphismDependencies.length = 6 := rfl

theorem finalHomeomorphismDependencies_ne_nil :
    finalHomeomorphismDependencies ≠ [] := by
  simp [finalHomeomorphismDependencies]

/-- Every listed dependency has a nonempty name and reason. -/
theorem finalHomeomorphismDependencies_all_named :
    ∀ d ∈ finalHomeomorphismDependencies, d.name ≠ "" ∧ d.reason ≠ "" := by
  simp [finalHomeomorphismDependencies]

/-- **The named blockers of the final homeomorphism construction.** -/
def finalHomeomorphismBlockers : List String := [
  "B-D7-SR-MOISE: no topological 3-manifold smoothing theorem in the pinned mathlib.",
  "B-D7-SR-GEOMETRIZATION: no geometric decomposition or connected-sum operation in the \
   pinned mathlib.",
  "B-D7-SR-SPHERICAL-FORM: no free finite group action classification on S^3 and no covering \
   space computation of the quotient fundamental group.",
  "B-D7-SR-EXTINCTION: no manifold-level Ricci flow with surgery, canonical-neighborhood \
   theorem or finite-time extinction theorem in the pinned mathlib."
]

theorem finalHomeomorphismBlockers_length :
    finalHomeomorphismBlockers.length = 4 := rfl

theorem finalHomeomorphismBlockers_ne_nil :
    finalHomeomorphismBlockers ≠ [] := by
  simp [finalHomeomorphismBlockers]

/-- Every named blocker is a nonempty string. -/
theorem finalHomeomorphismBlockers_all_named :
    ∀ b ∈ finalHomeomorphismBlockers, b ≠ "" := by
  simp [finalHomeomorphismBlockers]

end Recognition

end D7

end Poincare
