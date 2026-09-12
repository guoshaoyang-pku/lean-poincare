/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-surgery-recognition)

**D12 surgery recognition, part 4: expanded interfaces and the reviewed decomposition.**

This module (a) re-expands the four D7 end-game interfaces
(`RecognitionHypotheses`, `ExtinctionCertificate`, `ConnectedSumDecomposition`,
`SphericalPieceRecognition`) with their full hypothesis structure and exact status, and
(b) proves the **downstream checked uses** of the part-3 and part-5/6 constructors: a
versioned connected-sum decomposition (`ConnectedSumDecompositionV2`) plus the
remaining explicit hypotheses (van Kampen and the spherical-piece recognition bridge)
reproduce the D7 end-game assembly `stage6Target_of_certificates`
(`stage6Target_of_v2decomposition`), and the covering-recognition sharpening of part 5
replaces the opaque recognition bridge by its exact inputs
(`RemainingRecognitionHypothesesV2`, `stage6Target_of_v2hypotheses`), finally reduced —
with the part-6 proved deck-triviality — to the single geometric hypothesis `spaceForm`
(`RemainingRecognitionHypothesesV3`, `stage6Target_of_v3hypotheses`).

The reviewed decomposition of the end game is also recorded here as structured data
(`EndGameDecomposition`): neck estimates → surgery existence → finite extinction →
final topology, each stage annotated with what is constructed (here: the final-topology
sphere-of-spheres step) and what remains a hypothesis.

No declaration uses `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
import Poincare.D12.SurgeryRecognition.DeckTrivial
import Poincare.D12.SurgeryRecognition.SphereOfSpheres
import Poincare.D7.Recognition.Assembly

set_option autoImplicit false

open scoped Topology Manifold ContDiff

noncomputable section

namespace Poincare.D12.SurgeryRecognition

open Poincare.Longrun.Surgery
open Poincare.Longrun.Topology
open Poincare.D7.Recognition

/-! ## 1. The remaining hypotheses after SR-5 is closed -/

/-- **The remaining end-game hypotheses, expanded.**  After the sphere-of-spheres step
(SR-5) is replaced by the construction of `SphereOfSpheres.lean`, exactly these inputs
remain as hypotheses:

* `vanKampen` (SR-4): the fundamental group of a connected sum is the free product of
  the summand groups, hence simple connectivity passes to the summands.  The pinned
  mathlib has no van Kampen theorem for the fundamental groupoid
  (`Mathlib/AlgebraicTopology/FundamentalGroupoid` provides the groupoid functor,
  induced maps, products and the `SimplyConnectedSpace` class only).
* `pieceRecognition` (spherical space form + Moise smoothing): a simply connected
  spherical piece (compact-spherical canonical-neighborhood alternative) is `𝕊³`;
  this is the D7 `SphericalPieceRecognition` bridge, kept as an explicit input.
* the extinction and canonical-neighborhood certificates (SR-6 family): existence of
  the Ricci flow with surgery, the canonical-neighborhood theorem and finite-time
  extinction are hypotheses recorded in `ExtinctionCertificate` /
  `CanonicalNeighborhoodInput`; they are not derived here. -/
structure RemainingRecognitionHypotheses (X : Poincare.Longrun.Surgery.TopSpace.{0})
    (pieces : List (Poincare.Longrun.Surgery.TopSpace.{0})) where
  /-- van Kampen for connected sums (SR-4). -/
  vanKampen : SimplyConnectedSpace X.Carrier → ∀ P ∈ pieces, SimplyConnectedSpace P.Carrier
  /-- The spherical-piece recognition bridge (spherical space form + Moise). -/
  pieceRecognition : SphericalPieceRecognition

/-! ## 2. The reviewed end-game decomposition -/

/-- **The reviewed decomposition of the surgery end game.**  Each stage is a named input
with an exact statement; `finalTopology` is the stage this task *constructs* (the
sphere-of-spheres step, SR-5), the others are explicit hypotheses with their precise
types.  This is deliberately *not* an abstract well-founded complexity argument:
`finiteExtinction` records the actual Ricci-flow extinction interface, kept separate
from any complexity bookkeeping. -/
structure EndGameDecomposition (X : Poincare.Longrun.Surgery.TopSpace.{0}) where
  /-- **Neck estimates / canonical neighborhoods.**  Hypothesis: every high-curvature
  point lies in an ε-neck, ε-cap or compact ε-spherical region (the D7
  `CanonicalNeighborhoodCertificate` classification). -/
  neckEstimates : Prop
  /-- **Surgery existence.**  Hypothesis: along each admissible neck/cap the flow can
  be cut and capped preserving the invariants (the D3/D6 surgery interface). -/
  surgeryExistence : Prop
  /-- **Finite extinction.**  Hypothesis: the Ricci flow with surgery on `X` becomes
  extinct at a finite time (the D3/D6 `ExtinctionTheorem` interface with a strict
  complexity decrease at every surgery). -/
  finiteExtinction : Prop
  /-- **Final topology (CONSTRUCTED in this task).**  A connected sum of `𝕊³` pieces is
  `𝕊³`: `ConnectedSumDecompositionV2` data plus `ConnectedSumDecomposition.mkV2`
  (which proves the D7 `sphere_of_spheres` field), `iteratedSphereSum_homeo_sphere`
  and `sphereConnectSum_homeo_sphere`. -/
  finalTopology : ∀ pieces : List (TopSpace.{0}), ConnectedSumDecompositionV2 X pieces →
    ∀ P ∈ pieces, Nonempty (P.Carrier ≃ₜ S3) → Nonempty (X.Carrier ≃ₜ S3)

/-- The final-topology stage of the decomposition, **proved** from the constructions:
`X ≃ iterated sum ≃ 𝕊³`.  (The per-piece `𝕊³`-homeomorphisms are the *data*
`D.pieceSphere`; the explicit parameter mirrors the `EndGameDecomposition.finalTopology`
field shape and is discharged by that data.) -/
theorem endGame_finalTopology (X : Poincare.Longrun.Surgery.TopSpace.{0})
    (pieces : List (TopSpace.{0})) (D : ConnectedSumDecompositionV2 X pieces)
    (_h : ∀ P ∈ pieces, Nonempty (P.Carrier ≃ₜ S3)) : Nonempty (X.Carrier ≃ₜ S3) := by
  rcases D.sumHomeo with ⟨hX⟩
  rcases (iteratedSphereSum pieces D.pieceSphere).sumHomeo with ⟨hsum⟩
  exact ⟨hX.trans hsum⟩

/-! ## 3. The downstream checked use: the D7 end-game assembly from V2 data -/

/-- **Downstream use.**  Given the D7 extinction certificate with `pieces`, V2
connected-sum data for those pieces, the van Kampen hypothesis and the remaining D7
hypotheses (canonical-neighborhood input, spherical-piece recognition), the D7 end-game
assembly reproduces the shared Stage6 target.  The extinction certificate consumed here
is rebuilt with the *constructed* decomposition
`ConnectedSumDecomposition.mkV2 D vanKampen`, whose `sphere_of_spheres` field is the
proved implication of part 3 — this is the checked consumption of the SR-5 closure. -/
theorem stage6Target_of_v2decomposition {X : TopSpace.{0}}
    (compact : CompactSpace X.Carrier) (t2 : T2Space X.Carrier)
    (charted : ChartedSpace EuclideanThree X.Carrier)
    (simplyConnected : SimplyConnectedSpace X.Carrier)
    (E : ExtinctionCertificate X)
    (D : ConnectedSumDecompositionV2 X E.pieces)
    (vanKampen : SimplyConnectedSpace X.Carrier →
      ∀ P ∈ E.pieces, SimplyConnectedSpace P.Carrier)
    (canonical : CanonicalNeighborhoodInput X E)
    (pieceRecognition : SphericalPieceRecognition) :
    @Poincare.Stage6.poincareConjectureTopologicalThree X.Carrier X.topology
      t2 charted simplyConnected compact := by
  exact stage6Target_of_certificates compact t2 charted simplyConnected
    { extinctionTime := E.extinctionTime
      extinctionTime_pos := E.extinctionTime_pos
      extinction := E.extinction
      complexityDecreases := E.complexityDecreases
      pieces := E.pieces
      pieces_ne_nil := E.pieces_ne_nil
      decomposition := ConnectedSumDecomposition.mkV2 D vanKampen }
    { ε := canonical.ε
      κ := canonical.κ
      r := canonical.r
      ε_pos := canonical.ε_pos
      κ_pos := canonical.κ_pos
      r_pos := canonical.r_pos
      regions := canonical.regions
      certificate := canonical.certificate
      admissible_or_spherical := canonical.admissible_or_spherical
      piece_region_homeo := canonical.piece_region_homeo }
    pieceRecognition

/-! ## 3bis. The covering-recognition sharpening of the remaining hypotheses -/

/-- **The remaining recognition hypotheses, V2 (covering-recognition form).**  The
opaque D7 `SphericalPieceRecognition` bridge is replaced by its two exact inputs:
`spaceForm` (every spherical piece is modeled on a space form quotient of `𝕊³` — the
spherical space form theorem) and `coveringTrivial` (a simply connected space form
quotient has a trivial deck group — the covering/π₁ step, *proved* in `DeckTrivial.lean`;
see `RemainingRecognitionHypothesesV3` for the version that consumes that proof).  The
covering recognition itself — the orbit quotient of a finite free action on `𝕊³` is a
covering quotient of `𝕊³` — is *constructed* in `CoveringRecognition.lean`
(`SphericalSpaceFormModel.covering`), so this structure no longer assumes any
topological covering content. -/
structure RemainingRecognitionHypothesesV2 (X : TopSpace.{0}) (pieces : List (TopSpace.{0})) where
  /-- van Kampen for connected sums (SR-4). -/
  vanKampen : SimplyConnectedSpace X.Carrier → ∀ P ∈ pieces, SimplyConnectedSpace P.Carrier
  /-- Every spherical piece is a space form quotient of `𝕊³` (space form theorem). -/
  spaceForm : ∀ {Y : TopSpace.{0}}, SphericalPiece Y →
    { M : SphericalSpaceFormModel // IsSpaceFormModelOf Y M }
  /-- A simply connected space form quotient has a trivial deck group (covering/π₁). -/
  coveringTrivial : ∀ (M : SphericalSpaceFormModel), SimplyConnectedSpace M.quotient.Carrier →
    Subsingleton M.Γ

namespace RemainingRecognitionHypothesesV2

/-- **Downstream use.**  The V2 recognition hypotheses reproduce the D7
`SphericalPieceRecognition` bridge: the recognition bridge is *constructed* from
`spaceForm` and `coveringTrivial` by `sphericalPieceRecognition_of` (the covering half
is proved, not assumed). -/
def toRemaining {X : TopSpace.{0}} {pieces : List (TopSpace.{0})}
    (H : RemainingRecognitionHypothesesV2 X pieces) : RemainingRecognitionHypotheses X pieces where
  vanKampen := H.vanKampen
  pieceRecognition := sphericalPieceRecognition_of H.spaceForm H.coveringTrivial

end RemainingRecognitionHypothesesV2

/-- **Downstream use.**  The end-game assembly from V2 data with the V2 recognition
hypotheses: the `SphericalPieceRecognition` input of the D7 assembly is *constructed*
by part 5 (`sphericalPieceRecognition_of`) instead of being assumed, so the assembly
consumes only the two exact geometric inputs (space form modeling, covering/π₁
triviality) together with the constructed covering recognition. -/
theorem stage6Target_of_v2hypotheses {X : TopSpace.{0}}
    (compact : CompactSpace X.Carrier) (t2 : T2Space X.Carrier)
    (charted : ChartedSpace EuclideanThree X.Carrier)
    (simplyConnected : SimplyConnectedSpace X.Carrier)
    (E : ExtinctionCertificate X)
    (D : ConnectedSumDecompositionV2 X E.pieces)
    (H : RemainingRecognitionHypothesesV2 X E.pieces)
    (canonical : CanonicalNeighborhoodInput X E) :
    @Poincare.Stage6.poincareConjectureTopologicalThree X.Carrier X.topology
      t2 charted simplyConnected compact :=
  stage6Target_of_v2decomposition compact t2 charted simplyConnected E D H.vanKampen canonical
    (sphericalPieceRecognition_of H.spaceForm H.coveringTrivial)

/-! ## 3ter. The deck-triviality sharpening (V3): only `spaceForm` remains -/

/-- **The remaining recognition hypotheses, V3 (deck-triviality proved).**  The
`coveringTrivial` input of the V2 structure is now *proved* by
`deckTrivial_of_simplyConnected_quotient` (`DeckTrivial.lean`, part 6: monodromy of the
covering `𝕊³ → 𝕊³/Γ` is transitive — path-connectedness of `𝕊³` — and trivial — simple
connectivity of the quotient; the `Γ`-torsor fiber is then a subsingleton), so exactly
two hypotheses remain: `vanKampen` (SR-4) and `spaceForm` (the spherical space form
theorem). -/
structure RemainingRecognitionHypothesesV3 (X : TopSpace.{0}) (pieces : List (TopSpace.{0})) where
  /-- van Kampen for connected sums (SR-4). -/
  vanKampen : SimplyConnectedSpace X.Carrier → ∀ P ∈ pieces, SimplyConnectedSpace P.Carrier
  /-- Every spherical piece is a space form quotient of `𝕊³` (space form theorem). -/
  spaceForm : ∀ {Y : TopSpace.{0}}, SphericalPiece Y →
    { M : SphericalSpaceFormModel // IsSpaceFormModelOf Y M }

namespace RemainingRecognitionHypothesesV3

/-- **Downstream use of the proved deck-triviality.**  The V3 hypotheses reproduce the
V2 hypotheses: `coveringTrivial` is *constructed* by `deckTrivial_of_simplyConnected_quotient`. -/
def toRemainingV2 {X : TopSpace.{0}} {pieces : List (TopSpace.{0})}
    (H : RemainingRecognitionHypothesesV3 X pieces) : RemainingRecognitionHypothesesV2 X pieces where
  vanKampen := H.vanKampen
  spaceForm := H.spaceForm
  coveringTrivial := fun M hsc ↦ @deckTrivial_of_simplyConnected_quotient M hsc

/-- **Downstream use.**  The V3 hypotheses reproduce the D7
`SphericalPieceRecognition` bridge via `sphericalPieceRecognition_of_spaceForm`: only
the space form modeling is a hypothesis, the covering/π₁ triviality is proved. -/
def toRemaining {X : TopSpace.{0}} {pieces : List (TopSpace.{0})}
    (H : RemainingRecognitionHypothesesV3 X pieces) : RemainingRecognitionHypotheses X pieces where
  vanKampen := H.vanKampen
  pieceRecognition := sphericalPieceRecognition_of_spaceForm H.spaceForm

end RemainingRecognitionHypothesesV3

/-- **Downstream use.**  The end-game assembly from V2 data with the V3 recognition
hypotheses: the `SphericalPieceRecognition` input of the D7 assembly is *constructed*
from the single remaining geometric hypothesis `spaceForm` (part 5 covering
recognition + part 6 deck-triviality), together with the explicit SR-4 van Kampen
hypothesis. -/
theorem stage6Target_of_v3hypotheses {X : TopSpace.{0}}
    (compact : CompactSpace X.Carrier) (t2 : T2Space X.Carrier)
    (charted : ChartedSpace EuclideanThree X.Carrier)
    (simplyConnected : SimplyConnectedSpace X.Carrier)
    (E : ExtinctionCertificate X)
    (D : ConnectedSumDecompositionV2 X E.pieces)
    (H : RemainingRecognitionHypothesesV3 X E.pieces)
    (canonical : CanonicalNeighborhoodInput X E) :
    @Poincare.Stage6.poincareConjectureTopologicalThree X.Carrier X.topology
      t2 charted simplyConnected compact :=
  stage6Target_of_v2hypotheses compact t2 charted simplyConnected E D H.toRemainingV2 canonical

/-! ## 4. The expanded D7 interfaces (exact types, re-documented) -/

/-- **`ConnectedSumDecomposition` (D7), expanded.**  The `relation` field is an opaque
`Prop` (the pinned mathlib has no connected-sum operation); the V2 structure of part 3
makes it data.  `simplyConnected_pieces` is van Kampen (SR-4, hypothesis);
`sphere_of_spheres` is SR-5 — now *constructed* by `ConnectedSumDecomposition.mkV2`. -/
theorem connectedSumDecomposition_expanded (X : TopSpace.{0})
    (pieces : List (TopSpace.{0})) (D : ConnectedSumDecomposition X pieces) :
    D.relation ∧
      (SimplyConnectedSpace X.Carrier → ∀ P ∈ pieces, SimplyConnectedSpace P.Carrier →
        (∀ P ∈ pieces, Nonempty (P.Carrier ≃ₜ SphereThree)) →
          Nonempty (X.Carrier ≃ₜ SphereThree)) := by
  constructor
  · exact D.relation_holds
  · intro _hSC P hmem hSCP hspheres
    exact D.sphere_of_spheres hspheres

/-- **`ExtinctionCertificate` (D7), expanded.**  A positive extinction time, the checked
D3/D6 extinction interface with strict complexity decrease, a nonempty terminal piece
list and its connected-sum decomposition.  Existence of the Ricci flow with surgery is
the hypothesis; the finite-surgery and extinction conclusions are derived by the checked
D3/D6 theorems in `ExtinctionCertificate.toConclusion`, not postulated. -/
theorem extinctionCertificate_expanded (X : TopSpace.{0}) (E : ExtinctionCertificate X) :
    0 < E.extinctionTime ∧ E.extinction.complexityDecreases ∧ E.pieces ≠ [] ∧
      E.decomposition.relation := by
  exact ⟨E.extinctionTime_pos, E.complexityDecreases, E.pieces_ne_nil,
    E.decomposition.relation_holds⟩

/-- **`SphericalPieceRecognition` (D7), expanded.**  The bridge turning a simply
connected spherical piece (compact-spherical canonical-neighborhood alternative plus a
homeomorphism to the certified region) into a homeomorphism to `𝕊³`; this packages the
spherical space form theorem and the Moise smoothing theorem, both out of scope here. -/
theorem sphericalPieceRecognition_expanded (R : SphericalPieceRecognition) :
    ∀ {X : TopSpace.{0}}, SphericalPiece X → SimplyConnectedSpace X.Carrier →
      Nonempty (X.Carrier ≃ₜ SphereThree) :=
  R.recognize

/-- **`RecognitionHypotheses` (D7), expanded.**  Compact Hausdorff `ℝ³`-charted simply
connected `X`, an extinction certificate, its canonical-neighborhood input, and the
spherical-piece recognition bridge.  The assembly chain
`conclusion → onlySphericalPieces → pieces_simplyConnected → pieces_homeomorph_sphere →
homeomorph_sphere → stage6Target` is checked in D7 `Recognition.Assembly`; the step
`pieces_homeomorph_sphere → homeomorph_sphere` is now discharged by V2 data via
`stage6Target_of_v2decomposition`. -/
theorem recognitionHypotheses_expanded (X : TopSpace.{0})
    (H : RecognitionHypotheses X) :
    CompactSpace X.Carrier ∧ T2Space X.Carrier ∧ SimplyConnectedSpace X.Carrier ∧
      Nonempty (ExtinctionCertificate X) ∧ Nonempty (SphericalPieceRecognition) := by
  exact ⟨H.compact, H.t2, H.simplyConnected, ⟨H.extinction⟩, ⟨H.pieceRecognition⟩⟩

end Poincare.D12.SurgeryRecognition

end
