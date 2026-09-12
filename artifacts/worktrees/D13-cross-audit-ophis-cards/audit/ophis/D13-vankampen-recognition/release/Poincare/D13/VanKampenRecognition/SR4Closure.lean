/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-vankampen-recognition)

**D13 van Kampen recognition, part 4: SR-4 is closed and consumed by the Stage6
end-game assembly.**

The D7 ledger field `ConnectedSumDecomposition.simplyConnected_pieces` (the van
Kampen missing input SR-4) is replaced by a theorem for the D12 V2
decomposition: every piece of a V2 decomposition carries a homeomorphism to
`𝕊³`, and `𝕊³` is simply connected (`sphereThree_simplyConnectedSpace`, the van
Kampen computation of part 3), so every piece is simply connected — with no
use of the ambient hypothesis at all (the conclusion is strictly stronger than
the assumed field).

* `simplyConnected_of_homeo_sphere` — simple connectivity is transported along
  a homeomorphism to `𝕊³` (via mathlib's homotopy-equivalence transport);
* `simplyConnectedPieces_of_v2` — **SR-4 closure**: the van Kampen field of the
  D7 `ConnectedSumDecomposition` is *proved* for the V2 data;
* `ConnectedSumDecomposition.mkV2Complete` — the genuine D7 decomposition with
  **both** missing-input fields proved (`sphere_of_spheres` from D12's
  `iteratedSphereSum_homeo_sphere`, `simplyConnected_pieces` from this task);
* `RemainingRecognitionHypothesesV4` — after SR-4 and SR-5 the recognition
  chain carries exactly **one** geometric hypothesis: `spaceForm` (every
  spherical piece is modeled on a space form quotient of `𝕊³`; the covering
  and deck-triviality halves are the D12 theorems
  `sphericalPieceRecognition_of_spaceForm`);
* `stage6Target_of_v4hypotheses` — **downstream checked use**: the D7 end-game
  assembly `stage6Target_of_certificates` reproduces the shared Stage6 target
  from the V2 decomposition data, the V4 hypotheses (space form modeling only)
  and the remaining D7-level certificates (extinction, canonical neighborhoods).

No declaration uses `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
import Poincare.D13.VanKampenRecognition.SphereVanKampen
import Poincare.D12.SurgeryRecognition.ExpandedInterfaces

set_option autoImplicit false

open scoped Topology

noncomputable section

namespace Poincare.D13.VanKampenRecognition

open Poincare.Longrun.Surgery
open Poincare.Longrun.Topology
open Poincare.D12.SurgeryRecognition
open Poincare.D7.Recognition

/-! ## 1. Transport of simple connectivity along a homeomorphism to `𝕊³` -/

/-- **Simple connectivity is a homeomorphism invariant**, applied to the
3-sphere: a space homeomorphic to `𝕊³` is simply connected.  The homeomorphism
is a homotopy equivalence (`Homeomorph.toHomotopyEquiv`), and mathlib's
`ContinuousMap.HomotopyEquiv.simplyConnectedSpace` transports the instance
from the target. -/
def simplyConnected_of_homeo_sphere {X : Type*} [TopologicalSpace X] (e : X ≃ₜ S3) :
    SimplyConnectedSpace X :=
  e.toHomotopyEquiv.simplyConnectedSpace

/-! ## 2. SR-4: the van Kampen field of the connected-sum decomposition -/

/-- **SR-4 closure.**  For the D12 V2 decomposition (every piece homeomorphic
to `𝕊³` with the actual iterated connected sum data), the assumed D7 van
Kampen field `simplyConnected_pieces` is *proved*: every piece is simply
connected because it is homeomorphic to `𝕊³` and `𝕊³` is simply connected
(the van Kampen computation `sphereThree_simplyConnectedSpace`).  The ambient
simple-connectivity hypothesis is not even needed — the conclusion is strictly
stronger than the assumed field. -/
theorem simplyConnectedPieces_of_v2 {X : Poincare.Longrun.Surgery.TopSpace.{0}}
    {pieces : List (Poincare.Longrun.Surgery.TopSpace.{0})}
    (D : ConnectedSumDecompositionV2 X pieces) :
    SimplyConnectedSpace X.Carrier → ∀ P ∈ pieces, SimplyConnectedSpace P.Carrier := by
  intro _hX P hP
  exact simplyConnected_of_homeo_sphere (D.pieceSphere P hP).some

/-- **The D7 connected-sum decomposition with both missing-input fields
proved.**  `sphere_of_spheres` (SR-5) is D12's
`ConnectedSumDecomposition.mkV2` construction; `simplyConnected_pieces` (SR-4)
is `simplyConnectedPieces_of_v2`. -/
def ConnectedSumDecomposition.mkV2Complete {X : Poincare.Longrun.Surgery.TopSpace.{0}}
    {pieces : List (Poincare.Longrun.Surgery.TopSpace.{0})}
    (D : ConnectedSumDecompositionV2 X pieces) :
    Poincare.D7.Recognition.ConnectedSumDecomposition X pieces :=
  ConnectedSumDecomposition.mkV2 D (simplyConnectedPieces_of_v2 D)

/-! ## 2bis. The forward direction: the V2 summands and ambient space are simply
connected -/

/-- **The iterated connected sum of `𝕊³` summands is simply connected.**  It is
homeomorphic to `𝕊³` (D12's `iteratedSphereSum_homeo_sphere`) and `𝕊³` is
simply connected (`sphereThree_simplyConnectedSpace`).  This is the forward
direction of the van Kampen intuition recorded in the D7 docstring (a connected
sum of simply connected summands is simply connected); SR-4 is the converse,
also proved below. -/
theorem iteratedSphereSum_simplyConnected (pieces : List (Poincare.Longrun.Surgery.TopSpace.{0}))
    (h : ∀ P ∈ pieces, Nonempty (P.Carrier ≃ₜ S3)) :
    SimplyConnectedSpace (iteratedSphereSum pieces h).sum.Carrier :=
  simplyConnected_of_homeo_sphere (iteratedSphereSum pieces h).sumHomeo.some

/-- **For V2 data the ambient space is itself simply connected** (it is
homeomorphic to the iterated sum, hence to `𝕊³`).  Together with
`simplyConnectedPieces_of_v2` this shows that for a spherical connected-sum
decomposition the simple-connectivity hypothesis of SR-4 is in fact automatic. -/
theorem v2Ambient_simplyConnected {X : Poincare.Longrun.Surgery.TopSpace.{0}}
    {pieces : List (Poincare.Longrun.Surgery.TopSpace.{0})}
    (D : ConnectedSumDecompositionV2 X pieces) :
    SimplyConnectedSpace X.Carrier :=
  simplyConnected_of_homeo_sphere
    (D.sumHomeo.some.trans (iteratedSphereSum pieces D.pieceSphere).sumHomeo.some)

/-! ## 3. The V4 remaining hypotheses: only `spaceForm` -/

/-- **The remaining recognition hypotheses, V4 (SR-4 and SR-5 closed).**  After
the connected-sum topology inputs are discharged — SR-5 by the D12
construction and SR-4 by `simplyConnectedPieces_of_v2` — exactly one geometric
hypothesis remains in the recognition chain: `spaceForm`, the spherical space
form theorem (every spherical piece is a space form quotient of `𝕊³`).  The
covering-recognition half and the deck-triviality step are the *proved* D12
theorems bundled by `sphericalPieceRecognition_of_spaceForm`; the canonical
neighborhood, surgery and extinction inputs remain the separate D7-level
certificates, unchanged. -/
structure RemainingRecognitionHypothesesV4 (X : Poincare.Longrun.Surgery.TopSpace.{0})
    (pieces : List (Poincare.Longrun.Surgery.TopSpace.{0})) where
  /-- Every spherical piece is a space form quotient of `𝕊³` (space form theorem). -/
  spaceForm : ∀ {Y : TopSpace.{0}}, SphericalPiece Y →
    { M : SphericalSpaceFormModel // IsSpaceFormModelOf Y M }

namespace RemainingRecognitionHypothesesV4

/-- **Downstream use.**  The V4 hypotheses reproduce the V3 hypotheses: the
van Kampen field is *constructed* by `simplyConnectedPieces_of_v2` from the V2
data. -/
def toRemainingV3 {X : Poincare.Longrun.Surgery.TopSpace.{0}}
    {pieces : List (Poincare.Longrun.Surgery.TopSpace.{0})}
    (H : RemainingRecognitionHypothesesV4 X pieces)
    (D : ConnectedSumDecompositionV2 X pieces) : RemainingRecognitionHypothesesV3 X pieces where
  vanKampen := simplyConnectedPieces_of_v2 D
  spaceForm := H.spaceForm

/-- **Downstream use.**  The V4 hypotheses reproduce the D7
`RemainingRecognitionHypotheses`: both the van Kampen field and the
`SphericalPieceRecognition` bridge are constructed (the latter by
`sphericalPieceRecognition_of_spaceForm`, the D12 covering + proved
deck-triviality theorems). -/
def toRemaining {X : Poincare.Longrun.Surgery.TopSpace.{0}}
    {pieces : List (Poincare.Longrun.Surgery.TopSpace.{0})}
    (H : RemainingRecognitionHypothesesV4 X pieces)
    (D : ConnectedSumDecompositionV2 X pieces) :
    RemainingRecognitionHypotheses X pieces :=
  (H.toRemainingV3 D).toRemaining

end RemainingRecognitionHypothesesV4

/-! ## 4. The downstream checked use: the Stage6 end-game assembly -/

/-- **Downstream checked use.**  The D7 end-game assembly from the V2
decomposition data with the V4 recognition hypotheses: the Stage6 target
`poincareConjectureTopologicalThree` is reproduced from
`stage6Target_of_certificates` with the *constructed* decomposition
`ConnectedSumDecomposition.mkV2Complete D` (whose SR-4 and SR-5 fields are both
proved) and the *constructed* recognition bridge
`sphericalPieceRecognition_of_spaceForm H.spaceForm`.  The remaining inputs are
exactly: the D7 extinction certificate `E`, the canonical-neighborhood input
`canonical`, and the single geometric hypothesis `H.spaceForm`. -/
theorem stage6Target_of_v4hypotheses {X : TopSpace.{0}}
    (compact : CompactSpace X.Carrier) (t2 : T2Space X.Carrier)
    (charted : ChartedSpace EuclideanThree X.Carrier)
    (simplyConnected : SimplyConnectedSpace X.Carrier)
    (E : ExtinctionCertificate X)
    (D : ConnectedSumDecompositionV2 X E.pieces)
    (H : RemainingRecognitionHypothesesV4 X E.pieces)
    (canonical : CanonicalNeighborhoodInput X E) :
    @Poincare.Stage6.poincareConjectureTopologicalThree X.Carrier X.topology
      t2 charted simplyConnected compact :=
  stage6Target_of_v3hypotheses compact t2 charted simplyConnected E D (H.toRemainingV3 D) canonical

/-- **The fully-constructed decomposition consumed by the D7 assembly.**
Explicitly: the D7 `stage6Target_of_certificates` end game runs on the V2
decomposition with both topology fields proved and only `spaceForm` assumed. -/
theorem stage6Target_of_v4hypotheses_from_certificates {X : TopSpace.{0}}
    (compact : CompactSpace X.Carrier) (t2 : T2Space X.Carrier)
    (charted : ChartedSpace EuclideanThree X.Carrier)
    (simplyConnected : SimplyConnectedSpace X.Carrier)
    (E : ExtinctionCertificate X)
    (D : ConnectedSumDecompositionV2 X E.pieces)
    (H : RemainingRecognitionHypothesesV4 X E.pieces)
    (canonical : CanonicalNeighborhoodInput X E) :
    @Poincare.Stage6.poincareConjectureTopologicalThree X.Carrier X.topology
      t2 charted simplyConnected compact :=
  stage6Target_of_certificates compact t2 charted simplyConnected
    { extinctionTime := E.extinctionTime
      extinctionTime_pos := E.extinctionTime_pos
      extinction := E.extinction
      complexityDecreases := E.complexityDecreases
      pieces := E.pieces
      pieces_ne_nil := E.pieces_ne_nil
      decomposition := ConnectedSumDecomposition.mkV2Complete D }
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
    (sphericalPieceRecognition_of_spaceForm H.spaceForm)

end Poincare.D13.VanKampenRecognition

end
