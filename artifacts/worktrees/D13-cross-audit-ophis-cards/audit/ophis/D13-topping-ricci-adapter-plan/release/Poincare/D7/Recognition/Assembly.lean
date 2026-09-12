/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-sphere-recognition)

**D7 sphere recognition, part 2: the end-game logical assembly.**

This module assembles the three certificate layers into the interface-level conclusion and
connects it to the shared Stage6 statement-only Poincaré target:

1. **simply-connectedness** of the closed three-manifold (`RecognitionHypotheses.simplyConnected`);
2. the **canonical-neighborhood input** (`CanonicalNeighborhoodInput`), which classifies the
   high-curvature regions as surgery-admissible (neck/cap) or compact-spherical and certifies
   every terminal piece as compact-spherical;
3. the **extinction certificate** (`ExtinctionCertificate`), which supplies finite extinction
   time, the D3/D6 extinction interface and the connected-sum decomposition into terminal
   pieces.

The checked implication chain is, in order:

* `RecognitionHypotheses.conclusion` — the extinction certificate yields the interface-level
  conclusion `ExtinctionConclusion` ("the flow becomes extinct in finite time");
* `RecognitionHypotheses.onlySphericalPieces` — the canonical-neighborhood input turns every
  terminal piece into a `SphericalPiece` ("with only spherical pieces");
* `RecognitionHypotheses.pieces_simplyConnected` — van Kampen bridge of the connected-sum
  decomposition applied to the simple connectivity of the manifold;
* `RecognitionHypotheses.pieces_homeomorph_sphere` — spherical-piece recognition;
* `RecognitionHypotheses.homeomorph_sphere` — connected sum of `𝕊³` summands;
* `RecognitionHypotheses.stage6Target` — the Stage6 statement-only Poincaré target, discharged
  conditionally.

Every hypothesis is listed explicitly; the only opaque inputs are the named function fields of
`ConnectedSumDecomposition` and `SphericalPieceRecognition` (documented in the result card as
missing inputs).  No declaration uses `sorry`, `axiom`, `unsafe`, `native_decide` or
`proof_wanted`.
-/

import Poincare.D7.Recognition.Basic

set_option autoImplicit false

open scoped Topology Manifold ContDiff

namespace Poincare

namespace D7

namespace Recognition

open Poincare.D7.Canonical
open Poincare.D7.Compactness
open Poincare.Longrun.Surgery
open Poincare.Longrun.Topology

universe u

/-! ## 1. The end-game hypotheses -/

/-- **The end-game hypotheses.**  A closed three-manifold `X` (compact, Hausdorff, with an
`ℝ³`-atlas), together with simple connectivity, an extinction certificate, the
canonical-neighborhood input over that certificate, and the spherical-piece recognition
bridge.

The manifold hypotheses are listed as fields (rather than typeclass arguments) so that the
conditional theorem below has no hidden assumptions: every input appears in the structure and
in the unfolded theorem statement. -/
structure RecognitionHypotheses (X : TopSpace.{0}) : Type 1 where
  /-- The manifold is compact. -/
  compact : CompactSpace X.Carrier
  /-- The manifold is Hausdorff. -/
  t2 : T2Space X.Carrier
  /-- The manifold carries an `ℝ³`-atlas. -/
  charted : ChartedSpace EuclideanThree X.Carrier
  /-- The manifold is simply connected. -/
  simplyConnected : SimplyConnectedSpace X.Carrier
  /-- The extinction certificate of the surgery / neck-extinction analysis. -/
  extinction : ExtinctionCertificate X
  /-- The canonical-neighborhood classification of the flow. -/
  canonical : CanonicalNeighborhoodInput X extinction
  /-- The spherical-piece recognition bridge. -/
  pieceRecognition : SphericalPieceRecognition

namespace RecognitionHypotheses

variable {X : TopSpace.{0}} (H : RecognitionHypotheses X)

/-- **Checked assembly (extinction).**  The interface-level conclusion: the flow becomes
extinct in finite time.  The finite-surgery and extinction fields are the checked D3/D6
theorems, extracted by `ExtinctionCertificate.toConclusion`. -/
def conclusion : ExtinctionConclusion X :=
  H.extinction.toConclusion

/-- **Checked assembly (finite extinction time).**  There is a positive time at which the flow
is extinct. -/
theorem extinctsInFiniteTime : ∃ t : ℝ, 0 < t ∧ H.extinction.extinction.extincts :=
  H.extinction.extinctsInFiniteTime

/-- **Checked assembly (finitely many surgeries).** -/
theorem finitelyManySurgeries : H.extinction.extinction.finitelyManySurgeries :=
  H.extinction.finitelyManySurgeries

/-- **Checked assembly (only spherical pieces).**  Every terminal piece is a spherical piece,
by the canonical-neighborhood classification. -/
noncomputable def onlySphericalPieces (P : TopSpace.{0}) (hP : P ∈ H.extinction.pieces) :
    SphericalPiece P :=
  H.canonical.only_spherical P hP

/-- **Checked assembly (bundled interface-level conclusion).**  The flow becomes extinct in
finite time with only spherical pieces. -/
noncomputable def extinctionWithSphericalPieces : ExtinctionWithSphericalPieces X where
  conclusion := H.conclusion
  spherical := fun P hP => H.onlySphericalPieces P hP

/-- **Checked assembly (van Kampen).**  Every terminal piece is simply connected, because the
manifold is simply connected and is the connected sum of the pieces. -/
theorem pieces_simplyConnected :
    ∀ P ∈ H.extinction.pieces, SimplyConnectedSpace P.Carrier :=
  H.extinction.decomposition.simplyConnected_pieces H.simplyConnected

/-- **Checked assembly (recognition).**  Every terminal piece is homeomorphic to `𝕊³`. -/
theorem pieces_homeomorph_sphere :
    ∀ P ∈ H.extinction.pieces, Nonempty (P.Carrier ≃ₜ SphereThree) :=
  fun P hP =>
    H.pieceRecognition.recognize (H.onlySphericalPieces P hP)
      (H.pieces_simplyConnected P hP)

/-- **Checked assembly (connected sum).**  The manifold is homeomorphic to `𝕊³`: it is the
connected sum of terminal pieces, each of which is a `𝕊³`. -/
theorem homeomorph_sphere (H : RecognitionHypotheses X) :
    Nonempty (X.Carrier ≃ₜ SphereThree) :=
  H.extinction.decomposition.sphere_of_spheres H.pieces_homeomorph_sphere

/-- **Checked assembly (Stage6 target).**  The shared Stage6 statement-only Poincaré target
`Poincare.Stage6.poincareConjectureTopologicalThree` is discharged from the end-game
hypotheses.  The target is definitionally `Nonempty (X ≃ₜ 𝕊³)`; no content is added. -/
theorem stage6Target (H : RecognitionHypotheses X) :
    @Poincare.Stage6.poincareConjectureTopologicalThree X.Carrier X.topology H.t2 H.charted
      H.simplyConnected H.compact :=
  H.homeomorph_sphere

/-- **Checked assembly (all pieces are spherical).**  The "only spherical pieces" conclusion
in its bundled form: every member of the terminal piece list carries a `SphericalPiece` datum
and is homeomorphic to `𝕊³`. -/
theorem all_pieces_spherical_and_sphere (H : RecognitionHypotheses X) :
    ∀ P ∈ H.extinction.pieces,
      IsSphericalPiece P ∧ Nonempty (P.Carrier ≃ₜ SphereThree) :=
  fun P hP => ⟨⟨H.onlySphericalPieces P hP⟩, H.pieces_homeomorph_sphere P hP⟩

end RecognitionHypotheses

/-! ## 2. The conditional theorem with the hypotheses listed -/

/-- **The conditional Poincaré target.**  For every closed three-manifold `X` with an
`ℝ³`-atlas, if `X` is simply connected, carries an extinction certificate, carries the
canonical-neighborhood input over that certificate, and the spherical-piece recognition bridge
holds, then the Stage6 statement-only Poincaré target holds for `X`.

Every hypothesis is an explicit argument; the conclusion is the Stage6 alias
`Nonempty (X ≃ₜ 𝕊³)`. -/
theorem stage6Target_of_certificates {X : TopSpace.{0}}
    (compact : CompactSpace X.Carrier) (t2 : T2Space X.Carrier)
    (charted : ChartedSpace EuclideanThree X.Carrier)
    (simplyConnected : SimplyConnectedSpace X.Carrier)
    (extinction : ExtinctionCertificate X)
    (canonical : CanonicalNeighborhoodInput X extinction)
    (pieceRecognition : SphericalPieceRecognition) :
    @Poincare.Stage6.poincareConjectureTopologicalThree X.Carrier X.topology t2 charted
      simplyConnected compact :=
  (RecognitionHypotheses.mk compact t2 charted simplyConnected extinction canonical
    pieceRecognition).stage6Target

/-- **The interface-level conclusion, with the hypotheses listed.**  The same hypotheses
produce the bundled conclusion "the flow becomes extinct in finite time with only spherical
pieces". -/
theorem extinctionWithSphericalPieces_of_certificates {X : TopSpace.{0}}
    (compact : CompactSpace X.Carrier) (t2 : T2Space X.Carrier)
    (charted : ChartedSpace EuclideanThree X.Carrier)
    (simplyConnected : SimplyConnectedSpace X.Carrier)
    (extinction : ExtinctionCertificate X)
    (canonical : CanonicalNeighborhoodInput X extinction)
    (pieceRecognition : SphericalPieceRecognition) :
    ∃ W : ExtinctionWithSphericalPieces X,
      0 < W.conclusion.extinctionTime ∧ W.conclusion.extincts :=
  let H := RecognitionHypotheses.mk compact t2 charted simplyConnected extinction canonical
    pieceRecognition
  ⟨H.extinctionWithSphericalPieces,
    H.extinction.extinctionTime_pos,
    H.extinction.extinction.extincts_of_complexity H.extinction.complexityDecreases⟩

/-! ## 3. The surgery-level interface, re-exported -/

/-- **Checked composition.**  A high-curvature region together with its `NeckAnalysis` supplies
the target-invariant preservation obligation of a surgery step; compactness and orientability
remain explicit hypotheses, exactly as in `NeckAnalysis.certificate`. -/
theorem surgeryCertificate_of_neckAnalysis {P : LedgerPredicates.{0}} {X Y : TopSpace.{0}}
    {D : SurgeryDatum X Y} (N : NeckAnalysis P D) (hN : N.highCurvatureRegion)
    (hcompact : P.Compact X → P.Compact Y) (horientable : P.Orientable X → P.Orientable Y) :
    SurgeryCertificate P D :=
  N.certificate hN hcompact horientable

/-- **Checked composition.**  The target topological invariant is preserved along a certified
chain of surgery steps. -/
theorem simplyConnected_preserved_of_chainCertificate {P : LedgerPredicates.{0}}
    {X Y : TopSpace.{0}} {c : SurgeryChain X Y} (C : ChainCertificate P c) :
    P.SimplyConnected X → P.SimplyConnected Y :=
  C.simplyConnected_preserved

/-- **Checked composition (D3/D6 end-to-end).**  Extinction, the realization of the surgery
datum and target-invariant preservation, from the missing surgery inputs and a certified chain.
This is the D3/D6 theorem `Poincare.Longrun.Surgery.extincts_and_target`, re-exported at the
recognition layer. -/
theorem extincts_and_target_of_missingInputs {P : LedgerPredicates.{0}} {X Y : TopSpace.{0}}
    {D : SurgeryDatum X Y} (M : MissingInputs P D) (hN : M.neck.highCurvatureRegion)
    (hE : M.extinction.complexityDecreases)
    {c : SurgeryChain X Y} (C : ChainCertificate P c) (hX : P.SimplyConnected X) :
    M.extinction.extincts ∧ M.neck.realizesDatum ∧ P.SimplyConnected Y :=
  extincts_and_target M hN hE C hX

/-- **Checked composition.**  The surgery-admissible canonical alternatives feed the surgery
interface: a canonical-neighborhood certificate is classified as neck/cap or compact-spherical,
and the compact-spherical alternative is excluded from the surgery step. -/
theorem not_surgeryAdmissible_of_canonical_compactSpherical {ε κ r : ℝ}
    {X : PointedMetricSpace.{u}} {C : CanonicalNeighborhoodCertificate ε κ r X}
    (h : C.kind = CanonicalKind.compactSpherical) : ¬ IsSurgeryAdmissible C :=
  not_isSurgeryAdmissible_of_compactSpherical h

end Recognition

end D7

end Poincare
