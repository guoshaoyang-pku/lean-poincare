/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-sphere-recognition)

**D7 sphere recognition, part 1: the certificate vocabulary of the end-game assembly.**

This module fixes the *interfaces* consumed by the end-game logical assembly of the
Poincaré programme:

* the surgery-admissible alternatives of a canonical-neighborhood certificate
  (`IsSurgeryAdmissible`, `isSurgeryAdmissible_or_compactSpherical`);
* a **spherical terminal piece** (`SphericalPiece`), defined through the compact-spherical
  alternative of a canonical-neighborhood certificate plus a homeomorphism;
* the **connected-sum decomposition** of the original manifold into the terminal pieces,
  together with the two topological bridges that the pinned mathlib does not provide
  (van Kampen, and "a connected sum of `𝕊³` summands is `𝕊³`), recorded as explicit
  function fields `simplyConnected_pieces` and `sphere_of_spheres`;
* the **extinction certificate** supplied by the surgery / neck-extinction analysis,
  phrased over the checked D3/D6 extinction interface `Poincare.Longrun.Surgery.ExtinctionTheorem`
  (finite-time extinction is derived there by the checked theorem
  `ExtinctionTheorem.extincts_of_complexity`, never postulated here);
* the **interface-level conclusion** `ExtinctionConclusion`: the flow becomes extinct in finite
  time with only spherical pieces;
* the **canonical-neighborhood input** (`CanonicalNeighborhoodInput`) recording the family of
  high-curvature certificates of the flow and the fact that every terminal piece is certified
  by the compact-spherical alternative;
* the **spherical-piece recognition bridge** (`SphericalPieceRecognition`), the named missing
  input (spherical space form theorem + Moise smoothing) turning a simply connected spherical
  piece into a homeomorphism to `𝕊³`.

Nothing in this file asserts any geometric existence theorem.  Every missing input is an
explicit structure field or `Prop` parameter; the checked content is the interface algebra and
the construction of `SphericalPiece` data out of canonical-neighborhood certificates.

No declaration uses `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/

import Poincare.D7.Canonical.Statements
import Poincare.Longrun.Surgery.Missing
import Poincare.Longrun.Topology.Stage6Bridge

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

/-! ## 1. The surgery-admissible canonical alternatives -/

/-- **Surgery admissibility.**  A canonical-neighborhood certificate is surgery-admissible when
its kind is an ε-neck or an ε-cap: these are the two alternatives along which the flow is cut
and capped.  The third alternative, a compact ε-spherical region, is a terminal piece and is
never cut. -/
def IsSurgeryAdmissible {ε κ r : ℝ} {X : PointedMetricSpace.{u}}
    (C : CanonicalNeighborhoodCertificate ε κ r X) : Prop :=
  C.kind = CanonicalKind.neck ∨ C.kind = CanonicalKind.cap

/-- **Checked dichotomy.**  Every canonical-neighborhood certificate is either
surgery-admissible (neck or cap) or compact-spherical.  This is the checked form of the
classification consumed by the assembly: no fourth alternative exists. -/
theorem isSurgeryAdmissible_or_compactSpherical {ε κ r : ℝ} {X : PointedMetricSpace.{u}}
    (C : CanonicalNeighborhoodCertificate ε κ r X) :
    IsSurgeryAdmissible C ∨ C.kind = CanonicalKind.compactSpherical := by
  rcases C.kind_cases with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-- **Checked exclusion.**  The compact-spherical alternative is not surgery-admissible. -/
theorem not_isSurgeryAdmissible_of_compactSpherical {ε κ r : ℝ}
    {X : PointedMetricSpace.{u}} {C : CanonicalNeighborhoodCertificate ε κ r X}
    (h : C.kind = CanonicalKind.compactSpherical) : ¬ IsSurgeryAdmissible C := by
  rintro (h' | h') <;> rw [h] at h' <;> exact CanonicalKind.noConfusion h'

/-! ## 2. Spherical terminal pieces -/

/-- **A spherical terminal piece.**  A piece of the terminal extinction configuration that
carries the compact-spherical alternative of a canonical-neighborhood certificate at some
positive scale, together with a homeomorphism from the piece to the certified region.

The certificate field is the canonical-neighborhood classification datum
(`CanonicalNeighborhoodCertificate` of the D7 canonical layer); the scale, curvature
normalization and metric noncollapsing shadow are all carried by that certificate.  The
positive-curvature geometry itself is not formalized in the pinned mathlib (see the result
card of `D7-canonical-neighborhood`). -/
structure SphericalPiece (X : TopSpace.{0}) : Type 1 where
  /-- The ε of the compact-spherical certificate. -/
  ε : ℝ
  /-- The κ of the compact-spherical certificate. -/
  κ : ℝ
  /-- The scale of the compact-spherical certificate. -/
  r : ℝ
  /-- The certified region. -/
  region : PointedMetricSpace.{0}
  /-- The canonical-neighborhood certificate of the region. -/
  certificate : CanonicalNeighborhoodCertificate ε κ r region
  /-- The certificate selects the compact-spherical alternative. -/
  kind_eq : certificate.kind = CanonicalKind.compactSpherical
  /-- The terminal piece is homeomorphic to the certified region. -/
  homeo : Nonempty (X.Carrier ≃ₜ region)

namespace SphericalPiece

variable {X : TopSpace.{0}}

/-- The scale of a spherical piece is positive. -/
theorem scale_pos (P : SphericalPiece X) : 0 < P.r :=
  P.certificate.scale_pos

/-- The certificate of a spherical piece is compact-spherical. -/
theorem certificate_kind (P : SphericalPiece X) :
    P.certificate.kind = CanonicalKind.compactSpherical :=
  P.kind_eq

/-- The piece is homeomorphic to its certified region. -/
theorem homeomorphic (P : SphericalPiece X) : Nonempty (X.Carrier ≃ₜ P.region) :=
  P.homeo

/-- **Checked constructor.**  A compact-spherical canonical-neighborhood certificate for a
region homeomorphic to `X` makes `X` a spherical piece.  This is the construction used by the
assembly to turn the canonical-neighborhood classification of the terminal regions into
spherical pieces. -/
def ofCertificate {region : PointedMetricSpace.{0}} {ε κ r : ℝ}
    (C : CanonicalNeighborhoodCertificate ε κ r region)
    (h : C.kind = CanonicalKind.compactSpherical)
    (e : Nonempty (X.Carrier ≃ₜ region)) : SphericalPiece X where
  ε := ε
  κ := κ
  r := r
  region := region
  certificate := C
  kind_eq := h
  homeo := e

end SphericalPiece

/-- **The property-level form.**  A space carries a spherical piece when a `SphericalPiece`
datum exists for it. -/
def IsSphericalPiece (X : TopSpace.{0}) : Prop :=
  Nonempty (SphericalPiece X)

/-! ## 3. The connected-sum decomposition and its missing topological bridges -/

/-- **The connected-sum decomposition of the terminal configuration.**  `X` is the connected
sum of the finitely many terminal pieces.  The relation itself is an opaque `Prop` field (the
pinned mathlib has no connected-sum operation), and the two topological facts needed by the
assembly are explicit function fields:

* `simplyConnected_pieces` — van Kampen: the fundamental group of a connected sum is the free
  product of the fundamental groups of the summands, so if `X` is simply connected then so is
  every summand;
* `sphere_of_spheres` — a connected sum of summands each homeomorphic to `𝕊³` is itself
  homeomorphic to `𝕊³` (Moise: the connected sum of `𝕊³` summands is `𝕊³`).

Both are named missing inputs, not postulates of this development: they occur only as
hypotheses of conditional theorems. -/
structure ConnectedSumDecomposition (X : TopSpace.{0}) (pieces : List (TopSpace.{0})) :
    Type 1 where
  /-- Opaque: `X` is the connected sum of `pieces`. -/
  relation : Prop
  /-- The connected-sum relation holds. -/
  relation_holds : relation
  /-- **MISSING INPUT (van Kampen).**  Simple connectivity passes to the summands. -/
  simplyConnected_pieces : SimplyConnectedSpace X.Carrier →
    ∀ P ∈ pieces, SimplyConnectedSpace P.Carrier
  /-- **MISSING INPUT (connected sum of spheres).**  A connected sum of `𝕊³` summands is
  `𝕊³`. -/
  sphere_of_spheres : (∀ P ∈ pieces, Nonempty (P.Carrier ≃ₜ SphereThree)) →
    Nonempty (X.Carrier ≃ₜ SphereThree)

/-! ## 4. Extinction certificates and the interface-level conclusion -/

/-- The ledger used by the extinction interface: mathlib's compactness and simple
connectivity, with orientability trivially true (orientability is not consumed by the
extinction conclusion, and the pinned mathlib has no manifold orientability). -/
def extinctionLedger : LedgerPredicates.{0} :=
  canonicalLedger (fun _ : TopSpace.{0} => True)

/-- **The extinction certificate supplied by the surgery / neck-extinction analysis.**  The
certificate records the finite extinction time, the checked D3/D6 extinction interface
(`ExtinctionTheorem`, whose finite-surgery and extinction fields are derived by the checked
theorems of `Poincare.Longrun.Surgery.Missing`), the terminal pieces, and their connected-sum
decomposition.

The certificate does *not* contain the claim that the pieces are spherical: that comes from
`CanonicalNeighborhoodInput` below. -/
structure ExtinctionCertificate (X : TopSpace.{0}) : Type 1 where
  /-- The finite extinction time. -/
  extinctionTime : ℝ
  /-- The extinction time is positive. -/
  extinctionTime_pos : 0 < extinctionTime
  /-- The D3/D6 extinction interface. -/
  extinction : ExtinctionTheorem extinctionLedger
  /-- The surgery complexity strictly decreases at every surgery. -/
  complexityDecreases : extinction.complexityDecreases
  /-- The terminal pieces. -/
  pieces : List (TopSpace.{0})
  /-- The terminal configuration is nonempty. -/
  pieces_ne_nil : pieces ≠ []
  /-- The original manifold is the connected sum of the terminal pieces. -/
  decomposition : ConnectedSumDecomposition X pieces

/-- **The interface-level conclusion of the end game.**  The flow becomes extinct in finite
time with only spherical pieces: a positive extinction time, finitely many surgeries, the
extinction event, the terminal pieces, and their connected-sum decomposition.  The pieces
themselves are supplied by the canonical-neighborhood input, not stored here. -/
structure ExtinctionConclusion (X : TopSpace.{0}) : Type 1 where
  /-- The finite extinction time. -/
  extinctionTime : ℝ
  /-- The extinction time is positive. -/
  extinctionTime_pos : 0 < extinctionTime
  /-- Only finitely many surgeries occur. -/
  finiteSurgeries : Prop
  /-- The finitely-many-surgeries statement holds. -/
  finiteSurgeries_holds : finiteSurgeries
  /-- The flow becomes extinct. -/
  extincts : Prop
  /-- The extinction statement holds. -/
  extincts_holds : extincts
  /-- The terminal pieces. -/
  pieces : List (TopSpace.{0})
  /-- The terminal configuration is nonempty. -/
  pieces_ne_nil : pieces ≠ []
  /-- The connected-sum decomposition of the terminal configuration. -/
  decomposition : ConnectedSumDecomposition X pieces

/-- **The interface-level conclusion, bundled.**  The flow becomes extinct in finite time with
only spherical pieces: an `ExtinctionConclusion` together with a `SphericalPiece` datum for
every terminal piece.  The pieces are supplied by `CanonicalNeighborhoodInput`; this structure
is the exact object proved by the end-game assembly. -/
structure ExtinctionWithSphericalPieces (X : TopSpace.{0}) : Type 1 where
  /-- The extinction conclusion. -/
  conclusion : ExtinctionConclusion X
  /-- Every terminal piece is spherical. -/
  spherical : ∀ P ∈ conclusion.pieces, SphericalPiece P

namespace ExtinctionCertificate

variable {X : TopSpace.{0}}

/-- **Checked assembly.**  The extinction certificate yields the interface-level conclusion.
The finite-surgery and extinction fields are obtained from the checked D3/D6 theorems
`ExtinctionTheorem.finitelyMany_of_complexity` and `ExtinctionTheorem.extincts_of_complexity`,
not postulated. -/
def toConclusion (E : ExtinctionCertificate X) : ExtinctionConclusion X where
  extinctionTime := E.extinctionTime
  extinctionTime_pos := E.extinctionTime_pos
  finiteSurgeries := E.extinction.finitelyManySurgeries
  finiteSurgeries_holds := E.extinction.finitelyMany_of_complexity E.complexityDecreases
  extincts := E.extinction.extincts
  extincts_holds := E.extinction.extincts_of_complexity E.complexityDecreases
  pieces := E.pieces
  pieces_ne_nil := E.pieces_ne_nil
  decomposition := E.decomposition

/-- **Checked extraction (finite time).**  The extinction certificate yields a positive
extinction time at which the flow is extinct. -/
theorem extinctsInFiniteTime (E : ExtinctionCertificate X) :
    ∃ t : ℝ, 0 < t ∧ E.extinction.extincts :=
  ⟨E.extinctionTime, E.extinctionTime_pos,
    E.extinction.extincts_of_complexity E.complexityDecreases⟩

/-- **Checked extraction (finite surgeries).**  Only finitely many surgeries occur. -/
theorem finitelyManySurgeries (E : ExtinctionCertificate X) :
    E.extinction.finitelyManySurgeries :=
  E.extinction.finitelyMany_of_complexity E.complexityDecreases

end ExtinctionCertificate

/-! ## 5. The canonical-neighborhood input -/

/-- **The canonical-neighborhood input.**  The flow's high-curvature regions are listed
together with their canonical-neighborhood certificates, all at one admissible scale `r`; the
checked dichotomy `isSurgeryAdmissible_or_compactSpherical` classifies each certificate; and
every terminal piece of the extinction certificate is homeomorphic to a region certified by
the compact-spherical alternative.

The last field is the exact point at which the canonical-neighborhood classification feeds the
extinction conclusion: it turns the terminal regions into `SphericalPiece` data. -/
structure CanonicalNeighborhoodInput (X : TopSpace.{0}) (E : ExtinctionCertificate X) :
    Type 1 where
  /-- The ε of the canonical-neighborhood certificates. -/
  ε : ℝ
  /-- `ε > 0`. -/
  ε_pos : 0 < ε
  /-- The κ of the canonical-neighborhood certificates. -/
  κ : ℝ
  /-- `κ > 0`. -/
  κ_pos : 0 < κ
  /-- The admissible scale `r = r₀(ε, κ)`. -/
  r : ℝ
  /-- `r > 0`. -/
  r_pos : 0 < r
  /-- The high-curvature regions of the flow. -/
  regions : List (PointedMetricSpace.{0})
  /-- The canonical-neighborhood certificate of every region. -/
  certificate : ∀ R ∈ regions, CanonicalNeighborhoodCertificate ε κ r R
  /-- Every certificate is surgery-admissible or compact-spherical (checked dichotomy). -/
  admissible_or_spherical : ∀ (R : PointedMetricSpace.{0}) (hR : R ∈ regions),
    IsSurgeryAdmissible (certificate R hR) ∨
      (certificate R hR).kind = CanonicalKind.compactSpherical
  /-- Every terminal piece of the extinction is homeomorphic to a region certified by the
  compact-spherical alternative. -/
  piece_region_homeo : ∀ (P : TopSpace.{0}), P ∈ E.pieces →
    ∃ (R : PointedMetricSpace.{0}) (hR : R ∈ regions),
      (certificate R hR).kind = CanonicalKind.compactSpherical ∧
        Nonempty (P.Carrier ≃ₜ R)

namespace CanonicalNeighborhoodInput

variable {X : TopSpace.{0}} {E : ExtinctionCertificate X}

/-- **Checked assembly.**  A terminal piece certified by the compact-spherical alternative is
a spherical piece.  This constructs the `SphericalPiece` datum out of the
canonical-neighborhood certificate and the homeomorphism. -/
noncomputable def sphericalPiece (C : CanonicalNeighborhoodInput X E) (P : TopSpace.{0})
    (hP : P ∈ E.pieces) : SphericalPiece P :=
  let h := C.piece_region_homeo P hP
  SphericalPiece.ofCertificate (C.certificate h.choose h.choose_spec.choose)
    h.choose_spec.choose_spec.1 h.choose_spec.choose_spec.2

/-- **Checked assembly.**  Every terminal piece is spherical.  This is the "only spherical
pieces" half of the interface-level conclusion, derived from the canonical-neighborhood
classification. -/
noncomputable def only_spherical (C : CanonicalNeighborhoodInput X E) (P : TopSpace.{0})
    (hP : P ∈ E.pieces) : SphericalPiece P :=
  C.sphericalPiece P hP

/-- **Checked assembly.**  Every certificate of the input family is classified: neck or cap
(surgery-admissible) or compact-spherical. -/
theorem certificate_classified (C : CanonicalNeighborhoodInput X E)
    (R : PointedMetricSpace.{0}) (hR : R ∈ C.regions) :
    IsSurgeryAdmissible (C.certificate R hR) ∨
      (C.certificate R hR).kind = CanonicalKind.compactSpherical :=
  C.admissible_or_spherical R hR

end CanonicalNeighborhoodInput

/-! ## 6. The named recognition bridge -/

/-- **MISSING INPUT (spherical-piece recognition).**  A simply connected spherical terminal
piece is homeomorphic to `𝕊³`.

Mathematically this bundles the spherical space form theorem (`π₁(𝕊³/Γ) ≅ Γ`, so a simply
connected spherical space form has trivial Γ) with the Moise smoothing bridge that turns the
resulting topological identification into the homeomorphism used by the topological Poincaré
target.  The pinned mathlib contains neither.  The structure is a function field, never a
postulate: it occurs only as a hypothesis of conditional theorems. -/
structure SphericalPieceRecognition : Type 1 where
  /-- Every simply connected spherical piece is homeomorphic to `𝕊³`. -/
  recognize : ∀ {X : TopSpace.{0}}, SphericalPiece X → SimplyConnectedSpace X.Carrier →
    Nonempty (X.Carrier ≃ₜ SphereThree)

namespace SphericalPieceRecognition

/-- **Checked application.**  The recognition bridge applied to a spherical piece whose
carrier is simply connected produces a homeomorphism to `𝕊³`. -/
theorem recognize_piece (R : SphericalPieceRecognition) {X : TopSpace.{0}}
    (P : SphericalPiece X) (h : SimplyConnectedSpace X.Carrier) :
    Nonempty (X.Carrier ≃ₜ SphereThree) :=
  R.recognize P h

end SphericalPieceRecognition

end Recognition

end D7

end Poincare
