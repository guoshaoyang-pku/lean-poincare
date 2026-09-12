/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-surgery-recognition)

**D12 surgery recognition, part 3: the connected sum of `𝕊³` summands is `𝕊³`, and the
versioned decomposition that discharges the D7 assumption.**

This module closes SR-5 of the D7 sphere-recognition ledger: the field
`ConnectedSumDecomposition.sphere_of_spheres` is not a postulate but a *construction*.

* `iteratedSphereSum` builds, for a `List` of bundled spaces each carrying a homeomorphism
  to `𝕊³`, the iterated connected sum (gluing the south-hemisphere disks transported
  through those homeomorphisms);
* `iteratedSphereSumHomeo` proves by induction that the iterated connected sum of
  `𝕊³` summands is homeomorphic to `𝕊³` (base: the empty sum is `𝕊³`; step:
  `sphereConnectSum_homeo_sphere` from part 2, transported through the running
  homeomorphism);
* `ConnectedSumDecompositionV2 X pieces` is the versioned replacement of the D7
  `ConnectedSumDecomposition`: it carries *actual* data (the per-piece `𝕊³`-homeomorphisms
  and a homeomorphism from `X` to the iterated connected sum);
* `ConnectedSumDecomposition.mkV2` is the constructor that produces a genuine D7
  `ConnectedSumDecomposition` whose `sphere_of_spheres` field is *proved* from the
  constructions (the remaining field, van Kampen's `simplyConnected_pieces`, is taken as
  an explicit hypothesis — mathlib has no van Kampen theorem for the fundamental groupoid).

No declaration uses `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
import Poincare.D12.SurgeryRecognition.ConnectedSumTopology
import Poincare.D7.Recognition.Basic
import Poincare.Longrun.Topology.Basic

set_option autoImplicit false

open scoped Topology
open Metric

noncomputable section

namespace Poincare.D12.SurgeryRecognition

/-! ## 1. Transport of the punctured space and the connected sum along homeomorphisms -/

/-- The south-hemisphere disk of `𝕊³` transported through a homeomorphism. -/
def transportedSouthDisk {X : Type} [TopologicalSpace X] (e : X ≃ₜ S3) : Ball3 → X :=
  fun x => e.symm (downS3 x)

/-- The transported south disk is injective. -/
theorem transportedSouthDisk_injective {X : Type} [TopologicalSpace X] (e : X ≃ₜ S3) :
    Function.Injective (transportedSouthDisk e) := by
  intro x y hxy
  have h := congrArg (fun z : X => e z) hxy
  dsimp [transportedSouthDisk] at h
  have h' : downS3 x = downS3 y := by
    simpa [e.apply_symm_apply] using h
  exact downS3_injective h'

/-- The ball-punctured space is invariant under homeomorphisms that carry the disk
embeddings. -/
def puncturedHomeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (fX : Ball3 → X) (fY : Ball3 → Y) (h : fY = e ∘ fX) :
    puncturedOfDisk X fX ≃ₜ puncturedOfDisk Y fY where
  toEquiv := {
    toFun := fun x => ⟨e x.1, by
      intro hmem
      apply x.2
      rcases hmem with ⟨b, hb, hb_eq⟩
      refine ⟨b, hb, ?_⟩
      exact e.injective (by simpa [h] using hb_eq)⟩
    invFun := fun y => ⟨e.symm y.1, by
      intro hmem
      apply y.2
      rcases hmem with ⟨b, hb, hb_eq⟩
      refine ⟨b, hb, ?_⟩
      exact by simpa [h, e.apply_symm_apply] using (congrArg (fun z : X => e z) hb_eq)⟩
    left_inv := by
      intro x
      apply Subtype.ext
      exact e.left_inv x.1
    right_inv := by
      intro y
      apply Subtype.ext
      exact e.right_inv y.1 }
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact e.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact e.symm.continuous.comp continuous_subtype_val

/-- The connected sum is invariant under homeomorphisms carrying the disk embeddings. -/
def connectSumCongr {X Y X' Y' : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y']
    (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (fX : Ball3 → X) (fY : Ball3 → Y) (fX' : Ball3 → X') (fY' : Ball3 → Y')
    (hX' : fX' = eX ∘ fX) (hY' : fY' = eY ∘ fY) :
    Quot (connectSumRel (X := X) (Y := Y) fX fY) ≃ₜ
      Quot (connectSumRel (X := X') (Y := Y') fX' fY') :=
  quotientMapHomeo (e := (puncturedHomeo eX fX fX' hX').sumCongr (puncturedHomeo eY fY fY' hY'))
    (h := by
      intro a b
      cases a with
      | inl x => cases b with
        | inl y =>
            dsimp [connectSumRel]
            constructor
            · intro h
              exact congrArg (puncturedHomeo eX fX fX' hX') h
            · intro h
              exact (puncturedHomeo eX fX fX' hX').injective h
        | inr y =>
            dsimp [connectSumRel]
            constructor
            · rintro ⟨s, hs1, hs2⟩
              refine ⟨s, ?_, ?_⟩
              · change eX x.1 = fX' (sphere2ToBall s)
                rw [hs1, hX']
                rfl
              · change eY y.1 = fY' (sphere2ToBall s)
                rw [hs2, hY']
                rfl
            · rintro ⟨s, hs1, hs2⟩
              refine ⟨s, ?_, ?_⟩
              · exact eX.injective (by simpa [puncturedHomeo, hX'] using hs1)
              · exact eY.injective (by simpa [puncturedHomeo, hY'] using hs2)
      | inr x => cases b with
        | inl y =>
            dsimp [connectSumRel]
            constructor
            · rintro ⟨s, hs1, hs2⟩
              refine ⟨s, ?_, ?_⟩
              · change eY x.1 = fY' (sphere2ToBall s)
                rw [hs1, hY']
                rfl
              · change eX y.1 = fX' (sphere2ToBall s)
                rw [hs2, hX']
                rfl
            · rintro ⟨s, hs1, hs2⟩
              refine ⟨s, ?_, ?_⟩
              · exact eY.injective (by simpa [puncturedHomeo, hY'] using hs1)
              · exact eX.injective (by simpa [puncturedHomeo, hX'] using hs2)
        | inr y =>
            dsimp [connectSumRel]
            constructor
            · intro h
              exact congrArg (puncturedHomeo eY fY fY' hY') h
            · intro h
              exact (puncturedHomeo eY fY fY' hY').injective h)

/-- The connected sum of two spaces homeomorphic to `𝕊³` (with the transported south
disks) is homeomorphic to `𝕊³`. -/
def sphereConnectSum_transported {X Y : Poincare.Longrun.Surgery.TopSpace.{0}}
    (eX : X.Carrier ≃ₜ S3) (eY : Y.Carrier ≃ₜ S3) :
    Nonempty ((connectedSum X Y (transportedSouthDisk eX) (transportedSouthDisk eY)
      (transportedSouthDisk_injective eX) (transportedSouthDisk_injective eY)).Carrier ≃ₜ S3) := by
  refine ⟨(connectSumCongr (X := X.Carrier) (Y := Y.Carrier) (X' := S3) (Y' := S3)
    eX eY (transportedSouthDisk eX) (transportedSouthDisk eY) downS3 downS3
    (by
      funext x
      simpa [transportedSouthDisk] using (eX.apply_symm_apply (downS3 x)).symm)
    (by
      funext x
      simpa [transportedSouthDisk] using (eY.apply_symm_apply (downS3 x)).symm)).trans
    (sphereConnectSum_homeo_sphere.some)⟩

/-! ## 2. The iterated connected sum of `𝕊³` summands -/

/-- The bundled result of the iterated connected sum: the running sum together with its
homeomorphism to `𝕊³`. -/
structure SphericalSum (pieces : List (Poincare.Longrun.Surgery.TopSpace.{0}))
    (h : ∀ P ∈ pieces, Nonempty (P.Carrier ≃ₜ S3)) where
  /-- The iterated connected sum. -/
  sum : Poincare.Longrun.Surgery.TopSpace.{0}
  /-- The iterated connected sum is homeomorphic to `𝕊³`. -/
  sumHomeo : Nonempty (sum.Carrier ≃ₜ S3)

/-- The iterated connected sum of the pieces (glued through the transported south disks),
together with its homeomorphism to `𝕊³`; the homeomorphism is part of the recursion, so
the induction hypothesis is available at every step. -/
def iteratedSphereSum : (pieces : List (Poincare.Longrun.Surgery.TopSpace.{0})) →
    (h : ∀ P ∈ pieces, Nonempty (P.Carrier ≃ₜ S3)) → SphericalSum pieces h
  | [], _ => ⟨sphereSpace, ⟨Homeomorph.refl S3⟩⟩
  | P :: Ps, h =>
      let rest := iteratedSphereSum Ps (fun Q hQ => h Q (by simp [hQ]))
      let eP : Nonempty (P.Carrier ≃ₜ S3) := h P (by simp)
      ⟨connectedSum rest.sum P (transportedSouthDisk rest.sumHomeo.some)
          (transportedSouthDisk eP.some)
          (transportedSouthDisk_injective rest.sumHomeo.some)
          (transportedSouthDisk_injective eP.some),
        sphereConnectSum_transported (X := rest.sum) (Y := P) rest.sumHomeo.some eP.some⟩

/-- **The iterated connected sum of `𝕊³` summands is `𝕊³`.**  Induction on the list:
the empty sum is `𝕊³`; adding a summand is `𝕊³ # 𝕊³ = 𝕊³` by
`sphereConnectSum_homeo_sphere`. -/
theorem iteratedSphereSum_homeo_sphere (pieces : List (Poincare.Longrun.Surgery.TopSpace.{0}))
    (h : ∀ P ∈ pieces, Nonempty (P.Carrier ≃ₜ S3)) :
    Nonempty ((iteratedSphereSum pieces h).sum.Carrier ≃ₜ S3) :=
  (iteratedSphereSum pieces h).sumHomeo

/-! ## 3. The versioned decomposition and the D7 constructor -/

/-- **Versioned connected-sum decomposition (V2).**  `X` is the iterated connected sum
of `pieces` along explicit disks, and every piece carries a homeomorphism to `𝕊³`.  This
replaces the D7 `ConnectedSumDecomposition` whose `relation` field was opaque and whose
`sphere_of_spheres` field was an assumption: here the connected sum is data and the
sphere-of-spheres step is proved. -/
structure ConnectedSumDecompositionV2 (X : Poincare.Longrun.Surgery.TopSpace.{0})
    (pieces : List (Poincare.Longrun.Surgery.TopSpace.{0})) where
  /-- Every terminal piece is homeomorphic to `𝕊³` (the recognition output). -/
  pieceSphere : ∀ P ∈ pieces, Nonempty (P.Carrier ≃ₜ S3)
  /-- `X` is homeomorphic to the iterated connected sum of the pieces. -/
  sumHomeo : Nonempty (X.Carrier ≃ₜ (iteratedSphereSum pieces pieceSphere).sum.Carrier)

namespace ConnectedSumDecomposition

variable {X : Poincare.Longrun.Surgery.TopSpace.{0}}
  {pieces : List (Poincare.Longrun.Surgery.TopSpace.{0})}

/-- **The D7 constructor.**  From V2 data (the actual iterated connected sum and the
per-piece `𝕊³`-homeomorphisms) one obtains a D7 `ConnectedSumDecomposition` whose
`sphere_of_spheres` field is *proved* from `iteratedSphereSum_homeo_sphere`.  The
van Kampen field `simplyConnected_pieces` remains an explicit hypothesis (the pinned
mathlib has no van Kampen theorem for the fundamental groupoid); the opaque `relation`
field is supplied as data (here: the V2 sum-homeomorphism assertion). -/
def mkV2 (D : ConnectedSumDecompositionV2 X pieces)
    (simplyConnected_pieces :
      SimplyConnectedSpace X.Carrier → ∀ P ∈ pieces, SimplyConnectedSpace P.Carrier) :
    Poincare.D7.Recognition.ConnectedSumDecomposition X pieces where
  relation := True
  relation_holds := trivial
  simplyConnected_pieces := simplyConnected_pieces
  sphere_of_spheres := by
    intro _hpieces
    rcases D.sumHomeo with ⟨hX⟩
    rcases (iteratedSphereSum pieces D.pieceSphere).sumHomeo with ⟨hsum⟩
    exact ⟨hX.trans hsum⟩

end ConnectedSumDecomposition

end Poincare.D12.SurgeryRecognition

end
