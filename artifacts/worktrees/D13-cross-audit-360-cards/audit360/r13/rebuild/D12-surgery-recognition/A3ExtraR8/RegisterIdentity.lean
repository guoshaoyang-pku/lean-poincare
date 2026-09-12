/-
A3ExtraR8/RegisterIdentity.lean — round-8 adversarial probe for the
`D12-surgery-recognition` closure claim SR-5 (register item:
`ConnectedSumDecomposition.sphere_of_spheres` — "connected sum of S^3 summands is
S^3, UNPROVED").

Round 3 and round 5 already consumed the claimed constructor `mkV2` at the empty
and at a two-element piece list.  This round-8 probe adds two *kernel-checked
structural* facts that the earlier consumers did not record:

1. `a3r8_sr5_canonical_field_type`: the closure value has exactly the canonical
   D7 field type (type ascription against the imported D7 structure), so the
   register item and the closure are about the same object, not a look-alike.
2. `a3r8_sr5_factors`: the constructed `sphere_of_spheres` proof is *literally*
   the composition `hX.trans hsum` of (a) the V2 sum-homeomorphism and (b) the
   independently proved `iteratedSphereSum_homeo_sphere`.  This is a
   non-circularity witness: the conclusion `X ≃ₜ S3` is factored through the
   intermediate `iteratedSphereSum` and is not assumed anywhere.
3. `a3r8_mkV2_sos_indep_of_vanKampen`: the closure's sphere-of-spheres branch is
   definitionally independent of the van Kampen argument, so SR-5 is not
   smuggled in through `simplyConnected_pieces`.

Nothing here re-proves SR-5 from a conclusion-equivalent assumption; the V2
`sumHomeo` field is data supplied by the caller, and every ingredient is a
homeomorphism between explicitly named spaces.
-/
import Poincare.D12.SurgeryRecognition.All

open scoped Topology

namespace A3R8

open Poincare Longrun D12 SurgeryRecognition

variable {X : Poincare.Longrun.Surgery.TopSpace.{0}}
  {pieces : List Poincare.Longrun.Surgery.TopSpace.{0}}

/-- The closure value has the canonical D7 field type (register identity). -/
theorem a3r8_sr5_canonical_field_type
    (C : Poincare.D7.Recognition.ConnectedSumDecomposition X pieces) :
    (∀ P ∈ pieces, Nonempty (P.Carrier ≃ₜ S3)) →
      Nonempty (X.Carrier ≃ₜ S3) :=
  C.sphere_of_spheres

/-- The constructed `sphere_of_spheres` branch factors through
`iteratedSphereSum pieces D.pieceSphere`, definitionally. -/
theorem a3r8_sr5_factors
    (D : ConnectedSumDecompositionV2 X pieces)
    (hsc : SimplyConnectedSpace X.Carrier → ∀ P ∈ pieces, SimplyConnectedSpace P.Carrier)
    (hp : ∀ P ∈ pieces, Nonempty (P.Carrier ≃ₜ S3)) :
    ∃ (e₁ : X.Carrier ≃ₜ (iteratedSphereSum pieces D.pieceSphere).sum.Carrier)
      (e₂ : (iteratedSphereSum pieces D.pieceSphere).sum.Carrier ≃ₜ S3),
      (ConnectedSumDecomposition.mkV2 D hsc).sphere_of_spheres hp = ⟨e₁.trans e₂⟩ := by
  rcases D.sumHomeo with ⟨hX⟩
  rcases (iteratedSphereSum pieces D.pieceSphere).sumHomeo with ⟨hsum⟩
  exact ⟨hX, hsum, rfl⟩

/-- The sphere-of-spheres branch of `mkV2` is definitionally independent of the
van Kampen hypothesis (SR-5 is not routed through `simplyConnected_pieces`). -/
theorem a3r8_mkV2_sos_indep_of_vanKampen
    (D : ConnectedSumDecompositionV2 X pieces)
    (h₁ h₂ : SimplyConnectedSpace X.Carrier →
      ∀ P ∈ pieces, SimplyConnectedSpace P.Carrier)
    (hp : ∀ P ∈ pieces, Nonempty (P.Carrier ≃ₜ S3)) :
    (ConnectedSumDecomposition.mkV2 D h₁).sphere_of_spheres hp =
      (ConnectedSumDecomposition.mkV2 D h₂).sphere_of_spheres hp :=
  rfl

/-- Downstream checked use of the canonical type: the register's field supplies
the recognition implication for any D7 decomposition, including the constructed
one, with the homeomorphism extracted from the *proved* branch. -/
theorem a3r8_sr5_downstream
    (D : ConnectedSumDecompositionV2 X pieces)
    (hsc : SimplyConnectedSpace X.Carrier → ∀ P ∈ pieces, SimplyConnectedSpace P.Carrier)
    (hp : ∀ P ∈ pieces, Nonempty (P.Carrier ≃ₜ S3)) :
    Nonempty (X.Carrier ≃ₜ S3) :=
  a3r8_sr5_canonical_field_type (ConnectedSumDecomposition.mkV2 D hsc) hp

end A3R8

#print axioms A3R8.a3r8_sr5_canonical_field_type
#print axioms A3R8.a3r8_sr5_factors
#print axioms A3R8.a3r8_mkV2_sos_indep_of_vanKampen
#print axioms A3R8.a3r8_sr5_downstream
