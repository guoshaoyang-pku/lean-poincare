-- A3 round-3 independent downstream-use probe for D12-surgery-recognition.
-- Written by D13-cross-audit-360-cards; not derived from the producer card.
-- It builds an *independent* inhabitant of the V2 interface (the empty
-- connected-sum decomposition of S^3) and then applies the claimed SR-5
-- constructor `ConnectedSumDecomposition.mkV2`, extracting the *proved*
-- `sphere_of_spheres` field.  This is a fresh consumer: it exercises the
-- closure at a concrete instance rather than re-checking the producer's
-- downstream theorem.
import Poincare.D12.SurgeryRecognition.All

open scoped Topology

namespace A3R3

open Poincare Longrun D12 SurgeryRecognition

/-- New independent inhabitant of the V2 interface: the empty connected sum is `𝕊³`. -/
theorem a3_emptyV2 :
    ConnectedSumDecompositionV2 sphereSpace
      ([] : List Poincare.Longrun.Surgery.TopSpace.{0}) where
  pieceSphere := by intro P hP; simp at hP
  sumHomeo := ⟨Homeomorph.refl _⟩

/-- New downstream use: applying the claimed constructor to the independent
inhabitant yields a D7 decomposition whose `sphere_of_spheres` field is proved. -/
theorem a3_mkV2_sphere_of_spheres
    (h : ∀ P ∈ ([] : List Poincare.Longrun.Surgery.TopSpace.{0}),
      Nonempty (P.Carrier ≃ₜ S3)) :
    Nonempty (sphereSpace.Carrier ≃ₜ S3) :=
  (ConnectedSumDecomposition.mkV2 a3_emptyV2
      (by intro _ P hP; simp at hP)).sphere_of_spheres h

end A3R3

#print axioms A3R3.a3_emptyV2
#print axioms A3R3.a3_mkV2_sphere_of_spheres
