-- A3 round-5 independent downstream-use probe for D12-surgery-recognition.
-- Written by D13-cross-audit-360-cards; not derived from the producer card.
-- Round 3 consumed the claimed SR-5 closure only at the *empty* piece list.
-- This probe consumes it at a genuinely nonempty list (two S^3 summands),
-- exercising the recursive branch of `iteratedSphereSum` and
-- `sphereConnectSum_transported`, then feeds the result through the claimed
-- constructor `ConnectedSumDecomposition.mkV2` and extracts the *proved*
-- `sphere_of_spheres` field.  Nothing from the producer's own downstream
-- theorem is reused.
import Poincare.D12.SurgeryRecognition.All

open scoped Topology

namespace A3R5

open Poincare Longrun D12 SurgeryRecognition

/-- Fresh piece-sphere data for a two-element list, each piece via the identity
homeomorphism to `𝕊³`. -/
theorem a3_twoFold_pieceSphere :
    ∀ P ∈ ([sphereSpace, sphereSpace] : List Poincare.Longrun.Surgery.TopSpace.{0}),
      Nonempty (P.Carrier ≃ₜ S3) := by
  intro P hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl <;> exact ⟨Homeomorph.refl _⟩

/-- The proved iterated-sum theorem consumed at a nonempty list (two summands). -/
theorem a3_twoFold_homeo :
    Nonempty ((iteratedSphereSum [sphereSpace, sphereSpace]
      a3_twoFold_pieceSphere).sum.Carrier ≃ₜ S3) :=
  iteratedSphereSum_homeo_sphere [sphereSpace, sphereSpace] a3_twoFold_pieceSphere

/-- Fresh independent V2 inhabitant with two summands (the empty-list case was
the round-3 probe). -/
theorem a3_twoFoldV2 :
    ConnectedSumDecompositionV2 sphereSpace [sphereSpace, sphereSpace] where
  pieceSphere := a3_twoFold_pieceSphere
  sumHomeo := ⟨(Homeomorph.refl S3).trans a3_twoFold_homeo.some.symm⟩

/-- Fresh downstream use of the claimed SR-5 constructor on the nonempty instance. -/
theorem a3_twoFold_mkV2_sphere_of_spheres
    (hsc : SimplyConnectedSpace sphereSpace.Carrier →
      ∀ P ∈ ([sphereSpace, sphereSpace] : List Poincare.Longrun.Surgery.TopSpace.{0}),
        SimplyConnectedSpace P.Carrier) :
    Nonempty (sphereSpace.Carrier ≃ₜ S3) :=
  (ConnectedSumDecomposition.mkV2 a3_twoFoldV2 hsc).sphere_of_spheres
    a3_twoFold_pieceSphere

end A3R5

#print axioms A3R5.a3_twoFold_homeo
#print axioms A3R5.a3_twoFoldV2
#print axioms A3R5.a3_twoFold_mkV2_sphere_of_spheres
