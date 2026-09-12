/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-surgery-recognition)

**D12 surgery recognition: fail-closed axiom audit.**

Every declaration of the D12 modules is passed through `#print axioms`.
The accepted cone is `{}`, `{propext}`, `{Classical.choice}`, `{Quot.sound}` and
combinations.  Any other axiom — `sorryAx` in particular — fails the audit.
Generated from the declaration list of the audited modules.
-/
import Poincare.D12.SurgeryRecognition.All

namespace Poincare.D12.SurgeryRecognition

#print axioms R3
#print axioms R4
#print axioms Ball3
#print axioms S2Set
#print axioms S2
#print axioms S3Set
#print axioms S3
#print axioms OpenBall3
#print axioms S3Set_eq
#print axioms sphere_norm_eq_one
#print axioms sphere2_norm_eq_one
#print axioms sphere2_norm_eq_one_of_mem
#print axioms consVec3
#print axioms tailVec
#print axioms tailVec_consVec3
#print axioms consVec3_self_tail
#print axioms consVec3_fst
#print axioms norm_sq_consVec3
#print axioms tailVec_continuous
#print axioms consVec3_continuous
#print axioms tailVec_norm_le_one_of_norm_eq_one
#print axioms tailVec_norm_eq_one_of_norm_eq_one_and_fst_eq_zero
#print axioms ball3_norm_le_one
#print axioms height
#print axioms height_sq
#print axioms height_continuous
#print axioms upPoint
#print axioms downPoint
#print axioms upPoint_mem
#print axioms downPoint_mem
#print axioms upPoint_continuous
#print axioms downPoint_continuous
#print axioms upPoint_fst
#print axioms downPoint_fst
#print axioms northHemisphere
#print axioms southHemisphere
#print axioms equator
#print axioms up
#print axioms down
#print axioms up_continuous
#print axioms down_continuous
#print axioms sphereBallPart
#print axioms sphereBallPart_continuous
#print axioms northBall
#print axioms southBall
#print axioms northBall_continuous
#print axioms southBall_continuous
#print axioms northBall_up
#print axioms southBall_down
#print axioms height_sphereBallPart_eq_fst_of_nonneg
#print axioms height_sphereBallPart_eq_neg_fst_of_nonpos
#print axioms up_northBall
#print axioms down_southBall
#print axioms up_injective
#print axioms down_injective
#print axioms northHemisphereHomeo
#print axioms southHemisphereHomeo
#print axioms hemisphere_cover
#print axioms north_south_inter_eq_equator
#print axioms sphere2ToBall
#print axioms sphere2ToBall_continuous
#print axioms equatorHomeoS2
#print axioms glueRel
#print axioms glueRel_equiv
#print axioms DoubleBall
#print axioms glue_eq
#print axioms toSpherePre
#print axioms toSpherePre_respects
#print axioms toSphere
#print axioms toSphere_continuous
#print axioms ofSphere
#print axioms ofSphere_continuous
#print axioms toSphere_ofSphere
#print axioms ofSphere_toSphere
#print axioms doubleBallHomeoSphere
#print axioms ballOrigin
#print axioms northPole
#print axioms southPole
#print axioms toSphere_origin_first
#print axioms toSphere_origin_second
#print axioms ballEquator
#print axioms equator_both_copies
#print axioms quotientMapHomeo
#print axioms openBallInBall
#print axioms puncturedOfDisk
#print axioms connectSumRel
#print axioms sphere2ToBall_injective
#print axioms connectSumRel_equiv
#print axioms connectedSum
#print axioms downS3
#print axioms downS3_injective
#print axioms downPoint_sphereBallPart_eq_of_nonpos
#print axioms downS3_sphereBallPart_eq_of_eq_zero
#print axioms mem_downS3_openBall_iff
#print axioms southPuncture
#print axioms southPunctureHomeo
#print axioms downS3_image_S2_eq_equator
#print axioms sphereSpace
#print axioms sphereConnectSum
#print axioms hemiGlueRel
#print axioms hemiGlueRel_equiv
#print axioms up_mem_equator_iff
#print axioms northHemisphereHomeo_symm_apply
#print axioms northBall_injective
#print axioms northBall_mem_S2_iff
#print axioms hemiGlueRel_transport
#print axioms connectSumRel_transport
#print axioms sphereConnectSum_homeo_hemiQuot
#print axioms hemiQuot_homeo_DoubleBall
#print axioms sphereConnectSum_homeo_sphere
#print axioms transportedSouthDisk
#print axioms transportedSouthDisk_injective
#print axioms puncturedHomeo
#print axioms connectSumCongr
#print axioms sphereConnectSum_transported
#print axioms SphericalSum
#print axioms iteratedSphereSum
#print axioms iteratedSphereSum_homeo_sphere
#print axioms ConnectedSumDecompositionV2
#print axioms ConnectedSumDecomposition.mkV2
#print axioms RemainingRecognitionHypotheses
#print axioms EndGameDecomposition
#print axioms endGame_finalTopology
#print axioms stage6Target_of_v2decomposition
#print axioms connectedSumDecomposition_expanded
#print axioms extinctionCertificate_expanded
#print axioms sphericalPieceRecognition_expanded
#print axioms recognitionHypotheses_expanded

#check AntipodalGroup -- abbrev: no separate axiom cone; body covered by the token scan and by downstream cones
#print axioms antipodalVec
#print axioms antipodalVec_one
#print axioms antipodal
#print axioms antipodal_one
#print axioms antipodal_of_ne_one
#print axioms instSMulAntipodalGroupS3
#print axioms instMulActionAntipodalGroupS3
#print axioms instContinuousConstSMulAntipodalGroupS3
#print axioms antipodal_free
#print axioms antipodal_disjoint_ball
#print axioms finiteFreeOrbit_isQuotientCoveringMap
#print axioms antipodalQuotientCovering
#print axioms antipodalCoveringMap
#print axioms antipodalQuotient
#print axioms antipodal_fiber_equiv
#print axioms antipodalGroup_card
#print axioms antipodal_fiber_card_two
#print axioms antipodal_two_sheets
#print axioms SphericalSpaceFormModel
#print axioms SphericalSpaceFormModel.quotient
#print axioms SphericalSpaceFormModel.coveringQuotient
#print axioms SphericalSpaceFormModel.covering
#print axioms antipodalModel
#print axioms antipodalModel_nontrivial
#print axioms quotientHomeoOfSubsingleton
#print axioms IsSpaceFormModelOf
#print axioms sphericalPieceRecognition_of
#print axioms RemainingRecognitionHypothesesV2
#print axioms RemainingRecognitionHypothesesV2.toRemaining
#print axioms stage6Target_of_v2hypotheses
#print axioms sphereThree_pathConnectedSpace
#print axioms SphericalSpaceFormModel.spaceFormProjection
#print axioms SphericalSpaceFormModel.spaceFormProjection_covering
#print axioms SphericalSpaceFormModel.spaceFormFiberEquivGroup
#print axioms SphericalSpaceFormModel.spaceForm_monodromy_trivial
#print axioms SphericalSpaceFormModel.spaceForm_monodromy_transitive
#print axioms SphericalSpaceFormModel.spaceForm_fiber_subsingleton
#print axioms deckTrivial_of_simplyConnected_quotient
#print axioms sphericalPieceRecognition_of_spaceForm
#print axioms RemainingRecognitionHypothesesV3
#print axioms Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV3.toRemainingV2
#print axioms Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV3.toRemaining
#print axioms stage6Target_of_v3hypotheses

end Poincare.D12.SurgeryRecognition
