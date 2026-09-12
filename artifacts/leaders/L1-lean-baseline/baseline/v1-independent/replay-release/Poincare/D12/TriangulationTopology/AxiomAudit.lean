/-
Copyright (c) 2026 Poincare Lab (task D12-triangulation-topology). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Poincare.D12.TriangulationTopology.SphereGluing
import Poincare.D12.TriangulationTopology.Downstream
import Poincare.D12.TriangulationTopology.MoiseBranch
import Poincare.D12.TriangulationTopology.CoveringLemma
import Poincare.D12.TriangulationTopology.AntipodalQuotient
import Poincare.D12.TriangulationTopology.SimplexBoundary
import Poincare.D12.TriangulationTopology.HemisphereDisk
import Poincare.D12.TriangulationTopology.SimplexCone
import Poincare.D12.TriangulationTopology.SphereSimplyConnected
import Poincare.D12.TriangulationTopology.SpherePolygonal
import Poincare.D12.TriangulationTopology.SphereMissedPoint
import Poincare.D12.TriangulationTopology.SphereSimplyConnectedMain
import Poincare.D12.TriangulationTopology.SphereRecognition
import Poincare.D12.TriangulationTopology.DiskGluing
import Poincare.D12.TriangulationTopology.SphereOfTwoDisks
import Poincare.D12.TriangulationTopology.TwoHemisphereInstance

/-!
# D12 TriangulationTopology task-local axiom audit

This module emits `#print axioms` for every new declaration of `SphereGluing.lean`,
`CoveringLemma.lean` and `AntipodalQuotient.lean`.
The fail-closed programmatic audit is `tools/d12_axiom_audit.py` in the worktree root:
it parses this module's output and fails unless every printed axiom set is contained in
`{propext, Classical.choice, Quot.sound}` and every expected declaration name is present.
A negative control (`NegControl/NegControl.lean`) declares a forbidden axiom; the audit
script must *reject* it, which is itself checked.  The negative-control module is never
imported by any proof module.
-/

#print axioms Poincare.D12.TriangulationTopology.disk_boundary_eq_sphere
#print axioms Poincare.D12.TriangulationTopology.sphereCompactSpace
#print axioms Poincare.D12.TriangulationTopology.diskCompactSpace
#print axioms Poincare.D12.TriangulationTopology.iccCompactSpace
#print axioms Poincare.D12.TriangulationTopology.diskNonempty
#print axioms Poincare.D12.TriangulationTopology.esnoc
#print axioms Poincare.D12.TriangulationTopology.esnoc_last
#print axioms Poincare.D12.TriangulationTopology.esnoc_castSucc
#print axioms Poincare.D12.TriangulationTopology.esnoc_injective2
#print axioms Poincare.D12.TriangulationTopology.norm_sq_esnoc
#print axioms Poincare.D12.TriangulationTopology.norm_eq_one_iff_norm_sq_eq_one
#print axioms Poincare.D12.TriangulationTopology.sphereNonempty
#print axioms Poincare.D12.TriangulationTopology.norm_esnoc_smul_sqrt_sub_sq_eq_one
#print axioms Poincare.D12.TriangulationTopology.coneRel
#print axioms Poincare.D12.TriangulationTopology.coneMap_mem
#print axioms Poincare.D12.TriangulationTopology.coneMap
#print axioms Poincare.D12.TriangulationTopology.continuous_coneMap
#print axioms Poincare.D12.TriangulationTopology.coneMap_respects
#print axioms Poincare.D12.TriangulationTopology.coneMapQuot
#print axioms Poincare.D12.TriangulationTopology.continuous_coneMapQuot
#print axioms Poincare.D12.TriangulationTopology.coneMapQuot_surjective
#print axioms Poincare.D12.TriangulationTopology.coneMapQuot_injective
#print axioms Poincare.D12.TriangulationTopology.coneQuotHomeoDisk
#print axioms Poincare.D12.TriangulationTopology.suspRel
#print axioms Poincare.D12.TriangulationTopology.suspMap_mem
#print axioms Poincare.D12.TriangulationTopology.suspMap
#print axioms Poincare.D12.TriangulationTopology.continuous_suspMap
#print axioms Poincare.D12.TriangulationTopology.suspMap_respects
#print axioms Poincare.D12.TriangulationTopology.suspMapQuot
#print axioms Poincare.D12.TriangulationTopology.continuous_suspMapQuot
#print axioms Poincare.D12.TriangulationTopology.sqrt_one_sub_sq_eq_norm_of_norm_sq_add_sq_eq_one
#print axioms Poincare.D12.TriangulationTopology.suspMapQuot_surjective
#print axioms Poincare.D12.TriangulationTopology.suspMapQuot_injective
#print axioms Poincare.D12.TriangulationTopology.suspQuotHomeoSphere
#print axioms Poincare.D12.TriangulationTopology.doubleDiskRel
#print axioms Poincare.D12.TriangulationTopology.doubleDiskMap_mem_pos
#print axioms Poincare.D12.TriangulationTopology.doubleDiskMap_mem_neg
#print axioms Poincare.D12.TriangulationTopology.doubleDiskMap
#print axioms Poincare.D12.TriangulationTopology.continuous_doubleDiskMap
#print axioms Poincare.D12.TriangulationTopology.doubleDiskMap_respects
#print axioms Poincare.D12.TriangulationTopology.doubleDiskMapQuot
#print axioms Poincare.D12.TriangulationTopology.continuous_doubleDiskMapQuot
#print axioms Poincare.D12.TriangulationTopology.doubleDiskMapQuot_surjective
#print axioms Poincare.D12.TriangulationTopology.eq_neg_self_of_sqrt_eq_neg_sqrt
#print axioms Poincare.D12.TriangulationTopology.doubleDiskMapQuot_injective
#print axioms Poincare.D12.TriangulationTopology.doubleDiskQuotHomeoSphere
#print axioms Poincare.D12.TriangulationTopology.coneQuotHomeoTopCatDisk
#print axioms Poincare.D12.TriangulationTopology.suspQuotHomeoTopCatSphere
#print axioms Poincare.D12.TriangulationTopology.doubleDiskQuotHomeoTopCatSphere


#check Poincare.D12.TriangulationTopology.LocallyEuclideanOfDimension
#check Poincare.D12.TriangulationTopology.vanKampenSimplyConnectedCover
#check Poincare.D12.TriangulationTopology.simplexBoundaryHomeoSphere
#check Poincare.D12.TriangulationTopology.moiseWeakenedCW
#check Poincare.D12.TriangulationTopology.sphereThree_eq_sphere3
#check Poincare.D12.TriangulationTopology.disk3_boundary_eq_sphere2
#check Poincare.D12.TriangulationTopology.coneQuotNonempty
#check Poincare.D12.TriangulationTopology.suspQuotNonempty
#check Poincare.D12.TriangulationTopology.doubleDiskQuotNonempty
#check Poincare.D12.TriangulationTopology.sphereThreeGluedDisks
#check Poincare.D12.TriangulationTopology.sphereThreeSuspension
#check Poincare.D12.TriangulationTopology.coneOverSphere2HomeoDisk3

#check Poincare.D12.TriangulationTopology.coveringOfSimplyConnectedIsHomeo
#check Poincare.D12.TriangulationTopology.sphericalSpaceFormRecognition

#print axioms Poincare.D12.TriangulationTopology.coveringOfSimplyConnectedIsHomeo
#print axioms Poincare.D12.TriangulationTopology.coveringOfSimplyConnectedIsHomeo_bijective
#print axioms Poincare.D12.TriangulationTopology.coveringOfSimplyConnectedIsHomeo_of_nonempty
#print axioms Poincare.D12.TriangulationTopology.coveringMap_surjective_of_pathConnected
#print axioms Poincare.D12.TriangulationTopology.coveringMap_injective_of_simplyConnected
#print axioms Poincare.D12.TriangulationTopology.trivialization_id
#print axioms Poincare.D12.TriangulationTopology.isCoveringMap_id
#print axioms Poincare.D12.TriangulationTopology.diskContractible
#print axioms Poincare.D12.TriangulationTopology.diskSimplyConnected
#print axioms Poincare.D12.TriangulationTopology.diskCoverPipeline
#print axioms Poincare.D12.TriangulationTopology.locallyCompactSpace_of_compact_t2
#print axioms Poincare.D12.TriangulationTopology.zmod2_eq_zero_or_one
#print axioms Poincare.D12.TriangulationTopology.zmod2Mul_eq_ofAdd_one_or_one
#print axioms Poincare.D12.TriangulationTopology.antipodal_mul_self
#print axioms Poincare.D12.TriangulationTopology.sphere_eq_neg_self_impossible
#print axioms Poincare.D12.TriangulationTopology.antipodalSmul
#print axioms Poincare.D12.TriangulationTopology.one_ne_ofAdd_one
#print axioms Poincare.D12.TriangulationTopology.antipodalSmul_one
#print axioms Poincare.D12.TriangulationTopology.antipodalSmul_ofAdd_one
#print axioms Poincare.D12.TriangulationTopology.antipodalMulAction
#print axioms Poincare.D12.TriangulationTopology.antipodal_smul_one_eq
#print axioms Poincare.D12.TriangulationTopology.antipodal_smul_ofAdd_one_eq
#print axioms Poincare.D12.TriangulationTopology.continuous_antipodal_ofAdd_one
#print axioms Poincare.D12.TriangulationTopology.antipodalContinuousConstSMul
#print axioms Poincare.D12.TriangulationTopology.antipodalIsCancelSMul
#print axioms Poincare.D12.TriangulationTopology.RealProjective
#print axioms Poincare.D12.TriangulationTopology.antipodalQuotientCovering
#print axioms Poincare.D12.TriangulationTopology.rpCompactSpace
#print axioms Poincare.D12.TriangulationTopology.rpT2Space
#print axioms Poincare.D12.TriangulationTopology.rpNonempty
#print axioms Poincare.D12.TriangulationTopology.spherePathConnectedSpace_of_pos
#print axioms Poincare.D12.TriangulationTopology.rpPathConnectedSpace_of_pos
#print axioms Poincare.D12.TriangulationTopology.sphericalSpaceFormRecognition

#print axioms Poincare.D12.TriangulationTopology.simplexCenter
#print axioms Poincare.D12.TriangulationTopology.simplexCenter_pos
#print axioms Poincare.D12.TriangulationTopology.simplexCenter_total
#print axioms Poincare.D12.TriangulationTopology.simplexBoundarySet
#print axioms Poincare.D12.TriangulationTopology.SimplexBoundaryFn
#print axioms Poincare.D12.TriangulationTopology.simplexDir
#print axioms Poincare.D12.TriangulationTopology.simplexDir_last
#print axioms Poincare.D12.TriangulationTopology.simplexDir_castSucc
#print axioms Poincare.D12.TriangulationTopology.simplexDir_sum
#print axioms Poincare.D12.TriangulationTopology.simplexMin
#print axioms Poincare.D12.TriangulationTopology.simplexMin_le
#print axioms Poincare.D12.TriangulationTopology.le_simplexMin
#print axioms Poincare.D12.TriangulationTopology.simplexMin_attains
#print axioms Poincare.D12.TriangulationTopology.simplexMin_neg_of_unit
#print axioms Poincare.D12.TriangulationTopology.continuous_simplexDir_apply
#print axioms Poincare.D12.TriangulationTopology.continuous_simplexDir
#print axioms Poincare.D12.TriangulationTopology.continuous_simplexMin
#print axioms Poincare.D12.TriangulationTopology.simplexLambda
#print axioms Poincare.D12.TriangulationTopology.simplexLambda_pos_of_unit
#print axioms Poincare.D12.TriangulationTopology.continuous_sphere_simplexLambda
#print axioms Poincare.D12.TriangulationTopology.truncToCenter
#print axioms Poincare.D12.TriangulationTopology.truncToCenter_ne_zero
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryToSphere
#print axioms Poincare.D12.TriangulationTopology.continuous_truncToCenter
#print axioms Poincare.D12.TriangulationTopology.continuous_simplexBoundaryToSphere
#print axioms Poincare.D12.TriangulationTopology.sphereToSimplexBoundary
#print axioms Poincare.D12.TriangulationTopology.sphereToSimplexBoundary_mem
#print axioms Poincare.D12.TriangulationTopology.sphereToSimplexBoundaryFn
#print axioms Poincare.D12.TriangulationTopology.continuous_sphereToSimplexBoundaryFn
#print axioms Poincare.D12.TriangulationTopology.truncToCenter_sphereToSimplexBoundary
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryToSphere_sphereToSimplexBoundary
#print axioms Poincare.D12.TriangulationTopology.simplexMin_eq_zero_of_mem_boundary
#print axioms Poincare.D12.TriangulationTopology.simplexDir_of_simplexBoundaryToSphere
#print axioms Poincare.D12.TriangulationTopology.simplexMin_of_simplexBoundaryToSphere
#print axioms Poincare.D12.TriangulationTopology.sphereToSimplexBoundary_simplexBoundaryToSphere
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryFnHomeoSphere
#print axioms Poincare.D12.TriangulationTopology.SimplexBoundary
#print axioms Poincare.D12.TriangulationTopology.range_weights_eq_simplex
#print axioms Poincare.D12.TriangulationTopology.image_weights_boundary_eq
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryHomeoBoundaryFn
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryCompactSpace
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryT2Space
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryNonempty
#print axioms Poincare.D12.TriangulationTopology.LowerHemisphere
#print axioms Poincare.D12.TriangulationTopology.esnoc'
#print axioms Poincare.D12.TriangulationTopology.esnoc'_last
#print axioms Poincare.D12.TriangulationTopology.esnoc'_castSucc
#print axioms Poincare.D12.TriangulationTopology.norm_sq_esnoc'
#print axioms Poincare.D12.TriangulationTopology.lowerTrunc
#print axioms Poincare.D12.TriangulationTopology.esnoc'_lowerTrunc_eq
#print axioms Poincare.D12.TriangulationTopology.trunc_norm_sq_add_last_sq_eq_one
#print axioms Poincare.D12.TriangulationTopology.sqrt_one_sub_trunc_norm_sq_eq_neg_last
#print axioms Poincare.D12.TriangulationTopology.lowerHemisphereToDisk
#print axioms Poincare.D12.TriangulationTopology.diskToLowerHemisphere
#print axioms Poincare.D12.TriangulationTopology.continuous_esnoc'
#print axioms Poincare.D12.TriangulationTopology.continuous_lowerHemisphereToDisk
#print axioms Poincare.D12.TriangulationTopology.continuous_diskToLowerHemisphere
#print axioms Poincare.D12.TriangulationTopology.lowerHemisphereToDisk_diskToLowerHemisphere
#print axioms Poincare.D12.TriangulationTopology.diskToLowerHemisphere_lowerHemisphereToDisk
#print axioms Poincare.D12.TriangulationTopology.lowerHemisphereHomeoDisk
#print axioms Poincare.D12.TriangulationTopology.lowerHemisphereCompactSpace
#print axioms Poincare.D12.TriangulationTopology.lowerHemisphereT2Space
#print axioms Poincare.D12.TriangulationTopology.lowerHemisphereNonempty
#print axioms Poincare.D12.TriangulationTopology.vanKampenSimplyConnectedCover
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryHomeoSphere
#print axioms Poincare.D12.TriangulationTopology.moiseWeakenedCW
#print axioms Poincare.D12.TriangulationTopology.LocallyEuclideanOfDimension
#print axioms Poincare.D12.TriangulationTopology.sphereThree_eq_sphere3
#print axioms Poincare.D12.TriangulationTopology.disk3_boundary_eq_sphere2
#print axioms Poincare.D12.TriangulationTopology.coneQuotNonempty
#print axioms Poincare.D12.TriangulationTopology.suspQuotNonempty
#print axioms Poincare.D12.TriangulationTopology.doubleDiskQuotNonempty
#print axioms Poincare.D12.TriangulationTopology.sphereThreeGluedDisks
#print axioms Poincare.D12.TriangulationTopology.sphereThreeSuspension
#print axioms Poincare.D12.TriangulationTopology.coneOverSphere2HomeoDisk3

#print axioms Poincare.D12.TriangulationTopology.simplexSet
#print axioms Poincare.D12.TriangulationTopology.simplexFnNonempty
#print axioms Poincare.D12.TriangulationTopology.simplexFnT2Space
#print axioms Poincare.D12.TriangulationTopology.simplexConeMap
#print axioms Poincare.D12.TriangulationTopology.simplexConeMap_mem
#print axioms Poincare.D12.TriangulationTopology.continuous_sphereToSimplexBoundary_apply
#print axioms Poincare.D12.TriangulationTopology.continuous_sphereToSimplexBoundary
#print axioms Poincare.D12.TriangulationTopology.continuous_simplexConeMap
#print axioms Poincare.D12.TriangulationTopology.simplexConeMap_respects
#print axioms Poincare.D12.TriangulationTopology.simplexConeMapQuot
#print axioms Poincare.D12.TriangulationTopology.continuous_simplexConeMapQuot
#print axioms Poincare.D12.TriangulationTopology.truncToCenter_simplexConeMap
#print axioms Poincare.D12.TriangulationTopology.simplex_point_eq_center_add_norm_mul_dir
#print axioms Poincare.D12.TriangulationTopology.simplexConeMapQuot_injective
#print axioms Poincare.D12.TriangulationTopology.simplexConeMapQuot_surjective
#print axioms Poincare.D12.TriangulationTopology.sphereConeHomeoSimplex
#print axioms Poincare.D12.TriangulationTopology.simplexHomeoConeQuot
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryConeRel
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryConeMap
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryConeMap_mem
#print axioms Poincare.D12.TriangulationTopology.continuous_simplexBoundaryConeMap
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryConeMap_respects
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryConeMapQuot
#print axioms Poincare.D12.TriangulationTopology.continuous_simplexBoundaryConeMapQuot
#print axioms Poincare.D12.TriangulationTopology.simplexMin_le_center
#print axioms Poincare.D12.TriangulationTopology.simplexMin_lt_center_of_ne_center
#print axioms Poincare.D12.TriangulationTopology.simplexRadialTime
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryPoint
#print axioms Poincare.D12.TriangulationTopology.simplexRadialTime_nonneg
#print axioms Poincare.D12.TriangulationTopology.simplexRadialTime_le_one
#print axioms Poincare.D12.TriangulationTopology.simplexRadialTime_pos_of_ne_center
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryPoint_mem_of_ne_center
#print axioms Poincare.D12.TriangulationTopology.simplexRadialTime_eq_of_radial_repr
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryPoint_eq_of_radial_repr
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryConeMapQuot_injective
#print axioms Poincare.D12.TriangulationTopology.simplexVertexZero
#print axioms Poincare.D12.TriangulationTopology.simplexVertexZero_mem_boundary
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryConeMapQuot_surjective
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryConeHomeoSimplex
#print axioms Poincare.D12.TriangulationTopology.simplexHomeoBoundaryCone
#print axioms Poincare.D12.TriangulationTopology.simplexHomeoStdSimplexFn
#print axioms Poincare.D12.TriangulationTopology.simplexHomeoDisk
#print axioms Poincare.D12.TriangulationTopology.simplexHomeoBoundaryConeStd
#print axioms Poincare.D12.TriangulationTopology.simplexFnCompactSpace
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryFnCompactSpace
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryConeCompactSpace
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryConeT2Space
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryConeNonempty
#print axioms Poincare.D12.TriangulationTopology.quotMapHomeo
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryConeRel_iff_coneRel
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryConeHomeoSphereCone

/-! ## Node 6 (elementary polygonal route): subdivisions, chains, missed point, simply connectedness -/

-- SphereSimplyConnected.lean
#print axioms Poincare.D12.TriangulationTopology.linePoints_le_one_of_not_mem
#print axioms Poincare.D12.TriangulationTopology.linePoints_le_one_of_not_mem'
#print axioms Poincare.D12.TriangulationTopology.exists_not_mem_finset_submodule_union
#print axioms Poincare.D12.TriangulationTopology.span_pair_ne_top
#print axioms Poincare.D12.TriangulationTopology.segment_ne_zero
#print axioms Poincare.D12.TriangulationTopology.norm_segment_sq_lower_bound
#print axioms Poincare.D12.TriangulationTopology.norm_segment_sub_left_le
#print axioms Poincare.D12.TriangulationTopology.norm_segment_sub_left_le_two_thirds
#print axioms Poincare.D12.TriangulationTopology.segmentPath
#print axioms Poincare.D12.TriangulationTopology.segmentPath_sub_left_le_two_thirds
#print axioms Poincare.D12.TriangulationTopology.clampedMap
#print axioms Poincare.D12.TriangulationTopology.clampedMap_clamp_idem
#print axioms Poincare.D12.TriangulationTopology.clampedMap_of_mem_Icc
#print axioms Poincare.D12.TriangulationTopology.continuous_clampedMap
#print axioms Poincare.D12.TriangulationTopology.subdiv
#print axioms Poincare.D12.TriangulationTopology.exists_fine_subdivision
#print axioms Poincare.D12.TriangulationTopology.restrictionPiece
#print axioms Poincare.D12.TriangulationTopology.segPiece
#print axioms Poincare.D12.TriangulationTopology.restrictionChain
#print axioms Poincare.D12.TriangulationTopology.segChain
#print axioms Poincare.D12.TriangulationTopology.idChain
#print axioms Poincare.D12.TriangulationTopology.restrictionChain_source
#print axioms Poincare.D12.TriangulationTopology.restrictionChain_target
#print axioms Poincare.D12.TriangulationTopology.restrictionPiece_apply
#print axioms Poincare.D12.TriangulationTopology.restrictionPiece_id_apply
#print axioms Poincare.D12.TriangulationTopology.idChain_zero_apply
#print axioms Poincare.D12.TriangulationTopology.trans_apply_extend
#print axioms Poincare.D12.TriangulationTopology.restrictionPiece_extend_two_mul
#print axioms Poincare.D12.TriangulationTopology.restrictionPiece_id_extend_two_mul
#print axioms Poincare.D12.TriangulationTopology.restrictionChain_extend_two_mul_sub_one
#print axioms Poincare.D12.TriangulationTopology.restrictionChain_succ_apply
#print axioms Poincare.D12.TriangulationTopology.restrictionChain_apply_eq_clampedMap_idChain
#print axioms Poincare.D12.TriangulationTopology.idChain_zero
#print axioms Poincare.D12.TriangulationTopology.idChain_one
-- SpherePolygonal.lean
#print axioms Poincare.D12.TriangulationTopology.normalize_mem_sphere
#print axioms Poincare.D12.TriangulationTopology.interp_ne_zero
#print axioms Poincare.D12.TriangulationTopology.homotopic_of_dist_le
#print axioms Poincare.D12.TriangulationTopology.dist_restrictionPiece_left
#print axioms Poincare.D12.TriangulationTopology.dist_subdiv_succ_le
#print axioms Poincare.D12.TriangulationTopology.subdiv_not_antipodal
#print axioms Poincare.D12.TriangulationTopology.dist_segPiece_left
#print axioms Poincare.D12.TriangulationTopology.restrictionPiece_homotopic_segPiece
#print axioms Poincare.D12.TriangulationTopology.clampedMap_coe
#print axioms Poincare.D12.TriangulationTopology.clampedMap_of_one_le
#print axioms Poincare.D12.TriangulationTopology.restrictionChain_homotopic_segChain
#print axioms Poincare.D12.TriangulationTopology.loop_cast_source
#print axioms Poincare.D12.TriangulationTopology.loop_cast_target
#print axioms Poincare.D12.TriangulationTopology.loop_homotopic_segChain
-- SphereMissedPoint.lean
#print axioms Poincare.D12.TriangulationTopology.subdivPoint
#print axioms Poincare.D12.TriangulationTopology.segPiece_mem_span
#print axioms Poincare.D12.TriangulationTopology.subdivSpans
#print axioms Poincare.D12.TriangulationTopology.subdivSpans_proper
#print axioms Poincare.D12.TriangulationTopology.segChain_mem_iUnion_spans
#print axioms Poincare.D12.TriangulationTopology.exists_unit_notMem_segChain
-- SphereSimplyConnectedMain.lean
#print axioms Poincare.D12.TriangulationTopology.contractibleSpace_puncturedSphere
#print axioms Poincare.D12.TriangulationTopology.loop_nullhomotopic_of_forall_ne
#print axioms Poincare.D12.TriangulationTopology.subdiv_not_antipodal_all
#print axioms Poincare.D12.TriangulationTopology.simplyConnectedSpace_sphere
#print axioms Poincare.D12.TriangulationTopology.sphereSimplyConnectedSpaceOfFact
#print axioms Poincare.D12.TriangulationTopology.simplyConnectedSpace_sphereThree
#print axioms Poincare.D12.TriangulationTopology.sphereThreeSimplyConnectedSpace
-- SphereRecognition.lean
#print axioms Poincare.D12.TriangulationTopology.stage6Sphere_eq_sphereThree
#print axioms Poincare.D12.TriangulationTopology.stage6_sphereThreeSimplyConnected
#print axioms Poincare.D12.TriangulationTopology.longrun_missingSphereThreeSimplyConnected
#print axioms Poincare.D12.TriangulationTopology.stage6_sphereThreePiOneTrivial
#print axioms Poincare.D12.TriangulationTopology.longrun_missingSphereThreePiOneTrivial
#print axioms Poincare.D12.TriangulationTopology.sphereThree_fundamentalGroup_subsingleton
#print axioms Poincare.D12.TriangulationTopology.sphereThree_pi1_subsingleton
#print axioms Poincare.D12.TriangulationTopology.sphere_pi1_subsingleton
#print axioms Poincare.D12.TriangulationTopology.sphereThree_cover_isHomeo
#print axioms Poincare.D12.TriangulationTopology.sphereThree_identityCover
#print axioms Poincare.D12.TriangulationTopology.sphereThreeTarget_cover_isHomeo
#print axioms Poincare.D12.TriangulationTopology.sphereThreeTarget_homeo_sphereThree

#print axioms Poincare.D12.TriangulationTopology.SimplexFn
#print axioms Poincare.D12.TriangulationTopology.SimplexBoundaryCone
#print axioms Poincare.D12.TriangulationTopology.Sphere
#print axioms Poincare.D12.TriangulationTopology.Disk
#print axioms Poincare.D12.TriangulationTopology.ConeQuot
#print axioms Poincare.D12.TriangulationTopology.SuspCyl
#print axioms Poincare.D12.TriangulationTopology.SuspQuot
#print axioms Poincare.D12.TriangulationTopology.DoubleDisk
#print axioms Poincare.D12.TriangulationTopology.DoubleDiskQuot
#print axioms Poincare.D12.TriangulationTopology.sphere_cover_isHomeo

-- DiskGluing.lean (invocation 8: Alexander trick + arbitrary-boundary disk gluing)
#print axioms Poincare.D12.TriangulationTopology.PuncturedDisk
#print axioms Poincare.D12.TriangulationTopology.sphereBase
#print axioms Poincare.D12.TriangulationTopology.diskDirection
#print axioms Poincare.D12.TriangulationTopology.diskDirection_of_ne
#print axioms Poincare.D12.TriangulationTopology.radialExtend
#print axioms Poincare.D12.TriangulationTopology.radialExtend_apply
#print axioms Poincare.D12.TriangulationTopology.norm_radialExtend
#print axioms Poincare.D12.TriangulationTopology.radialExtend_zero
#print axioms Poincare.D12.TriangulationTopology.diskDirection_radialExtend
#print axioms Poincare.D12.TriangulationTopology.continuous_diskDirection_punctured
#print axioms Poincare.D12.TriangulationTopology.continuousOn_diskDirection
#print axioms Poincare.D12.TriangulationTopology.continuous_radialExtend
#print axioms Poincare.D12.TriangulationTopology.sphereToDisk
#print axioms Poincare.D12.TriangulationTopology.sphereToDisk_coe
#print axioms Poincare.D12.TriangulationTopology.diskDirection_sphereToDisk
#print axioms Poincare.D12.TriangulationTopology.radialExtend_sphereToDisk
#print axioms Poincare.D12.TriangulationTopology.radialExtend_id
#print axioms Poincare.D12.TriangulationTopology.radialExtend_comp
#print axioms Poincare.D12.TriangulationTopology.alexanderHomeo
#print axioms Poincare.D12.TriangulationTopology.alexanderHomeo_refl
#print axioms Poincare.D12.TriangulationTopology.alexanderHomeo_zero
#print axioms Poincare.D12.TriangulationTopology.alexanderHomeo_sphereToDisk
#print axioms Poincare.D12.TriangulationTopology.alexanderHomeo_eq_refl_iff
#print axioms Poincare.D12.TriangulationTopology.diskGlueRel
#print axioms Poincare.D12.TriangulationTopology.DiskGlueQuot
#print axioms Poincare.D12.TriangulationTopology.quotMapHomeo_mk
#print axioms Poincare.D12.TriangulationTopology.diskGlueSumHomeo
#print axioms Poincare.D12.TriangulationTopology.diskGlueSumHomeo_inl
#print axioms Poincare.D12.TriangulationTopology.diskGlueSumHomeo_inr
#print axioms Poincare.D12.TriangulationTopology.alexanderHomeo_symm_sphereToDisk
#print axioms Poincare.D12.TriangulationTopology.diskGlueRel_transport
#print axioms Poincare.D12.TriangulationTopology.diskGlueRel_id_iff_doubleDiskRel
#print axioms Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere
#print axioms Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere_refl_apply
#print axioms Poincare.D12.TriangulationTopology.diskGlueQuotCompactSpace
#print axioms Poincare.D12.TriangulationTopology.diskGlueQuotT2Space
#print axioms Poincare.D12.TriangulationTopology.diskGlueQuotNonempty

-- SphereOfTwoDisks.lean (invocation 8: closed-cover sphere recognition)
#print axioms Poincare.D12.TriangulationTopology.sphereOfTwoDisks

-- TwoHemisphereInstance.lean (invocation 8: non-vacuity instance, node 13a)
#print axioms Poincare.D12.TriangulationTopology.UpperHemisphere
#print axioms Poincare.D12.TriangulationTopology.sphere_trunc_norm_sq_add_last_sq_eq_one
#print axioms Poincare.D12.TriangulationTopology.sqrt_one_sub_trunc_norm_sq_eq_last
#print axioms Poincare.D12.TriangulationTopology.upperHemisphereToDisk
#print axioms Poincare.D12.TriangulationTopology.diskToUpperHemisphere
#print axioms Poincare.D12.TriangulationTopology.continuous_upperHemisphereToDisk
#print axioms Poincare.D12.TriangulationTopology.continuous_diskToUpperHemisphere
#print axioms Poincare.D12.TriangulationTopology.upperHemisphereToDisk_diskToUpperHemisphere
#print axioms Poincare.D12.TriangulationTopology.diskToUpperHemisphere_upperHemisphereToDisk
#print axioms Poincare.D12.TriangulationTopology.upperHemisphereHomeoDisk
#print axioms Poincare.D12.TriangulationTopology.upperHemisphereCompactSpace
#print axioms Poincare.D12.TriangulationTopology.upperHemisphereT2Space
#print axioms Poincare.D12.TriangulationTopology.upperHemisphereNonempty
#print axioms Poincare.D12.TriangulationTopology.lowerHemisphere_boundary_eq_inter
#print axioms Poincare.D12.TriangulationTopology.lowerHemisphere_isClosed
#print axioms Poincare.D12.TriangulationTopology.upperHemisphere_isClosed
#print axioms Poincare.D12.TriangulationTopology.hemisphere_cover
#print axioms Poincare.D12.TriangulationTopology.hemisphere_charts_agree
#print axioms Poincare.D12.TriangulationTopology.sphereOfTwoDisks_hemisphere_instance
