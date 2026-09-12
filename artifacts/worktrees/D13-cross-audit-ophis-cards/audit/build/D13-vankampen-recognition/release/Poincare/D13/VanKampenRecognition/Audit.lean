/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-vankampen-recognition)

**D13 van Kampen recognition: fail-closed axiom audit.**

Every declaration of the four authored D13 modules is passed through
`#print axioms`.  The accepted cone is `{}`, `{propext}`, `{Classical.choice}`,
`{Quot.sound}` and combinations.  Any other axiom — `sorryAx` in particular —
fails the audit.  Generated from the declaration list of the audited modules.
-/
import Poincare.D13.VanKampenRecognition.All

namespace Poincare.D13.VanKampenRecognition


#print axioms Poincare.D13.VanKampenRecognition.FreeProduct_subsingleton
#print axioms Poincare.D13.VanKampenRecognition.FreeProduct_factor_subsingleton
#print axioms Poincare.D13.VanKampenRecognition.fundamentalGroup_subsingleton_of_cover
#print axioms Poincare.D13.VanKampenRecognition.one_add_firstCoord_ne_zero
#print axioms Poincare.D13.VanKampenRecognition.one_sub_firstCoord_ne_zero
#print axioms Poincare.D13.VanKampenRecognition.one_add_norm_sq_ne_zero
#print axioms Poincare.D13.VanKampenRecognition.tailVec_norm_sq_eq_sum_succ
#print axioms Poincare.D13.VanKampenRecognition.stereoSouthFun
#print axioms Poincare.D13.VanKampenRecognition.stereoSouthInvFun
#print axioms Poincare.D13.VanKampenRecognition.stereoSouthFun_coord
#print axioms Poincare.D13.VanKampenRecognition.stereoSouthInvFun_fst
#print axioms Poincare.D13.VanKampenRecognition.stereoSouthInvFun_succ
#print axioms Poincare.D13.VanKampenRecognition.stereoSouthFun_norm_sq
#print axioms Poincare.D13.VanKampenRecognition.stereoSouthInvFun_mem
#print axioms Poincare.D13.VanKampenRecognition.stereoSouthInvFun_ne_southPole
#print axioms Poincare.D13.VanKampenRecognition.stereoSouthInv_stereoSouth_fst
#print axioms Poincare.D13.VanKampenRecognition.stereoSouthInv_stereoSouth_succ
#print axioms Poincare.D13.VanKampenRecognition.stereoSouth_left_inv
#print axioms Poincare.D13.VanKampenRecognition.stereoSouth_stereoSouthInv_coord
#print axioms Poincare.D13.VanKampenRecognition.stereoSouth_right_inv
#print axioms Poincare.D13.VanKampenRecognition.stereoSouthFun_continuous
#print axioms Poincare.D13.VanKampenRecognition.stereoSouthInvFun_continuous
#print axioms Poincare.D13.VanKampenRecognition.stereoSouth
#print axioms Poincare.D13.VanKampenRecognition.stereoNorthFun
#print axioms Poincare.D13.VanKampenRecognition.stereoNorthInvFun
#print axioms Poincare.D13.VanKampenRecognition.stereoNorthFun_coord
#print axioms Poincare.D13.VanKampenRecognition.stereoNorthInvFun_fst
#print axioms Poincare.D13.VanKampenRecognition.stereoNorthInvFun_succ
#print axioms Poincare.D13.VanKampenRecognition.stereoNorthFun_norm_sq
#print axioms Poincare.D13.VanKampenRecognition.stereoNorthInvFun_mem
#print axioms Poincare.D13.VanKampenRecognition.stereoNorthInvFun_ne_northPole
#print axioms Poincare.D13.VanKampenRecognition.stereoNorthInv_stereoNorth_fst
#print axioms Poincare.D13.VanKampenRecognition.stereoNorthInv_stereoNorth_succ
#print axioms Poincare.D13.VanKampenRecognition.stereoNorth_left_inv
#print axioms Poincare.D13.VanKampenRecognition.stereoNorth_stereoNorthInv_coord
#print axioms Poincare.D13.VanKampenRecognition.stereoNorth_right_inv
#print axioms Poincare.D13.VanKampenRecognition.stereoNorthFun_continuous
#print axioms Poincare.D13.VanKampenRecognition.stereoNorthInvFun_continuous
#print axioms Poincare.D13.VanKampenRecognition.stereoNorth
#print axioms Poincare.D13.VanKampenRecognition.e1
#print axioms Poincare.D13.VanKampenRecognition.e1_norm_eq_one
#print axioms Poincare.D13.VanKampenRecognition.sphereBase
#print axioms Poincare.D13.VanKampenRecognition.northPole_ne_southPole
#print axioms Poincare.D13.VanKampenRecognition.sphereBase_ne_southPole
#print axioms Poincare.D13.VanKampenRecognition.sphereBase_ne_northPole
#print axioms Poincare.D13.VanKampenRecognition.northDeleted
#print axioms Poincare.D13.VanKampenRecognition.southDeleted
#print axioms Poincare.D13.VanKampenRecognition.band
#print axioms Poincare.D13.VanKampenRecognition.northDeleted_simplyConnected
#print axioms Poincare.D13.VanKampenRecognition.southDeleted_simplyConnected
#print axioms Poincare.D13.VanKampenRecognition.northInNorthDeleted
#print axioms Poincare.D13.VanKampenRecognition.northDeletedNorthImage
#print axioms Poincare.D13.VanKampenRecognition.band_eq_inter
#print axioms Poincare.D13.VanKampenRecognition.rank_R3
#print axioms Poincare.D13.VanKampenRecognition.bandHomeo
#print axioms Poincare.D13.VanKampenRecognition.band_pathConnectedSpace
#print axioms Poincare.D13.VanKampenRecognition.sphereVanKampenCover
#print axioms Poincare.D13.VanKampenRecognition.coverFundamentalGroupSubsingleton
#print axioms Poincare.D13.VanKampenRecognition.sphereThree_fundamentalGroupSubsingleton
#print axioms Poincare.D13.VanKampenRecognition.loops_nullhomotopic_of_subsingleton_fundamentalGroup
#print axioms Poincare.D13.VanKampenRecognition.sphereThree_simplyConnectedSpace
#print axioms Poincare.D13.VanKampenRecognition.simplyConnected_of_homeo_sphere
#print axioms Poincare.D13.VanKampenRecognition.simplyConnectedPieces_of_v2
#print axioms Poincare.D13.VanKampenRecognition.ConnectedSumDecomposition.mkV2Complete
#print axioms Poincare.D13.VanKampenRecognition.iteratedSphereSum_simplyConnected
#print axioms Poincare.D13.VanKampenRecognition.v2Ambient_simplyConnected
#print axioms Poincare.D13.VanKampenRecognition.RemainingRecognitionHypothesesV4
#print axioms Poincare.D13.VanKampenRecognition.RemainingRecognitionHypothesesV4.toRemainingV3
#print axioms Poincare.D13.VanKampenRecognition.RemainingRecognitionHypothesesV4.toRemaining
#print axioms Poincare.D13.VanKampenRecognition.stage6Target_of_v4hypotheses
#print axioms Poincare.D13.VanKampenRecognition.stage6Target_of_v4hypotheses_from_certificates

end Poincare.D13.VanKampenRecognition
