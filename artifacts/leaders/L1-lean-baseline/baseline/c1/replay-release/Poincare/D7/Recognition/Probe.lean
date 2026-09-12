/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-sphere-recognition)

**D7 sphere recognition: API probe.**

`#check` commands for the public interface of `Poincare.D7.Recognition`.  This file contains no
declarations; it is the machine-checkable record that every named declaration of the module
exists with the expected type.
-/

import Poincare.D7.Recognition.All

set_option autoImplicit false

open scoped Topology Manifold ContDiff

namespace Poincare.D7.Recognition

/-! ## Certificate vocabulary (`Basic.lean`) -/

#check @IsSurgeryAdmissible
#check @isSurgeryAdmissible_or_compactSpherical
#check @not_isSurgeryAdmissible_of_compactSpherical
#check @SphericalPiece
#check @SphericalPiece.scale_pos
#check @SphericalPiece.certificate_kind
#check @SphericalPiece.homeomorphic
#check @SphericalPiece.ofCertificate
#check @IsSphericalPiece
#check @ConnectedSumDecomposition
#check @ConnectedSumDecomposition.simplyConnected_pieces
#check @ConnectedSumDecomposition.sphere_of_spheres
#check @extinctionLedger
#check @ExtinctionCertificate
#check @ExtinctionConclusion
#check @ExtinctionCertificate.toConclusion
#check @ExtinctionCertificate.extinctsInFiniteTime
#check @ExtinctionCertificate.finitelyManySurgeries
#check @ExtinctionWithSphericalPieces
#check @CanonicalNeighborhoodInput
#check @CanonicalNeighborhoodInput.sphericalPiece
#check @CanonicalNeighborhoodInput.only_spherical
#check @CanonicalNeighborhoodInput.certificate_classified
#check @SphericalPieceRecognition
#check @SphericalPieceRecognition.recognize_piece

/-! ## End-game assembly (`Assembly.lean`) -/

#check @RecognitionHypotheses
#check @RecognitionHypotheses.conclusion
#check @RecognitionHypotheses.extinctsInFiniteTime
#check @RecognitionHypotheses.finitelyManySurgeries
#check @RecognitionHypotheses.onlySphericalPieces
#check @RecognitionHypotheses.extinctionWithSphericalPieces
#check @RecognitionHypotheses.pieces_simplyConnected
#check @RecognitionHypotheses.pieces_homeomorph_sphere
#check @RecognitionHypotheses.homeomorph_sphere
#check @RecognitionHypotheses.stage6Target
#check @RecognitionHypotheses.all_pieces_spherical_and_sphere
#check @stage6Target_of_certificates
#check @extinctionWithSphericalPieces_of_certificates
#check @surgeryCertificate_of_neckAnalysis
#check @simplyConnected_preserved_of_chainCertificate
#check @extincts_and_target_of_missingInputs
#check @not_surgeryAdmissible_of_canonical_compactSpherical

/-! ## Statement-only final construction (`Homeomorphism.lean`) -/

#check @missingMoiseSmoothingBridge
#check @missingGeometrizationOutput
#check @missingFinalHomeomorphismConstruction
#check @missingMoiseSmoothingBridge_iff
#check @missingGeometrizationOutput_iff
#check @missingFinalHomeomorphismConstruction_iff
#check @missingFinalHomeomorphismConstruction_iff_missingPoincareConjectureTopologicalThree
#check @stage6Target_of_missingFinalHomeomorphismConstruction
#check @missingFinalHomeomorphismConstruction_of_missingPoincare
#check @smoothTarget_of_topologicalTarget_and_moise
#check @sphericalPieces_of_geometrization
#check @finalHomeomorphismConstruction_of_certificateFamily
#check @finalHomeomorphismDependencies
#check @finalHomeomorphismDependencies_length
#check @finalHomeomorphismDependencies_ne_nil
#check @finalHomeomorphismDependencies_all_named
#check @finalHomeomorphismBlockers
#check @finalHomeomorphismBlockers_length
#check @finalHomeomorphismBlockers_ne_nil
#check @finalHomeomorphismBlockers_all_named

end Poincare.D7.Recognition
