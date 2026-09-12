/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-sphere-recognition)

**D7 sphere recognition: axiom audit.**

`#print axioms` on every declaration of `Poincare.D7.Recognition`.  This file contains no
declarations of its own; it is the machine-checkable record required by the result card.  A
successful run reports only Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) and never `sorryAx`.

The output is captured by

```text
lake env lean release/Poincare/D7/Recognition/Audit.lean
```
-/

import Poincare.D7.Recognition.All

set_option autoImplicit false

namespace Poincare.D7.Recognition

/-! ## Certificate vocabulary (`Basic.lean`) -/

#print axioms IsSurgeryAdmissible
#print axioms isSurgeryAdmissible_or_compactSpherical
#print axioms not_isSurgeryAdmissible_of_compactSpherical
#print axioms SphericalPiece
#print axioms SphericalPiece.scale_pos
#print axioms SphericalPiece.certificate_kind
#print axioms SphericalPiece.homeomorphic
#print axioms SphericalPiece.ofCertificate
#print axioms IsSphericalPiece
#print axioms ConnectedSumDecomposition
#print axioms ConnectedSumDecomposition.simplyConnected_pieces
#print axioms ConnectedSumDecomposition.sphere_of_spheres
#print axioms extinctionLedger
#print axioms ExtinctionCertificate
#print axioms ExtinctionConclusion
#print axioms ExtinctionCertificate.toConclusion
#print axioms ExtinctionCertificate.extinctsInFiniteTime
#print axioms ExtinctionCertificate.finitelyManySurgeries
#print axioms ExtinctionWithSphericalPieces
#print axioms CanonicalNeighborhoodInput
#print axioms CanonicalNeighborhoodInput.sphericalPiece
#print axioms CanonicalNeighborhoodInput.only_spherical
#print axioms CanonicalNeighborhoodInput.certificate_classified
#print axioms SphericalPieceRecognition
#print axioms SphericalPieceRecognition.recognize_piece

/-! ## End-game assembly (`Assembly.lean`) -/

#print axioms RecognitionHypotheses
#print axioms RecognitionHypotheses.conclusion
#print axioms RecognitionHypotheses.extinctsInFiniteTime
#print axioms RecognitionHypotheses.finitelyManySurgeries
#print axioms RecognitionHypotheses.onlySphericalPieces
#print axioms RecognitionHypotheses.extinctionWithSphericalPieces
#print axioms RecognitionHypotheses.pieces_simplyConnected
#print axioms RecognitionHypotheses.pieces_homeomorph_sphere
#print axioms RecognitionHypotheses.homeomorph_sphere
#print axioms RecognitionHypotheses.stage6Target
#print axioms RecognitionHypotheses.all_pieces_spherical_and_sphere
#print axioms stage6Target_of_certificates
#print axioms extinctionWithSphericalPieces_of_certificates
#print axioms surgeryCertificate_of_neckAnalysis
#print axioms simplyConnected_preserved_of_chainCertificate
#print axioms extincts_and_target_of_missingInputs
#print axioms not_surgeryAdmissible_of_canonical_compactSpherical

/-! ## Statement-only final construction (`Homeomorphism.lean`) -/

#print axioms missingMoiseSmoothingBridge
#print axioms missingGeometrizationOutput
#print axioms missingFinalHomeomorphismConstruction
#print axioms missingMoiseSmoothingBridge_iff
#print axioms missingGeometrizationOutput_iff
#print axioms missingFinalHomeomorphismConstruction_iff
#print axioms missingFinalHomeomorphismConstruction_iff_missingPoincareConjectureTopologicalThree
#print axioms stage6Target_of_missingFinalHomeomorphismConstruction
#print axioms missingFinalHomeomorphismConstruction_of_missingPoincare
#print axioms smoothTarget_of_topologicalTarget_and_moise
#print axioms sphericalPieces_of_geometrization
#print axioms finalHomeomorphismConstruction_of_certificateFamily
#print axioms finalHomeomorphismDependencies
#print axioms finalHomeomorphismDependencies_length
#print axioms finalHomeomorphismDependencies_ne_nil
#print axioms finalHomeomorphismDependencies_all_named
#print axioms finalHomeomorphismBlockers
#print axioms finalHomeomorphismBlockers_length
#print axioms finalHomeomorphismBlockers_ne_nil
#print axioms finalHomeomorphismBlockers_all_named

end Poincare.D7.Recognition
