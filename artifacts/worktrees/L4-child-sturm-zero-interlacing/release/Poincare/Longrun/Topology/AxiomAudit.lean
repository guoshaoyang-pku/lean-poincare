/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D3-kappa-ledger)
-/
import Poincare.Longrun.Topology.MissingTheorems

/-!
# Poincare.Longrun.Topology.AxiomAudit

`#print axioms` audit for every declaration of the Stage-D3 topology interface layer.

Expected output for every entry: dependence on at most the three Lean kernel axioms
`propext`, `Classical.choice`, `Quot.sound` — and in particular **no** `sorryAx`, no
project-specific postulate, no `Mathlib.Wanted` declaration.

This file contains no definitions and no proofs; it exists so that the foundational-dependency report is
part of the checked build.
-/

open scoped Manifold ContDiff Topology ENNReal

/-! ## Basic model spaces -/

#print axioms Poincare.Longrun.Topology.threeManifoldModel_def
#print axioms Poincare.Longrun.Topology.sphereThree_def

/-! ## Compact 3-manifold interface and consequences -/

#print axioms Poincare.Longrun.Topology.CompactThreeManifold.toSigmaCompactSpace
#print axioms Poincare.Longrun.Topology.CompactThreeManifold.toParacompactSpace
#print axioms Poincare.Longrun.Topology.CompactThreeManifold.toLocallyCompactSpace
#print axioms Poincare.Longrun.Topology.CompactThreeManifold.toSecondCountableTopology
#print axioms Poincare.Longrun.Topology.CompactThreeManifold.toTopologicalManifold
#print axioms Poincare.Longrun.Topology.CompactThreeManifold.exists_finite_chart_cover
#print axioms Poincare.Longrun.Topology.CompactThreeManifold.exists_mem_chart_source

/-! ## Non-collapsing certificate and consequences -/

#print axioms Poincare.Longrun.Topology.KappaNoncollapsingCertificate.volume_ball_pos
#print axioms Poincare.Longrun.Topology.KappaNoncollapsingCertificate.volume_ball_ne_zero
#print axioms Poincare.Longrun.Topology.KappaNoncollapsingCertificate.mono
#print axioms Poincare.Longrun.Topology.KappaNoncollapsingCertificate.volume_unit_ball_lower
#print axioms Poincare.Longrun.Topology.KappaNoncollapsingCertificate.exists_uniform_unit_ball_lower_bound
#print axioms Poincare.Longrun.Topology.KappaNoncollapsingCertificate.apply

/-! ## Normalized-volume interfaces and consequences -/

#print axioms Poincare.Longrun.Topology.NormalizedVolumeLowerBound.apply
#print axioms Poincare.Longrun.Topology.NormalizedVolumeLowerBound.nonneg
#print axioms Poincare.Longrun.Topology.NormalizedVolumeLowerBound.pos
#print axioms Poincare.Longrun.Topology.NormalizedVolumeLowerBound.mono
#print axioms Poincare.Longrun.Topology.NormalizedVolumeLowerBound.bddBelow_range
#print axioms Poincare.Longrun.Topology.NormalizedVolumeLowerBound.exists_lower_bound
#print axioms Poincare.Longrun.Topology.NormalizedVolumeLowerBound.add
#print axioms Poincare.Longrun.Topology.NormalizedVolumeLowerBound.smul
#print axioms Poincare.Longrun.Topology.NormalizedVolumeLowerBound.const_iff
#print axioms Poincare.Longrun.Topology.kappaNoncollapsingCertificate_iff_normalizedBallVolumeLowerBound
#print axioms Poincare.Longrun.Topology.NormalizedBallVolumeLowerBound.toKappaNoncollapsingCertificate
#print axioms Poincare.Longrun.Topology.NormalizedBallVolumeLowerBound.volume_ball_pos
#print axioms Poincare.Longrun.Topology.NormalizedBallVolumeLowerBound.mono
#print axioms Poincare.Longrun.Topology.KappaNoncollapsingCertificate.toNormalizedBallVolumeLowerBound
#print axioms Poincare.Longrun.Topology.normalizedBallVolume_nonneg
#print axioms Poincare.Longrun.Topology.NormalizedBallVolumeLowerBound.unit_ball_lower

/-! ## Stage6 bridges -/

#print axioms Poincare.Longrun.Topology.stage6Target_iff_sphereRecognition
#print axioms Poincare.Longrun.Topology.stage6Target_iff_stage6Alias
#print axioms Poincare.Longrun.Topology.stage6Target_of_sphereRecognition
#print axioms Poincare.Longrun.Topology.compactThreeManifold_stage6Hypotheses
#print axioms Poincare.Longrun.Topology.stage6Target_of_compactThreeManifold
#print axioms Poincare.Longrun.Topology.stage6SphereSimplyConnected_iff
#print axioms Poincare.Longrun.Topology.stage6SphereThreePiOneTrivial_iff
#print axioms Poincare.Longrun.Topology.pathConnectedSpace_sphereThree
#print axioms Poincare.Longrun.Topology.simplyConnectedSpace_sphereThree_iff
#print axioms Poincare.Longrun.Topology.stage6SphereThreePiOneTrivial_iff_stage6SphereSimplyConnected

-- The shared Stage6 statement-only targets themselves:
#print axioms Poincare.Stage6.poincareConjectureTopologicalThree
#print axioms Poincare.Stage6.poincareConjectureTopologicalThree_iff_conclusion
#print axioms Poincare.Stage6.sphereThreeSimplyConnected
#print axioms Poincare.Stage6.sphereThreePiOneTrivial

/-! ## Missing-theorem ledger: checked companions -/

#print axioms Poincare.Longrun.Topology.missingKappaNoncollapsing_iff
#print axioms Poincare.Longrun.Topology.missingNormalizedNoLocalCollapsing_iff
#print axioms Poincare.Longrun.Topology.missingKappaNoncollapsing_iff_missingNormalizedNoLocalCollapsing
#print axioms Poincare.Longrun.Topology.kappaCertificate_of_missingKappaNoncollapsing
#print axioms Poincare.Longrun.Topology.unit_ball_lower_bound_of_missingKappaNoncollapsing
#print axioms Poincare.Longrun.Topology.missingSphereThreeSimplyConnected_iff_stage6
#print axioms Poincare.Longrun.Topology.missingSphereThreePiOneTrivial_iff_stage6
#print axioms Poincare.Longrun.Topology.missingPoincareConjectureTopologicalThree_iff
#print axioms Poincare.Longrun.Topology.stage6Target_of_missingPoincareConjectureTopologicalThree
#print axioms Poincare.Longrun.Topology.decidableSphereRecognition_of_missingSphereRecognitionAlgorithm
#print axioms Poincare.Longrun.Topology.missingSphereThreeSimplyConnected_iff_pathConnected_and_fundamentalGroup
#print axioms Poincare.Longrun.Topology.missingSphereThreeSimplyConnected_iff_piOneTrivial

/-! ## Statement-only ledger and interface definitions -/

#print axioms Poincare.Longrun.Topology.normalizedBallVolume
#print axioms Poincare.Longrun.Topology.stage6Target
#print axioms Poincare.Longrun.Topology.missingKappaNoncollapsing
#print axioms Poincare.Longrun.Topology.missingNormalizedNoLocalCollapsing
#print axioms Poincare.Longrun.Topology.missingKappaNoncollapsingOfMuMonotonicity
#print axioms Poincare.Longrun.Topology.missingReducedVolumeMonotonicity
#print axioms Poincare.Longrun.Topology.missingConjugateHeatKernel
#print axioms Poincare.Longrun.Topology.missingKappaPersistenceUnderSurgery
#print axioms Poincare.Longrun.Topology.missingCanonicalNeighborhoodTheorem
#print axioms Poincare.Longrun.Topology.missingSphereThreeSimplyConnected
#print axioms Poincare.Longrun.Topology.missingSphereThreePiOneTrivial
#print axioms Poincare.Longrun.Topology.missingPoincareConjectureTopologicalThree
#print axioms Poincare.Longrun.Topology.missingPoincareConjectureSmoothThree
#print axioms Poincare.Longrun.Topology.missingSphereRecognitionAlgorithm
