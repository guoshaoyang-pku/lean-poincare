/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-kappa-noncollapsing-conditional)

**D7 conditional κ-noncollapsing: `#print axioms` audit.**

Every principal declaration of the conditional κ-noncollapsing assembly is printed here.
The expected cones are `{propext, Classical.choice, Quot.sound}`, the empty cone for the
blocker/ledger declarations, and possibly `{propext}`; any `sorryAx`, project axiom,
`Lean.ofReduceBool` or `Lean.trustCompiler` would be a hard failure.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/

import Poincare.D7.Kappa.All

/-! ## Basic: comparison hypothesis and monotonicity step -/

#print axioms Poincare.D7.Kappa.BallVolumeComparison
#print axioms Poincare.D7.Kappa.BallVolumeComparison.apply
#print axioms Poincare.D7.Kappa.BallVolumeComparison.mono
#print axioms Poincare.D7.Kappa.uniformReducedVolumeLowerBound
#print axioms Poincare.D7.Kappa.phi_uniformLowerBound

/-! ## Basic: the conditional K1/K2 theorems -/

#print axioms Poincare.D7.Kappa.normalizedBallVolumeLowerBound_of_entropy_and_volumeComparison
#print axioms Poincare.D7.Kappa.kappaNoncollapsing_of_entropy_and_volumeComparison
#print axioms Poincare.D7.Kappa.volume_ball_lower_of_entropy_and_volumeComparison

/-! ## Basic: the extended certificate -/

#print axioms Poincare.D7.Kappa.KappaComparisonData
#print axioms Poincare.D7.Kappa.KappaComparisonData.uniform_volume_lower
#print axioms Poincare.D7.Kappa.KappaComparisonData.toKappaCertificate
#print axioms Poincare.D7.Kappa.KappaCertificate
#print axioms Poincare.D7.Kappa.KappaCertificate.volume_ball_lower
#print axioms Poincare.D7.Kappa.KappaCertificate.volume_ball_pos
#print axioms Poincare.D7.Kappa.KappaCertificate.volume_ball_ne_zero
#print axioms Poincare.D7.Kappa.KappaCertificate.toNormalizedBallVolumeLowerBound
#print axioms Poincare.D7.Kappa.KappaCertificate.volume_unit_ball_lower
#print axioms Poincare.D7.Kappa.KappaCertificate.exists_uniform_unit_ball_lower_bound
#print axioms Poincare.D7.Kappa.KappaCertificate.mono
#print axioms Poincare.D7.Kappa.KappaCertificate.uniform_volume_lower
#print axioms Poincare.D7.Kappa.kappaCertificate_of_entropy_and_volumeComparison

/-! ## EntropyBridge: the D7 entropy interface -/

#print axioms Poincare.D7.Kappa.perelmanWMu_monotone_and_uniformReducedVolume
#print axioms Poincare.D7.Kappa.kappaNoncollapsing_of_perelmanWMu
#print axioms Poincare.D7.Kappa.kappaComparisonData_of_perelmanWMu
#print axioms Poincare.D7.Kappa.kappaCertificate_of_perelmanWMu
#print axioms Poincare.D7.Kappa.kappaNoncollapsing_of_reducedVolumeWDuality
#print axioms Poincare.D7.Kappa.volume_ball_lower_of_reducedVolumeWDuality

/-! ## Statements: the state-only statement and the named inputs -/

#print axioms Poincare.D7.Kappa.PerelmanNoncollapsingConclusion
#print axioms Poincare.D7.Kappa.perelmanNoncollapsingConclusion_iff
#print axioms Poincare.D7.Kappa.fullPerelmanNoncollapsing
#print axioms Poincare.D7.Kappa.fullPerelmanNoncollapsing_iff
#print axioms Poincare.D7.Kappa.fullPerelmanNoncollapsing_iff_missingKappaNoncollapsing
#print axioms Poincare.D7.Kappa.fullPerelmanNoncollapsing_of_comparisonData
#print axioms Poincare.D7.Kappa.fullPerelmanNoncollapsing_of_entropy_and_comparison
#print axioms Poincare.D7.Kappa.missingKappaNoncollapsingOfMuMonotonicity_of_comparisonData
#print axioms Poincare.D7.Kappa.BlockerBallVolumeComparison
#print axioms Poincare.D7.Kappa.BlockerAncientSolutionRigidity
#print axioms Poincare.D7.Kappa.BlockerEntropyNormalisation
#print axioms Poincare.D7.Kappa.BlockerUniformKappa
#print axioms Poincare.D7.Kappa.perelmanNoncollapsingDependencies
#print axioms Poincare.D7.Kappa.perelmanNoncollapsingDependencies_length
#print axioms Poincare.D7.Kappa.perelmanNoncollapsingDependencies_ne_nil
#print axioms Poincare.D7.Kappa.perelmanNoncollapsingDependencies_all_named
#print axioms Poincare.D7.Kappa.perelmanNoncollapsingBlockers
#print axioms Poincare.D7.Kappa.perelmanNoncollapsingBlockers_length
#print axioms Poincare.D7.Kappa.perelmanNoncollapsingBlockers_ne_nil
#print axioms Poincare.D7.Kappa.perelmanNoncollapsingBlockers_all_named

/-! ## Nonvacuity: kernel-checked instances -/

#print axioms Poincare.D7.Kappa.ballVolumeComparison_unit
#print axioms Poincare.D7.Kappa.ballVolumeComparison_unit_half
#print axioms Poincare.D7.Kappa.kappaNoncollapsing_of_entropy_and_volumeComparison_unit
#print axioms Poincare.D7.Kappa.kappaNoncollapsing_of_perelmanWMu_unit
#print axioms Poincare.D7.Kappa.uniformReducedVolumeLowerBound_unit
#print axioms Poincare.D7.Kappa.perelmanWMu_monotone_and_uniformReducedVolume_zero
#print axioms Poincare.D7.Kappa.unitKappaComparisonData
#print axioms Poincare.D7.Kappa.unitKappaCertificate
#print axioms Poincare.D7.Kappa.kappaNoncollapsing_unit
#print axioms Poincare.D7.Kappa.unitKappaCertificate_volume_ball_pos
#print axioms Poincare.D7.Kappa.unitKappaCertificate_half
#print axioms Poincare.D7.Kappa.unitKappaCertificate_half_uniform_volume_lower
#print axioms Poincare.D7.Kappa.unitKappaCertificate_normalized
#print axioms Poincare.D7.Kappa.perelmanNoncollapsingConclusion_unit
#print axioms Poincare.D7.Kappa.fullPerelmanNoncollapsing_unit
#print axioms Poincare.D7.Kappa.fullPerelmanNoncollapsing_of_comparisonData_unit
#print axioms Poincare.D7.Kappa.fullPerelmanNoncollapsing_of_entropy_and_comparison_unit
#print axioms Poincare.D7.Kappa.missingKappaNoncollapsingOfMuMonotonicity_unit
#print axioms Poincare.D7.Kappa.perelmanNoncollapsingDependencies_nonvacuous
