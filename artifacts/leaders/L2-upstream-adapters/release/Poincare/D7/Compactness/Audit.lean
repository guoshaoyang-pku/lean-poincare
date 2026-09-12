/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-gh-compactness)

**D7 Gromov–Hausdorff / Cheeger–Gromov compactness: `#print axioms` audit.**

Every principal declaration of the pointed GH / Cheeger–Gromov compactness assembly is
printed here.  The expected cones are `{propext, Classical.choice, Quot.sound}` for the
analytic content, the empty cone for the structural definitions, ledger and blocker
declarations, and possibly `{propext}`.  Any `sorryAx`, project axiom, `Lean.ofReduceBool`
or `Lean.trustCompiler` would be a hard failure.

There is no unproved hole, no extra logical postulate, no kernel bypass, no native
evaluation and no statement stub in this file.
-/

import Poincare.D7.Compactness.All

/-! ## Basic: pointed spaces and GH convergence data -/

#print axioms Poincare.D7.Compactness.PointedMetricSpace
#print axioms Poincare.D7.Compactness.PointedMetricSpace.unit
#print axioms Poincare.D7.Compactness.PointedMetricSpace.unit_base
#print axioms Poincare.D7.Compactness.GHConvergenceData
#print axioms Poincare.D7.Compactness.GHConvergenceData.dist_approx_le
#print axioms Poincare.D7.Compactness.GHConvergenceData.dist_le_dist_approx
#print axioms Poincare.D7.Compactness.GHConvergenceData.tendsto_abs_distortion
#print axioms Poincare.D7.Compactness.GHConvergenceData.tendsto_base_dist
#print axioms Poincare.D7.Compactness.GHConvergenceData.tendsto_approx_base
#print axioms Poincare.D7.Compactness.GHConvergenceData.refl
#print axioms Poincare.D7.Compactness.GHConvergenceData.mono
#print axioms Poincare.D7.Compactness.GHConvergenceData.monoFilter
#print axioms Poincare.D7.Compactness.GHConvergenceData.comp

/-! ## Basic: the precompactness certificate and finite completeness -/

#print axioms Poincare.D7.Compactness.GHPrecompactCertificate
#print axioms Poincare.D7.Compactness.GHPrecompactCertificate.exists_net
#print axioms Poincare.D7.Compactness.GHPrecompactCertificate.monoBound
#print axioms Poincare.D7.Compactness.GHPrecompactCertificate.const
#print axioms Poincare.D7.Compactness.finiteCompleteSpace

/-! ## TotalBounded: total-boundedness consequences -/

#print axioms Poincare.D7.Compactness.GHPrecompactCertificate.coveringNumber
#print axioms Poincare.D7.Compactness.GHPrecompactCertificate.card_net_le_coveringNumber
#print axioms Poincare.D7.Compactness.GHPrecompactCertificate.net_nonempty
#print axioms Poincare.D7.Compactness.GHPrecompactCertificate.uniform_finite_net
#print axioms Poincare.D7.Compactness.GHPrecompactCertificate.totallyBounded_closedBall
#print axioms Poincare.D7.Compactness.GHPrecompactCertificate.totallyBounded_ball
#print axioms Poincare.D7.Compactness.GHPrecompactCertificate.isCompact_closedBall
#print axioms Poincare.D7.Compactness.GHPrecompactCertificate.isCompact_closedBall_any
#print axioms Poincare.D7.Compactness.GHPrecompactCertificate.properSpace
#print axioms Poincare.D7.Compactness.GHPrecompactCertificate.totallyBounded_univ_of_bounded
#print axioms Poincare.D7.Compactness.GHPrecompactCertificate.compactSpace_of_bounded
#print axioms Poincare.D7.Compactness.GHPrecompactCertificate.isBounded_closedBall

/-! ## ToyCompactness: pigeonhole and the toy compactness theorem -/

#print axioms Poincare.D7.Compactness.exists_strictMono_const_of_fin
#print axioms Poincare.D7.Compactness.ConstSubsequence
#print axioms Poincare.D7.Compactness.constSubsequence
#print axioms Poincare.D7.Compactness.finiteFamilyCertificate
#print axioms Poincare.D7.Compactness.finiteFamily_precompact
#print axioms Poincare.D7.Compactness.toyCompactnessData
#print axioms Poincare.D7.Compactness.toyCompactness_finiteFamily
#print axioms Poincare.D7.Compactness.finiteFamily_totallyBounded
#print axioms Poincare.D7.Compactness.finiteFamily_isCompact_closedBall
#print axioms Poincare.D7.Compactness.finiteFamily_properSpace
#print axioms Poincare.D7.Compactness.totallyBounded_univ_of_fintype
#print axioms Poincare.D7.Compactness.compactSpace_of_fintype
#print axioms Poincare.D7.Compactness.toyCompactness_const

/-! ## ManifoldStatements: state-only statements, reductions and ledger -/

#print axioms Poincare.D7.Compactness.ManifoldFamilyHypotheses
#print axioms Poincare.D7.Compactness.CheegerGromovConvergenceData
#print axioms Poincare.D7.Compactness.ghConvergence_of_cheegerGromov
#print axioms Poincare.D7.Compactness.missingPointedGHConvergentSubsequence
#print axioms Poincare.D7.Compactness.missingPointedGHConvergentSubsequence_iff
#print axioms Poincare.D7.Compactness.missingCheegerGromovCompactness
#print axioms Poincare.D7.Compactness.missingCheegerGromovCompactness_iff
#print axioms Poincare.D7.Compactness.ghSubsequence_of_cheegerGromov
#print axioms Poincare.D7.Compactness.smoothPart_of_cheegerGromov
#print axioms Poincare.D7.Compactness.cheegerGromov_of_ghSubsequence
#print axioms Poincare.D7.Compactness.cheegerGromov_of_ghPrecompact_and_smoothUpgrade
#print axioms Poincare.D7.Compactness.totallyBounded_of_precompactCertificate
#print axioms Poincare.D7.Compactness.cheegerGromovConclusion_of_finiteFamily
#print axioms Poincare.D7.Compactness.BlockerCurvatureTensor
#print axioms Poincare.D7.Compactness.BlockerCurvatureTensor_ne_nil
#print axioms Poincare.D7.Compactness.BlockerHarmonicCoordinates
#print axioms Poincare.D7.Compactness.BlockerHarmonicCoordinates_ne_nil
#print axioms Poincare.D7.Compactness.BlockerInjectivityRadius
#print axioms Poincare.D7.Compactness.BlockerInjectivityRadius_ne_nil
#print axioms Poincare.D7.Compactness.BlockerSmoothConvergence
#print axioms Poincare.D7.Compactness.BlockerSmoothConvergence_ne_nil
#print axioms Poincare.D7.Compactness.BlockerGHSubsequence
#print axioms Poincare.D7.Compactness.BlockerGHSubsequence_ne_nil
#print axioms Poincare.D7.Compactness.cheegerGromovDependencies
#print axioms Poincare.D7.Compactness.cheegerGromovDependencies_length
#print axioms Poincare.D7.Compactness.cheegerGromovDependencies_ne_nil
#print axioms Poincare.D7.Compactness.cheegerGromovDependencies_all_named
#print axioms Poincare.D7.Compactness.cheegerGromovBlockers
#print axioms Poincare.D7.Compactness.cheegerGromovBlockers_length
#print axioms Poincare.D7.Compactness.cheegerGromovBlockers_ne_nil
#print axioms Poincare.D7.Compactness.cheegerGromovBlockers_all_named

/-! ## Nonvacuity: kernel-checked witnesses -/

#print axioms Poincare.D7.Compactness.unitFamily
#print axioms Poincare.D7.Compactness.unitFamilyPrecompact
#print axioms Poincare.D7.Compactness.unitFamilyGHData
#print axioms Poincare.D7.Compactness.unitFamilyComp
#print axioms Poincare.D7.Compactness.unitFamilyMonoFilter
#print axioms Poincare.D7.Compactness.unitFamily_coveringNumber
#print axioms Poincare.D7.Compactness.unitFamily_uniform_finite_net
#print axioms Poincare.D7.Compactness.unitFamily_totallyBounded
#print axioms Poincare.D7.Compactness.unitFamily_isCompact_closedBall
#print axioms Poincare.D7.Compactness.unitFamily_properSpace
#print axioms Poincare.D7.Compactness.unitFamily_compactSpace
#print axioms Poincare.D7.Compactness.unitManifoldHypotheses
#print axioms Poincare.D7.Compactness.unitCheegerGromovConclusion
#print axioms Poincare.D7.Compactness.missingCheegerGromovCompactness_unit
#print axioms Poincare.D7.Compactness.missingPointedGHConvergentSubsequence_unit
#print axioms Poincare.D7.Compactness.unitFinFamily
#print axioms Poincare.D7.Compactness.unitFinFamilyCertificate
#print axioms Poincare.D7.Compactness.unitFinFamily_toyCompactness
#print axioms Poincare.D7.Compactness.unitFinFamily_cheegerGromov
#print axioms Poincare.D7.Compactness.unitFinFamily_witness_strictMono
#print axioms Poincare.D7.Compactness.unitFinFamily_witness_const
