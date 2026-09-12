/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-gh-compactness)

**D7 Gromov–Hausdorff / Cheeger–Gromov compactness: compilable API probe.**

`#check` commands for the public API of the assembly.  The probe compiles with exit code 0
and is part of the verification transcript; it contains no unproved hole, no extra logical
postulate, no kernel bypass, no native evaluation and no statement stub.
-/

import Poincare.D7.Compactness.All

/-! ## 1. Pointed metric spaces and GH convergence data -/

#check Poincare.D7.Compactness.PointedMetricSpace
#check Poincare.D7.Compactness.PointedMetricSpace.unit
#check Poincare.D7.Compactness.GHConvergenceData
#check Poincare.D7.Compactness.GHConvergenceData.dist_approx_le
#check Poincare.D7.Compactness.GHConvergenceData.dist_le_dist_approx
#check Poincare.D7.Compactness.GHConvergenceData.tendsto_abs_distortion
#check Poincare.D7.Compactness.GHConvergenceData.tendsto_base_dist
#check Poincare.D7.Compactness.GHConvergenceData.tendsto_approx_base
#check Poincare.D7.Compactness.GHConvergenceData.refl
#check Poincare.D7.Compactness.GHConvergenceData.mono
#check Poincare.D7.Compactness.GHConvergenceData.monoFilter
#check Poincare.D7.Compactness.GHConvergenceData.comp

/-! ## 2. The precompactness certificate -/

#check Poincare.D7.Compactness.GHPrecompactCertificate
#check Poincare.D7.Compactness.GHPrecompactCertificate.exists_net
#check Poincare.D7.Compactness.GHPrecompactCertificate.monoBound
#check Poincare.D7.Compactness.GHPrecompactCertificate.const
#check Poincare.D7.Compactness.finiteCompleteSpace

/-! ## 3. Total-boundedness consequences -/

#check Poincare.D7.Compactness.GHPrecompactCertificate.coveringNumber
#check Poincare.D7.Compactness.GHPrecompactCertificate.card_net_le_coveringNumber
#check Poincare.D7.Compactness.GHPrecompactCertificate.net_nonempty
#check Poincare.D7.Compactness.GHPrecompactCertificate.uniform_finite_net
#check Poincare.D7.Compactness.GHPrecompactCertificate.totallyBounded_closedBall
#check Poincare.D7.Compactness.GHPrecompactCertificate.totallyBounded_ball
#check Poincare.D7.Compactness.GHPrecompactCertificate.isCompact_closedBall
#check Poincare.D7.Compactness.GHPrecompactCertificate.isCompact_closedBall_any
#check Poincare.D7.Compactness.GHPrecompactCertificate.properSpace
#check Poincare.D7.Compactness.GHPrecompactCertificate.totallyBounded_univ_of_bounded
#check Poincare.D7.Compactness.GHPrecompactCertificate.compactSpace_of_bounded
#check Poincare.D7.Compactness.GHPrecompactCertificate.isBounded_closedBall

/-! ## 4. The toy compactness theorem -/

#check Poincare.D7.Compactness.exists_strictMono_const_of_fin
#check Poincare.D7.Compactness.ConstSubsequence
#check Poincare.D7.Compactness.constSubsequence
#check Poincare.D7.Compactness.finiteFamilyCertificate
#check Poincare.D7.Compactness.finiteFamily_precompact
#check Poincare.D7.Compactness.toyCompactnessData
#check Poincare.D7.Compactness.toyCompactness_finiteFamily
#check Poincare.D7.Compactness.finiteFamily_totallyBounded
#check Poincare.D7.Compactness.finiteFamily_isCompact_closedBall
#check Poincare.D7.Compactness.finiteFamily_properSpace
#check Poincare.D7.Compactness.totallyBounded_univ_of_fintype
#check Poincare.D7.Compactness.compactSpace_of_fintype
#check Poincare.D7.Compactness.toyCompactness_const

/-! ## 5. The state-only Cheeger–Gromov statements and the ledger -/

#check Poincare.D7.Compactness.ManifoldFamilyHypotheses
#check Poincare.D7.Compactness.CheegerGromovConvergenceData
#check Poincare.D7.Compactness.ghConvergence_of_cheegerGromov
#check Poincare.D7.Compactness.missingPointedGHConvergentSubsequence
#check Poincare.D7.Compactness.missingPointedGHConvergentSubsequence_iff
#check Poincare.D7.Compactness.missingCheegerGromovCompactness
#check Poincare.D7.Compactness.missingCheegerGromovCompactness_iff
#check Poincare.D7.Compactness.ghSubsequence_of_cheegerGromov
#check Poincare.D7.Compactness.smoothPart_of_cheegerGromov
#check Poincare.D7.Compactness.cheegerGromov_of_ghSubsequence
#check Poincare.D7.Compactness.cheegerGromov_of_ghPrecompact_and_smoothUpgrade
#check Poincare.D7.Compactness.totallyBounded_of_precompactCertificate
#check Poincare.D7.Compactness.cheegerGromovConclusion_of_finiteFamily
#check Poincare.D7.Compactness.cheegerGromovDependencies
#check Poincare.D7.Compactness.cheegerGromovDependencies_length
#check Poincare.D7.Compactness.cheegerGromovDependencies_all_named
#check Poincare.D7.Compactness.cheegerGromovBlockers
#check Poincare.D7.Compactness.cheegerGromovBlockers_length
#check Poincare.D7.Compactness.cheegerGromovBlockers_all_named

/-! ## 6. Non-vacuity witnesses -/

#check Poincare.D7.Compactness.unitFamily
#check Poincare.D7.Compactness.unitFamilyPrecompact
#check Poincare.D7.Compactness.unitFamilyGHData
#check Poincare.D7.Compactness.unitFamilyComp
#check Poincare.D7.Compactness.unitFamilyMonoFilter
#check Poincare.D7.Compactness.unitFamily_coveringNumber
#check Poincare.D7.Compactness.unitFamily_uniform_finite_net
#check Poincare.D7.Compactness.unitFamily_totallyBounded
#check Poincare.D7.Compactness.unitFamily_isCompact_closedBall
#check Poincare.D7.Compactness.unitFamily_properSpace
#check Poincare.D7.Compactness.unitFamily_compactSpace
#check Poincare.D7.Compactness.unitManifoldHypotheses
#check Poincare.D7.Compactness.unitCheegerGromovConclusion
#check Poincare.D7.Compactness.missingCheegerGromovCompactness_unit
#check Poincare.D7.Compactness.missingPointedGHConvergentSubsequence_unit
#check Poincare.D7.Compactness.unitFinFamilyCertificate
#check Poincare.D7.Compactness.unitFinFamily_toyCompactness
#check Poincare.D7.Compactness.unitFinFamily_cheegerGromov
#check Poincare.D7.Compactness.unitFinFamily_witness_strictMono
#check Poincare.D7.Compactness.unitFinFamily_witness_const
