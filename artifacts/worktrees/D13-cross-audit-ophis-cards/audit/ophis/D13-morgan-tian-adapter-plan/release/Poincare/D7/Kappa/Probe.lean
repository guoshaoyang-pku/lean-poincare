/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-kappa-noncollapsing-conditional)

**D7 conditional κ-noncollapsing: compilable API probe.**

`#check` commands for the public API of the assembly.  The probe compiles with exit code 0 and
is part of the verification transcript; it contains no `sorry`, `axiom`, `unsafe`,
`native_decide` or `proof_wanted`.
-/

import Poincare.D7.Kappa.All

/-! ## 1. The comparison hypothesis and the monotonicity step -/

#check Poincare.D7.Kappa.BallVolumeComparison
#check Poincare.D7.Kappa.BallVolumeComparison.apply
#check Poincare.D7.Kappa.BallVolumeComparison.mono
#check Poincare.D7.Kappa.uniformReducedVolumeLowerBound
#check Poincare.D7.Kappa.phi_uniformLowerBound

/-! ## 2. The conditional K1/K2 theorems -/

#check Poincare.D7.Kappa.normalizedBallVolumeLowerBound_of_entropy_and_volumeComparison
#check Poincare.D7.Kappa.kappaNoncollapsing_of_entropy_and_volumeComparison
#check Poincare.D7.Kappa.volume_ball_lower_of_entropy_and_volumeComparison

/-! ## 3. The extended certificate -/

#check Poincare.D7.Kappa.KappaComparisonData
#check Poincare.D7.Kappa.KappaComparisonData.uniform_volume_lower
#check Poincare.D7.Kappa.KappaComparisonData.toKappaCertificate
#check Poincare.D7.Kappa.KappaCertificate
#check Poincare.D7.Kappa.KappaCertificate.volume_ball_lower
#check Poincare.D7.Kappa.KappaCertificate.volume_ball_pos
#check Poincare.D7.Kappa.KappaCertificate.toNormalizedBallVolumeLowerBound
#check Poincare.D7.Kappa.KappaCertificate.mono
#check Poincare.D7.Kappa.KappaCertificate.uniform_volume_lower
#check Poincare.D7.Kappa.kappaCertificate_of_entropy_and_volumeComparison

/-! ## 4. The entropy bridge -/

#check Poincare.D7.Kappa.perelmanWMu_monotone_and_uniformReducedVolume
#check Poincare.D7.Kappa.kappaNoncollapsing_of_perelmanWMu
#check Poincare.D7.Kappa.kappaComparisonData_of_perelmanWMu
#check Poincare.D7.Kappa.kappaCertificate_of_perelmanWMu
#check Poincare.D7.Kappa.kappaNoncollapsing_of_reducedVolumeWDuality

/-! ## 5. The state-only statement and the named inputs -/

#check Poincare.D7.Kappa.PerelmanNoncollapsingConclusion
#check Poincare.D7.Kappa.fullPerelmanNoncollapsing
#check Poincare.D7.Kappa.fullPerelmanNoncollapsing_iff_missingKappaNoncollapsing
#check Poincare.D7.Kappa.fullPerelmanNoncollapsing_of_comparisonData
#check Poincare.D7.Kappa.fullPerelmanNoncollapsing_of_entropy_and_comparison
#check Poincare.D7.Kappa.missingKappaNoncollapsingOfMuMonotonicity_of_comparisonData
#check Poincare.D7.Kappa.perelmanNoncollapsingDependencies
#check Poincare.D7.Kappa.perelmanNoncollapsingBlockers

/-! ## 6. Non-vacuity witnesses -/

#check Poincare.D7.Kappa.ballVolumeComparison_unit
#check Poincare.D7.Kappa.kappaNoncollapsing_of_entropy_and_volumeComparison_unit
#check Poincare.D7.Kappa.kappaNoncollapsing_of_perelmanWMu_unit
#check Poincare.D7.Kappa.unitKappaCertificate
#check Poincare.D7.Kappa.kappaNoncollapsing_unit
#check Poincare.D7.Kappa.perelmanNoncollapsingConclusion_unit
#check Poincare.D7.Kappa.fullPerelmanNoncollapsing_unit
