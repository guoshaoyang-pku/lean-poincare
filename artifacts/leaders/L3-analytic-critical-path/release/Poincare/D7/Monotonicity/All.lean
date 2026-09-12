/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-perelman-conditional-monotonicity)

**D7 conditional monotonicity assembly: umbrella module and axiom audit.**

This is the umbrella module of the `D7-perelman-conditional-monotonicity` task.  It imports
the whole assembly:

* `BochnerCertificate` / `BochnerGradientEstimate` — the D7 Bochner / Weitzenböck
  certificate of task `D7-bochner-formula`, vendored unchanged under
  `Poincare/D7/Monotonicity/` because the Bochner package is not part of this scaffold;
* `ConjugateHeatCertificate` — the D7 conjugate-heat certificate of task
  `D7-conjugate-heat-interface`, vendored unchanged;
* `ReducedVolumeInput` — the D7 reduced-volume certificate of task
  `D7-reduced-length-volume` (imported from the scaffold), its dictionary into the D3
  `EntropyData` interface, and the open `B-D7-W-REDUCED-DUALITY` input;
* `FMonotonicity` — the conditional `F`-monotonicity transfer
  `PerelmanFAnalyticHypotheses.perelmanFMonotone_of_analyticHypotheses`;
* `WMuMonotonicity` — the conditional `W`/`μ`-monotonicity transfer
  `perelmanWMuMonotone_of_kernelHypotheses`;
* `Nonvacuity` — kernel-checked instances of every transfer theorem.

The `#print axioms` audit below is the kernel-level evidence that no axiom outside
`{propext, Classical.choice, Quot.sound}` is used.  There is no `sorry`, `axiom`, `unsafe`,
`native_decide` or `proof_wanted` in any authored file.
-/

import Poincare.D7.Monotonicity.BochnerCertificate
import Poincare.D7.Monotonicity.BochnerGradientEstimate
import Poincare.D7.Monotonicity.ConjugateHeatCertificate
import Poincare.D7.Monotonicity.ReducedVolumeInput
import Poincare.D7.Monotonicity.FMonotonicity
import Poincare.D7.Monotonicity.WMuMonotonicity
import Poincare.D7.Monotonicity.Nonvacuity
import Poincare.D7.Monotonicity.Blockers

/-! ## Axiom audit: vendored D7 Bochner certificate -/

#print axioms Poincare.D7.Bochner.BochnerCertificate
#print axioms Poincare.D7.Bochner.BochnerCertificate.bochner'
#print axioms Poincare.D7.Bochner.BochnerCertificate.roughLaplacian_le_oneFormLaplacian
#print axioms Poincare.D7.Bochner.GradientCertificate
#print axioms Poincare.D7.Bochner.GradientCertificate.bochner_inequality
#print axioms Poincare.D7.Bochner.GradientCertificate.gradient_estimate
#print axioms Poincare.D7.Bochner.gradientCertificateOfData

/-! ## Axiom audit: vendored D7 conjugate-heat certificate -/

#print axioms Poincare.D7.ConjugateHeat.ConjugateHeatData
#print axioms Poincare.D7.ConjugateHeat.ConjugateHeatData.formal_adjoint
#print axioms Poincare.D7.ConjugateHeat.ConjugateHeatData.isConjugateHeatJet_iff
#print axioms Poincare.D7.ConjugateHeat.ConjugateHeatIBPCertificate
#print axioms Poincare.D7.ConjugateHeat.ConjugateHeatIBPCertificate.heatPairing_eq_conjugatePairing
#print axioms Poincare.D7.ConjugateHeat.conjugateHeatIBPCertificate

/-! ## Axiom audit: reduced-volume input -/

#print axioms Poincare.D7.Monotonicity.reducedVolume_antitone_of_certificate
#print axioms Poincare.D7.Monotonicity.reducedVolume_le_of_le
#print axioms Poincare.D7.Monotonicity.neg_log_reducedVolume_monotoneOn
#print axioms Poincare.D7.Monotonicity.log_reducedVolume_antitoneOn
#print axioms Poincare.D7.Monotonicity.hasConjugateWeight_of_reducedLengthDensity
#print axioms Poincare.D7.Monotonicity.ReducedVolumeWDuality
#print axioms Poincare.D7.Monotonicity.antitoneOn_of_reducedVolumeWDuality
#print axioms Poincare.D7.Monotonicity.W_le_of_le_of_reducedVolumeWDuality

/-! ## Axiom audit: conditional `F`-monotonicity -/

#print axioms Poincare.D7.Monotonicity.PerelmanFAnalyticHypotheses
#print axioms Poincare.D7.Monotonicity.PerelmanFAnalyticHypotheses.toBridge
#print axioms Poincare.D7.Monotonicity.PerelmanFAnalyticHypotheses.toCertificate
#print axioms Poincare.D7.Monotonicity.PerelmanFAnalyticHypotheses.bochner_inequality
#print axioms Poincare.D7.Monotonicity.PerelmanFAnalyticHypotheses.gradient_estimate
#print axioms Poincare.D7.Monotonicity.PerelmanFAnalyticHypotheses.perelmanFMonotone_of_analyticHypotheses
#print axioms Poincare.D7.Monotonicity.PerelmanFAnalyticHypotheses.perelmanFMonotone_initial_le
#print axioms Poincare.D7.Monotonicity.PerelmanFAnalyticHypotheses.perelmanFMonotone_dissipation_nonneg
#print axioms Poincare.D7.Monotonicity.PerelmanFAnalyticHypotheses.perelmanFMonotone_eq_on_Icc_of_eq_at

/-! ## Axiom audit: conditional `W`/`μ`-monotonicity -/

#print axioms Poincare.D7.Monotonicity.PerelmanWKernelHypotheses
#print axioms Poincare.D7.Monotonicity.PerelmanWKernelHypotheses.weight_derivative_eq
#print axioms Poincare.D7.Monotonicity.PerelmanWKernelHypotheses.formal_adjoint
#print axioms Poincare.D7.Monotonicity.PerelmanWKernelHypotheses.ibp_pairing_eq
#print axioms Poincare.D7.Monotonicity.PerelmanWKernelHypotheses.w_dissipation_nonneg
#print axioms Poincare.D7.Monotonicity.PerelmanWKernelHypotheses.perelmanWMonotone_of_kernelHypotheses
#print axioms Poincare.D7.Monotonicity.PerelmanWKernelHypotheses.perelmanW_initial_le
#print axioms Poincare.D7.Monotonicity.w_monotoneOn_of_F_extra
#print axioms Poincare.D7.Monotonicity.muOfFamily
#print axioms Poincare.D7.Monotonicity.muOfFamily_monotoneOn
#print axioms Poincare.D7.Monotonicity.PerelmanMuKernelHypotheses
#print axioms Poincare.D7.Monotonicity.perelmanMuMonotone_of_kernelHypotheses
#print axioms Poincare.D7.Monotonicity.forwardReducedVolume
#print axioms Poincare.D7.Monotonicity.forwardReducedVolume_monotoneOn
#print axioms Poincare.D7.Monotonicity.PerelmanWMuKernelHypotheses
#print axioms Poincare.D7.Monotonicity.reducedVolumeEnvelope_monotoneOn
#print axioms Poincare.D7.Monotonicity.perelmanWMuMonotone_of_kernelHypotheses
#print axioms Poincare.D7.Monotonicity.perelmanMu_le_reducedVolumeEnvelope
#print axioms Poincare.D7.Monotonicity.perelmanMu_sandwich

/-! ## Axiom audit: non-vacuity instances -/

#print axioms Poincare.D7.Monotonicity.oneGradientCertificate
#print axioms Poincare.D7.Monotonicity.oneGradientCertificate_hessNormSq
#print axioms Poincare.D7.Monotonicity.oneGradientCertificate_gradient_estimate
#print axioms Poincare.D7.Monotonicity.trivialMetricFlowInterface
#print axioms Poincare.D7.Monotonicity.trivialConjugateHeatData
#print axioms Poincare.D7.Monotonicity.trivialConjugateHeatData_ibp_zero
#print axioms Poincare.D7.Monotonicity.unitConstantEntropyData
#print axioms Poincare.D7.Monotonicity.unitConstantEntropyData_conj
#print axioms Poincare.D7.Monotonicity.unitConstantEntropyData_F
#print axioms Poincare.D7.Monotonicity.unitConstantEntropyData_W
#print axioms Poincare.D7.Monotonicity.unitConstantEntropyData_FDissipation
#print axioms Poincare.D7.Monotonicity.perelmanFAnalyticHypotheses_zero
#print axioms Poincare.D7.Monotonicity.perelmanFMonotone_zero
#print axioms Poincare.D7.Monotonicity.perelmanFAnalyticHypotheses_zero_gradient_estimate
#print axioms Poincare.D7.Monotonicity.perelmanWKernelHypotheses_zero
#print axioms Poincare.D7.Monotonicity.perelmanWMonotone_zero
#print axioms Poincare.D7.Monotonicity.perelmanWKernelHypotheses_zero_ibp
#print axioms Poincare.D7.Monotonicity.perelmanMuKernelHypotheses_zero
#print axioms Poincare.D7.Monotonicity.perelmanMuMonotone_zero
#print axioms Poincare.D7.Monotonicity.constantReducedVolumeCertificate
#print axioms Poincare.D7.Monotonicity.perelmanWMuKernelHypotheses_zero
#print axioms Poincare.D7.Monotonicity.perelmanWMuMonotone_zero
#print axioms Poincare.D7.Monotonicity.perelmanMu_sandwich_zero
#print axioms Poincare.D7.Monotonicity.reducedVolumeWDuality_zero
#print axioms Poincare.D7.Monotonicity.perelmanWAntitone_zero
#print axioms Poincare.D7.Monotonicity.hasConjugateWeight_of_reducedLengthDensity_zero

/-! ## Axiom audit: the named open-hypothesis ledger -/

#print axioms Poincare.D7.Monotonicity.BlockerFWeightedIBP
#print axioms Poincare.D7.Monotonicity.BlockerFWeightedLaplacian
#print axioms Poincare.D7.Monotonicity.BlockerFBochner
#print axioms Poincare.D7.Monotonicity.BlockerFDerivative
#print axioms Poincare.D7.Monotonicity.BlockerFConjugateMeasure
#print axioms Poincare.D7.Monotonicity.BlockerFRegularity
#print axioms Poincare.D7.Monotonicity.BlockerFUpperBound
#print axioms Poincare.D7.Monotonicity.BlockerWFirstVariation
#print axioms Poincare.D7.Monotonicity.BlockerWRegularity
#print axioms Poincare.D7.Monotonicity.BlockerWUpperBound
#print axioms Poincare.D7.Monotonicity.BlockerMuInfimum
#print axioms Poincare.D7.Monotonicity.BlockerMuReducedVolume
#print axioms Poincare.D7.Monotonicity.BlockerWReducedDuality
#print axioms Poincare.D7.Monotonicity.monotonicityBlockers
#print axioms Poincare.D7.Monotonicity.monotonicityBlockers_length
#print axioms Poincare.D7.Monotonicity.monotonicityBlockers_ne_nil
#print axioms Poincare.D7.Monotonicity.monotonicityBlockers_all_named
