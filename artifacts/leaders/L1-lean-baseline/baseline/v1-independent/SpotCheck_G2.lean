/- INDEPENDENT spot-check driver (verifier lane) -/
import Poincare.D7.Kappa.All
import Poincare.D7.Kappa.Audit
import Poincare.D7.Kappa.EntropyBridge
import Poincare.D7.Kappa.Nonvacuity
import Poincare.D7.Kappa.Probe
import Poincare.D7.Kappa.Statements
import Poincare.D7.Monotonicity.All
import Poincare.D7.Monotonicity.Blockers
import Poincare.D7.Monotonicity.BochnerCertificate
import Poincare.D7.Monotonicity.BochnerGradientEstimate
import Poincare.D7.Monotonicity.ConjugateHeatCertificate
import Poincare.D7.Monotonicity.FMonotonicity
import Poincare.D7.Monotonicity.Nonvacuity
import Poincare.D7.Monotonicity.WMuMonotonicity

#print axioms Poincare.D7.Bochner.BochnerCertificate.mk.injEq
#print axioms Poincare.D7.Bochner.GradientCertificate._sizeOf_inst
#print axioms Poincare.D7.ConjugateHeat.ConjugateHeatData.mk.sizeOf_spec
#print axioms Poincare.D7.ConjugateHeat.Jet.deriv
#print axioms Poincare.D7.Kappa.kappaNoncollapsing_of_reducedVolumeWDuality
#print axioms Poincare.D7.Monotonicity.BlockerFWeightedIBP
#print axioms Poincare.D7.Monotonicity.PerelmanFAnalyticHypotheses.rec
#print axioms Poincare.D7.Monotonicity.PerelmanWKernelHypotheses.mk._flat_ctor
#print axioms Poincare.D7.Monotonicity.PerelmanWMuKernelHypotheses.reducedVolume
#print axioms Poincare.D7.Monotonicity.monotonicityBlockers_length
#print axioms Poincare.D7.Monotonicity.perelmanWMuKernelHypotheses_zero
