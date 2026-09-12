/-
Task `D3-entropy-interface`: consolidated `#print axioms` audit.

**Scope and honesty boundary.** This file only prints axiom dependencies of the
declarations in `Poincare.Longrun.Entropy`.  It proves no mathematics and is not
a proof of Perelman's entropy monotonicity or of the Poincaré conjecture.

Expected output: every declaration depends only on
`[propext, Classical.choice, Quot.sound]` (or on a subset).  No declaration may
report `sorryAx`, and no project axiom may appear.
-/
import Poincare.Longrun.Entropy

namespace Poincare.Longrun.Entropy

/-! ## `Functional` -/

#print axioms EntropyData
#print axioms EntropyData.F
#print axioms EntropyData.extra
#print axioms EntropyData.W
#print axioms EntropyData.FDissipation
#print axioms EntropyData.HasConjugateWeight
#print axioms EntropyData.conjugateWeight_pos
#print axioms EntropyData.integrable_extra
#print axioms EntropyData.W_eq
#print axioms EntropyData.FDissipation_nonneg
#print axioms EntropyData.F_mono_integrand

/-! ## `Certificate` -/

#print axioms MonotoneCertificate
#print axioms MonotoneCertificate.F_le_of_le
#print axioms MonotoneCertificate.F_ge_at
#print axioms MonotoneCertificate.le_upper
#print axioms MonotoneCertificate.eq_of_le_of_eq
#print axioms AntitoneCertificate
#print axioms AntitoneCertificate.F_le_of_le
#print axioms AntitoneCertificate.F_le_at
#print axioms AntitoneCertificate.lower_le_value
#print axioms AntitoneCertificate.eq_of_le_of_eq
#print axioms ContinuousMonotoneCertificate
#print axioms ContinuousMonotoneCertificate.monotoneOn
#print axioms ContinuousMonotoneCertificate.F_ge_initial
#print axioms ContinuousMonotoneCertificate.eq_on_Icc_of_eq_at
#print axioms ContinuousMonotoneCertificate.toMonotoneCertificateOnIci
#print axioms ContinuousAntitoneCertificate
#print axioms ContinuousAntitoneCertificate.antitoneOn
#print axioms ContinuousAntitoneCertificate.F_le_initial
#print axioms ContinuousAntitoneCertificate.lower_le_initial
#print axioms ContinuousAntitoneCertificate.eq_on_Icc_of_eq_at
#print axioms ContinuousAntitoneCertificate.toAntitoneCertificateOnIci
#print axioms LinearDecayCertificate
#print axioms LinearDecayCertificate.F_le_initial
#print axioms LinearDecayCertificate.time_le
#print axioms LinearDecayCertificate.lower_le_value
#print axioms zeroEntropyData
#print axioms zeroEntropyData_F
#print axioms continuousMonotoneCertificate_zero
#print axioms continuousAntitoneCertificate_zero

/-! ## `Bridge` (statement-only) -/

#print axioms WeightedCalculus
#print axioms gradInner
#print axioms WeightedIBPStatement
#print axioms WeightedLaplacianStatement
#print axioms BochnerStatement
#print axioms ConjugateMeasureEvolutionStatement
#print axioms FDerivativeStatement
#print axioms EntropyFunctionalRegularityStatement
#print axioms EntropyRegularityBridge
#print axioms continuousMonotoneCertificateOfBridge
#print axioms zeroCalculus
#print axioms entropyRegularityBridge_zero
#print axioms continuousMonotoneCertificate_zero_viaBridge

/-! ## `DiscreteHeat` (D2-pde-foundation consumption) -/

#print axioms Poincare.Longrun.PDE.HeatGridEvolution.energy_antitone
#print axioms Poincare.Longrun.PDE.zeroHeatGridEvolution
#print axioms heatEnergyCertificate
#print axioms heatEnergy_le_initial
#print axioms heatEnergy_nonneg
#print axioms heatEnergy_eq_of_eq_initial
#print axioms heatEnergyCertificate_zero

/-! ## `FiniteGeometry` (D2-geometry-foundation consumption) -/

#print axioms finiteCurvatureDatum
#print axioms finiteCurvatureDatum_F
#print axioms finiteCurvatureDatum_F_zero
#print axioms finiteCurvatureDatum_W
#print axioms finiteCurvatureDatum_FDissipation
#print axioms finiteCurvatureDatum_F_add

end Poincare.Longrun.Entropy
