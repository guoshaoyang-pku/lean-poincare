import Poincare.D7.Reduced.Basic
import Poincare.D7.Reduced.Certificate
import Poincare.D7.Reduced.Statements
import Poincare.D7.Reduced.Gaussian

/-!
# Poincare.D7.Reduced.Audit

Per-declaration axiom report for the `D7-reduced-length-volume` layer.  Every principal
declaration of the layer is printed with `#print axioms`; the expected cones are `{}`,
`{propext}`, `{propext, Quot.sound}` or `{propext, Classical.choice, Quot.sound}`.  This file
contains no proofs and no new declarations.
-/

namespace Poincare.D7.Reduced

-- Basic layer.
#print axioms MetricFlowInterface.metric_add_right
#print axioms MetricFlowInterface.metric_smul_right
#print axioms MetricFlowInterface.LIntegrandAlong
#print axioms MetricFlowInterface.LlengthAlong
#print axioms MetricFlowInterface.LIntegrand
#print axioms MetricFlowInterface.Llength
#print axioms MetricFlowInterface.Llength_eq_LlengthAlong
#print axioms MetricFlowInterface.reducedLengthAlong
#print axioms MetricFlowInterface.reducedLength
#print axioms MetricFlowInterface.LlengthAlong_nonneg
#print axioms MetricFlowInterface.reducedLengthAlong_nonneg
#print axioms LPath.length
#print axioms LPath.reducedLength
#print axioms LPath.length_nonneg
#print axioms LPath.reducedLength_nonneg
#print axioms IsLMinimizer
#print axioms ReducedLengthData.length
#print axioms ReducedLengthData.reducedLength
#print axioms ReducedLengthData.reducedLength_nonneg

-- Certificate layer.
#print axioms ReducedVolumeCertificate.antitoneOn
#print axioms ReducedVolumeCertificate.reducedVolume
#print axioms ReducedVolumeCertificate.reducedVolume_antitone
#print axioms ReducedVolumeCertificate.volume_le_of_le
#print axioms ReducedVolumeCertificate.volume_le_at
#print axioms ReducedVolumeCertificate.volume_le_one
#print axioms ReducedVolumeCertificate.neg_log_monotoneOn
#print axioms FiniteReducedVolumeCertificate.volume
#print axioms FiniteReducedVolumeCertificate.volume_antitone
#print axioms FiniteReducedVolumeCertificate.reducedVolume
#print axioms FiniteReducedVolumeCertificate.reducedVolume_antitone
#print axioms FiniteReducedVolumeCertificate.volume_le_of_le
#print axioms ReducedLengthDensityCertificate.density
#print axioms ReducedLengthDensityCertificate.volume
#print axioms ReducedLengthDensityCertificate.hasDerivAt_normalisation
#print axioms ReducedLengthDensityCertificate.density_hasDerivAt
#print axioms ReducedLengthDensityCertificate.density_derivative_nonpos
#print axioms ReducedLengthDensityCertificate.toFiniteCertificate
#print axioms ReducedLengthDensityCertificate.volume_antitone
#print axioms ReducedLengthDensityCertificate.reducedVolume
#print axioms ReducedLengthDensityCertificate.reducedVolume_antitone
#print axioms ReducedLengthDensityCertificate.volume_le_of_le
#print axioms zeroReducedLengthDensityCertificate
#print axioms criticalReducedLengthDensityCertificate
#print axioms criticalReducedLengthDensityCertificate_density
#print axioms criticalReducedLengthDensityCertificate_volume
#print axioms zeroReducedLengthDensityCertificate_volume_antitone

-- Statements layer.
#print axioms LMinimizerExistence
#print axioms ReducedVolumeMonotonicity
#print axioms reducedVolumeMonotonicity_of_certificate
#print axioms JacobianComparisonInterface
#print axioms JacobianComparison
#print axioms BlockerLMinimizerExistence
#print axioms BlockerJacobianComparison
#print axioms BlockerReducedVolumeMonotonicity
#print axioms BlockerLMinimizerExistence_ne_nil
#print axioms BlockerJacobianComparison_ne_nil
#print axioms BlockerReducedVolumeMonotonicity_ne_nil
#print axioms reducedVolumeDependencies
#print axioms reducedVolumeDependencies_length
#print axioms reducedVolumeDependencies_ne_nil
#print axioms reducedVolumeDependencies_all_named

-- Gaussian layer.
#print axioms gaussianFlow
#print axioms gaussianFlow_scalarCurvature
#print axioms gaussianFlow_metric
#print axioms gaussianPath
#print axioms gaussianVelocity
#print axioms integral_one_div_sqrt
#print axioms gaussian_integrand
#print axioms gaussian_LlengthAlong
#print axioms gaussian_reducedLengthAlong
#print axioms gaussianPath_hasDerivAt
#print axioms intervalIntegrable_one_div_sqrt
#print axioms gaussianLPath
#print axioms gaussian_length_le
#print axioms gaussian_isLMinimizer
#print axioms gaussianReducedLengthData
#print axioms gaussianReducedLengthData_reducedLength
#print axioms gaussianLMinimizerExistence

end Poincare.D7.Reduced
