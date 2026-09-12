import Poincare.D7.Reduced.Basic
import Poincare.D7.Reduced.Certificate
import Poincare.D7.Reduced.Statements
import Poincare.D7.Reduced.Gaussian

/-!
# Poincare.D7.Reduced.Probe

Compilable API probe for the `D7-reduced-length-volume` layer: every principal definition and
theorem of the layer is `#check`ed, so that a consumer can see the exact statements.  This file
contains no proofs and no new declarations.
-/

open MeasureTheory intervalIntegral Set
open scoped RealInnerProductSpace

namespace Poincare.D7.Reduced

-- Basic layer: the stated metric-flow interface and the `L`-length functional.
#check MetricFlowInterface
#check MetricFlowInterface.metric_add_right
#check MetricFlowInterface.metric_smul_right
#check MetricFlowInterface.LIntegrandAlong
#check MetricFlowInterface.LlengthAlong
#check MetricFlowInterface.LIntegrand
#check MetricFlowInterface.Llength
#check MetricFlowInterface.Llength_eq_LlengthAlong
#check MetricFlowInterface.reducedLengthAlong
#check MetricFlowInterface.reducedLength
#check MetricFlowInterface.LlengthAlong_nonneg
#check MetricFlowInterface.reducedLengthAlong_nonneg
#check LPath
#check LPath.length
#check LPath.reducedLength
#check LPath.length_nonneg
#check LPath.reducedLength_nonneg
#check IsLMinimizer
#check ReducedLengthData
#check ReducedLengthData.length
#check ReducedLengthData.reducedLength
#check ReducedLengthData.reducedLength_nonneg

-- Certificate layer: reduced-volume certificates and monotonicity consequences.
#check ReducedVolumeCertificate
#check ReducedVolumeCertificate.antitoneOn
#check ReducedVolumeCertificate.reducedVolume
#check ReducedVolumeCertificate.reducedVolume_antitone
#check ReducedVolumeCertificate.volume_le_of_le
#check ReducedVolumeCertificate.volume_le_at
#check ReducedVolumeCertificate.volume_le_one
#check ReducedVolumeCertificate.neg_log_monotoneOn
#check FiniteReducedVolumeCertificate
#check FiniteReducedVolumeCertificate.volume
#check FiniteReducedVolumeCertificate.volume_antitone
#check FiniteReducedVolumeCertificate.reducedVolume
#check FiniteReducedVolumeCertificate.reducedVolume_antitone
#check FiniteReducedVolumeCertificate.volume_le_of_le
#check ReducedLengthDensityCertificate
#check ReducedLengthDensityCertificate.density
#check ReducedLengthDensityCertificate.volume
#check ReducedLengthDensityCertificate.hasDerivAt_normalisation
#check ReducedLengthDensityCertificate.density_hasDerivAt
#check ReducedLengthDensityCertificate.density_derivative_nonpos
#check ReducedLengthDensityCertificate.toFiniteCertificate
#check ReducedLengthDensityCertificate.volume_antitone
#check ReducedLengthDensityCertificate.reducedVolume
#check ReducedLengthDensityCertificate.reducedVolume_antitone
#check ReducedLengthDensityCertificate.volume_le_of_le
#check zeroReducedLengthDensityCertificate
#check criticalReducedLengthDensityCertificate
#check criticalReducedLengthDensityCertificate_density
#check criticalReducedLengthDensityCertificate_volume
#check zeroReducedLengthDensityCertificate_volume_antitone

-- Statements layer: state-only propositions and the missing-dependency ledger.
#check LMinimizerExistence
#check ReducedVolumeMonotonicity
#check reducedVolumeMonotonicity_of_certificate
#check JacobianComparisonInterface
#check JacobianComparison
#check BlockerLMinimizerExistence
#check BlockerJacobianComparison
#check BlockerReducedVolumeMonotonicity
#check reducedVolumeDependencies
#check reducedVolumeDependencies_length
#check reducedVolumeDependencies_all_named

-- Gaussian layer: the explicit computation and the minimiser.
#check gaussianFlow
#check gaussianFlow_scalarCurvature
#check gaussianFlow_metric
#check gaussianPath
#check gaussianVelocity
#check integral_one_div_sqrt
#check gaussian_integrand
#check gaussian_LlengthAlong
#check gaussian_reducedLengthAlong
#check gaussianPath_hasDerivAt
#check intervalIntegrable_one_div_sqrt
#check gaussianLPath
#check gaussian_length_le
#check gaussian_isLMinimizer
#check gaussianReducedLengthData
#check gaussianReducedLengthData_reducedLength
#check gaussianLMinimizerExistence

end Poincare.D7.Reduced
