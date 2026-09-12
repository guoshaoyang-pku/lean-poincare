import Poincare.D11.ReducedVolume.All

/-!
# Poincare.D11.ReducedVolume.Audit

Per-declaration axiom report for the `D11-reduced-volume-euclidean` layer.  Every principal
declaration of the layer is printed with `#print axioms`; the expected cones are `{}`,
`{propext}`, `{propext, Quot.sound}` or `{propext, Classical.choice, Quot.sound}`.  This file
contains no proofs and no new declarations.
-/

namespace Poincare.D11.ReducedVolume

-- Basic.
#print axioms euclideanFlow
#print axioms euclideanFlow_scalarCurvature
#print axioms euclideanFlow_metric
#print axioms flatLIntegrand
#print axioms flatLlength
#print axioms flatLlength_eq_LlengthAlong
#print axioms flatReducedLength
#print axioms flatReducedLength_eq_reducedLength
#print axioms heatKernelReducedDistance
#print axioms heatKernelReducedDistance_eq
#print axioms heatKernel_asymptotics
#print axioms heatKernelReducedDistance_nonneg
#print axioms heatKernelReducedDistance_eq_reducedLength
#print axioms heatKernelReducedDistance_zero

-- StraightRays.
#print axioms straightRay
#print axioms straightRayVelocity
#print axioms straightRay_eq_gaussianPath
#print axioms straightRayVelocity_eq_gaussianVelocity
#print axioms straightRay_zero
#print axioms straightRay_tau
#print axioms straightRay_hasDerivAt
#print axioms straightRayLPath
#print axioms straightRay_length
#print axioms straightRay_reducedLength
#print axioms heatKernelReducedDistance_eq_straightRayReducedLength
#print axioms straightRay_isLMinimizer
#print axioms euclidean_LMinimizerExistence
#print axioms flatDeficit
#print axioms flatDeficit_eq_normSq
#print axioms flatDeficit_nonneg
#print axioms flatDeficit_integral
#print axioms ae_velocity_eq_of_deficit_integral_zero
#print axioms LMinimizer_eq_straightRay
#print axioms IsLMinimizer_of_eq_straightRay
#print axioms minimizer_iff_eq_straightRay

-- Volume.
#print axioms reducedVolumeIntegrand
#print axioms reducedVolumeIntegrandUnnormalized
#print axioms reducedVolume
#print axioms euclideanReducedVolume
#print axioms reducedVolumeIntegrand_eq_gaussianKernel
#print axioms reducedVolumeIntegrandUnnormalized_eq
#print axioms reducedVolumeIntegrandUnnormalized_eq_gaussianKernel
#print axioms integral_reducedVolumeIntegrandUnnormalized
#print axioms integral_reducedVolumeIntegrandUnnormalized_constant
#print axioms reducedVolume_eq_one
#print axioms euclideanReducedVolume_eq_one
#print axioms reducedVolume_constant
#print axioms reducedVolume_nonneg

-- Statements.
#print axioms ManifoldReducedVolumeInterface
#print axioms ReducedVolumeMonotonicityTheorem
#print axioms generalMonotonicityMissingDependencies
#print axioms generalMonotonicityMissingDependencies_ne_nil
#print axioms generalMonotonicityMissingDependencies_length
#print axioms euclideanManifoldReducedVolumeInterface
#print axioms euclideanManifoldReducedVolumeInterface_flow
#print axioms euclideanManifoldReducedVolumeInterface_dimension
#print axioms euclideanManifoldReducedVolumeInterface_reducedDistance
#print axioms euclideanManifoldReducedVolumeInterface_reducedVolume
#print axioms euclidean_manifoldReducedVolumeMonotonicity
#print axioms euclideanReducedVolumeCertificate
#print axioms euclideanReducedVolumeCertificate_flow
#print axioms euclideanReducedVolumeCertificate_volume
#print axioms euclideanReducedVolumeCertificate_derivative
#print axioms euclideanReducedVolumeCertificate_antitoneOn
#print axioms euclidean_reducedVolumeMonotonicity
#print axioms flatLExponential
#print axioms flatLExponential_det
#print axioms euclideanJacobianComparisonInterface
#print axioms euclideanJacobianComparisonInterface_jacobian
#print axioms euclideanJacobianComparisonInterface_comparison
#print axioms euclidean_jacobianComparison
#print axioms euclidean_manifold_LMinimizerExistence
#print axioms EuclideanReducedVolumeAnchor
#print axioms euclideanReducedVolumeAnchor

end Poincare.D11.ReducedVolume
