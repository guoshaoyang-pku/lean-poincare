import Poincare.D11.ReducedVolume.All

/-!
# Poincare.D11.ReducedVolume.Probe

Compilable API probe for the `D11-reduced-volume-euclidean` layer: one `#check` per principal
declaration, so downstream consumers (notably the D7 reduced-length / reduced-volume layer and
the verifier) can resolve every name.  This file contains no proofs and no new declarations.
-/

namespace Poincare.D11.ReducedVolume

-- Basic: flat interface and L-length.
#check euclideanFlow
#check euclideanFlow_scalarCurvature
#check euclideanFlow_metric
#check flatLIntegrand
#check flatLlength
#check flatLlength_eq_LlengthAlong
#check flatReducedLength
#check flatReducedLength_eq_reducedLength
#check heatKernelReducedDistance
#check heatKernelReducedDistance_eq
#check heatKernel_asymptotics
#check heatKernelReducedDistance_nonneg
#check heatKernelReducedDistance_eq_reducedLength
#check heatKernelReducedDistance_zero

-- StraightRays: the L-geodesics from the origin are straight rays.
#check straightRay
#check straightRayVelocity
#check straightRay_eq_gaussianPath
#check straightRayVelocity_eq_gaussianVelocity
#check straightRay_zero
#check straightRay_tau
#check straightRay_hasDerivAt
#check straightRayLPath
#check straightRay_length
#check straightRay_reducedLength
#check heatKernelReducedDistance_eq_straightRayReducedLength
#check straightRay_isLMinimizer
#check euclidean_LMinimizerExistence
#check flatDeficit
#check flatDeficit_eq_normSq
#check flatDeficit_nonneg
#check flatDeficit_integral
#check ae_velocity_eq_of_deficit_integral_zero
#check LMinimizer_eq_straightRay
#check IsLMinimizer_of_eq_straightRay
#check minimizer_iff_eq_straightRay

-- Volume: integrand = Gaussian, reduced volume = 1.
#check reducedVolumeIntegrand
#check reducedVolumeIntegrandUnnormalized
#check reducedVolume
#check euclideanReducedVolume
#check reducedVolumeIntegrand_eq_gaussianKernel
#check reducedVolumeIntegrandUnnormalized_eq
#check reducedVolumeIntegrandUnnormalized_eq_gaussianKernel
#check integral_reducedVolumeIntegrandUnnormalized
#check integral_reducedVolumeIntegrandUnnormalized_constant
#check reducedVolume_eq_one
#check euclideanReducedVolume_eq_one
#check reducedVolume_constant
#check reducedVolume_nonneg

-- Statements: named Props, manifold interface, Euclidean instantiation.
#check ManifoldReducedVolumeInterface
#check ReducedVolumeMonotonicityTheorem
#check generalMonotonicityMissingDependencies
#check generalMonotonicityMissingDependencies_ne_nil
#check generalMonotonicityMissingDependencies_length
#check euclideanManifoldReducedVolumeInterface
#check euclideanManifoldReducedVolumeInterface_flow
#check euclideanManifoldReducedVolumeInterface_dimension
#check euclideanManifoldReducedVolumeInterface_reducedDistance
#check euclideanManifoldReducedVolumeInterface_reducedVolume
#check euclidean_manifoldReducedVolumeMonotonicity
#check euclideanReducedVolumeCertificate
#check euclideanReducedVolumeCertificate_flow
#check euclideanReducedVolumeCertificate_volume
#check euclideanReducedVolumeCertificate_derivative
#check euclideanReducedVolumeCertificate_antitoneOn
#check euclidean_reducedVolumeMonotonicity
#check flatLExponential
#check flatLExponential_det
#check euclideanJacobianComparisonInterface
#check euclideanJacobianComparisonInterface_jacobian
#check euclideanJacobianComparisonInterface_comparison
#check euclidean_jacobianComparison
#check euclidean_manifold_LMinimizerExistence
#check EuclideanReducedVolumeAnchor
#check euclideanReducedVolumeAnchor

end Poincare.D11.ReducedVolume
