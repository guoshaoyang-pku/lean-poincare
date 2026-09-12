import Poincare.D7.TensorLaplacian.Example
import Poincare.D7.TensorLaplacian.Blocked

/-!
# Poincare.D7.TensorLaplacian.Probe

**D7 tensor Laplacian layer, part 6: a compilable API probe.**

Every command in this file is checked by `lake env lean`. `#check` records the declarations that
are present and reused; `#check_failure` records the declarations that are **absent** at the
pinned mathlib revision `7974e751bece493b6ff508039423ca9fa2452fa8` and that are the named
blockers of `Poincare.D7.TensorLaplacian.Blocked`.
-/

open scoped BigOperators

namespace Poincare
namespace D7
namespace TensorLaplacian

/-! ## The finite-dimensional layer -/

-- The tensor-data interface and its curvature certificate.
#check @TensorConnectionData
#check @TensorConnectionData.nabla
#check @TensorConnectionData.curvature
#check @TensorConnectionData.curvature_certificate
#check @TensorConnectionData.curvature_skew
#check @TensorConnectionData.second_covariant_derivative_commutation

-- The rough Laplacian.
#check @TensorConnectionData.roughLaplacianₗ
#check @TensorConnectionData.roughLaplacian
#check @TensorConnectionData.roughLaplacian_apply
#check @TensorConnectionData.roughLaplacian_add
#check @TensorConnectionData.roughLaplacian_smul

-- The commutation formulas.
#check @TensorConnectionData.commutator_term
#check @TensorConnectionData.roughLaplacian_commutator_general
#check @TensorConnectionData.roughLaplacian_commutator_of_bracket_zero
#check @TensorConnectionData.HasParallelCurvature
#check @TensorConnectionData.ricciContraction
#check @TensorConnectionData.roughLaplacian_commutator_of_parallel
#check @TensorConnectionData.RicciCommutationCertificate
#check @TensorConnectionData.roughLaplacian_commutator_ricci
#check @TensorConnectionData.ScalarCurvatureCommutationCertificate
#check @TensorConnectionData.roughLaplacian_commutator_frame_trace
#check @TensorConnectionData.roughLaplacian_commutator_eq_zero_of_flat

-- The evolution identity.
#check @ricciNormSq
#check @ricciNormSq_nonneg
#check @traceH
#check @pairingH
#check @ricciFlowVelocity
#check @IsRicciFlowVelocity
#check @traceH_ricciFlowVelocity
#check @pairingH_ricciFlowVelocity
#check @ScalarEvolutionCertificate
#check @ScalarEvolutionCertificate.traceH_eq
#check @ScalarEvolutionCertificate.pairingH_eq
#check @ScalarEvolutionCertificate.variation_rhs_eq
#check @ScalarEvolutionCertificate.scalarDeriv_eq
#check @ScalarEvolutionCertificate.scalar_evolution
#check @ScalarEvolutionCertificate.scalar_evolution_iff
#check @flatCertificate

-- Concrete inhabitants.
#check @scalarTensorData
#check @vectorTensorData
#check @prodTensorData
#check @So3Example.so3_ricciNormSq_pos
#check @So3Example.so3EvolutionCertificate
#check @So3Example.so3_evolution_identity
#check @So3Example.so3_evolution_rhs_pos
#check @So3Example.so3_vector_curvature_witness
#check @WrongBianchiData
#check @wrongBianchiExample
#check @wrongBianchi_identity_fails

-- The blocked smooth layer.
#check @SmoothTensorLaplacianDatum
#check @IsSmoothTensorLaplacianDatum
#check @SmoothCurvatureCertificateStatement
#check @SmoothCommutationStatement
#check @SmoothFrameTraceCommutationStatement
#check @SmoothScalarEvolutionDatum
#check @IsSmoothScalarEvolutionDatum
#check @SmoothScalarEvolutionStatement
#check @MissingMathlibDependencies
#check @PresentMathlibDependencies

/-! ## Present mathlib API -/

#check @CovariantDerivative
#check @CovariantDerivative.leviCivitaConnection
#check @CovariantDerivative.IsLeviCivitaConnection
#check @CovariantDerivative.torsion
#check @CovariantDerivative.IsMetricCompatible
#check @mfderiv
#check @ContMDiff
#check @TangentSpace
#check @TangentBundle
#check @IsRiemannianManifold
#check @ModelWithCorners
#check @IsManifold
#check @LinearMap.trace
#check @LinearMap.comp
#check @LinearMap.comp_assoc
#check @HasDerivAt
#check @HasDerivAt.unique
#check @Finset.sum_sub_distrib
#check @Finset.sum_add_distrib
#check @Finset.mul_sum
#check @Finset.smul_sum
#check @Finset.single_le_sum

/-! ## Absent mathlib API (the blockers) -/

#check_failure Hessian
#check_failure LaplaceBeltrami
#check_failure Riemann
#check_failure Ricci
#check_failure roughLaplacian
#check_failure TensorBundle
#check_failure CovariantDerivative.curvature
#check_failure CovariantDerivative.secondCovariantDerivative
#check_failure Manifold.curvature
#check_failure Manifold.divergence
#check_failure RiemannianVolumeMeasure
#check_failure Manifold.stokes

end TensorLaplacian
end D7
end Poincare
