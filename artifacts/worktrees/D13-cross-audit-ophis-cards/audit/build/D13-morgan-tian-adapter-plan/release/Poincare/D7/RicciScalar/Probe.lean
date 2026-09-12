import Poincare.D7.RicciScalar.Bridge

/-!
# Poincare.D7.RicciScalar.Probe

**D7 Ricci/scalar layer, part 8: the compilable API probe.**

Every `#check` below must succeed against the pinned toolchain, and every `#check_failure` must
fail (recording a genuinely absent declaration). The probe records both the mathlib API reused by
this layer and the exact absent declarations that keep the variation interface conditional.

## Reused mathlib API

`LinearMap.trace`, `LinearMap.trace_eq_matrix_trace`, `LinearMap.trace_smulRight`,
`LinearMap.trace_id`, `LinearMap.trace_prodMap'`, `Module.Basis.prod` and its coordinate
lemmas, `Fintype.sum_sum_type`, `HasDerivAt.sum`, `hasDerivAt_const`, `crossProduct`,
`cross_dot_cross`, `cross_cross_eq_smul_sub_smul'`.

## Absent mathlib API

`CovariantDerivative.curvature`, `RiemannTensor`, `RiemannianCurvature`, `RicciTensor`,
`Bianchi`, `CovariantDerivative.ricci`: the pinned mathlib revision
`7974e751bece493b6ff508039423ca9fa2452fa8` has no curvature tensor for a covariant derivative,
which is why the manifold-level constructions of this program are explicit blocked `Prop`s.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators

namespace Poincare
namespace D7
namespace RicciScalar

/-! ## 1. Reused mathlib API -/

#check LinearMap.trace
#check LinearMap.trace_eq_matrix_trace
#check LinearMap.trace_smulRight
#check LinearMap.trace_id
#check LinearMap.trace_prodMap'
#check Module.Basis.prod
#check Module.Basis.prod_apply_inl_fst
#check Module.Basis.prod_apply_inr_snd
#check Module.Basis.prod_repr_inl
#check Module.Basis.reindex
#check Fintype.sum_sum_type
#check HasDerivAt.sum
#check hasDerivAt_const
#check crossProduct
#check cross_dot_cross
#check cross_cross_eq_smul_sub_smul'

/-! ## 2. Absent mathlib curvature API (the recorded gap) -/

#check_failure CovariantDerivative.curvature
#check_failure RiemannTensor
#check_failure RiemannianCurvature
#check_failure RicciTensor
#check_failure Bianchi
#check_failure CovariantDerivative.ricci

/-! ## 3. The D7 Ricci/scalar API index -/

#check ricciTrace
#check ricciTrace_basis_independent
#check ricciTensor
#check ricciTensor_eq_ricciOperator
#check ricciTensor_eq_basisTrace
#check ricciTensor_symm
#check scalarMetricTrace
#check scalarBasisSum
#check scalarMetricTrace_basis_independent
#check scalarBasisSum_congr_orthonormal
#check scalarCurvature_eq_basisTrace
#check scalarCurvature_eq_d2
#check prodData
#check prodData_ricciForm
#check prodData_scalarCurvature
#check FlowPath
#check FlowPath.MetricFlowEquation
#check FlowPath.RicciFlowEquation
#check FlowPath.LeviCivitaEvolution
#check FlowPath.LeviCivitaEvolutionStatement
#check FlowPath.TraceCommutationStatement
#check FlowPath.ScalarVariationStatement
#check FlowPath.scalarVariation_of_traceCommutation
#check FlowPath.constFlow_scalarVariation

end RicciScalar
end D7
end Poincare
