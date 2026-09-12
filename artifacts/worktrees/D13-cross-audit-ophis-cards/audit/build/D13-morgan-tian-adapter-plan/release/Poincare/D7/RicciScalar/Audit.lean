import Poincare.D7.RicciScalar.Bridge

/-!
# Poincare.D7.RicciScalar.Audit

**D7 Ricci/scalar layer, part 7: the per-declaration axiom audit.**

This module runs `#print axioms` on every principal declaration of the layer. The expected
cones are `{}`, `{propext}`, `{propext, Quot.sound}` or
`{propext, Classical.choice, Quot.sound}`; the only axioms permitted by the task are `propext`,
`Classical.choice` and `Quot.sound`. In particular, no declaration may depend on `sorryAx`, and
none of the sources contains `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.

The unproved variation interfaces are `Prop`-valued definitions and structures with no proof;
`#print axioms` on them reports the axioms used by the *statement*, which audits the interface
(no hidden assumption).
-/

open scoped BigOperators

namespace Poincare
namespace D7
namespace RicciScalar

/-! ## Ricci as a basis trace and its basis-independence -/

#print axioms ricciTrace
#print axioms ricciTrace_apply
#print axioms ricciTrace_eq_ricciSum
#print axioms ricciTrace_eq_d2
#print axioms ricciTrace_eq_ricciForm
#print axioms ricciForm_eq_ricciTrace
#print axioms ricciTrace_basis_independent
#print axioms ricciForm_eq_ricciOperator
#print axioms ricciTrace_eq_ricciOperator
#print axioms ricciTensor
#print axioms ricciTensor_eq_ricciOperator
#print axioms ricciTensor_eq_basisTrace
#print axioms ricciForm_symm_via_symmetries
#print axioms ricciTrace_symm
#print axioms ricciForm_symm'
#print axioms ricciTensor_symm
#print axioms zero_ricciForm
#print axioms ricciTrace_zero

/-! ## Scalar curvature as the metric trace and its basis-independence -/

#print axioms scalarMetricTrace
#print axioms scalarBasisSum
#print axioms scalarMetricTrace_eq_scalarCurvature
#print axioms scalarBasisSum_eq_scalarCurvature
#print axioms scalarBasisSum_eq_metricTrace
#print axioms scalarCurvature_eq_basisTrace
#print axioms scalarMetricTrace_eq_trace_basis
#print axioms scalarMetricTrace_basis_independent
#print axioms raiseIndex_congr
#print axioms scalarCurvature_congr_metric_form
#print axioms scalarBasisSum_congr_orthonormal
#print axioms scalarCurvature_eq_d2
#print axioms scalarMetricTrace_eq_d2
#print axioms scalarCurvature_zero
#print axioms scalarMetricTrace_zero

/-! ## The product structure and scalar additivity -/

#print axioms prodBracket
#print axioms prodBracket_bracket
#print axioms prodConn
#print axioms prodConn_nabla
#print axioms prodConn_lie
#print axioms prodForm
#print axioms prodForm_apply
#print axioms prodMetric
#print axioms prodData
#print axioms prodData_form_apply
#print axioms prodData_nabla
#print axioms prodData_basis_inl
#print axioms prodData_basis_inr
#print axioms prodConn_curvature_apply
#print axioms prodData_curvature_apply
#print axioms prodData_curvatureForm_apply
#print axioms prodData_endoRicci
#print axioms prodData_ricciForm
#print axioms prodData_scalarCurvature
#print axioms prodData_scalarMetricTrace

/-! ## The variation interface -/

#print axioms FlowPath
#print axioms FlowPath.scal
#print axioms FlowPath.ricci
#print axioms FlowPath.metricForm
#print axioms FlowPath.nabla
#print axioms FlowPath.bracket
#print axioms FlowPath.curvature
#print axioms FlowPath.MetricFlowEquation
#print axioms FlowPath.RicciFlowEquation
#print axioms FlowPath.LeviCivitaEvolution
#print axioms FlowPath.LeviCivitaEvolutionStatement
#print axioms FlowPath.curvVel
#print axioms FlowPath.CurvatureEvolutionStatement
#print axioms FlowPath.TraceCommutationStatement
#print axioms FlowPath.ScalarVariationStatement
#print axioms FlowPath.scalarVariation_of_traceCommutation
#print axioms FlowPath.scalarVariation_of_traceCommutationStatement
#print axioms FlowPath.RicciFlowScalarVariationStatement
#print axioms FlowPath.ricciFlowScalarVariation_of_traceCommutation
#print axioms FlowPath.ScalarVariationInterface
#print axioms FlowPath.BlockerLeviCivitaEvolution
#print axioms FlowPath.BlockerTraceCommutation
#print axioms FlowPath.BlockerScalarVariation
#print axioms FlowPath.BlockerLeviCivitaEvolution_ne_nil
#print axioms FlowPath.BlockerTraceCommutation_ne_nil
#print axioms FlowPath.BlockerScalarVariation_ne_nil
#print axioms FlowPath.constFlow
#print axioms FlowPath.constFlow_scalarVariation

/-! ## The concrete non-vacuous model -/

#print axioms so3_trace_comp
#print axioms so3_ricciForm_apply
#print axioms so3_ricciForm_e_self
#print axioms so3_scalarCurvature
#print axioms permBasis
#print axioms so3_ricciTrace_e0_e0
#print axioms so3_ricciTrace_basis_independent_witness
#print axioms so3_ricciTrace_permBasis_e0_e0
#print axioms prodData_so3_scalarCurvature
#print axioms prodData_so3_ricciForm

/-! ## The D2 bridges and the Perelman ledger target -/

#print axioms ricci_add_d2
#print axioms ricci_smul_d2
#print axioms scalarCurvature_add_d2
#print axioms scalarCurvature_smul_d2
#print axioms ricciTrace_eq_d2_ricciSum
#print axioms scalarCurvature_eq_d2_sum_basis
#print axioms BlockerPerelmanScalarRealization
#print axioms BlockerPerelmanScalarRealization_ne_nil
#print axioms PerelmanScalarCurvatureRealization

end RicciScalar
end D7
end Poincare
