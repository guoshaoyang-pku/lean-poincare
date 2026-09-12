import Poincare.Longrun.CurvatureODE

/-!
# Audit/CurvatureODEAudit

Axiom audit for the `D2-ricci-ode-cluster`. Every principal declaration of
`Poincare.Longrun.CurvatureODE` is printed with `#print axioms`. The expected allowed axioms
are exactly `propext`, `Classical.choice`, `Quot.sound`; `sorryAx` must not appear.

Run with:

```text
lake env lean Audit/CurvatureODEAudit.lean
```
-/

namespace Poincare
namespace Longrun
namespace CurvatureODE

/-! ## State -/

#print axioms diagonalEndomorphism_basis
#print axioms trace_diagonalEndomorphism
#print axioms form_diagonalEndomorphism
#print axioms diagonalEndomorphism_selfAdjoint
#print axioms scalarOfState_eq_trace
#print axioms scalarOfState_stateOfCurvature
#print axioms stateOfCurvature_zero

/-! ## Evolution -/

#print axioms ReactionField.eval_nonneg
#print axioms ReactionField.hamilton_eval
#print axioms ReactionField.hamilton_eval_zero
#print axioms zero_evolutionRelation
#print axioms zero_discreteEvolution

/-! ## Scalar ODE lemmas -/

#print axioms le_left_of_hasDerivWithinAt_nonpos
#print axioms le_zero_of_hasDerivWithinAt_le_mul
#print axioms ge_zero_of_hasDerivWithinAt_mul_le

/-! ## Invariant region -/

#print axioms component_monotone
#print axioms nonneg_component
#print axioms nonneg_orthant_invariant
#print axioms component_monotone_discrete
#print axioms nonneg_orthant_invariant_discrete
#print axioms zero_orthant_invariant

/-! ## Monotonicity -/

#print axioms hasDerivWithinAt_scalarFunctional
#print axioms scalarFunctional_monotone
#print axioms scalarOfState_monotone
#print axioms scalarFunctional_monotone_discrete
#print axioms scalarOfState_monotone_discrete
#print axioms zero_scalar_monotone
#print axioms ReactionField.hamilton_eval_pos

/-! ## Bridge (explicit missing interface) -/

#print axioms ManifoldCurvatureRealization
#print axioms MetricFamilySolvesRicciFlow
#print axioms MetricCurvatureShadow
#print axioms TensorRicciFlowODERealization
#print axioms TensorRicciFlowODEBridge
#print axioms evolutionRelation_of_bridge
#print axioms ricciDiagonal_nonneg_of_bridge
#print axioms scalarCurvature_monotone_of_bridge
#print axioms bridge_state_eq_ricciDiagonal

end CurvatureODE
end Longrun
end Poincare
