import Poincare.D7.ShortTime
import Poincare.D7.ShortTime.Example

/-!
# Poincare.D7.ShortTime.Audit

Kernel axiom audit for the `D7-hamilton-short-time` layer. Each `#print axioms` line below
reports the axiom dependencies of one principal declaration. The expected cones are
`{}` (definitions, blockers, concrete matrix computations) and
`{propext, Classical.choice, Quot.sound}` (theorems using classical logic / mathlib analysis).
Any occurrence of `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, or a project axiom is a
failure of the task's no-`sorry`/no-`axiom`/no-`native_decide` requirement.
-/

open scoped Matrix
open Poincare.D7.ShortTime

/-! ## Basic.lean -/

#print axioms Poincare.D7.ShortTime.RicciFlowData
#print axioms Poincare.D7.ShortTime.RicciFlowData.ricciVectorField
#print axioms Poincare.D7.ShortTime.RicciFlowData.ricciVectorField_apply
#print axioms Poincare.D7.ShortTime.RicciFlowData.ricci_flow_eq_vectorField
#print axioms Poincare.D7.ShortTime.deTurckRHS
#print axioms Poincare.D7.ShortTime.deTurckRHS_def
#print axioms Poincare.D7.ShortTime.deTurckRHS_eq_ricciVectorField_sub
#print axioms Poincare.D7.ShortTime.DeTurckCertificate
#print axioms Poincare.D7.ShortTime.DeTurckCertificate.isUnit_det_gauge
#print axioms Poincare.D7.ShortTime.DeTurckCertificate.deturck_flow_eq
#print axioms Poincare.D7.ShortTime.DeTurckCertificate.ricci_congruence_gauge
#print axioms Poincare.D7.ShortTime.DeTurckCertificate.pullback
#print axioms Poincare.D7.ShortTime.DeTurckCertificate.pullback_apply
#print axioms Poincare.D7.ShortTime.DeTurckCertificate.pullback_symm
#print axioms Poincare.D7.ShortTime.DeTurckCertificate.pullback_zero

/-! ## ODE.lean -/

#print axioms Poincare.D7.ShortTime.LipschitzVectorField
#print axioms Poincare.D7.ShortTime.LipschitzVectorField.lipschitzOnWith
#print axioms Poincare.D7.ShortTime.LipschitzVectorField.solution_unique
#print axioms Poincare.D7.ShortTime.LipschitzVectorField.solution_eq
#print axioms Poincare.D7.ShortTime.RicciLipschitzInterface
#print axioms Poincare.D7.ShortTime.RicciLipschitzInterface.toLipschitzVectorField
#print axioms Poincare.D7.ShortTime.RicciLipschitzInterface.solution_unique
#print axioms Poincare.D7.ShortTime.RicciLipschitzInterface.solution_eq

/-! ## MatrixDeriv.lean -/

#print axioms Poincare.D7.ShortTime.hasDerivAt_transpose
#print axioms Poincare.D7.ShortTime.hasDerivAt_mul
#print axioms Poincare.D7.ShortTime.hasDerivAt_mul_three
#print axioms Poincare.D7.ShortTime.hasDerivAt_const_matrix
#print axioms Poincare.D7.ShortTime.hasDerivAt_add_matrix
#print axioms Poincare.D7.ShortTime.hasDerivAt_sub_matrix
#print axioms Poincare.D7.ShortTime.hasDerivAt_neg_matrix
#print axioms Poincare.D7.ShortTime.hasDerivAt_const_smul_matrix
#print axioms Poincare.D7.ShortTime.hasDerivAt_smul_const_matrix
#print axioms Poincare.D7.ShortTime.hasDerivAt_id_smul_matrix

/-! ## Gauge.lean -/

#print axioms Poincare.D7.ShortTime.gaugeAction
#print axioms Poincare.D7.ShortTime.gaugeAction_apply
#print axioms Poincare.D7.ShortTime.gaugeAction_transpose
#print axioms Poincare.D7.ShortTime.gaugeAction_inv
#print axioms Poincare.D7.ShortTime.gauge_pullback_algebra
#print axioms Poincare.D7.ShortTime.deTurckRHS_add_gauge
#print axioms Poincare.D7.ShortTime.gauge_pullback_deTurckRHS
#print axioms Poincare.D7.ShortTime.gaugeInv_ricci_congruence

/-! ## Equivalence.lean -/

#print axioms Poincare.D7.ShortTime.DeTurckCertificate.gaugeInvDeriv_eq
#print axioms Poincare.D7.ShortTime.DeTurckCertificate.gauge_conj_inv
#print axioms Poincare.D7.ShortTime.DeTurckCertificate.gaugeInv_ricci_congruence'
#print axioms Poincare.D7.ShortTime.DeTurckCertificate.pullback_hasDerivAt_at
#print axioms Poincare.D7.ShortTime.DeTurckCertificate.pullback_hasDerivAt_of
#print axioms Poincare.D7.ShortTime.DeTurckCertificate.pullback_hasDerivAt_of_Ioo
#print axioms Poincare.D7.ShortTime.DeTurckCertificate.pullback_hasDerivAt
#print axioms Poincare.D7.ShortTime.DeTurckCertificate.pullback_solves_ricciFlow
#print axioms Poincare.D7.ShortTime.DeTurckCertificate.pullback_eq_metric
#print axioms Poincare.D7.ShortTime.DeTurckCertificate.gaugeInv_hasDerivAt
#print axioms Poincare.D7.ShortTime.DeTurckCertificate.ricciFlow_gauge_recover

/-! ## Statements.lean -/

#print axioms Poincare.D7.ShortTime.DeTurckParabolicProblem
#print axioms Poincare.D7.ShortTime.DeTurckShortTimeExistence
#print axioms Poincare.D7.ShortTime.DeTurckToRicciConversion
#print axioms Poincare.D7.ShortTime.matrixProblem
#print axioms Poincare.D7.ShortTime.matrixProblem_deTurckToRicciConversion
#print axioms Poincare.D7.ShortTime.MissingDependency
#print axioms Poincare.D7.ShortTime.BlockerDeTurckShortTime
#print axioms Poincare.D7.ShortTime.BlockerDeTurckConversion
#print axioms Poincare.D7.ShortTime.BlockerDeTurckShortTime_ne_nil
#print axioms Poincare.D7.ShortTime.BlockerDeTurckConversion_ne_nil
#print axioms Poincare.D7.ShortTime.quasilinearParabolicDependencies
#print axioms Poincare.D7.ShortTime.quasilinearParabolicDependencies_length
#print axioms Poincare.D7.ShortTime.quasilinearParabolicDependencies_ne_nil
#print axioms Poincare.D7.ShortTime.quasilinearParabolicDependencies_all_named

/-! ## Example.lean -/

#print axioms Poincare.D7.ShortTime.einsteinRicci
#print axioms Poincare.D7.ShortTime.einsteinRicci_symm
#print axioms Poincare.D7.ShortTime.einsteinRicci_congruence
#print axioms Poincare.D7.ShortTime.hasDerivAt_exp_smul
#print axioms Poincare.D7.ShortTime.einsteinRicciFlowData
#print axioms Poincare.D7.ShortTime.flatRicciFlowData
#print axioms Poincare.D7.ShortTime.trivialDeTurckCertificate
#print axioms Poincare.D7.ShortTime.nilpotent_gauge_correction
#print axioms Poincare.D7.ShortTime.nilpotent_deTurckRHS
#print axioms Poincare.D7.ShortTime.nilpotentDeTurckCertificate
#print axioms Poincare.D7.ShortTime.nilpotentB
#print axioms Poincare.D7.ShortTime.nilpotentH
#print axioms Poincare.D7.ShortTime.nilpotentH_transpose
#print axioms Poincare.D7.ShortTime.nilpotentB_sq
#print axioms Poincare.D7.ShortTime.nilpotentB_H_B
#print axioms Poincare.D7.ShortTime.nilpotentB_H_add_ne_zero
#print axioms Poincare.D7.ShortTime.concreteDeTurckCertificate
#print axioms Poincare.D7.ShortTime.concreteDeTurck_metric_deriv_ne_zero
#print axioms Poincare.D7.ShortTime.trivial_pullback_eq
