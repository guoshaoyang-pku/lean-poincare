import Poincare.D7.ShortTime

/-!
# Poincare.D7.ShortTime.Probe

Compilable API probe for the `D7-hamilton-short-time` layer. Every `#check` below must succeed
(the file is compiled with `lake env lean` and must exit 0); this is a smoke test that the
public names and types are exactly as documented in the umbrella module.
-/

open scoped Matrix
open Poincare.D7.ShortTime

/-! ## The model data -/

#check @RicciFlowData
#check @RicciFlowData.ricci
#check @RicciFlowData.ricci_symm
#check @RicciFlowData.ricci_congruence
#check @RicciFlowData.metric
#check @RicciFlowData.metric_symm
#check @RicciFlowData.ricci_flow
#check @RicciFlowData.ricciVectorField
#check @RicciFlowData.ricci_flow_eq_vectorField
#check @deTurckRHS
#check @deTurckRHS_def
#check @deTurckRHS_eq_ricciVectorField_sub

/-! ## The DeTurck certificate -/

#check @DeTurckCertificate
#check @DeTurckCertificate.gauge
#check @DeTurckCertificate.gaugeInv
#check @DeTurckCertificate.gaugeField
#check @DeTurckCertificate.gauge_ode
#check @DeTurckCertificate.gaugeInvDeriv
#check @DeTurckCertificate.gaugeInv_ode
#check @DeTurckCertificate.gauge_zero
#check @DeTurckCertificate.gaugeInv_zero
#check @DeTurckCertificate.inv_mul
#check @DeTurckCertificate.mul_inv
#check @DeTurckCertificate.deturckMetric
#check @DeTurckCertificate.deturck_symm
#check @DeTurckCertificate.deturck_flow
#check @DeTurckCertificate.deturck_zero
#check @DeTurckCertificate.isUnit_det_gauge
#check @DeTurckCertificate.pullback
#check @DeTurckCertificate.pullback_symm
#check @DeTurckCertificate.pullback_zero

/-! ## The Lipschitz ODE interface -/

#check @LipschitzVectorField
#check @LipschitzVectorField.solution_unique
#check @LipschitzVectorField.solution_eq
#check @RicciLipschitzInterface
#check @RicciLipschitzInterface.toLipschitzVectorField
#check @RicciLipschitzInterface.solution_unique
#check @RicciLipschitzInterface.solution_eq

/-! ## Matrix calculus -/

#check @hasDerivAt_transpose
#check @hasDerivAt_mul
#check @hasDerivAt_mul_three
#check @hasDerivAt_const_matrix
#check @hasDerivAt_add_matrix
#check @hasDerivAt_sub_matrix
#check @hasDerivAt_neg_matrix
#check @hasDerivAt_const_smul_matrix
#check @hasDerivAt_smul_const_matrix
#check @hasDerivAt_id_smul_matrix

/-! ## Gauge algebra -/

#check @gaugeAction
#check @gaugeAction_transpose
#check @gaugeAction_inv
#check @gauge_pullback_algebra
#check @deTurckRHS_add_gauge
#check @gauge_pullback_deTurckRHS
#check @gaugeInv_ricci_congruence

/-! ## The algebraic equivalence -/

#check @DeTurckCertificate.gaugeInvDeriv_eq
#check @DeTurckCertificate.gauge_conj_inv
#check @DeTurckCertificate.pullback_hasDerivAt_at
#check @DeTurckCertificate.pullback_hasDerivAt_of
#check @DeTurckCertificate.pullback_hasDerivAt_of_Ioo
#check @DeTurckCertificate.pullback_hasDerivAt
#check @DeTurckCertificate.pullback_solves_ricciFlow
#check @DeTurckCertificate.pullback_eq_metric
#check @DeTurckCertificate.gaugeInv_hasDerivAt
#check @DeTurckCertificate.ricciFlow_gauge_recover

/-! ## State-only statements and the missing-dependency ledger -/

#check @DeTurckParabolicProblem
#check @DeTurckShortTimeExistence
#check @DeTurckToRicciConversion
#check @matrixProblem
#check @matrixProblem_deTurckToRicciConversion
#check @MissingDependency
#check @BlockerDeTurckShortTime
#check @BlockerDeTurckConversion
#check @BlockerDeTurckShortTime_ne_nil
#check @BlockerDeTurckConversion_ne_nil
#check @quasilinearParabolicDependencies
#check @quasilinearParabolicDependencies_length
#check @quasilinearParabolicDependencies_ne_nil
#check @quasilinearParabolicDependencies_all_named

/-! ## Non-vacuity witnesses -/

#check @einsteinRicci
#check @einsteinRicci_symm
#check @einsteinRicci_congruence
#check @hasDerivAt_exp_smul
#check @einsteinRicciFlowData
#check @flatRicciFlowData
#check @trivialDeTurckCertificate
#check @nilpotent_gauge_correction
#check @nilpotent_deTurckRHS
#check @nilpotentDeTurckCertificate
#check @nilpotentB
#check @nilpotentH
#check @nilpotentH_transpose
#check @nilpotentB_sq
#check @nilpotentB_H_B
#check @nilpotentB_H_add_ne_zero
#check @concreteDeTurckCertificate
#check @concreteDeTurck_metric_deriv_ne_zero
#check @trivial_pullback_eq
