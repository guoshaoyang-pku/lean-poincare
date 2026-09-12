import Poincare.D7.LeviCivita.Smoke

/-!
# Poincare.D7.LeviCivita.Audit

**D7 Levi-Civita smoothness layer, part 7: kernel axiom audit.**

`#print axioms` for every theorem proved in the new layer. Every line must print a subset of
`{propext, Classical.choice, Quot.sound}`; in particular no project `axiom`, `sorryAx`,
`native_decide`, or `proof_wanted` may appear. The output of this file is captured as the axiom
audit log of the result card.

The state-only `def`s (`LeviCivitaSmoothnessStatement`, `SmoothLeviCivitaExistenceStatement`,
`CovariantDerivativeCurvatureMatchesD7`, the blocker strings and dependency lists) are
definitions of `Prop`/`String`/`List String` with no proof; `#print axioms` on them lists only the
axioms of their bodies (none for the strings, and the ambient logical axioms for the `Prop`s).
-/

open Poincare.Longrun.Geometry

/-! ## Basic: affine combinations and the mean connection -/

#print axioms Poincare.D7.LeviCivita.affineConnection_apply
#print axioms Poincare.D7.LeviCivita.isMetricCompatible_affine
#print axioms Poincare.D7.LeviCivita.isTorsionFree_affine
#print axioms Poincare.D7.LeviCivita.isLeviCivita_affine
#print axioms Poincare.D7.LeviCivita.affineConnection_one
#print axioms Poincare.D7.LeviCivita.affineConnection_zero
#print axioms Poincare.D7.LeviCivita.affineConnection_self
#print axioms Poincare.D7.LeviCivita.meanConnection_apply
#print axioms Poincare.D7.LeviCivita.isMetricCompatible_mean
#print axioms Poincare.D7.LeviCivita.isTorsionFree_mean
#print axioms Poincare.D7.LeviCivita.isLeviCivita_mean
#print axioms Poincare.D7.LeviCivita.meanConnection_self
#print axioms Poincare.D7.LeviCivita.meanConnection_comm
#print axioms Poincare.D7.LeviCivita.meanConnection_eq_left
#print axioms Poincare.D7.LeviCivita.meanConnection_eq_right

/-! ## Basic: the difference tensor -/

#print axioms Poincare.D7.LeviCivita.differenceTensor_apply
#print axioms Poincare.D7.LeviCivita.differenceTensor_add_left
#print axioms Poincare.D7.LeviCivita.differenceTensor_add_right
#print axioms Poincare.D7.LeviCivita.differenceTensor_self
#print axioms Poincare.D7.LeviCivita.differenceTensor_antisymm
#print axioms Poincare.D7.LeviCivita.differenceTensor_symm
#print axioms Poincare.D7.LeviCivita.differenceTensor_metric_antisymm
#print axioms Poincare.D7.LeviCivita.differenceTensor_eq_zero_of_isLeviCivita
#print axioms Poincare.D7.LeviCivita.eq_sub_differenceTensor

/-! ## The D7 curvature data lifting -/

#print axioms Poincare.D7.Curvature.RiemannCurvatureData.meanData_conn
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.meanData_metric
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.meanData_lie
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.meanData_self
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.differenceTensor_symm

/-! ## Connection coefficients -/

#print axioms Poincare.D7.LeviCivita.sum_connectionCoefficient_smul
#print axioms Poincare.D7.LeviCivita.form_nabla_basis
#print axioms Poincare.D7.LeviCivita.isMetricCompatible_coefficient_relation
#print axioms Poincare.D7.LeviCivita.isTorsionFree_coefficient_relation
#print axioms Poincare.D7.LeviCivita.connectionCoefficient_affine
#print axioms Poincare.D7.LeviCivita.connectionCoefficient_mean
#print axioms Poincare.D7.LeviCivita.connectionCoefficient_difference
#print axioms Poincare.D7.LeviCivita.isMetricCompatible_coefficient_relation_affine
#print axioms Poincare.D7.LeviCivita.isTorsionFree_coefficient_relation_affine

/-! ## The smooth coefficient interface -/

#print axioms Poincare.D7.LeviCivita.contMDiff_const_smul_field
#print axioms Poincare.D7.LeviCivita.contMDiff_coefficientField
#print axioms Poincare.D7.LeviCivita.contMDiff_coefficientField_comp_chart
#print axioms Poincare.D7.LeviCivita.affineField_apply
#print axioms Poincare.D7.LeviCivita.contMDiff_affineField
#print axioms Poincare.D7.LeviCivita.coefficientField_affineField
#print axioms Poincare.D7.LeviCivita.SmoothCoefficientSystem.affineCombination
#print axioms Poincare.D7.LeviCivita.SmoothCoefficientSystem.mean
#print axioms Poincare.D7.LeviCivita.SmoothCoefficientSystem.pullback
#print axioms Poincare.D7.LeviCivita.SmoothCoefficientSystem.const
#print axioms Poincare.D7.LeviCivita.SmoothCoefficientSystem.const_coeff
#print axioms Poincare.D7.LeviCivita.SmoothCoefficientSystem.affineCombination_coeff
#print axioms Poincare.D7.LeviCivita.SmoothCoefficientSystem.mean_coeff

/-! ## The Koszul chart-smoothness theorem -/

#print axioms Poincare.D7.LeviCivita.contDiff_fderiv_coefficient
#print axioms Poincare.D7.LeviCivita.contDiff_christoffelSymbol
#print axioms Poincare.D7.LeviCivita.contDiff_euclidean_christoffel

/-! ## The state-only Props and their blockers -/

#print axioms Poincare.D7.LeviCivita.BlockerLeviCivitaSmoothness_ne_nil
#print axioms Poincare.D7.LeviCivita.BlockerCovariantDerivativeCurvature_ne_nil
#print axioms Poincare.D7.LeviCivita.BlockerSecondBianchi_ne_nil
#print axioms Poincare.D7.LeviCivita.LeviCivitaSmoothnessMissingDependencies_ne_nil
#print axioms Poincare.D7.LeviCivita.CovariantDerivativeCurvatureMissingDependencies_ne_nil
#print axioms Poincare.D7.LeviCivita.leviCivitaConnection_isLeviCivitaConnection
#print axioms Poincare.D7.LeviCivita.smoothLeviCivitaExistence_of_smoothness
#print axioms Poincare.D7.LeviCivita.leviCivitaSmoothness_iff_contMDiff
#print axioms Poincare.D7.LeviCivita.covariantDerivativeCurvatureMatchesD7_of_data
#print axioms Poincare.D7.LeviCivita.covariantDerivativeCurvatureStatement_of_matchesD7
