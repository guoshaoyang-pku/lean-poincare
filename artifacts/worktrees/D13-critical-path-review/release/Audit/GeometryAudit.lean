import Poincare.Longrun.Geometry

/-!
# Audit: `#print axioms` for the D2-geometry-foundation principal declarations

This file is not part of the `Poincare` library glob (`Poincare.+`); it is the audit driver
for the task. Every principal declaration of the cluster is checked to depend only on Lean's
three standard axioms `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx` and no
project axiom may appear.
-/

#print axioms Poincare.Longrun.Geometry.MetricData
#print axioms Poincare.Longrun.Geometry.MetricData.nondegenerate
#print axioms Poincare.Longrun.Geometry.MetricData.form_raiseIndex
#print axioms Poincare.Longrun.Geometry.MetricData.toScalarContractionData
#print axioms Poincare.Longrun.Geometry.MetricData.scalarCurvature_eq_sum_basis

#print axioms Poincare.Longrun.Geometry.LieBracketData
#print axioms Poincare.Longrun.Geometry.LieBracketData.jacobi_reverse
#print axioms Poincare.Longrun.Geometry.LieBracketData.jacobi_corollary
#print axioms Poincare.Longrun.Geometry.LieBracketData.bracket_bracket_comm

#print axioms Poincare.Longrun.Geometry.AbstractConnection
#print axioms Poincare.Longrun.Geometry.AbstractConnection.nabla_swap
#print axioms Poincare.Longrun.Geometry.AbstractConnection.curvature
#print axioms Poincare.Longrun.Geometry.AbstractConnection.curvature_skew
#print axioms Poincare.Longrun.Geometry.AbstractConnection.curvature_bianchi
#print axioms Poincare.Longrun.Geometry.AbstractConnection.toCurvatureOperator
#print axioms Poincare.Longrun.Geometry.AbstractConnection.zero_toCurvatureOperator

#print axioms Poincare.Longrun.Geometry.meanConnection
#print axioms Poincare.Longrun.Geometry.mean_curvature_apply
#print axioms Poincare.Longrun.Geometry.mean_endoRicci
#print axioms Poincare.Longrun.Geometry.mean_ricci_comm

#print axioms Poincare.CurvatureAlgebra.CurvatureOperator.endoRicci_add
#print axioms Poincare.CurvatureAlgebra.CurvatureOperator.endoRicci_smul
#print axioms Poincare.CurvatureAlgebra.CurvatureOperator.ricci_add
#print axioms Poincare.CurvatureAlgebra.CurvatureOperator.ricci_smul
#print axioms Poincare.CurvatureAlgebra.CurvatureOperator.scalarCurvature_add
#print axioms Poincare.CurvatureAlgebra.CurvatureOperator.scalarCurvature_smul

#print axioms Poincare.Longrun.Geometry.curvatureForm
#print axioms Poincare.Longrun.Geometry.curvatureForm_first_pair_skew
#print axioms Poincare.Longrun.Geometry.curvatureForm_first_bianchi

#print axioms Poincare.Longrun.Geometry.IsTorsionFree
#print axioms Poincare.Longrun.Geometry.IsMetricCompatible
#print axioms Poincare.Longrun.Geometry.IsLeviCivita
#print axioms Poincare.Longrun.Geometry.leviCivita_nabla_unique
#print axioms Poincare.Longrun.Geometry.meanConnection_isMetricCompatible_iff
#print axioms Poincare.Longrun.Geometry.LeviCivitaData
#print axioms Poincare.Longrun.Geometry.LeviCivitaData.toCurvatureOperator
#print axioms Poincare.Longrun.Geometry.leviCivitaExistence_iff_nonempty
#print axioms Poincare.Longrun.Geometry.LeviCivitaExistenceStatement
#print axioms Poincare.Longrun.Geometry.CovariantDerivativeCurvatureStatement
