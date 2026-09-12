import Poincare.L4.GeodesicComparison.ConstantCurvatureRauchLower
import Poincare.L4.GeodesicComparison.ConjugatePointBound

open Poincare.L4.GeodesicComparison

-- File A
#check @Poincare.L4.GeodesicComparison.jacobiSol_pos_of_nonpos
#check @Poincare.L4.GeodesicComparison.jacobiSol_monotoneOn_of_nonpos
#check @Poincare.L4.GeodesicComparison.jacobiSol_second_deriv_bound_nonpos
#check @Poincare.L4.GeodesicComparison.rauch_lower_of_jacobi_constCurv
#check @Poincare.L4.GeodesicComparison.constCurvModel_le_jacobi
#check @Poincare.L4.GeodesicComparison.sinh_quarter_le_three
#check @Poincare.L4.GeodesicComparison.sinh_one_le_three
#check @Poincare.L4.GeodesicComparison.rauch_lower_constCurv_witness
#check @Poincare.L4.GeodesicComparison.constCurvModel_le_jacobi_witness
-- File B
#check @Poincare.L4.GeodesicComparison.JacobiSolutionOn.mono
#check @Poincare.L4.GeodesicComparison.conjugate_point_bound
#check @Poincare.L4.GeodesicComparison.conjugate_point_bound_witness
-- File C
#check @Poincare.L4.GeodesicComparison.jacobi_le_constCurvModel
#check @Poincare.L4.GeodesicComparison.jacobiSolTwo_le_model_witness

-- supporting statements
#check @Poincare.L4.GeodesicComparison.jacobiSol_second_deriv_bound
#check @Poincare.L4.GeodesicComparison.rauch_upper_of_jacobi_constCurv
#check @Poincare.D12.ComparisonGeodesics.riccati_ge_of_singular_normalization
#check @Poincare.D10.jacobiSolSphere_firstZero
#check @Poincare.D10.jacobiSol_of_pos
#check @Poincare.D10.jacobiSol_of_neg
#check @Poincare.D10.jacobiSolHyperbolic
#check @Poincare.D10.jacobiSol_zero
#check @Poincare.D10.jacobiDeriv_zero
#check @Poincare.D10.jacobiDeriv_of_neg
