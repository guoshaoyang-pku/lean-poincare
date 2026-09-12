import Poincare.L4.GeodesicComparison.ConstantCurvatureRauch
import Poincare.L4.ManifoldIBP.WeightedSelfAdjointness

open Poincare.L4.GeodesicComparison Poincare.L4.ManifoldIBP
open Poincare.D12.ComparisonGeodesics

#print axioms Poincare.L4.GeodesicComparison.jacobiSol_pos_of_nonneg
#print axioms Poincare.L4.GeodesicComparison.jacobiSol_jacobiSolutionOn
#print axioms Poincare.L4.GeodesicComparison.jacobiSol_second_deriv_bound
#print axioms Poincare.L4.GeodesicComparison.rauch_upper_of_jacobi_constCurv
#print axioms Poincare.L4.GeodesicComparison.rauch_constCurv_witness
#print axioms Poincare.L4.ManifoldIBP.metricInnerInverse_comm
#print axioms Poincare.L4.ManifoldIBP.gradInnerInverse_comm
#print axioms Poincare.L4.ManifoldIBP.halfSpaceAtlas_weightedLaplacian_selfAdjoint

#check @Poincare.L4.GeodesicComparison.jacobiSol_pos_of_nonneg
#check @Poincare.L4.GeodesicComparison.jacobiSol_jacobiSolutionOn
#check @Poincare.L4.GeodesicComparison.jacobiSol_second_deriv_bound
#check @Poincare.L4.GeodesicComparison.rauch_upper_of_jacobi_constCurv
#check @Poincare.L4.GeodesicComparison.rauch_constCurv_witness
#check @Poincare.L4.ManifoldIBP.metricInnerInverse_comm
#check @Poincare.L4.ManifoldIBP.gradInnerInverse_comm
#check @Poincare.L4.ManifoldIBP.halfSpaceAtlas_weightedLaplacian_selfAdjoint
