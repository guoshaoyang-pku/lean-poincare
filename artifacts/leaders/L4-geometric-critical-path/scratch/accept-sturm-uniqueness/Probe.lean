/-
Reviewer probe for L4/GeodesicComparison/SturmUniqueness.lean
Read-only w.r.t. the artifact: imports it and prints checks/axioms.
-/
import Poincare.L4.GeodesicComparison.TwoSidedSturm
import Poincare.L4.GeodesicComparison.SturmUniqueness

open Poincare.L4.GeodesicComparison

-- Elaborated types (full binder structure)
#check @sturmModel_pos_at_right
#check @sturmModel_eq_zero_at_pi_sqrt
#check @wronskian_sturmModel_eq_zero_of_pos
#check @exists_smul_sturmModel_of_wronskian_eq_zero
#check @wronskian_sturmModel_eq_zero_of_curvature_eq
#check @exists_smul_sturmModel_of_curvature_eq
#check @eq_zero_of_wronskian_sturmModel_eq_zero
#check @no_first_zero_of_curvature_le_of_lt_pi
#check @no_first_zero_before_pi_sqrt_of_curvature_le
#check @nonvanishing_near_left_of_deriv_ne
#check @no_zero_of_curvature_le_of_deriv_ne
#check @strict_span_necessary

-- Axiom cones
#print axioms sturmModel_pos_at_right
#print axioms sturmModel_eq_zero_at_pi_sqrt
#print axioms wronskian_sturmModel_eq_zero_of_pos
#print axioms exists_smul_sturmModel_of_wronskian_eq_zero
#print axioms wronskian_sturmModel_eq_zero_of_curvature_eq
#print axioms exists_smul_sturmModel_of_curvature_eq
#print axioms eq_zero_of_wronskian_sturmModel_eq_zero
#print axioms no_first_zero_of_curvature_le_of_lt_pi
#print axioms no_first_zero_before_pi_sqrt_of_curvature_le
#print axioms nonvanishing_near_left_of_deriv_ne
#print axioms no_zero_of_curvature_le_of_deriv_ne
#print axioms strict_span_necessary

-- Revised TwoSidedSturm witness (additional scope)
#check @Poincare.L4.GeodesicComparison.sturmModel_first_zero_witness
#print axioms Poincare.L4.GeodesicComparison.sturmModel_first_zero_witness
#print axioms Poincare.L4.GeodesicComparison.eq_curvature_of_first_jacobi_zero_before_pi_sqrt
#print axioms Poincare.L4.GeodesicComparison.first_jacobi_zero_le_of_curvature_deficit
#print axioms Poincare.L4.GeodesicComparison.const_curvature_deficit_no_first_zero
#print axioms Poincare.L4.GeodesicComparison.sin_no_first_zero_before_pi_div_sqrt_two
#print axioms Poincare.L4.GeodesicComparison.jacobiSolutionOn_mono_Icc
#print axioms Poincare.L4.GeodesicComparison.eq_curvature_of_first_jacobi_zero_of_curvature_le
