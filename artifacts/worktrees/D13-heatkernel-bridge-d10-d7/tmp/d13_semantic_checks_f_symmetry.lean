import Poincare.D13.HeatKernelBridge.LaplacianSymmetryRefutation

open Poincare.D13.HeatKernelBridge
open MeasureTheory Filter
open scoped Topology

-- The naive formal self-adjointness axiom is false for the honest flat Laplacian (checked).
#check @flatLineSpacetime
#check @hasDerivAt_tanh_real
#check @tendsto_tanh_atTop_real
#check @tendsto_tanh_atBot_real
#check @hasDerivAt_log_cosh
#check @contDiff_log_cosh
#check @laplacian_log_cosh
#check @integrable_one_sub_tanh_sq
#check @integral_one_sub_tanh_sq
#check @not_forall_laplacian_symmetric_flatLine
#print axioms not_forall_laplacian_symmetric_flatLine
#print axioms integral_one_sub_tanh_sq
#print axioms laplacian_log_cosh
