-- D13 twelfth invocation: semantic transcript for the Dirichlet gap, the Poincaré inequality and
-- the long-time asymptotics (convergence of the pinned finite heat kernel to equilibrium).
import Poincare.D13.HeatKernelBridge.FiniteErgodicity
import Poincare.D7.HeatKernel.ErgodicityStatus

open MeasureTheory Filter
open scoped Topology Matrix

-- the mean-zero condition, the Dirichlet form and its positivity
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.meanZero
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.meanZero_sub_const
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichlet_inner_nonneg
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletForm
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletForm_nonneg
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletForm_eq_neg_quadraticForm
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletForm_eq_zero_iff

-- the variance identity and the quantitative Poincaré inequality
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.sum_sq_sub_eq
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.sum_sq_sub_eq_of_meanZero
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletForm_ge_of_weight
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.minWeight
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.minWeight_le
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.minWeight_pos
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletGap
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletGap_pos
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.poincare_inequality

-- mean conservation and the Gronwall energy decay
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.sum_laplacian_eq_zero
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.hasDerivAt_mean
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.energy_decay_of_meanZero

-- the equilibrium function and the kernel's convergence to it
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.equilibrium
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.one_sub_inv_card_nonneg
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_column_sum
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_shift_meanZero
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.laplacian_sub_const
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_shift_hasDerivAt
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_tendsto_entry
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.energy_dirac_sub_equilibrium
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_shift_tendsto_energy
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_shift_energy_decay
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_energy_decay
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_energy_decay_gap
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_tendsto_equilibrium_energy
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_pointwise_decay

-- sharpness on the complete graph
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_minWeight
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_dirichletGap
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_dirichletForm_eq
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_poincare_attained
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphKernelForm
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.sum_mul_one_apply
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_laplacian_kernelForm
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphKernelForm_hasDerivAt
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphKernelForm_tendsto
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_finiteHeatKernel
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_energy_decay_sharp
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_energy_decay_attained

-- the D7-level consumer
#check @Poincare.D7.HeatKernel.finite_pinned_dirichlet_gap_pos
#check @Poincare.D7.HeatKernel.finite_pinned_poincare
#check @Poincare.D7.HeatKernel.finite_pinned_kernel_energy_decay
#check @Poincare.D7.HeatKernel.finite_pinned_kernel_tendsto_equilibrium
#check @Poincare.D7.HeatKernel.finite_pinned_kernel_pointwise_convergence
#check @Poincare.D7.HeatKernel.finite_pinned_equilibrium_invariant
#check @Poincare.D7.HeatKernel.finite_pinned_ergodicity_summary
#check @Poincare.D7.HeatKernel.finite_pinned_complete_graph_sharp
#check @Poincare.D7.HeatKernel.finite_pinned_complete_graph_gap
