-- D13 tenth invocation: semantic transcript for the finite pinned conjugate uniqueness theorem.
import Poincare.D13.HeatKernelBridge.FiniteConjugateUniqueness
import Poincare.D7.ConjugateHeat.UniquenessStatus

open MeasureTheory Filter
open scoped Topology

-- the Grönwall-weighted energy and backward uniqueness
#check @Poincare.D13.HeatKernelBridge.tendsto_const_sub_nhdsGT
#check @Poincare.D13.HeatKernelBridge.exp_energy_antitoneOn
#check @Poincare.D13.HeatKernelBridge.eq_zero_of_backward_hasDerivAt_of_tendsto
#check @Poincare.D13.HeatKernelBridge.eq_of_backward_hasDerivAt_of_tendsto

-- terminal Dirac data and conjugate uniqueness at the interface level
#check @Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDE.tendsto_singleFun
#check @Poincare.D13.HeatKernelBridge.eq_of_conjugatePDE_of_tendsto
#check @Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDE.eq_of_same

-- the finite pinned conjugate model
#check @Poincare.D13.HeatKernelBridge.finiteConjugateSpacetime
#check @Poincare.D13.HeatKernelBridge.finiteConjugateKernel
#check @Poincare.D13.HeatKernelBridge.finiteConjugateKernel_pos
#check @Poincare.D13.HeatKernelBridge.finiteConjugateKernel_hasDerivAt
#check @Poincare.D13.HeatKernelBridge.finiteConjugateKernel_tendsto_singleFun
#check @Poincare.D13.HeatKernelBridge.finiteConjugateKernel_anticausal
#check @Poincare.D13.HeatKernelBridge.finite_isConjugateHeatKernelPDE
#check @Poincare.D13.HeatKernelBridge.eq_finiteConjugateKernel_of_isConjugateHeatKernelPDE
#check @Poincare.D13.HeatKernelBridge.exists_unique_finiteConjugateKernel

-- D7-level consumption
#check @Poincare.D7.ConjugateHeat.finite_conjugate_interface_unique
#check @Poincare.D7.ConjugateHeat.finite_conjugate_canonical_unique
#check @Poincare.D7.ConjugateHeat.finite_conjugate_exists_unique
#check @Poincare.D7.ConjugateHeat.finite_conjugate_wellposed_summary

-- axiom cones
#print axioms Poincare.D13.HeatKernelBridge.exists_unique_finiteConjugateKernel
#print axioms Poincare.D13.HeatKernelBridge.exp_energy_antitoneOn
#print axioms Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDE.eq_of_same
#print axioms Poincare.D13.HeatKernelBridge.finite_isConjugateHeatKernelPDE
#print axioms Poincare.D7.ConjugateHeat.finite_conjugate_exists_unique
#print axioms Poincare.D7.ConjugateHeat.finite_conjugate_wellposed_summary

-- non-vacuity: the canonical conjugate kernel inhabits the repaired predicate
example (G : Poincare.D13.HeatKernelBridge.FiniteHeatOperator (Fin 2)) (t₀ : ℝ) :
    Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDE
        (Poincare.D13.HeatKernelBridge.finiteConjugateSpacetime G) t₀
        (Poincare.D12.HeatDomain.AdmissibleTestClass.continuousIntegrableClass
          (Measure.count : Measure (Fin 2)))
        (Poincare.D13.HeatKernelBridge.finiteConjugateKernel G t₀) :=
  Poincare.D13.HeatKernelBridge.finite_isConjugateHeatKernelPDE G t₀
