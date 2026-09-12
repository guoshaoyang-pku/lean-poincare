-- D13 tenth invocation: semantic transcript for the pinned-operator uniqueness theorem.
import Poincare.D13.HeatKernelBridge.FiniteUniqueness
import Poincare.D7.HeatKernel.UniquenessStatus

open MeasureTheory Filter
open scoped Topology

-- the energy functional, its dissipation and the energy method
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.energy
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.energy_nonneg
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.energy_eq_zero_iff
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.hasDerivAt_energy_of
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.hasDerivAt_energy
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.energy_antitoneOn
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.tendsto_energy_zero
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.eq_zero_of_hasDerivAt_of_tendsto_zero
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.eq_of_hasDerivAt_of_tendsto

-- singleton test functions and the pointwise Dirac initial data
#check @Poincare.D13.HeatKernelBridge.singleFun
#check @Poincare.D13.HeatKernelBridge.singleFun_apply_self
#check @Poincare.D13.HeatKernelBridge.singleFun_apply_of_ne
#check @Poincare.D13.HeatKernelBridge.singleFun_apply
#check @Poincare.D13.HeatKernelBridge.continuous_singleFun
#check @Poincare.D13.HeatKernelBridge.integrable_singleFun
#check @Poincare.D13.HeatKernelBridge.continuousIntegrableClass_singleFun
#check @Poincare.D13.HeatKernelBridge.count_isFiniteMeasureOnCompacts
#check @Poincare.D13.HeatKernelBridge.hasCompactSupport_singleFun
#check @Poincare.D13.HeatKernelBridge.continuousCompactSupportClass_singleFun
#check @Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.tendsto_singleFun
#check @Poincare.D13.HeatKernelBridge.finiteHeatKernel_tendsto_singleFun
#check @Poincare.D13.HeatKernelBridge.finiteHeatKernel_causal

-- kernel-level uniqueness and the causal existence-and-uniqueness statement
#check @Poincare.D13.HeatKernelBridge.eq_of_pde_of_dirac
#check @Poincare.D13.HeatKernelBridge.eq_finiteHeatKernel_of_pde_of_dirac
#check @Poincare.D13.HeatKernelBridge.eq_finiteHeatKernel_of_isHeatKernelPDE
#check @Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.eq_of_same
#check @Poincare.D13.HeatKernelBridge.exists_unique_finiteHeatKernel

-- D7-level consumption
#check @Poincare.D7.HeatKernel.finite_pinned_kernel_unique
#check @Poincare.D7.HeatKernel.finite_pinned_interface_unique
#check @Poincare.D7.HeatKernel.finite_pinned_canonical_unique
#check @Poincare.D7.HeatKernel.finite_pinned_exists_unique
#check @Poincare.D7.HeatKernel.finite_pinned_wellposed_summary

-- axiom cones
#print axioms Poincare.D13.HeatKernelBridge.exists_unique_finiteHeatKernel
#print axioms Poincare.D13.HeatKernelBridge.eq_finiteHeatKernel_of_isHeatKernelPDE
#print axioms Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.eq_of_same
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.hasDerivAt_energy
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.eq_zero_of_hasDerivAt_of_tendsto_zero
#print axioms Poincare.D13.HeatKernelBridge.continuousCompactSupportClass_singleFun
#print axioms Poincare.D7.HeatKernel.finite_pinned_kernel_unique
#print axioms Poincare.D7.HeatKernel.finite_pinned_wellposed_summary

-- non-vacuity: the causal existence-and-uniqueness statement has the canonical witness, and the
-- interface uniqueness applies to the canonical inhabitant of the repaired predicate
example : ∃ K : Fin 2 → Fin 2 → ℝ → ℝ,
    (∀ x y t, t ≤ 0 → K x y t = 0) ∧
    (∀ x y t, 0 < t → HasDerivAt (fun s : ℝ => K x y s)
      ((Poincare.D13.HeatKernelBridge.completeGraphOperator (Fin 2)).laplacian
        (fun z => K z y t) x) t) ∧
    (∀ z y : Fin 2, Tendsto (fun t : ℝ => K z y t) (𝓝[>] (0 : ℝ))
      (𝓝 (if z = y then 1 else 0))) := by
  obtain ⟨K, hK, _⟩ := Poincare.D13.HeatKernelBridge.exists_unique_finiteHeatKernel
    (Poincare.D13.HeatKernelBridge.completeGraphOperator (Fin 2))
  exact ⟨K, hK⟩

-- ... and the uniqueness theorem applies to any kernel with the pinned PDE and Dirac data
example (G : Poincare.D13.HeatKernelBridge.FiniteHeatOperator (Fin 2))
    (K : Fin 2 → Fin 2 → ℝ → ℝ)
    (hK : ∀ x y t, 0 < t → HasDerivAt (fun s : ℝ => K x y s)
      (G.laplacian (fun z => K z y t) x) t)
    (hd : ∀ z y : Fin 2, Tendsto (fun t : ℝ => K z y t) (𝓝[>] (0 : ℝ))
      (𝓝 (if z = y then 1 else 0))) :
    ∀ z y : Fin 2, ∀ t : ℝ, 0 < t →
      K z y t = Poincare.D13.HeatKernelBridge.finiteHeatKernel G z y t :=
  Poincare.D13.HeatKernelBridge.eq_finiteHeatKernel_of_pde_of_dirac G hK hd

example (G : Poincare.D13.HeatKernelBridge.FiniteHeatOperator (Fin 2)) :
    Poincare.D13.HeatKernelBridge.IsHeatKernelPDE
        (Poincare.D13.HeatKernelBridge.finiteHeatSpacetime G)
        (Poincare.D12.HeatDomain.AdmissibleTestClass.continuousIntegrableClass
          (Measure.count : Measure (Fin 2)))
        (Poincare.D13.HeatKernelBridge.finiteHeatKernel G) :=
  Poincare.D13.HeatKernelBridge.finite_isHeatKernelPDE G
