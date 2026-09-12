-- D13 eleventh invocation: semantic transcript for the conjugate scalar-curvature term, the
-- mass-law obstruction of the v2 predicate, and the corrected mass-law predicate (v3).
import Poincare.D13.HeatKernelBridge.ConjugateScalarCurvature
import Poincare.D7.ConjugateHeat.ScalarCurvatureStatus

open MeasureTheory Filter
open scoped Topology

-- general matrix-exponential lemmas for an arbitrary generator
#check @Poincare.D13.HeatKernelBridge.exp_smul_shift_eq
#check @Poincare.D13.HeatKernelBridge.exp_smul_pos_of_pos_entries
#check @Poincare.D13.HeatKernelBridge.exp_smul_entry_hasDerivAt
#check @Poincare.D13.HeatKernelBridge.reversed_exp_entry_hasDerivAt
#check @Poincare.D13.HeatKernelBridge.tendsto_exp_smul_entry

-- the pointwise scalar-curvature operator and the curvature spacetime
#check @Poincare.D13.HeatKernelBridge.scalarMulLin
#check @Poincare.D13.HeatKernelBridge.scalarMulLin_selfAdjoint
#check @Poincare.D13.HeatKernelBridge.finiteConjugateSpacetimeWith
#check @Poincare.D13.HeatKernelBridge.finiteConjugateSpacetimeWith_zero

-- the mass law and the v2 normalization obstruction
#check @Poincare.D13.HeatKernelBridge.hasDerivAt_sum_of_solvesPDE
#check @Poincare.D13.HeatKernelBridge.sum_scalarMul_eq_zero_of_isConjugateHeatKernelPDE
#check @Poincare.D13.HeatKernelBridge.not_exists_isConjugateHeatKernelPDE_of_nonneg_scalarMul
#check @Poincare.D13.HeatKernelBridge.not_exists_isConjugateHeatKernelPDE_bool_scalarCurvature

-- the curvature kernel and its laws
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.scalarCurvatureGenerator
#check @Poincare.D13.HeatKernelBridge.FiniteHeatOperator.curvatureShifted_pos
#check @Poincare.D13.HeatKernelBridge.finiteConjKernelWith
#check @Poincare.D13.HeatKernelBridge.finiteConjKernelWith_pos
#check @Poincare.D13.HeatKernelBridge.finiteConjKernelWith_hasDerivAt
#check @Poincare.D13.HeatKernelBridge.finiteConjKernelWith_mass_hasDerivAt
#check @Poincare.D13.HeatKernelBridge.finiteConjKernelWith_tendsto_singleFun
#check @Poincare.D13.HeatKernelBridge.finiteConjKernelWith_mass_tendsto
#check @Poincare.D13.HeatKernelBridge.finiteConjKernelWith_dirac

-- the mass-law predicate (v3) and its well-posedness
#check @Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDEMassLaw
#check @Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDEMassLaw.v3
#check @Poincare.D13.HeatKernelBridge.finite_isConjugateHeatKernelPDEMassLaw
#check @Poincare.D13.HeatKernelBridge.scalarCurvature_energy_bound
#check @Poincare.D13.HeatKernelBridge.eq_finiteConjKernelWith_of_isConjugateHeatKernelPDEMassLaw
#check @Poincare.D13.HeatKernelBridge.exists_unique_finiteConjKernelWith
#check @Poincare.D13.HeatKernelBridge.isConjugateHeatKernelPDEMassLaw_of_isConjugateHeatKernelPDE
#check @Poincare.D13.HeatKernelBridge.continuousIntegrableClass_const_one

-- D7-level consumption
#check @Poincare.D7.ConjugateHeat.conjugate_normalization_forces_curvature_mass_zero
#check @Poincare.D7.ConjugateHeat.no_conjugate_kernel_of_nonneg_scalar_curvature
#check @Poincare.D7.ConjugateHeat.finite_conjugate_mass_law
#check @Poincare.D7.ConjugateHeat.finite_conjugate_scalar_curvature_witness
#check @Poincare.D7.ConjugateHeat.finite_conjugate_scalar_curvature_exists_unique
#check @Poincare.D7.ConjugateHeat.finite_conjugate_scalar_curvature_canonical_unique
#check @Poincare.D7.ConjugateHeat.conjugate_scalar_curvature_status_summary

-- axiom cones
#print axioms Poincare.D13.HeatKernelBridge.not_exists_isConjugateHeatKernelPDE_of_nonneg_scalarMul
#print axioms Poincare.D13.HeatKernelBridge.finite_isConjugateHeatKernelPDEMassLaw
#print axioms Poincare.D13.HeatKernelBridge.exists_unique_finiteConjKernelWith
#print axioms Poincare.D13.HeatKernelBridge.isConjugateHeatKernelPDEMassLaw_of_isConjugateHeatKernelPDE
#print axioms Poincare.D13.HeatKernelBridge.not_exists_isConjugateHeatKernelPDE_bool_scalarCurvature
#print axioms Poincare.D7.ConjugateHeat.conjugate_scalar_curvature_status_summary

-- kernel-checked uses: the v3 predicate is inhabited by the curvature kernel for an arbitrary
-- coefficient R, the v2 predicate is refuted for R = 1 on the two-point complete-graph model, and
-- the curvature kernel is the unique anticausal solution of the curvature problem
example (G : Poincare.D13.HeatKernelBridge.FiniteHeatOperator (Fin 2)) (R : Fin 2 → ℝ)
    (t₀ : ℝ) :
    Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDEMassLaw
        (Poincare.D13.HeatKernelBridge.finiteConjugateSpacetimeWith G R) t₀
        (Poincare.D12.HeatDomain.AdmissibleTestClass.continuousIntegrableClass
          (Measure.count : Measure (Fin 2)))
        (Poincare.D13.HeatKernelBridge.finiteConjKernelWith G R t₀) :=
  Poincare.D13.HeatKernelBridge.finite_isConjugateHeatKernelPDEMassLaw G R t₀

example :
    ¬ ∃ K : Bool → Bool → ℝ → ℝ,
      Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDE
        (Poincare.D13.HeatKernelBridge.finiteConjugateSpacetimeWith
          (Poincare.D13.HeatKernelBridge.completeGraphOperator Bool) (fun _ => (1 : ℝ))) 0
        (Poincare.D12.HeatDomain.AdmissibleTestClass.continuousIntegrableClass
          (Measure.count : Measure Bool)) K :=
  Poincare.D13.HeatKernelBridge.not_exists_isConjugateHeatKernelPDE_bool_scalarCurvature

example (G : Poincare.D13.HeatKernelBridge.FiniteHeatOperator (Fin 2)) (R : Fin 2 → ℝ)
    (t₀ : ℝ) :
    ∃! K : Fin 2 → Fin 2 → ℝ → ℝ,
      (∀ x y t, t₀ ≤ t → K x y t = 0) ∧
      (∀ x y t, t < t₀ → HasDerivAt (fun s : ℝ => K x y s)
        (-(G.laplacian (fun z => K z y t) x) + R x * K x y t) t) ∧
      (∀ z y : Fin 2, Tendsto (fun t : ℝ => K z y t) (𝓝[<] t₀)
        (𝓝 (if z = y then 1 else 0))) :=
  Poincare.D13.HeatKernelBridge.exists_unique_finiteConjKernelWith G R t₀
