/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.FiniteConjugateUniqueness
import Poincare.D7.ConjugateHeat.Status

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D7.ConjugateHeat.UniquenessStatus

**D7-level well-posedness of the pinned finite conjugate-heat problem.**

The D13 companion `Poincare.D13.HeatKernelBridge.FiniteConjugateUniqueness` proves, by a
Grönwall-weighted energy argument, that the repaired conjugate-heat predicate
`IsConjugateHeatKernelPDE` has at most one solution below the terminal time, and that the canonical
time-reversed matrix-exponential kernel is that solution. This module records the result at the D7
level:

* `finite_conjugate_interface_unique` — two inhabitants of the conjugate predicate over the same
  finite counting-measure spacetime agree below the terminal time;
* `finite_conjugate_canonical_unique` — every inhabitant equals the canonical time-reversed kernel;
* `finite_conjugate_exists_unique` — among anticausal kernels the conjugate problem with the
  pointwise terminal Dirac data has exactly one solution;
* `finite_conjugate_wellposed_summary` — existence, uniqueness and canonical identification.

**Scope.** This is the finite-dimensional conjugate model. It does **not** prove manifold conjugate
existence or backward uniqueness, and no named blocker is closed. No legacy D7 file is edited. All
proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D7.ConjugateHeat

open Poincare.D13.HeatKernelBridge
open Poincare.D12.HeatDomain

variable {X : Type*} [Fintype X] [DecidableEq X] [TopologicalSpace X] [MeasurableSpace X]
  [MeasurableSingletonClass X]

/-- **D7-level conjugate uniqueness (interface form)**: two inhabitants of the repaired conjugate
predicate over the same finite counting-measure spacetime with the pinned Laplacian agree below the
terminal time, provided the scalar-curvature quadratic form is bounded below. -/
theorem finite_conjugate_interface_unique (G : FiniteHeatOperator X)
    {S : ConjugateHeatSpacetime X} {t₀ : ℝ} (hL : S.laplacian = G.laplacian)
    (hvol : S.volume = Measure.count)
    {C : ℝ} (hR : ∀ u : X → ℝ, -(C * G.energy u) ≤ ∑ x, u x * S.scalarMul u x)
    {C' : AdmissibleTestClass X S.volume} {K₁ K₂ : X → X → ℝ → ℝ}
    (h₁ : IsConjugateHeatKernelPDE S t₀ C' K₁) (h₂ : IsConjugateHeatKernelPDE S t₀ C' K₂)
    (hC : ∀ y : X, C'.cls (singleFun y)) :
    ∀ z y t, t < t₀ → K₁ z y t = K₂ z y t :=
  IsConjugateHeatKernelPDE.eq_of_same G hL hvol hR h₁ h₂ hC

/-- **D7-level identification of the canonical conjugate witness**: every inhabitant of the
repaired conjugate predicate over the finite counting-measure spacetime with the pinned Laplacian
equals the time-reversed matrix-exponential kernel below the terminal time. -/
theorem finite_conjugate_canonical_unique (G : FiniteHeatOperator X) (t₀ : ℝ)
    {C : AdmissibleTestClass X (Measure.count : Measure X)} {K : X → X → ℝ → ℝ}
    (h : IsConjugateHeatKernelPDE (finiteConjugateSpacetime G) t₀ C K)
    (hC : ∀ y : X, C.cls (singleFun y)) :
    ∀ z y t, t < t₀ → K z y t = finiteConjugateKernel G t₀ z y t :=
  eq_finiteConjugateKernel_of_isConjugateHeatKernelPDE G t₀ h hC

/-- **D7-level conjugate well-posedness**: among anticausal kernels the pinned finite conjugate
problem with the pointwise terminal Dirac data has exactly one solution. -/
theorem finite_conjugate_exists_unique (G : FiniteHeatOperator X) (t₀ : ℝ) :
    ∃! K : X → X → ℝ → ℝ,
      (∀ x y t, t₀ ≤ t → K x y t = 0) ∧
      (∀ x y t, t < t₀ → HasDerivAt (fun s : ℝ => K x y s)
        (-(G.laplacian (fun z => K z y t) x)) t) ∧
      (∀ z y : X, Tendsto (fun t : ℝ => K z y t) (𝓝[<] t₀)
        (𝓝 (if z = y then 1 else 0))) :=
  exists_unique_finiteConjugateKernel G t₀

/-- **D7 conjugate status summary**: the repaired conjugate predicate has a witness on the finite
counting-measure spacetime, any two such witnesses agree below the terminal time, and every witness
is the canonical time-reversed kernel there. -/
theorem finite_conjugate_wellposed_summary [DiscreteTopology X] (G : FiniteHeatOperator X)
    (t₀ : ℝ) :
    (∃ K : X → X → ℝ → ℝ,
        IsConjugateHeatKernelPDE (finiteConjugateSpacetime G) t₀
          (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X)) K) ∧
      (∀ K₁ K₂ : X → X → ℝ → ℝ,
        IsConjugateHeatKernelPDE (finiteConjugateSpacetime G) t₀
          (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X)) K₁ →
        IsConjugateHeatKernelPDE (finiteConjugateSpacetime G) t₀
          (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X)) K₂ →
        ∀ z y t, t < t₀ → K₁ z y t = K₂ z y t) ∧
      (∀ K : X → X → ℝ → ℝ,
        IsConjugateHeatKernelPDE (finiteConjugateSpacetime G) t₀
          (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X)) K →
        ∀ z y t, t < t₀ → K z y t = finiteConjugateKernel G t₀ z y t) := by
  refine ⟨⟨finiteConjugateKernel G t₀, finite_isConjugateHeatKernelPDE G t₀⟩, ?_, ?_⟩
  · intro K₁ K₂ h₁ h₂
    exact finite_conjugate_interface_unique G rfl rfl
      (C := 0) (by intro u; simp [finiteConjugateSpacetime]) h₁ h₂
      (fun y => continuousIntegrableClass_singleFun y)
  · intro K h
    exact finite_conjugate_canonical_unique G t₀ h (fun y => continuousIntegrableClass_singleFun y)

end Poincare.D7.ConjugateHeat
