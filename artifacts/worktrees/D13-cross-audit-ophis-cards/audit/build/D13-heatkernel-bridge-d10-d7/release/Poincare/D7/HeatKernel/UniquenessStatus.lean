/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.FiniteUniqueness
import Poincare.D7.HeatKernel.FiniteStatus

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D7.HeatKernel.UniquenessStatus

**D7-level uniqueness of the pinned finite heat kernel.**

The D13 companion `Poincare.D13.HeatKernelBridge.FiniteUniqueness` proves, by the classical energy
method, that the pinned finite heat-kernel problem has *at most one* solution on positive times:
along a solution of `∂_t u = Δ u` the `ℓ²` energy `∑ x, (u x)^2` is antitone (its derivative is
`2 * ∑ x, u x * Δ u x ≤ 0` by the pinned operator's dissipativity), so a solution whose components
tend to `0` as `t → 0⁺` vanishes identically. Reading the Dirac limit against the singleton test
functions turns that into uniqueness for the D7 interface. This module records the result at the D7
level:

* `finite_pinned_kernel_unique` — any kernel with the pinned PDE and the pointwise Dirac initial
  data is the canonical matrix-exponential kernel for `t > 0`;
* `finite_pinned_interface_unique` — two `IsHeatKernelPDE` inhabitants over the same finite
  counting-measure spacetime agree for `t > 0`;
* `finite_pinned_canonical_unique` — every inhabitant of the repaired predicate over the finite
  counting-measure spacetime with the pinned Laplacian equals the canonical kernel;
* `finite_pinned_exists_unique` — among causal kernels the pinned PDE problem with the pointwise
  Dirac initial data has exactly one solution (the existence half is
  `finiteHeatKernel`, proved in `FiniteSpaceHeat.lean`);
* `finite_pinned_wellposed_summary` — the combination: existence, uniqueness, and identification of
  the witness, at the D7 level.

**Scope.** Together with `Poincare.D7.HeatKernel.FiniteStatus` this makes the pinned finite interface
problem *well posed* (existence and uniqueness). It does **not** prove
`D7-HEAT-KERNEL-EXISTENCE`: the manifold existence and uniqueness theorems (maximum principle and
parabolic regularity on a Riemannian manifold) remain open, and no named blocker is closed. No
legacy D7 file is edited. All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`,
or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D7.HeatKernel

open Poincare.D13.HeatKernelBridge
open Poincare.D12.HeatDomain

variable {X : Type*} [Fintype X] [DecidableEq X] [TopologicalSpace X] [MeasurableSpace X]
  [MeasurableSingletonClass X]

/-- **D7-level uniqueness (pointwise form)**: a kernel with the pinned Laplacian, the genuine PDE in
the time variable and the pointwise Dirac initial data is the canonical matrix-exponential kernel
for every positive time. -/
theorem finite_pinned_kernel_unique (G : FiniteHeatOperator X) {K : X → X → ℝ → ℝ}
    (hpde : ∀ x y t, 0 < t → HasDerivAt (fun s : ℝ => K x y s)
      (G.laplacian (fun z => K z y t) x) t)
    (hdirac : ∀ z y : X, Tendsto (fun t : ℝ => K z y t) (𝓝[>] (0 : ℝ))
      (𝓝 (if z = y then 1 else 0))) :
    ∀ z y t, 0 < t → K z y t = finiteHeatKernel G z y t :=
  eq_finiteHeatKernel_of_pde_of_dirac G hpde hdirac

/-- **D7-level uniqueness (interface form)**: two inhabitants of the repaired predicate over the
same finite counting-measure spacetime with the pinned Laplacian agree for every positive time,
provided the admissible class contains the singleton test functions. -/
theorem finite_pinned_interface_unique (G : FiniteHeatOperator X) {S : HeatSpacetime X}
    (hL : S.laplacian = G.laplacian) (hvol : S.volume = Measure.count)
    {C : AdmissibleTestClass X S.volume} (hC : ∀ y : X, C.cls (singleFun y))
    {K₁ K₂ : X → X → ℝ → ℝ}
    (h₁ : IsHeatKernelPDE S C K₁) (h₂ : IsHeatKernelPDE S C K₂) :
    ∀ z y t, 0 < t → K₁ z y t = K₂ z y t :=
  IsHeatKernelPDE.eq_of_same hL hvol h₁ h₂ hC

/-- **D7-level identification of the canonical witness**: every inhabitant of the repaired predicate
over the finite counting-measure spacetime with the pinned Laplacian and the admissible integrable
class (on a discrete topology, where the singletons are admissible test functions) equals the
canonical matrix-exponential kernel for `t > 0`. -/
theorem finite_pinned_canonical_unique [DiscreteTopology X] (G : FiniteHeatOperator X)
    {S : HeatSpacetime X} (hL : S.laplacian = G.laplacian) (hvol : S.volume = Measure.count)
    {K : X → X → ℝ → ℝ}
    (h : IsHeatKernelPDE S (AdmissibleTestClass.continuousIntegrableClass S.volume) K) :
    ∀ z y t, 0 < t → K z y t = finiteHeatKernel G z y t := by
  refine eq_finiteHeatKernel_of_isHeatKernelPDE G hL hvol h ?_
  intro y
  simpa [AdmissibleTestClass.continuousIntegrableClass, hvol] using
    (continuousIntegrableClass_singleFun (X := X) y)

/-- **D7-level well-posedness**: among causal kernels (those vanishing for `t ≤ 0`, the
normalization convention of `finiteHeatKernel`) the pinned finite PDE problem with the pointwise
Dirac initial data has exactly one solution. -/
theorem finite_pinned_exists_unique (G : FiniteHeatOperator X) :
    ∃! K : X → X → ℝ → ℝ,
      (∀ x y t, t ≤ 0 → K x y t = 0) ∧
      (∀ x y t, 0 < t → HasDerivAt (fun s : ℝ => K x y s)
        (G.laplacian (fun z => K z y t) x) t) ∧
      (∀ z y : X, Tendsto (fun t : ℝ => K z y t) (𝓝[>] (0 : ℝ))
        (𝓝 (if z = y then 1 else 0))) :=
  exists_unique_finiteHeatKernel G

/-- **D7 status summary (existence and uniqueness)**: over a pinned finite Laplace operator the
repaired predicate has a witness on the finite counting-measure spacetime, any two such witnesses
agree on positive times, and every witness is the canonical matrix-exponential kernel there. -/
theorem finite_pinned_wellposed_summary [DiscreteTopology X] (G : FiniteHeatOperator X) :
    (∃ K : X → X → ℝ → ℝ,
        IsHeatKernelPDE (finiteHeatSpacetime G)
          (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X)) K) ∧
      (∀ K₁ K₂ : X → X → ℝ → ℝ,
        IsHeatKernelPDE (finiteHeatSpacetime G)
          (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X)) K₁ →
        IsHeatKernelPDE (finiteHeatSpacetime G)
          (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X)) K₂ →
        ∀ z y t, 0 < t → K₁ z y t = K₂ z y t) ∧
      (∀ K : X → X → ℝ → ℝ,
        IsHeatKernelPDE (finiteHeatSpacetime G)
          (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X)) K →
        ∀ z y t, 0 < t → K z y t = finiteHeatKernel G z y t) := by
  refine ⟨finite_pinned_kernel_exists G, ?_, ?_⟩
  · intro K₁ K₂ h₁ h₂
    exact finite_pinned_interface_unique G rfl rfl
      (fun y => continuousIntegrableClass_singleFun y) h₁ h₂
  · intro K h
    exact finite_pinned_canonical_unique G rfl rfl h

end Poincare.D7.HeatKernel
