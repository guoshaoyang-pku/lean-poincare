/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.ConjugateHeatBridge

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D7.ConjugateHeat.Status

**D7-level consumption of the D13 conjugate-heat bridge.**

This new D7 module (no existing D7 file is edited) records, at the D7 level, what the D13 bridge
established for the conjugate-heat half of the interface:

* `not_conjugateHeatKernelExistenceStatement`: the D7 `ConjugateHeatKernelExistenceStatement` is
  **false as formalized** — the schematic `ConjugateHeatSpacetime` leaves the Laplacian free, and
  the two-point datum with the identity Laplacian satisfies the Riemannian hypothesis predicate
  while admitting no kernel at all. The proof is the D13 refutation, consumed here at the D7 level;
* `ConjugateHeatKernelCorrectedDomainStatement`: the corrected-domain statement at the honest flat
  family (the pinned Euclidean Laplacian, the D12 admissible test class, the genuine `HasDerivAt`
  heat-equation field) and its proof `conjugateHeatKernelCorrectedDomainStatement_proved`, obtained
  by consuming the D13 transport of the D10 Euclidean kernel;
* `conjugate_heat_snapshot_refuted`: on the honest flat conjugate spacetime in positive dimension
  the time-reversed D10 kernel inhabits the repaired predicate while the legacy snapshot predicate
  is refuted (`flat_conjugate_repaired_scope` consumption), so the legacy `solves` field must be
  replaced, not constrained;
* `conjugate_heat_status_summary`: the conjunction of the refutation, the corrected-domain
  existence and the exact-failure localization.

**Scope.** No blocker is claimed closed: the manifold-side conjugate heat kernel existence (the
named `B-D7-CONJUGATE-HEAT-KERNEL-EXISTENCE`) remains open. What is checked at the D7 level is the
refutation of the schematic statement and the corrected-domain flat existence and failure
localization. All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D7.ConjugateHeat

open Poincare.D12.HeatDomain
open Poincare.D13.HeatKernelBridge

/-- **The D7 conjugate-heat kernel existence statement is false as formalized.** Consumes the D13
refutation: the two-point schematic Riemannian conjugate-heat spacetime with the identity Laplacian
satisfies `IsRiemannianConjugateHeatSpacetime` and admits no kernel, because the `solves` field
forces `K = 0` against strict positivity. -/
theorem not_conjugateHeatKernelExistenceStatement :
    ¬ ConjugateHeatKernelExistenceStatement.{0} :=
  Poincare.D13.HeatKernelBridge.not_conjugateHeatKernelExistenceStatement

/-- **The corrected-domain conjugate-heat statement at the honest flat family** (D7-level
statement, `def … : Prop`): for every dimension and terminal time there is a kernel inhabiting the
versioned predicate `IsConjugateHeatKernelPDE` — the conjugate heat equation as a genuine
`HasDerivAt` statement — on the D12 corrected admissible test class, with the pinned Euclidean
Laplacian. Proved below by consuming the D13 transport. -/
def ConjugateHeatKernelCorrectedDomainStatement : Prop :=
  ∀ n : ℕ, ∃ (K : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ → ℝ) (t₀ : ℝ),
    IsConjugateHeatKernelPDE (flatConjugateHeatSpacetime n) t₀
      (AdmissibleTestClass.continuousIntegrableClass (flatConjugateHeatSpacetime n).volume) K

/-- **The corrected-domain flat conjugate statement is proved** by the D13 transport of the D10
Euclidean kernel (the time-reversed Gaussian). -/
theorem conjugateHeatKernelCorrectedDomainStatement_proved :
    ConjugateHeatKernelCorrectedDomainStatement :=
  flatConjugateCorrectedDomainExistence_proved

/-- **D7-level corrected-domain existence at a fixed dimension and terminal time**: the
time-reversed D10 kernel is an explicit witness, consuming the D13 inhabitant
`flat_isConjugateHeatKernelPDE_integrableClass`. -/
theorem exists_flatConjugateKernelPDE (n : ℕ) (t₀ : ℝ) :
    ∃ K : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ → ℝ,
      IsConjugateHeatKernelPDE (flatConjugateHeatSpacetime n) t₀
        (AdmissibleTestClass.continuousIntegrableClass (flatConjugateHeatSpacetime n).volume) K :=
  ⟨flatConjugateKernel n t₀, flat_isConjugateHeatKernelPDE_integrableClass n t₀⟩

/-- **Mass conservation and symmetry of the conjugate kernel at the D7 level**: the time-reversed
D10 kernel is symmetric in its space arguments and has unit mass at every backward time before the
terminal time. These are the two algebraic properties the D7 conjugate-heat plan asks for,
consumed from the D13 structural theorems `flatConjugateKernel_symm` and
`flatConjugateKernel_mass`. -/
theorem conjugate_heat_mass_and_symmetry (n : ℕ) (t₀ : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : t < t₀) :
    flatConjugateKernel n t₀ x y t = flatConjugateKernel n t₀ y x t ∧
      ∫ z, flatConjugateKernel n t₀ z y t ∂(flatConjugateHeatSpacetime n).volume = 1 :=
  ⟨flatConjugateKernel_symm n t₀ x y t, flatConjugateKernel_mass n t₀ y ht⟩

/-- **Chapman–Kolmogorov law of the backward family at the D7 level**: composing two backward
steps is the convolution of the two conjugate kernels, consumed from the D13 theorem
`flatConjugateKernel_semigroup`. -/
theorem conjugate_heat_chapman_kolmogorov (n : ℕ) (t₀ : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) {s t : ℝ} (hs : s < t₀) (ht : t < t₀)
    (hst : t₀ < s + t) (hst2 : s + t < 2 * t₀) :
    flatConjugateKernel n t₀ x y (s + t - t₀)
      = ∫ z, flatConjugateKernel n t₀ x z s * flatConjugateKernel n t₀ z y t
          ∂(flatConjugateHeatSpacetime n).volume :=
  flatConjugateKernel_semigroup n t₀ x y hs ht hst hst2

/-- **The legacy snapshot field is refuted on the honest flat model in positive dimension** (D7
level): the same time-reversed D10 kernel that inhabits the repaired predicate fails the legacy
`IsConjugateHeatKernel` predicate there, so the legacy `solves` field must be replaced by the
genuine PDE. -/
theorem conjugate_heat_snapshot_refuted (n : ℕ) (hn : 0 < n) (t₀ : ℝ) :
    IsConjugateHeatKernelPDE (flatConjugateHeatSpacetime n) t₀
        (AdmissibleTestClass.continuousIntegrableClass (flatConjugateHeatSpacetime n).volume)
        (flatConjugateKernel n t₀) ∧
      ¬ IsConjugateHeatKernel (flatConjugateHeatSpacetime n) t₀
        (flatConjugateKernel n t₀) :=
  flat_conjugate_repaired_scope n hn t₀

/-- **The D7-level conjugate-heat status summary.** The schematic existence statement is refuted,
the corrected-domain flat statement is proved in every dimension, and in positive dimension the
legacy snapshot predicate fails on the honest model that inhabits the repaired predicate. -/
theorem conjugate_heat_status_summary :
    (¬ ConjugateHeatKernelExistenceStatement.{0}) ∧
      ConjugateHeatKernelCorrectedDomainStatement ∧
        (∀ n : ℕ, 0 < n → ∀ t₀ : ℝ,
          IsConjugateHeatKernelPDE (flatConjugateHeatSpacetime n) t₀
              (AdmissibleTestClass.continuousIntegrableClass
                (flatConjugateHeatSpacetime n).volume)
              (flatConjugateKernel n t₀) ∧
            ¬ IsConjugateHeatKernel (flatConjugateHeatSpacetime n) t₀
              (flatConjugateKernel n t₀)) :=
  ⟨not_conjugateHeatKernelExistenceStatement,
    conjugateHeatKernelCorrectedDomainStatement_proved,
    fun n hn t₀ => flat_conjugate_repaired_scope n hn t₀⟩

end Poincare.D7.ConjugateHeat
