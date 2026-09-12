/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.FiniteSpaceHeat

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D7.HeatKernel.FiniteStatus

**D7-level consumption of the pinned-operator finite existence theorem.**

The D13 companion `Poincare.D13.HeatKernelBridge.FiniteSpaceHeat` proves that over a finite
space with a *pinned* genuine finite Laplace operator (`FiniteHeatOperator`: symmetric,
constant-annihilating, strictly positive off-diagonal), the repaired D7 predicate
`IsHeatKernelPDE` has a witness, namely the matrix-exponential kernel. This module records that
result at the D7 level, together with the structural facts that make it non-vacuous:

* `finite_pinned_kernel_exists` — the repaired-predicate witness;
* `finite_pinned_operator_structure` — the pinned operator annihilates constants and is nonzero
  (so it is not the zero-Laplacian counterexample of `DataRefutation.lean`);
* `finite_pinned_legacy_datum` — a genuine legacy `HeatKernelData` with the *full* pointwise
  initial condition, with the pinned operator and the counting measure;
* `finite_pinned_dataV1` — the corrected-domain `HeatKernelDataV1` datum;
* `finite_pinned_spacetime_closed` — the model spacetime is a closed Riemannian manifold in the
  schematic sense;
* `finite_pinned_kernel_nondegenerate` — strictly positive off-diagonal entries, so the kernel is
  not the degenerate identity kernel;
* `finite_heat_status_summary` — the conjunction.

**Scope.** This is the finite-dimensional model of the manifold existence theorem. It does *not*
prove `D7-HEAT-KERNEL-EXISTENCE`; it proves that the repaired predicate is satisfiable over a
hypothesis class that pins the operator — the interface repair the earlier D13 invocations
identified as necessary, and the reason all universally quantified statements over the bare
schematic interface are false. No legacy D7 file is edited. All proofs are complete: no `sorry`,
`axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology Matrix

namespace Poincare.D7.HeatKernel

open Poincare.D13.HeatKernelBridge
open Poincare.D12.HeatDomain

variable {X : Type*} [Fintype X] [DecidableEq X] [TopologicalSpace X] [MeasurableSpace X]
  [MeasurableSingletonClass X]

/-- **D7-level pinned-operator existence**: the repaired predicate has a witness for every pinned
finite Laplace operator. -/
theorem finite_pinned_kernel_exists (G : FiniteHeatOperator X) :
    ∃ K : X → X → ℝ → ℝ,
      IsHeatKernelPDE (finiteHeatSpacetime G)
        (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X)) K :=
  ⟨finiteHeatKernel G, finite_isHeatKernelPDE G⟩

/-- **The pinned operator is a genuine Laplacian**: it annihilates constants, and it is not the
zero operator as soon as the space has two distinct points. -/
theorem finite_pinned_operator_structure (G : FiniteHeatOperator X) (h : ∃ x y : X, x ≠ y) :
    G.laplacian ≠ 0 ∧ G.laplacian (fun _ => 1) = 0 :=
  ⟨G.laplacian_ne_zero h, G.laplacian_one⟩

/-- **A genuine legacy D7 datum** for the pinned finite operator: the full `HeatKernelData` with the
pointwise initial condition over all continuous test functions, the pinned Laplacian and the
counting measure. -/
theorem finite_pinned_legacy_datum (G : FiniteHeatOperator X) :
    ∃ D : HeatKernelData X,
      D.kernel = finiteHeatKernel G ∧ D.laplacian = G.laplacian ∧
        D.volume = (Measure.count : Measure X) :=
  ⟨finiteHeatKernelData G, rfl, rfl, rfl⟩

/-- **The corrected-domain datum** (`HeatKernelDataV1`) of the pinned finite kernel. -/
theorem finite_pinned_dataV1 (G : FiniteHeatOperator X) :
    ∃ D : Poincare.D13.HeatKernelBridge.HeatKernelDataV1 X,
      D.kernel = finiteHeatKernel G :=
  ⟨finiteHeatKernelDataV1 G, rfl⟩

/-- **Dissipativity of the pinned operator** at the D7 level: the quadratic form is nonpositive, so
the pinned finite Laplacian is negative semidefinite (the discrete Dirichlet energy is nonnegative). -/
theorem finite_pinned_operator_dissipative (G : FiniteHeatOperator X) (u : X → ℝ) :
    (∑ x, u x * G.laplacian u x ≤ 0) ∧
      (0 ≤ ∑ x, ∑ y, G.L x y * (u x - u y) ^ 2) :=
  ⟨G.laplacian_quadraticForm_nonpos u, G.laplacian_dirichlet_nonneg u⟩

/-- **The discrete maximum principle and mass conservation** at the D7 level: the pinned finite heat
semigroup maps nonnegative functions to nonnegative functions, preserves the total mass, and is
`ℓ¹`-nonexpansive. -/
theorem finite_pinned_max_principle (G : FiniteHeatOperator X) {t : ℝ} (ht : 0 ≤ t)
    {u : X → ℝ} (hu : ∀ x, 0 ≤ u x) :
    (∀ x, 0 ≤ (NormedSpace.exp (t • G.L) *ᵥ u) x) ∧
      (∑ x, (NormedSpace.exp (t • G.L) *ᵥ u) x = ∑ x, u x) ∧
      (∑ x, |(NormedSpace.exp (t • G.L) *ᵥ u) x| ≤ ∑ x, |u x|) :=
  ⟨fun x => G.exp_smul_mulVec_nonneg ht hu x, G.exp_smul_mulVec_sum t u,
    G.exp_smul_mulVec_abs_sum_le ht u⟩

/-- The finite model spacetime is a closed Riemannian manifold in the schematic sense. -/
theorem finite_pinned_spacetime_closed (G : FiniteHeatOperator X) :
    IsClosedRiemannianManifold (finiteHeatSpacetime G) :=
  finiteHeatSpacetime_isClosedRiemannian G

/-- **Non-degeneracy**: the pinned kernel has strictly positive off-diagonal entries at time `1`, so
it is not the degenerate identity kernel that inhabits the bare interface with `C_lo = 0`. -/
theorem finite_pinned_kernel_nondegenerate (G : FiniteHeatOperator X) {x y : X} (hxy : x ≠ y) :
    0 < finiteHeatKernel G x y 1 ∧ finiteHeatKernel G x y 1 ≠ 0 :=
  ⟨finiteHeatKernel_pos G one_pos x y, ne_of_gt (finiteHeatKernel_pos G one_pos x y)⟩

/-- **D7 status summary** of the pinned finite model: existence of a repaired-predicate witness,
strict positivity at positive times, non-degeneracy, a nonzero constant-annihilating Laplacian, and
closedness of the schematic spacetime. -/
theorem finite_heat_status_summary (G : FiniteHeatOperator X) (h : ∃ x y : X, x ≠ y) :
    (∃ K : X → X → ℝ → ℝ,
        IsHeatKernelPDE (finiteHeatSpacetime G)
          (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X)) K) ∧
      (∀ (x y : X) (t : ℝ), 0 < t → 0 < finiteHeatKernel G x y t) ∧
      G.laplacian ≠ 0 ∧ G.laplacian (fun _ => 1) = 0 ∧
      IsClosedRiemannianManifold (finiteHeatSpacetime G) :=
  ⟨finite_pinned_kernel_exists G,
    fun x y t ht => finiteHeatKernel_pos G ht x y,
    G.laplacian_ne_zero h, G.laplacian_one, finiteHeatSpacetime_isClosedRiemannian G⟩

end Poincare.D7.HeatKernel
