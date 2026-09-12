/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.FiniteErgodicity
import Poincare.D7.HeatKernel.FiniteStatus

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D7.HeatKernel.ErgodicityStatus

**D7-level long-time asymptotics of the pinned finite heat kernel.**

The D13 companion `Poincare.D13.HeatKernelBridge.FiniteErgodicity` proves, for a pinned finite
Laplace operator `G`, the finite-dimensional counterpart of the spectral-gap half of the manifold
heat-kernel long-time theory:

* the Dirichlet form is nonnegative and vanishes exactly on the constants;
* the *combinatorial Dirichlet gap* `dirichletGap G = card X * minWeight G` (the cardinality times
  the minimal off-diagonal entry) is strictly positive and satisfies the Poincaré inequality
  `dirichletGap G * energy u ≤ dirichletForm G u` on mean-zero functions;
* along a mean-zero solution of `∂_t u = Δ u` the Gronwall-weighted energy is antitone, so the
  energy decays like `exp (-(2 * gap) * t)`;
* the deviation of the canonical kernel from the equilibrium (uniform) function
  `equilibrium x = (card X)⁻¹` is mean-zero, solves the same equation, and has the Dirac energy
  `1 - (card X)⁻¹` at `t → 0⁺`, so the kernel converges to equilibrium with the exponential bound
  `|K x y t - (card X)⁻¹| ≤ sqrt (1 - (card X)⁻¹) * exp (-(gap * t))`.

This module records those statements at the D7 level, where `finiteHeatKernel` is the kernel of the
genuine legacy datum `finiteHeatKernelData`:

* `finite_pinned_dirichlet_gap_pos` — the spectral gap is strictly positive;
* `finite_pinned_poincare` — the Poincaré inequality;
* `finite_pinned_kernel_energy_decay` — the exponential energy decay to equilibrium;
* `finite_pinned_kernel_tendsto_equilibrium` — convergence of the energy to `0` at infinity;
* `finite_pinned_kernel_pointwise_convergence` — the pointwise exponential bound;
* `finite_pinned_equilibrium_invariant` — the equilibrium function is invariant under the semigroup;
* `finite_pinned_ergodicity_summary` — the conjunction;
* `finite_pinned_complete_graph_sharp`, `finite_pinned_complete_graph_gap` — sharpness on the
  complete graph: the gap is exactly `card X` and the decay bound is attained.

**Scope and honesty.** This is the finite-dimensional model of the long-time (ergodic) behaviour of
the heat kernel — the spectral-theory item in the list of remaining manifold content of
`D7-HEAT-KERNEL-EXISTENCE`. It does **not** prove that blocker: the Laplace–Beltrami operator, the
manifold Poincaré inequality, parabolic regularity and the manifold heat-kernel construction remain
open, and no named blocker is closed. No legacy D7 file is edited. All proofs are complete: no
`sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology Matrix

namespace Poincare.D7.HeatKernel

open Poincare.D13.HeatKernelBridge
open Poincare.D13.HeatKernelBridge.FiniteHeatOperator
open Poincare.D12.HeatDomain

variable {X : Type*} [Fintype X] [DecidableEq X] [TopologicalSpace X] [MeasurableSpace X]
  [MeasurableSingletonClass X]

/-- **D7-level spectral gap**: the combinatorial Dirichlet gap of a pinned finite Laplace operator
is strictly positive as soon as the space has two distinct points. -/
theorem finite_pinned_dirichlet_gap_pos (G : FiniteHeatOperator X) (h : ∃ x y : X, x ≠ y) :
    0 < G.dirichletGap h :=
  G.dirichletGap_pos h

/-- **D7-level Poincaré inequality**: the Dirichlet form dominates the gap times the energy on every
mean-zero function. -/
theorem finite_pinned_poincare (G : FiniteHeatOperator X) (h : ∃ x y : X, x ≠ y)
    {u : X → ℝ} (hmean : meanZero u) :
    G.dirichletGap h * G.energy u ≤ G.dirichletForm u :=
  G.poincare_inequality h hmean

/-- **D7-level exponential energy decay to equilibrium**: the energy of the deviation of the pinned
heat kernel from the equilibrium function decays at rate `2 * gap`. -/
theorem finite_pinned_kernel_energy_decay (G : FiniteHeatOperator X) (y : X)
    (h : ∃ x y : X, x ≠ y) {T : ℝ} (hT : 0 < T) :
    G.energy (fun x => finiteHeatKernel G x y T - equilibrium (X := X) x) ≤
      (1 - (Fintype.card X : ℝ)⁻¹) * Real.exp (-(2 * G.dirichletGap h) * T) :=
  finiteHeatKernel_energy_decay_gap G y h hT

/-- **D7-level convergence to equilibrium**: the energy of the kernel's deviation from the
equilibrium function tends to `0` at infinity. -/
theorem finite_pinned_kernel_tendsto_equilibrium (G : FiniteHeatOperator X) (y : X)
    (h : ∃ x y : X, x ≠ y) :
    Tendsto
      (fun t : ℝ => G.energy (fun x => finiteHeatKernel G x y t - equilibrium (X := X) x))
      atTop (𝓝 0) :=
  finiteHeatKernel_tendsto_equilibrium_energy G y
    (fun u hu => G.poincare_inequality h hu) (G.dirichletGap_pos h)

/-- **D7-level pointwise exponential convergence**: the kernel converges to the equilibrium value
`(card X)⁻¹` pointwise with the gap rate. -/
theorem finite_pinned_kernel_pointwise_convergence (G : FiniteHeatOperator X) (y : X)
    (h : ∃ x y : X, x ≠ y) {t : ℝ} (ht : 0 < t) (x : X) :
    |finiteHeatKernel G x y t - equilibrium (X := X) x| ≤
      Real.sqrt (1 - (Fintype.card X : ℝ)⁻¹) * Real.exp (-(G.dirichletGap h * t)) :=
  finiteHeatKernel_pointwise_decay G y (fun u hu => G.poincare_inequality h hu) ht x

/-- **D7-level invariance of the equilibrium function**: the pinned semigroup fixes the uniform
function, so the equilibrium is the invariant state the kernel converges to. -/
theorem finite_pinned_equilibrium_invariant (G : FiniteHeatOperator X) {t : ℝ} :
    (NormedSpace.exp (t • G.L)) *ᵥ (equilibrium (X := X)) = equilibrium (X := X) := by
  have h1 : (equilibrium (X := X)) = (Fintype.card X : ℝ)⁻¹ • (fun _ : X => (1 : ℝ)) := by
    funext x
    simp [equilibrium]
  rw [h1, Matrix.mulVec_smul]
  exact congrArg (fun v : X → ℝ => (Fintype.card X : ℝ)⁻¹ • v) (G.exp_smul_mulVec_ones t)

/-- **D7-level sharpness (complete graph)**: for the complete-graph pinned operator the exponential
decay bound at the Dirichlet gap is attained for every positive time, so the combinatorial gap is the
true spectral gap there. -/
theorem finite_pinned_complete_graph_sharp (h : ∃ x y : X, x ≠ y) (y : X) {t : ℝ} (ht : 0 < t) :
    (completeGraphOperator X).energy
        (fun x => finiteHeatKernel (completeGraphOperator X) x y t - equilibrium (X := X) x) =
      (1 - (Fintype.card X : ℝ)⁻¹) *
        Real.exp (-(2 * (completeGraphOperator X).dirichletGap h) * t) :=
  completeGraphOperator_energy_decay_attained h y ht

/-- **D7-level value of the complete-graph gap**: the gap of the complete-graph operator is exactly
the cardinality of the space. -/
theorem finite_pinned_complete_graph_gap (h : ∃ x y : X, x ≠ y) :
    (completeGraphOperator X).dirichletGap h = (Fintype.card X : ℝ) :=
  completeGraphOperator_dirichletGap h

/-- **D7 status summary (ergodicity)**: the pinned finite heat kernel has a strictly positive
Dirichlet gap, satisfies the Poincaré inequality, converges to the equilibrium function both in
energy and pointwise at the gap rate, and the equilibrium is the invariant state. -/
theorem finite_pinned_ergodicity_summary (G : FiniteHeatOperator X) (y : X)
    (h : ∃ x y : X, x ≠ y) :
    (0 < G.dirichletGap h) ∧
      (∀ u : X → ℝ, meanZero u → G.dirichletGap h * G.energy u ≤ G.dirichletForm u) ∧
      (∀ T : ℝ, 0 < T →
        G.energy (fun x => finiteHeatKernel G x y T - equilibrium (X := X) x) ≤
          (1 - (Fintype.card X : ℝ)⁻¹) * Real.exp (-(2 * G.dirichletGap h) * T)) ∧
      Tendsto
        (fun t : ℝ => G.energy (fun x => finiteHeatKernel G x y t - equilibrium (X := X) x))
        atTop (𝓝 0) :=
  ⟨G.dirichletGap_pos h, fun u hu => G.poincare_inequality h hu,
    fun T hT => finiteHeatKernel_energy_decay_gap G y h hT,
    finite_pinned_kernel_tendsto_equilibrium G y h⟩

end Poincare.D7.HeatKernel
