/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.WeakHeatEquation
import Poincare.D13.HeatKernelBridge.FiniteSpaceHeat

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D13.HeatKernelBridge.WeakFinite

**D13 heat-kernel bridge, companion note 4: the weak heat equation for the pinned finite model.**

`WeakHeatEquation.lean` proved the weak (test-paired) heat equation for the explicit D10 Euclidean
kernel, where the certificates came from Gaussian estimates. This file instantiates the same weak
interface on a **second, non-flat model**: the pinned finite Markov-chain kernel of
`FiniteSpaceHeat.lean` over the counting measure. The certificates are proved by finite-dimensional
arguments, with a different analytic shape from the Gaussian ones:

* `finiteHeatKernel_abs_le_one`: every entry of the pinned kernel is in `[0,1]` at positive times
  (nonnegativity plus the Gaussian upper bound `exp_smul_le_one`);
* `finiteLaplacianBound G = ∑ x, ∑ z, |G.L x z|`: the total mass of the operator matrix, a uniform
  bound in space and time;
* `finiteHeatKernel_laplacian_abs_le`: `|Δ_x K(x,y,t)| ≤ finiteLaplacianBound G` for every
  `t ∈ [a,b]` with `a > 0`, by the finite triangle inequality and the entry bound;
* `finiteWeakHeatCertificates`: the four certificates for the pinned finite kernel; measurability
  and integrability come from `Integrable.of_finite` (a finite type with measurable singletons and
  finite counting measure);
* `finite_weakHeatKernel`: the pinned finite kernel inhabits `IsWeakHeatKernelPDE` on the
  corrected admissible domain, via the transfer `IsHeatKernelPDE.toWeak` applied to
  `finite_isHeatKernelPDE`.

Together with `flat_weakHeatKernel_integrable` this shows the weak interface is inhabited by two
structurally different models (a flat Euclidean family in every dimension and a finite reversible
Markov chain), so the interface is not tied to the Gaussian certificate proof. No named blocker is
closed. All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D13.HeatKernelBridge

open Poincare.D12.HeatDomain

variable {X : Type*} [Fintype X] [DecidableEq X] [TopologicalSpace X] [MeasurableSpace X]
  [MeasurableSingletonClass X]

/-- **The uniform bound for the finite Laplacian pairing**: the total mass of the operator matrix.
On the time interval `[a,b]` with `a > 0` the paired Laplacian of the pinned kernel is bounded by
this constant. -/
noncomputable def finiteLaplacianBound (G : FiniteHeatOperator X) : ℝ :=
  ∑ x, ∑ z, |G.L x z|

theorem finiteLaplacianBound_nonneg (G : FiniteHeatOperator X) : 0 ≤ finiteLaplacianBound G :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **The entries of the pinned kernel are bounded by one** in absolute value at positive times. -/
theorem finiteHeatKernel_abs_le_one (G : FiniteHeatOperator X) {t : ℝ} (ht : 0 < t) (x y : X) :
    |finiteHeatKernel G x y t| ≤ 1 := by
  rw [abs_of_nonneg (finiteHeatKernel_nonneg G x y t), finiteHeatKernel_of_pos G ht x y]
  exact G.exp_smul_le_one ht x y

/-- **Local uniform bound on the paired Laplacian of the pinned finite kernel.** For `0 < a ≤ t`
and every space point, `|Δ_x K(x,y,t)| ≤ finiteLaplacianBound G`: the finite sum is bounded by the
triangle inequality, each kernel entry by one, and the row mass by the total mass. -/
theorem finiteHeatKernel_laplacian_abs_le (G : FiniteHeatOperator X) (y : X) {a b t : ℝ}
    (ha : 0 < a) (ht : t ∈ Set.Icc a b) (x : X) :
    |G.laplacian (fun z => finiteHeatKernel G z y t) x| ≤ finiteLaplacianBound G := by
  have htpos : 0 < t := lt_of_lt_of_le ha ht.1
  rw [FiniteHeatOperator.laplacian_apply, Matrix.mulVec, dotProduct]
  calc |∑ z, G.L x z * finiteHeatKernel G z y t|
      ≤ ∑ z, |G.L x z * finiteHeatKernel G z y t| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z, |G.L x z| * |finiteHeatKernel G z y t| := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [abs_mul]
    _ ≤ ∑ z, |G.L x z| * 1 := by
        refine Finset.sum_le_sum fun z _ => ?_
        exact mul_le_mul_of_nonneg_left (finiteHeatKernel_abs_le_one G htpos z y) (abs_nonneg _)
    _ = ∑ z, |G.L x z| := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [mul_one]
    _ ≤ ∑ w, ∑ z, |G.L w z| := by
        have hsingle : ∑ w, (if w = x then ∑ z, |G.L x z| else 0) = ∑ z, |G.L x z| := by
          rw [Finset.sum_eq_single x]
          · simp
          · intro b _ hb
            simp [hb]
          · intro hx
            exact absurd (Finset.mem_univ x) hx
        rw [← hsingle]
        refine Finset.sum_le_sum fun w _ => ?_
        by_cases hw : w = x
        · subst hw; simp
        · simp only [hw, ite_false]
          exact Finset.sum_nonneg fun z _ => abs_nonneg _

/-- **The four weak-heat certificates for the pinned finite kernel.** Measurability and
integrability are the finite-type instances (`Integrable.of_finite`); the local uniform bound is
`finiteHeatKernel_laplacian_abs_le`. -/
theorem finiteWeakHeatCertificates (G : FiniteHeatOperator X) :
    WeakHeatCertificates (finiteHeatSpacetime G)
      (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X))
      (finiteHeatKernel G) where
  snapshot_measurable := fun φ _ y t _ =>
    (Integrable.of_finite (μ := Measure.count)
      (f := fun x => φ x * finiteHeatKernel G x y t)).1
  snapshot_integrable := fun φ _ y t _ =>
    Integrable.of_finite (μ := Measure.count)
      (f := fun x => φ x * finiteHeatKernel G x y t)
  laplacian_measurable := fun φ _ y t _ =>
    (Integrable.of_finite (μ := Measure.count)
      (f := fun x => φ x * (finiteHeatSpacetime G).laplacian (fun z => finiteHeatKernel G z y t) x)).1
  laplacian_locally_bounded := fun y a b ha _ =>
    ⟨finiteLaplacianBound G, fun x t ht =>
      finiteHeatKernel_laplacian_abs_le G y ha ht x⟩

/-- **The pinned finite heat kernel satisfies the weak heat equation on the corrected admissible
domain.** The pointwise PDE `finiteHeatKernel_hasDerivAt` (through `finite_isHeatKernelPDE`) and
the finite certificates feed the transfer `IsHeatKernelPDE.toWeak`. -/
theorem finite_weakHeatKernel (G : FiniteHeatOperator X) :
    IsWeakHeatKernelPDE (finiteHeatSpacetime G)
      (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X))
      (finiteHeatKernel G) :=
  (finite_isHeatKernelPDE G).toWeak (finiteWeakHeatCertificates G)

/-- **The weak interface is inhabited by the finite model, simultaneously with the pointwise
predicate.** On every finite space with a pinned Laplace operator there is a weak heat kernel in
the sense of `IsWeakHeatKernelPDE`, namely the explicit matrix-exponential kernel, and it also
satisfies the pointwise PDE predicate `IsHeatKernelPDE`. -/
theorem finite_weak_and_pde_inhabited (G : FiniteHeatOperator X) :
    IsWeakHeatKernelPDE (finiteHeatSpacetime G)
        (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X))
        (finiteHeatKernel G) ∧
      IsHeatKernelPDE (finiteHeatSpacetime G)
        (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X))
        (finiteHeatKernel G) :=
  ⟨finite_weakHeatKernel G, finite_isHeatKernelPDE G⟩

end Poincare.D13.HeatKernelBridge
