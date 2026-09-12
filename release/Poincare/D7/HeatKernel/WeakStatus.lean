/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.WeakHeatEquation
import Poincare.D13.HeatKernelBridge.WeakFinite

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D7.HeatKernel.WeakStatus

**D7-namespaced consumer of the D13 weak (test-paired) heat-equation bridge.**

This module records, at the D7 level, what the D13 companion note `WeakHeatEquation.lean` proved:
the heat equation of the D7 heat-kernel interfaces is consumed downstream in its *weak* form,
paired against the corrected admissible-test-function domain of D12. No existing D7 file is
edited; this is a new consumer module.

* `HeatKernelData.toHeatSpacetime`: the schematic spacetime datum attached to a legacy D7
  `HeatKernelData` (the unused `timeDerivative` field is set to `0`);
* `heatKernelData_weakHeatEquation`: **every legacy D7 heat-kernel datum satisfies the weak heat
  equation on every admissible test class on which the analytic certificates hold**, directly from
  its `heatEquation` field and mathlib's dominated differentiation under the integral sign. The
  certificates (snapshot measurability/integrability, paired-Laplacian measurability and local
  boundedness) are the explicit manifold-side analytic input; they are hypotheses of this theorem,
  not axioms;
* `heatKernelDataV1_weakHeatEquation`: the same for the corrected-domain bridge datum
  `HeatKernelDataV1`, from its D11 core `heatEquation`;
* `flat_weakHeatEquation_integrable` / `flat_weakHeatEquation_cc`: the D10 Euclidean kernel
  inhabits the weak equation in every dimension on both standard admissible classes (the
  certificates are *proved* there);
* `flat_weak_and_snapshot_refuted`: the weak equation is aligned with the repaired PDE predicate
  and not with the defective D7 snapshot field — in positive dimension the flat kernel satisfies
  the weak equation while `IsHeatKernelV1` is refuted for it;
* `finite_weakHeatEquation`: the pinned finite model (the second, non-flat model of the interface)
  satisfies the weak equation over the counting measure;
* `weak_status_summary`: the D7-level conjunction of the above.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D7.HeatKernel

open Poincare.D11.HeatKernelBridge
open Poincare.D12.HeatDomain
open Poincare.D13.HeatKernelBridge

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- **The schematic spacetime datum attached to a legacy D7 heat-kernel datum.** The volume,
Laplacian, distance and dimension are those of the datum; the `timeDerivative` field (which the
weak equation does not use, and which cannot represent `∂_t` on functions of the space variable) is
set to `0`. -/
noncomputable def HeatKernelData.toHeatSpacetime (D : HeatKernelData X) : HeatSpacetime X where
  volume := D.volume
  laplacian := D.laplacian
  timeDerivative := 0
  dist := D.dist
  dim := D.dim

@[simp]
theorem HeatKernelData.toHeatSpacetime_volume (D : HeatKernelData X) :
    D.toHeatSpacetime.volume = D.volume := rfl

@[simp]
theorem HeatKernelData.toHeatSpacetime_laplacian (D : HeatKernelData X) :
    D.toHeatSpacetime.laplacian = D.laplacian := rfl

@[simp]
theorem HeatKernelData.toHeatSpacetime_timeDerivative (D : HeatKernelData X) :
    D.toHeatSpacetime.timeDerivative = 0 := rfl

@[simp]
theorem HeatKernelData.toHeatSpacetime_dist (D : HeatKernelData X) :
    D.toHeatSpacetime.dist = D.dist := rfl

@[simp]
theorem HeatKernelData.toHeatSpacetime_dim (D : HeatKernelData X) :
    D.toHeatSpacetime.dim = D.dim := rfl

/-- **The legacy D7 heat-kernel datum satisfies the weak heat equation on the corrected
admissible-test-function domain.** The proof is the pointwise `heatEquation` field of the D7
structure fed into the D13 transfer `weakHeatKernelPDE_of_hasDerivAt`; the analytic certificates
are the explicit hypotheses. -/
theorem heatKernelData_weakHeatEquation (D : HeatKernelData X)
    (C : AdmissibleTestClass X D.volume)
    (hc : WeakHeatCertificates D.toHeatSpacetime C D.kernel) :
    IsWeakHeatKernelPDE D.toHeatSpacetime C D.kernel :=
  weakHeatKernelPDE_of_hasDerivAt (fun x y t ht => D.heatEquation x y t ht) hc

/-- **The corrected-domain bridge datum satisfies the weak heat equation.** For a
`HeatKernelDataV1` datum the pointwise PDE is the D11 core `heatEquation` field; the weak equation
follows on any admissible class on which the certificates hold. -/
theorem heatKernelDataV1_weakHeatEquation (D : HeatKernelDataV1 X)
    (C : AdmissibleTestClass X D.volume)
    (hc : WeakHeatCertificates D.toHeatSpacetime C D.kernel) :
    IsWeakHeatKernelPDE D.toHeatSpacetime C D.kernel :=
  weakHeatKernelPDE_of_hasDerivAt (fun x y t ht => D.core.heatEquation x y t ht) hc

/-- **The flat D10 kernel in weak form** (continuous-integrable class), re-exported at the D7
level. -/
theorem flat_weakHeatEquation_integrable (n : ℕ) :
    IsWeakHeatKernelPDE (flatHeatSpacetime n)
      (AdmissibleTestClass.continuousIntegrableClass (flatHeatSpacetime n).volume)
      (flatKernel n) :=
  flat_weakHeatKernel_integrable n

/-- **The flat D10 kernel in weak form** (`C_c` class), re-exported at the D7 level. -/
theorem flat_weakHeatEquation_cc (n : ℕ) :
    IsWeakHeatKernelPDE (flatHeatSpacetime n)
      (AdmissibleTestClass.continuousCompactSupportClass
        (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (flatKernel n) :=
  flat_weakHeatKernel_cc n

/-- **The weak equation is aligned with the repaired predicate, not with the defective snapshot
field.** In every positive dimension the D10 kernel satisfies the weak heat equation on the
corrected admissible domain while the legacy snapshot predicate `IsHeatKernelV1` is refuted by the
same kernel on the same flat spacetime. -/
theorem flat_weak_and_snapshot_refuted (n : ℕ) (hn : 0 < n) :
    IsWeakHeatKernelPDE (flatHeatSpacetime n)
        (AdmissibleTestClass.continuousIntegrableClass (flatHeatSpacetime n).volume)
        (flatKernel n) ∧
      ¬ IsHeatKernelV1 (flatHeatSpacetime n)
        (AdmissibleTestClass.continuousIntegrableClass (flatHeatSpacetime n).volume)
        (flatKernel n) :=
  flat_weak_snapshot_refuted n hn

/-- **D7-level status summary.** The legacy interface's pointwise heat equation transfers to the
weak equation on the corrected domain, the D10 Euclidean kernel inhabits the weak equation in every
dimension on both standard classes, and in positive dimension it does so while the legacy snapshot
predicate is refuted. -/
theorem weak_status_summary (n : ℕ) (hn : 0 < n) :
    (∀ {X : Type*} [TopologicalSpace X] [MeasurableSpace X] (D : HeatKernelData X)
        (C : AdmissibleTestClass X D.volume),
        WeakHeatCertificates D.toHeatSpacetime C D.kernel →
        IsWeakHeatKernelPDE D.toHeatSpacetime C D.kernel) ∧
      IsWeakHeatKernelPDE (flatHeatSpacetime n)
        (AdmissibleTestClass.continuousIntegrableClass (flatHeatSpacetime n).volume)
        (flatKernel n) ∧
      IsWeakHeatKernelPDE (flatHeatSpacetime n)
        (AdmissibleTestClass.continuousCompactSupportClass
          (volume : Measure (EuclideanSpace ℝ (Fin n))))
        (flatKernel n) ∧
      ¬ IsHeatKernelV1 (flatHeatSpacetime n)
        (AdmissibleTestClass.continuousIntegrableClass (flatHeatSpacetime n).volume)
        (flatKernel n) :=
  ⟨fun D C hc => heatKernelData_weakHeatEquation D C hc,
    flat_weakHeatKernel_integrable n, flat_weakHeatKernel_cc n,
    (flat_weak_snapshot_refuted n hn).2⟩

/-- **The pinned finite model satisfies the weak heat equation on the corrected domain.** For every
finite space with a pinned Laplace operator the explicit matrix-exponential kernel inhabits
`IsWeakHeatKernelPDE` over the counting measure; the certificates are proved by finite-dimensional
arguments in `Poincare.D13.HeatKernelBridge.WeakFinite`. This is the second, non-flat model of the
weak interface. -/
theorem finite_weakHeatEquation {X : Type*} [Fintype X] [DecidableEq X] [TopologicalSpace X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (G : FiniteHeatOperator X) :
    IsWeakHeatKernelPDE (finiteHeatSpacetime G)
      (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X))
      (finiteHeatKernel G) :=
  finite_weakHeatKernel G

end Poincare.D7.HeatKernel
