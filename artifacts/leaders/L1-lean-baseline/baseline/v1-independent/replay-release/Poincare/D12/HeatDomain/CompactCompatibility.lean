/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-heat-domain-repair)
-/

import Poincare.D12.HeatDomain.TestFunction
import Poincare.D7.HeatKernel.Instance
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D12.HeatDomain.CompactCompatibility

**D12 heat-domain repair, part 3: precisely scoped compatibility for compact finite-measure
settings.**

The D7 literal field `initialCondition` (quantifying over *all* continuous test functions) is
overstrong on noncompact Euclidean space (see `Counterexample.lean`). This module proves the
precise scope in which the legacy statement is *correct*: on a compact space with a finite
reference measure every continuous function is automatically bounded and hence integrable, so the
repaired weak condition (v1, integrable class) and the legacy full condition coincide, and both
coincide with the `C_c` version — on a compact space every continuous function has compact support.

Consequences proved here:

* `weakInitialCondition_iff_full_of_compact_finiteMeasure`: `D.WeakInitialCondition ↔
  D.FullInitialCondition` for any bridge core `D` on a compact space with finite `D.volume`;
* the same for the versioned v1 interface (integrable class and `C_c` class);
* a downstream construction `toHeatKernelData_of_weak_compact_finiteMeasure` that upgrades a core
  satisfying the versioned weak condition to a genuine legacy `Poincare.D7.HeatKernel.HeatKernelData`
  *without changing any D7 definition* — the legacy interface is kept unchanged and is justified in
  exactly this scope (which covers the intended compact-manifold applications, whose Riemannian
  volume is finite);
* the legacy D7 one-point instance `punitHeatKernelData` is checked against the compatibility
  theorem as a concrete compact finite-measure example.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D12.HeatDomain

open Poincare.D11.HeatKernelBridge

/-! ## Continuous functions on compact finite-measure spaces are integrable -/

/-- **Every continuous real-valued function on a compact space is integrable for a finite
measure.** Boundedness comes from compactness (`BoundedContinuousFunction.mkOfCompact`),
integrability from boundedness and finiteness of the measure
(`BoundedContinuousFunction.integrable`). This is the one expanded regularity hypothesis that makes
the legacy D7 field sound: it is automatic in the compact finite-measure scope and fails in the
noncompact scope (see `Counterexample.lean`). -/
theorem continuous_integrable_of_compactSpace_finiteMeasure {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} (hf : Continuous f) : Integrable f μ :=
  BoundedContinuousFunction.integrable μ (BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩)

/-! ## The legacy full condition and the repaired weak condition coincide -/

/-- **Precisely scoped compatibility.** On a compact space with finite reference measure, D11's
weak (distributional) initial condition and the literal D7 full initial condition are equivalent:
every continuous test function is integrable, so the extra hypothesis of the weak form is automatic.
The D7 legacy definition is therefore exactly right in the compact finite-measure setting, and only
there; `Counterexample.lean` shows the failure of the full condition on noncompact Euclidean space
in every positive dimension. -/
theorem weakInitialCondition_iff_full_of_compact_finiteMeasure {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {D : HeatKernelCore X} [IsFiniteMeasure D.volume] :
    D.WeakInitialCondition ↔ D.FullInitialCondition := by
  constructor
  · intro h x f hf
    exact h x f hf (continuous_integrable_of_compactSpace_finiteMeasure D.volume hf)
  · exact HeatKernelCore.WeakInitialCondition.of_full

/-- The versioned v1 interface (continuous-integrable class) is equivalent to the legacy full
condition in the compact finite-measure scope. -/
theorem weakInitialConditionFor_integrableClass_iff_full_of_compact_finiteMeasure
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {D : HeatKernelCore X} [IsFiniteMeasure D.volume] :
    WeakInitialConditionFor D (AdmissibleTestClass.continuousIntegrableClass D.volume) ↔
      D.FullInitialCondition := by
  rw [← WeakInitialConditionFor.iff_integrableClass,
    weakInitialCondition_iff_full_of_compact_finiteMeasure (D := D)]

/-- **On a compact space every continuous function has compact support** (its support is closed in
the compact space). So on compact spaces the `C_c` class is exactly the class of all continuous
functions. -/
theorem ccClass_cls_iff_continuous_of_compactSpace {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) :
    (AdmissibleTestClass.continuousCompactSupportClass μ).cls f ↔ Continuous f := by
  constructor
  · exact fun h => h.1
  · intro hf
    exact ⟨hf, (isClosed_tsupport f).isCompact⟩

/-- The versioned v1 interface (`C_c` class) is equivalent to the legacy full condition in the
compact finite-measure scope: on a compact space the `C_c` class is all continuous functions, so
the three conditions (full, weak-integrable, weak-`C_c`) coincide. -/
theorem weakInitialConditionFor_ccClass_iff_full_of_compact_finiteMeasure
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {D : HeatKernelCore X} [IsFiniteMeasure D.volume] :
    WeakInitialConditionFor D (AdmissibleTestClass.continuousCompactSupportClass D.volume) ↔
      D.FullInitialCondition := by
  constructor
  · intro h x f hf
    exact h x f ((ccClass_cls_iff_continuous_of_compactSpace D.volume f).mpr hf)
  · intro hfull x f hf
    exact hfull x f hf.1

/-! ## Downstream use: upgrading to the legacy D7 datum in the compact finite-measure scope -/

/-- **Downstream construction.** In the compact finite-measure scope, a bridge core satisfying the
repaired (versioned) weak initial condition produces a genuine legacy
`Poincare.D7.HeatKernel.HeatKernelData` through the unchanged D11 bridge map `toHeatKernelData`.
The legacy D7 definition is consumed downstream exactly as it stands; nothing in D7 or D11 was
edited. -/
noncomputable def toHeatKernelData_of_weak_compact_finiteMeasure {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {D : HeatKernelCore X} [IsFiniteMeasure D.volume] (h : D.WeakInitialCondition) :
    Poincare.D7.HeatKernel.HeatKernelData X :=
  D.toHeatKernelData ((weakInitialCondition_iff_full_of_compact_finiteMeasure (D := D)).mp h)

/-- The upgraded datum forgets back to the original core. -/
@[simp]
theorem toHeatKernelData_of_weak_compact_finiteMeasure_toCore {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {D : HeatKernelCore X} [IsFiniteMeasure D.volume] (h : D.WeakInitialCondition) :
    (toHeatKernelData_of_weak_compact_finiteMeasure (D := D) h).toCore = D := rfl

/-- The upgraded datum carries the legacy literal initial condition (its D7 field), which in this
scope is the same statement as the weak condition it came from. -/
theorem toHeatKernelData_of_weak_compact_finiteMeasure_initialCondition {X : Type*}
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {D : HeatKernelCore X} [IsFiniteMeasure D.volume] (h : D.WeakInitialCondition)
    (x : X) (f : X → ℝ) (hf : Continuous f) :
    Tendsto (fun t : ℝ =>
        ∫ y, (toHeatKernelData_of_weak_compact_finiteMeasure (D := D) h).kernel x y t * f y
          ∂(toHeatKernelData_of_weak_compact_finiteMeasure (D := D) h).volume)
      (𝓝[>] (0 : ℝ)) (𝓝 (f x)) :=
  (toHeatKernelData_of_weak_compact_finiteMeasure (D := D) h).initialCondition x f hf

/-! ## Concrete compact finite-measure check on the legacy D7 instance -/

universe u

/-- The legacy D7 one-point datum (Dirac measure on the compact space `PUnit`) satisfies the
compatibility: its core's weak and full initial conditions coincide. This exercises the scoped
compatibility theorem on an existing D7 object rather than on an ad hoc one. -/
theorem punitHeatKernelData_core_weak_iff_full :
    (Poincare.D7.HeatKernel.punitHeatKernelData.{u}.toCore : HeatKernelCore.{u} PUnit.{u + 1}).WeakInitialCondition ↔
      (Poincare.D7.HeatKernel.punitHeatKernelData.{u}.toCore : HeatKernelCore.{u} PUnit.{u + 1}).FullInitialCondition := by
  haveI : IsFiniteMeasure (Poincare.D7.HeatKernel.punitHeatKernelData.{u}.toCore).volume := by
    change IsFiniteMeasure (Measure.dirac PUnit.unit)
    infer_instance
  exact weakInitialCondition_iff_full_of_compact_finiteMeasure
    (D := Poincare.D7.HeatKernel.punitHeatKernelData.{u}.toCore)

/-- The legacy D7 one-point datum is recovered from its core by the compact finite-measure
downstream construction applied to the weak condition it provably satisfies. -/
theorem punitHeatKernelData_toCore_weakInitialCondition :
    (Poincare.D7.HeatKernel.punitHeatKernelData.toCore).WeakInitialCondition :=
  HeatKernelCore.WeakInitialCondition.of_full
    (Poincare.D7.HeatKernel.punitHeatKernelData.toCore_fullInitialCondition)

end Poincare.D12.HeatDomain
