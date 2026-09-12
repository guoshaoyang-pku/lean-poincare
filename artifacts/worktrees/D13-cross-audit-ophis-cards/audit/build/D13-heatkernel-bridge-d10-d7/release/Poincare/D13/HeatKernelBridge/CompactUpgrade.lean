/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.Basic
import Poincare.D12.HeatDomain.CompactCompatibility

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D13.HeatKernelBridge.CompactUpgrade

**D13 heat-kernel bridge, part 3: upgrading corrected-domain data to the legacy D7 interface in
the compact finite-measure scope.**

The legacy D7 literal initial condition (over *all* continuous test functions) is exactly right on
a compact space with a finite reference measure: every continuous function is then automatically
bounded, hence integrable (`Poincare.D12.HeatDomain.continuous_integrable_of_compactSpace_finiteMeasure`),
so the corrected admissible-test-function condition and the legacy condition coincide (the three
D12 compatibility equivalences). This module makes the transport *to the D7 `HeatKernelData`
interface* explicit:

* `toHeatKernelData_of_integrableClass`: a corrected-domain V1 datum whose class is the
  continuous-integrable class upgrades to a genuine legacy `Poincare.D7.HeatKernel.HeatKernelData`
  on any compact space with finite volume — through the unchanged D11 bridge map
  `HeatKernelCore.toHeatKernelData` and the D12 compatibility equivalence;
* `toHeatKernelData_of_ccClass`: the same for a `C_c`-class V1 datum (measures finite on compacts
  are finite on a compact space), via the D12 `C_c` compatibility equivalence.

The upgrade is a construction, not a proposition: it produces the legacy datum, forgets back to the
original core (`..._toCore`), carries the legacy literal initial condition
(`..._initialCondition`), and is a left inverse to the legacy embedding `ofHeatKernelData` in this
scope (`ofHeatKernelData_upgrade_eq`): on compact finite-measure spaces the corrected-domain
interface and the legacy D7 interface carry exactly the same data.

This is the sense in which the bridge transports D10 to the **D7 `HeatKernelData` interface**:
the corrected domain is needed only where the legacy quantifier is overstrong (noncompact spaces
such as `ℝⁿ`); on the intended closed (compact) manifold setting, whose Riemannian volume is
finite, the corrected-domain datum *is* a legacy D7 datum.

The legacy D7/D11/D12 definitions are imported and consumed, never edited.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D13.HeatKernelBridge

open Poincare.D11.HeatKernelBridge
open Poincare.D12.HeatDomain
open HeatKernelDataV1

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-! ## The upgrade construction, integrable class -/

/-- **Corrected-domain datum → legacy D7 datum, integrable class, compact finite-measure scope.**
A V1 datum whose admissible class is the continuous-integrable class upgrades to a genuine
`Poincare.D7.HeatKernel.HeatKernelData` on a compact space with finite reference measure: the
versioned condition is D11's weak condition (D12 `iff_integrableClass`), and weak = full in this
scope (D12 `weakInitialCondition_iff_full_of_compact_finiteMeasure`). -/
noncomputable def toHeatKernelData_of_integrableClass [CompactSpace X] [OpensMeasurableSpace X]
    (D : HeatKernelDataV1 X) [IsFiniteMeasure D.core.volume]
    (hC : D.IsIntegrableClassVariant) : Poincare.D7.HeatKernel.HeatKernelData X := by
  have hIC : WeakInitialConditionFor D.core
      (AdmissibleTestClass.continuousIntegrableClass D.core.volume) :=
    hC ▸ D.initialConditionFor
  exact Poincare.D12.HeatDomain.toHeatKernelData_of_weak_compact_finiteMeasure (D := D.core)
    ((WeakInitialConditionFor.iff_integrableClass (D := D.core)).mpr hIC)

/-- The upgrade forgets back to the original core. -/
@[simp]
theorem toHeatKernelData_of_integrableClass_toCore [CompactSpace X] [OpensMeasurableSpace X]
    (D : HeatKernelDataV1 X) [IsFiniteMeasure D.core.volume]
    (hC : D.IsIntegrableClassVariant) :
    (toHeatKernelData_of_integrableClass (D := D) hC).toCore = D.core := by
  simp [toHeatKernelData_of_integrableClass]

/-- The upgraded datum carries the legacy literal initial condition (its D7 field). -/
theorem toHeatKernelData_of_integrableClass_initialCondition [CompactSpace X]
    [OpensMeasurableSpace X] (D : HeatKernelDataV1 X) [IsFiniteMeasure D.core.volume]
    (hC : D.IsIntegrableClassVariant) (x : X) (f : X → ℝ) (hf : Continuous f) :
    Tendsto (fun t : ℝ => ∫ y, (toHeatKernelData_of_integrableClass (D := D) hC).kernel x y t * f y
        ∂(toHeatKernelData_of_integrableClass (D := D) hC).volume) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) :=
  (toHeatKernelData_of_integrableClass (D := D) hC).initialCondition x f hf

/-! ## The upgrade construction, `C_c` class -/

/-- **Corrected-domain datum → legacy D7 datum, `C_c` class, compact scope.** A V1 datum whose
admissible class is the `C_c` class upgrades to a genuine legacy D7 datum on a compact space: a
measure finite on compacts is finite on the compact whole space, and in that scope the `C_c`
versioned condition is the legacy full condition (D12
`weakInitialConditionFor_ccClass_iff_full_of_compact_finiteMeasure`). -/
noncomputable def toHeatKernelData_of_ccClass [CompactSpace X] [OpensMeasurableSpace X]
    (D : HeatKernelDataV1 X) [IsFiniteMeasureOnCompacts D.core.volume]
    (hC : D.testClass = AdmissibleTestClass.continuousCompactSupportClass D.core.volume) :
    Poincare.D7.HeatKernel.HeatKernelData X := by
  haveI : IsFiniteMeasure D.core.volume :=
    ⟨(inferInstance : IsFiniteMeasureOnCompacts D.core.volume).lt_top_of_isCompact isCompact_univ⟩
  have hIC : WeakInitialConditionFor D.core
      (AdmissibleTestClass.continuousCompactSupportClass D.core.volume) :=
    hC ▸ D.initialConditionFor
  have hfull : D.core.FullInitialCondition :=
    (weakInitialConditionFor_ccClass_iff_full_of_compact_finiteMeasure (D := D.core)).mp hIC
  exact D.core.toHeatKernelData hfull

/-- The `C_c` upgrade forgets back to the original core. -/
@[simp]
theorem toHeatKernelData_of_ccClass_toCore [CompactSpace X] [OpensMeasurableSpace X]
    (D : HeatKernelDataV1 X) [IsFiniteMeasureOnCompacts D.core.volume]
    (hC : D.testClass = AdmissibleTestClass.continuousCompactSupportClass D.core.volume) :
    (toHeatKernelData_of_ccClass (D := D) hC).toCore = D.core := by
  simp [toHeatKernelData_of_ccClass]

/-- The `C_c` upgraded datum carries the legacy literal initial condition (its D7 field). -/
theorem toHeatKernelData_of_ccClass_initialCondition [CompactSpace X] [OpensMeasurableSpace X]
    (D : HeatKernelDataV1 X) [IsFiniteMeasureOnCompacts D.core.volume]
    (hC : D.testClass = AdmissibleTestClass.continuousCompactSupportClass D.core.volume)
    (x : X) (f : X → ℝ) (hf : Continuous f) :
    Tendsto (fun t : ℝ => ∫ y, (toHeatKernelData_of_ccClass (D := D) hC).kernel x y t * f y
        ∂(toHeatKernelData_of_ccClass (D := D) hC).volume) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) :=
  (toHeatKernelData_of_ccClass (D := D) hC).initialCondition x f hf

/-! ## Round trip: legacy embedding and upgrade are inverse in the compact finite-measure scope -/

/-- **The upgrade is a left inverse of the legacy embedding.** In the compact finite-measure scope,
embedding a legacy D7 datum into the corrected-domain interface and upgrading again recovers the
original datum: the corrected-domain interface carries exactly the same data as the legacy D7
interface there. (The finiteness hypothesis is stated for `D.toCore.volume`, definitionally the
same measure as `D.volume`.) -/
theorem ofHeatKernelData_upgrade_eq [CompactSpace X] [OpensMeasurableSpace X]
    (D : Poincare.D7.HeatKernel.HeatKernelData X) [IsFiniteMeasure D.toCore.volume] :
    toHeatKernelData_of_integrableClass (D := ofHeatKernelData D)
        (ofHeatKernelData_integrableClassVariant D) = D := by
  conv_rhs =>
    rw [← Poincare.D11.HeatKernelBridge.HeatKernelCore.toCore_toHeatKernelData D]
  change D.toCore.toHeatKernelData _ = D.toCore.toHeatKernelData _
  congr 1

/-- **Data-level existence is equivalent in the compact finite-measure scope.** For a fixed bridge
core on a compact space with finite reference measure, the existence of a corrected-domain V1 datum
with that core (integrable-class variant) is *equivalent* to the existence of a legacy D7
`HeatKernelData` with that core: the forward direction is the upgrade construction, the backward
direction is the legacy embedding. This is the existential form of the statement that the corrected
domain loses nothing on the intended closed-manifold setting. -/
theorem exists_v1_iff_exists_legacy {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [CompactSpace X] [OpensMeasurableSpace X]
    (core : Poincare.D11.HeatKernelBridge.HeatKernelCore X) [IsFiniteMeasure core.volume] :
    (∃ D : HeatKernelDataV1 X, D.toCore = core ∧ D.IsIntegrableClassVariant) ↔
      (∃ D : Poincare.D7.HeatKernel.HeatKernelData X, D.toCore = core) := by
  constructor
  · rintro ⟨D, hcore, hC⟩
    obtain rfl : core = D.core := by simpa using hcore.symm
    exact ⟨toHeatKernelData_of_integrableClass (D := D) hC,
      toHeatKernelData_of_integrableClass_toCore (D := D) hC⟩
  · rintro ⟨D, hcore⟩
    exact ⟨ofHeatKernelData D, by simpa using hcore,
      ofHeatKernelData_integrableClassVariant D⟩

end Poincare.D13.HeatKernelBridge
