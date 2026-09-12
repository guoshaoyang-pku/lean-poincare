/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.Basic
import Poincare.D12.HeatDomain.FlatInstance
import Poincare.D12.HeatDomain.Counterexample
import Poincare.D11.HeatKernelBridge.ZeroDimension

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D13.HeatKernelBridge.EuclideanTransport

**D13 heat-kernel bridge, part 2: the D10 Euclidean heat kernel transported to the corrected
-domain D7 interface in every dimension.**

The explicit Euclidean heat kernel of `Poincare.D10.HeatKernelEuclidean`,
`gaussianKernel n t z = (4 π t) ^ (-n/2) · exp (-‖z‖²/(4t))`, satisfies every analytic field of
the D7 interface unconditionally in every dimension `n : ℕ` (D11 `EuclideanInstance`), and its
Dirac initial condition holds against every admissible test function (D11 `InitialCondition`,
re-typed through the D12 v1 interface in `Poincare.D12.HeatDomain.FlatInstance`). This file
assembles the two pieces into the corrected-domain D7 interface:

* `flatHeatKernelDataV1_integrable n : HeatKernelDataV1 (EuclideanSpace ℝ (Fin n))` — the
  transport against the continuous-integrable class;
* `flatHeatKernelDataV1_cc n : HeatKernelDataV1 (EuclideanSpace ℝ (Fin n))` — the transport
  against the `C_c` (continuous compact support) class;

both in **every** dimension `n`, with no restriction. The transported datum carries the genuine
D10 kernel at positive times (`flatHeatKernelDataV1_integrable_kernel_eq_gaussian`), the D10 mass
normalization (`flatHeatKernelDataV1_integrable_normalization`), the Chapman–Kolmogorov semigroup
identity, and the heat equation — the D7 analytic fields, now on the corrected domain.

The precise scope of the transport is made explicit at the D7 level:

* in every **positive** dimension no *legacy* `Poincare.D7.HeatKernel.HeatKernelData` with the
  explicit Euclidean core exists (D12 `Counterexample`, `not_exists_heatKernelData_flat_of_pos`),
  while the corrected-domain V1 datum exists — `flat_v1_exists_not_legacy_of_pos`;
* in dimension `0` the full legacy datum exists (D11 `ZeroDimension`) and is re-embedded by the
  bridge — `flat_legacy_exists_zero`, `flat_v1_of_legacy_zero`.

Non-vacuity is tested concretely: the nondegenerate bump `bump n z = max 0 (1 - ‖z‖²)` has limit
`1` through the transported datum (`flatHeatKernelDataV1_cc_bump_initialCondition`).

The D10 core datum, the D11 weak-condition theorems and the D12 versioned interface are imported
and consumed exactly as they stand; nothing is re-proved and no D7/D10/D11/D12 definition is
edited.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D13.HeatKernelBridge

open Poincare.D11.HeatKernelBridge
open Poincare.D10.HeatKernelEuclidean
open Poincare.D12.HeatDomain
open HeatKernelDataV1

/-! ## The transport, integrable class -/

/-- **D10 → corrected-domain D7, integrable class, every dimension.** The explicit D10 Euclidean
heat-kernel core `flatHeatKernelCore n` together with the continuous-integrable admissible class
and the D12 re-typed weak initial condition forms a corrected-domain D7 datum
`HeatKernelDataV1 (EuclideanSpace ℝ (Fin n))` for every `n : ℕ`. -/
noncomputable def flatHeatKernelDataV1_integrable (n : ℕ) :
    HeatKernelDataV1 (EuclideanSpace ℝ (Fin n)) where
  core := flatHeatKernelCore n
  testClass := AdmissibleTestClass.continuousIntegrableClass (flatHeatKernelCore n).volume
  initialConditionFor := flatHeatKernelCore_weakInitialConditionFor_integrableClass n

/-! ## The transport, `C_c` class -/

/-- **D10 → corrected-domain D7, `C_c` class, every dimension.** The same transport against the
continuous-compact-support admissible class, directly from D11
`flatKernel_tendsto_integral_of_hasCompactSupport`. The class is stated over Lebesgue `volume`,
which is definitionally the datum's own volume. -/
noncomputable def flatHeatKernelDataV1_cc (n : ℕ) :
    HeatKernelDataV1 (EuclideanSpace ℝ (Fin n)) where
  core := flatHeatKernelCore n
  testClass := AdmissibleTestClass.continuousCompactSupportClass
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
  initialConditionFor := flatHeatKernelCore_weakInitialConditionFor_ccClass n

/-! ## Simp data and variant certificates -/

@[simp]
theorem flatHeatKernelDataV1_integrable_core (n : ℕ) :
    (flatHeatKernelDataV1_integrable n).core = flatHeatKernelCore n := rfl

@[simp]
theorem flatHeatKernelDataV1_cc_core (n : ℕ) :
    (flatHeatKernelDataV1_cc n).core = flatHeatKernelCore n := rfl

@[simp]
theorem flatHeatKernelDataV1_integrable_volume (n : ℕ) :
    (flatHeatKernelDataV1_integrable n).volume =
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := rfl

@[simp]
theorem flatHeatKernelDataV1_cc_volume (n : ℕ) :
    (flatHeatKernelDataV1_cc n).volume =
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := rfl

@[simp]
theorem flatHeatKernelDataV1_integrable_kernel (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    (flatHeatKernelDataV1_integrable n).kernel x y t = flatKernel n x y t := rfl

@[simp]
theorem flatHeatKernelDataV1_cc_kernel (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    (flatHeatKernelDataV1_cc n).kernel x y t = flatKernel n x y t := rfl

/-- The integrable-class transport is an integrable-class variant by construction. -/
theorem flatHeatKernelDataV1_integrable_integrableClassVariant (n : ℕ) :
    IsIntegrableClassVariant (flatHeatKernelDataV1_integrable n) := rfl

/-- The `C_c` transport carries the `C_c` class for Lebesgue volume, definitionally the datum's
own volume (stated over literal `volume`, as in the D12 module). -/
theorem flatHeatKernelDataV1_cc_testClass_eq_ccClass (n : ℕ) :
    (flatHeatKernelDataV1_cc n).testClass =
      AdmissibleTestClass.continuousCompactSupportClass
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := rfl

/-! ## The transported kernel is the genuine D10 kernel -/

/-- **The transported kernel is the D10 kernel.** At every positive time the kernel carried by the
corrected-domain D7 datum is the explicit D10 Gaussian kernel
`gaussianKernel n t (x - y) = (4 π t) ^ (-n/2) · exp (-‖x - y‖²/(4t))`. -/
theorem flatHeatKernelDataV1_integrable_kernel_eq_gaussian (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 < t) :
    (flatHeatKernelDataV1_integrable n).kernel x y t = gaussianKernel n t (x - y) :=
  flatKernel_of_pos n x y ht

/-- The same for the `C_c` transport. -/
theorem flatHeatKernelDataV1_cc_kernel_eq_gaussian (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 < t) :
    (flatHeatKernelDataV1_cc n).kernel x y t = gaussianKernel n t (x - y) :=
  flatKernel_of_pos n x y ht

/-! ## The D7 analytic fields of the transported datum -/

/-- Normalization of the transported datum: total mass `1` at every positive time (D10
`gaussianKernel_integral` through the D11 core). -/
theorem flatHeatKernelDataV1_integrable_normalization (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 < t) :
    ∫ y, (flatHeatKernelDataV1_integrable n).kernel x y t
      ∂(flatHeatKernelDataV1_integrable n).volume = 1 :=
  HeatKernelDataV1.normalization (flatHeatKernelDataV1_integrable n) x ht

/-- Chapman–Kolmogorov semigroup identity of the transported datum (D10
`gaussianKernel_convolution` through the D11 core). -/
theorem flatHeatKernelDataV1_integrable_semigroup (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (flatHeatKernelDataV1_integrable n).kernel x y (s + t)
      = ∫ z, (flatHeatKernelDataV1_integrable n).kernel x z s *
          (flatHeatKernelDataV1_integrable n).kernel z y t
        ∂(flatHeatKernelDataV1_integrable n).volume :=
  HeatKernelDataV1.semigroup (flatHeatKernelDataV1_integrable n) x y hs ht

/-- Heat equation of the transported datum at every positive time (D10
`hasDerivAt_gaussianKernel` / `laplacian_gaussianKernel` through the D11 core). -/
theorem flatHeatKernelDataV1_integrable_heatEquation (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (flatHeatKernelDataV1_integrable n).kernel x y s)
      ((flatHeatKernelDataV1_integrable n).laplacian
        (fun z => (flatHeatKernelDataV1_integrable n).kernel z y t) x) t :=
  HeatKernelDataV1.heatEquation (flatHeatKernelDataV1_integrable n) x y ht

/-- Gaussian upper bound of the transported datum. -/
theorem flatHeatKernelDataV1_integrable_gaussianUpperBound (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 < t) :
    (flatHeatKernelDataV1_integrable n).kernel x y t ≤
      (flatHeatKernelDataV1_integrable n).C_up * t ^ (-((flatHeatKernelDataV1_integrable n).dim / 2)) *
        Real.exp (-((flatHeatKernelDataV1_integrable n).dist x y) ^ 2 /
          ((flatHeatKernelDataV1_integrable n).c_up * t)) :=
  HeatKernelDataV1.gaussianUpperBound (flatHeatKernelDataV1_integrable n) x y ht

/-- The corrected initial condition of the transported datum against the integrable class (D12
`flatHeatKernelCore_weakInitialConditionFor_integrableClass`). -/
theorem flatHeatKernelDataV1_integrable_initialCondition (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Continuous f) (hfi : Integrable f volume) :
    Tendsto (fun t : ℝ => ∫ y, (flatHeatKernelDataV1_integrable n).kernel x y t * f y)
      (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  exact (flatHeatKernelDataV1_integrable n).initialConditionFor x f ⟨hf, hfi⟩

/-- The corrected initial condition of the transported datum against the `C_c` class (D12
`flatHeatKernelCore_weakInitialConditionFor_ccClass`). -/
theorem flatHeatKernelDataV1_cc_initialCondition (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Continuous f) (hfs : HasCompactSupport f) :
    Tendsto (fun t : ℝ => ∫ y, (flatHeatKernelDataV1_cc n).kernel x y t * f y)
      (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  exact (flatHeatKernelDataV1_cc n).initialConditionFor x f ⟨hf, hfs⟩

/-! ## Non-vacuity of the transported condition -/

/-- **Non-vacuity, through the transported datum.** The nondegenerate compactly supported bump
`bump n z = max 0 (1 - ‖z‖²)` converges to `bump n 0 = 1` (a nonzero limit value) through the
`C_c` transport at `x = 0`; the corrected-domain interface is inhabited by a nondegenerate test
function and the asserted limit is not the trivial zero statement. -/
theorem flatHeatKernelDataV1_cc_bump_initialCondition (n : ℕ) :
    Tendsto (fun t : ℝ => ∫ y : EuclideanSpace ℝ (Fin n),
        (flatHeatKernelDataV1_cc n).kernel 0 y t * bump n y
          ∂(flatHeatKernelDataV1_cc n).volume)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  simpa [bump_zero n] using
    (flatHeatKernelDataV1_cc n).initialConditionFor 0 (bump n) (bump_mem_ccClass n)

/-! ## The precise scope: corrected-domain datum in every dimension, legacy datum only in
dimension 0 -/

/-- **In every positive dimension the corrected-domain V1 datum exists while no legacy D7 datum
with the explicit Euclidean core exists.** This is the exact content of the transport: for the
flat kernel the corrected admissible-test-function domain is the *only* D7-level interface
available in positive dimension, and the bridge supplies its inhabitant in every dimension. -/
theorem flat_v1_exists_not_legacy_of_pos (n : ℕ) (hn : 0 < n) :
    (∃ D : HeatKernelDataV1 (EuclideanSpace ℝ (Fin n)), D.toCore = flatHeatKernelCore n) ∧
      ¬ ∃ D : Poincare.D7.HeatKernel.HeatKernelData (EuclideanSpace ℝ (Fin n)),
        D.toCore = flatHeatKernelCore n := by
  constructor
  · exact ⟨flatHeatKernelDataV1_integrable n, rfl⟩
  · exact not_exists_heatKernelData_flat_of_pos n hn

/-- **Dimension 0: the full legacy datum exists** (D11 `ZeroDimension.flatHeatKernelData_zero`). -/
theorem flat_legacy_exists_zero :
    ∃ D : Poincare.D7.HeatKernel.HeatKernelData (EuclideanSpace ℝ (Fin 0)),
      D.toCore = flatHeatKernelCore 0 :=
  ⟨flatHeatKernelData_zero, flatHeatKernelData_zero_toCore⟩

/-- In dimension 0 the legacy datum re-embeds into the corrected-domain interface. -/
theorem flat_v1_of_legacy_zero :
    (ofHeatKernelData flatHeatKernelData_zero).core = flatHeatKernelCore 0 := by
  simp [ofHeatKernelData_core, flatHeatKernelData_zero_toCore]

end Poincare.D13.HeatKernelBridge
