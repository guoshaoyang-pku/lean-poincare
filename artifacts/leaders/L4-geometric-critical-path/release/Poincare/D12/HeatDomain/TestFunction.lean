/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-heat-domain-repair)
-/

import Poincare.D11.HeatKernelBridge.Basic

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D12.HeatDomain.TestFunction

**D12 heat-domain repair, part 1: the versioned admissible-test-function interface (v1).**

The D7 interface (`Poincare.D7.HeatKernel.HeatKernelData.initialCondition`) and its D11 isolation
(`Poincare.D11.HeatKernelBridge.HeatKernelCore.FullInitialCondition`) quantify over *every*
continuous test function. On noncompact Euclidean space this is overstrong: the Bochner integral of
a non-integrable integrand is `0`, so a continuous test function growing faster than every Gaussian
makes the integral vanish identically while `f x ≠ 0`. This module defines the repair: a *versioned*
interface that only ever tests against an **admissible test-function class** — a class of functions
that is certified continuous and integrable for the datum's own reference measure.

The two standard classes are

* `continuousCompactSupportClass` (`C_c`): `Continuous f ∧ HasCompactSupport f` — the classical
  distributional test class (v1);
* `continuousIntegrableClass`: `Continuous f ∧ Integrable f μ` — the explicitly suitable integrable
  class (v1).

Both classes are *admissible*: membership is a pair of certificates of continuity and
integrability, so the weak initial condition stated against a class is well typed (the integrand is
well defined for every member) without assuming the D7/D11 `FullInitialCondition` anywhere.

The legacy definitions (`HeatKernelData`, `HeatKernelCore`, `FullInitialCondition`,
`WeakInitialCondition`) are left completely unchanged; the versioned condition
`WeakInitialConditionFor` is proved equivalent to D11's `WeakInitialCondition` for the integrable
class, and `CompactCompatibility.lean` proves that on compact finite-measure spaces the versioned
condition coincides with the legacy full condition.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D12.HeatDomain

/-- The version tag of the D12 admissible-test-function interface. Bump this only in a *new*
versioned definition; the v1 definitions below keep their names and the legacy D7/D11 definitions
are never edited. -/
def AdmissibleTestClass.v1 : ℕ := 1

/-- **An admissible test-function class (v1).** A class `cls` of real-valued test functions on `X`
together with certificates that every member is continuous and integrable for the reference measure
`μ`. Continuity and integrability are exactly the two hypotheses needed for the weak initial
condition to be a well-posed statement about Bochner integrals, and they are exactly what the D7
literal field over-requires (it demands the statement for *all* continuous functions, integrable or
not). -/
structure AdmissibleTestClass (X : Type*) [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) where
  /-- The class of admissible test functions. -/
  cls : (X → ℝ) → Prop
  /-- Every admissible test function is continuous. -/
  cls_continuous : ∀ ⦃f : X → ℝ⦄, cls f → Continuous f
  /-- Every admissible test function is integrable for the reference measure. -/
  cls_integrable : ∀ ⦃f : X → ℝ⦄, cls f → Integrable f μ

namespace AdmissibleTestClass

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] {μ : Measure X}

/-- **The continuous-compact-support class** `C_c` (v1). Continuity is the first certificate,
integrability follows from compact support for measures that are finite on compacts (the standard
hypothesis, satisfied by Lebesgue measure on Euclidean space and by every finite measure). -/
def continuousCompactSupportClass (μ : Measure X) [OpensMeasurableSpace X]
    [IsFiniteMeasureOnCompacts μ] : AdmissibleTestClass X μ where
  cls := fun f => Continuous f ∧ HasCompactSupport f
  cls_continuous := fun f hf => hf.1
  cls_integrable := fun f hf => hf.1.integrable_of_hasCompactSupport hf.2

/-- **The continuous-integrable class** (v1). The explicitly suitable integrable class used by the
D11 weak initial condition: the certificates are exactly the two hypotheses of
`HeatKernelCore.WeakInitialCondition`. -/
def continuousIntegrableClass (μ : Measure X) : AdmissibleTestClass X μ where
  cls := fun f => Continuous f ∧ Integrable f μ
  cls_continuous := fun f hf => hf.1
  cls_integrable := fun f hf => hf.2

variable [OpensMeasurableSpace X] [IsFiniteMeasureOnCompacts μ]

/-- Every continuous compactly supported function is a member of the continuous-integrable class:
`C_c` is an admissible subclass of the integrable class (v1). -/
theorem continuousCompactSupportClass_subset_continuousIntegrableClass (f : X → ℝ) :
    (continuousCompactSupportClass μ).cls f → (continuousIntegrableClass μ).cls f := by
  intro hf
  exact ⟨hf.1, hf.1.integrable_of_hasCompactSupport hf.2⟩

/-- The integrable class is inhabited: the zero function is continuous and integrable. (Non-vacuity
of the *initial condition* itself is tested in `FlatInstance.lean` with a nondegenerate compactly
supported bump function.) -/
theorem continuousIntegrableClass_inhabited : ∃ f : X → ℝ, (continuousIntegrableClass μ).cls f :=
  ⟨0, continuous_zero, integrable_zero (ε' := ℝ) (μ := μ)⟩

end AdmissibleTestClass

/-- **The versioned weak initial condition (v1).** A core datum `D` converges to the Dirac delta
against every function of an admissible test class `C` for the datum's own volume. This is the D12
repair of the overstrong D7 field: the test-function domain is part of the statement, certified
continuous and integrable, instead of the free quantifier `∀ f, Continuous f`. -/
def WeakInitialConditionFor {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (D : Poincare.D11.HeatKernelBridge.HeatKernelCore X)
    (C : AdmissibleTestClass X D.volume) : Prop :=
  ∀ (x : X) (f : X → ℝ), C.cls f →
    Tendsto (fun t : ℝ => ∫ y, D.kernel x y t * f y ∂D.volume) (𝓝[>] (0 : ℝ)) (𝓝 (f x))

namespace WeakInitialConditionFor

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  {D : Poincare.D11.HeatKernelBridge.HeatKernelCore X}

/-- For the continuous-integrable class the versioned condition is *exactly* D11's
`HeatKernelCore.WeakInitialCondition`: the repair is an interface change (the class is part of the
statement), not a change of the proved mathematics. -/
theorem iff_integrableClass :
    D.WeakInitialCondition ↔
      WeakInitialConditionFor D (AdmissibleTestClass.continuousIntegrableClass D.volume) := by
  constructor
  · intro h x f hf
    exact h x f hf.1 hf.2
  · intro h x f hf hfi
    exact h x f ⟨hf, hfi⟩

/-- The `C_c` (continuous compact support) class: the versioned condition for the integrable class
implies the versioned condition for `C_c`, because `C_c` functions are admissible and integrable.
This holds on any space where `C_c` functions are integrable (measures finite on compacts). -/
theorem of_integrableClass_of_ccClass [OpensMeasurableSpace X]
    [IsFiniteMeasureOnCompacts D.volume]
    (h : WeakInitialConditionFor D (AdmissibleTestClass.continuousIntegrableClass D.volume)) :
    WeakInitialConditionFor D (AdmissibleTestClass.continuousCompactSupportClass D.volume) := by
  intro x f hf
  exact h x f (AdmissibleTestClass.continuousCompactSupportClass_subset_continuousIntegrableClass f hf)

end WeakInitialConditionFor

end Poincare.D12.HeatDomain
