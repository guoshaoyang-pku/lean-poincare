/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D12.HeatDomain.TestFunction

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D13.HeatKernelBridge.Basic

**D13 heat-kernel bridge, part 1: the D7 `HeatKernelData` interface on the corrected
admissible-test-function domain (v1).**

`LONG_PLAN` names a `HeatKernelBridge` module transporting the D10 Euclidean heat kernel
(`Poincare.D10.HeatKernelEuclidean`) to the D7 heat-kernel interface
(`Poincare.D7.HeatKernel.HeatKernelData`). The D11 bridge (`Poincare.D11.HeatKernelBridge`)
already isolates the one D7 field that is unsatisfiable by the explicit Euclidean kernel — the
literal pointwise initial condition over *all* continuous test functions — as
`HeatKernelCore.FullInitialCondition`; the D12 repair (`Poincare.D12.HeatDomain`) replaces that
quantifier by a versioned admissible-test-function interface
(`AdmissibleTestClass` / `WeakInitialConditionFor`) and proves the D11 Euclidean core inhabits it
in every dimension. This module completes the transport named by `LONG_PLAN` at the D7 level:

`HeatKernelDataV1 X` is the D7 interface with the defective field replaced by the corrected one:
it bundles

* a `HeatKernelCore` (`core`), i.e. every analytic field of the D7 interface except the pointwise
  initial condition — Gaussian upper/lower bounds, symmetry, the Chapman–Kolmogorov semigroup law,
  normalization, and the heat equation;
* an admissible test-function class `testClass` for the core's own volume;
* the versioned initial condition `initialConditionFor` of `Poincare.D12.HeatDomain` against that
  class.

So a `HeatKernelDataV1` carries exactly the D7 content on the corrected domain. The two directions
of the transport are proved in the companion files:

* `EuclideanTransport.lean`: the explicit D10 Euclidean heat kernel produces a
  `HeatKernelDataV1 (EuclideanSpace ℝ (Fin n))` in **every** dimension `n` (both admissible
  classes); in every positive dimension no *legacy* `HeatKernelData` with that kernel exists
  (D12 `Counterexample`), so the corrected-domain interface is exactly the statement available
  for the flat kernel;
* `CompactUpgrade.lean`: on a compact space with finite reference measure — the intended closed
  (compact) manifold setting, whose Riemannian volume is finite — every `HeatKernelDataV1`
  upgrades to a genuine legacy `Poincare.D7.HeatKernel.HeatKernelData` through the unchanged D11
  bridge map, and every legacy datum is a V1 datum, so the corrected domain loses nothing there.

The legacy D7/D10/D11/D12 definitions are imported and consumed, never edited. Versioning is by
naming plus the tag `HeatKernelDataV1.v1`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D13.HeatKernelBridge

open Poincare.D11.HeatKernelBridge
open Poincare.D12.HeatDomain

/-- The version tag of the corrected-domain D7 interface. Bump this only in a *new* versioned
definition; the v1 definitions below keep their names and the legacy D7/D11/D12 definitions are
never edited. -/
def HeatKernelDataV1.v1 : ℕ := 1

/-- **The D7 heat-kernel interface on the corrected admissible-test-function domain (v1).** A
core datum (all analytic fields of `Poincare.D7.HeatKernel.HeatKernelData` except the pointwise
initial condition) together with an admissible test-function class for the core's own volume and
the versioned weak initial condition against that class. This is the D12-repaired form of the D7
interface: the test-function domain is an explicit part of the statement, certified continuous and
integrable, instead of the overstrong free quantifier `∀ f, Continuous f`. -/
structure HeatKernelDataV1 (X : Type*) [TopologicalSpace X] [MeasurableSpace X] where
  /-- The core datum: every analytic field of the D7 interface except the pointwise initial
  condition. -/
  core : Poincare.D11.HeatKernelBridge.HeatKernelCore X
  /-- The admissible test-function class for the core's own volume. -/
  testClass : Poincare.D12.HeatDomain.AdmissibleTestClass X core.volume
  /-- The versioned weak initial condition against the admissible class. -/
  initialConditionFor : Poincare.D12.HeatDomain.WeakInitialConditionFor core testClass

namespace HeatKernelDataV1

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- Forget the corrected-domain wrapper: the underlying D11 bridge core. -/
def toCore (D : HeatKernelDataV1 X) : Poincare.D11.HeatKernelBridge.HeatKernelCore X := D.core

@[simp]
theorem toCore_core (D : HeatKernelDataV1 X) : D.toCore = D.core := rfl

/-- The reference measure of a V1 datum. -/
def volume (D : HeatKernelDataV1 X) : Measure X := D.core.volume

/-- The distance entering the Gaussian bounds of a V1 datum. -/
def dist (D : HeatKernelDataV1 X) : X → X → ℝ := D.core.dist

/-- The dimension entering the Gaussian factor of a V1 datum. -/
def dim (D : HeatKernelDataV1 X) : ℝ := D.core.dim

/-- The upper constant of a V1 datum. -/
def C_up (D : HeatKernelDataV1 X) : ℝ := D.core.C_up

/-- The upper decay constant of a V1 datum. -/
def c_up (D : HeatKernelDataV1 X) : ℝ := D.core.c_up

/-- The lower constant of a V1 datum. -/
def C_lo (D : HeatKernelDataV1 X) : ℝ := D.core.C_lo

/-- The lower decay constant of a V1 datum. -/
def c_lo (D : HeatKernelDataV1 X) : ℝ := D.core.c_lo

/-- The heat kernel of a V1 datum. -/
def kernel (D : HeatKernelDataV1 X) : X → X → ℝ → ℝ := D.core.kernel

/-- The Laplace operator of a V1 datum. -/
def laplacian (D : HeatKernelDataV1 X) : (X → ℝ) →ₗ[ℝ] (X → ℝ) := D.core.laplacian

@[simp]
theorem volume_eq (D : HeatKernelDataV1 X) : D.volume = D.core.volume := rfl

@[simp]
theorem kernel_eq (D : HeatKernelDataV1 X) (x y : X) (t : ℝ) :
    D.kernel x y t = D.core.kernel x y t := rfl

@[simp]
theorem dist_eq (D : HeatKernelDataV1 X) (x y : X) : D.dist x y = D.core.dist x y := rfl

@[simp]
theorem dim_eq (D : HeatKernelDataV1 X) : D.dim = D.core.dim := rfl

@[simp]
theorem C_up_eq (D : HeatKernelDataV1 X) : D.C_up = D.core.C_up := rfl

@[simp]
theorem c_up_eq (D : HeatKernelDataV1 X) : D.c_up = D.core.c_up := rfl

@[simp]
theorem C_lo_eq (D : HeatKernelDataV1 X) : D.C_lo = D.core.C_lo := rfl

@[simp]
theorem c_lo_eq (D : HeatKernelDataV1 X) : D.c_lo = D.core.c_lo := rfl

@[simp]
theorem laplacian_eq (D : HeatKernelDataV1 X) : D.laplacian = D.core.laplacian := rfl

/-- A V1 datum is an *integrable-class variant* if its admissible class is exactly the
continuous-integrable class of the D12 repair. -/
def IsIntegrableClassVariant (D : HeatKernelDataV1 X) : Prop :=
  D.testClass = AdmissibleTestClass.continuousIntegrableClass D.core.volume

/-- A V1 datum is a *`C_c` variant* if its admissible class is exactly the continuous-compact
-support class of the D12 repair (defined for measures finite on compacts, the standard hypothesis
satisfied by Lebesgue measure on Euclidean space and by every finite measure). -/
def IsCcClassVariant (D : HeatKernelDataV1 X) [OpensMeasurableSpace X]
    [IsFiniteMeasureOnCompacts D.core.volume] : Prop :=
  D.testClass = AdmissibleTestClass.continuousCompactSupportClass D.core.volume

/-! ## The D7 analytic fields, transferred to the corrected-domain interface -/

/-- The kernel of a V1 datum is nonnegative. -/
theorem kernel_nonneg (D : HeatKernelDataV1 X) (x y : X) (t : ℝ) : 0 ≤ D.kernel x y t :=
  D.core.kernel_nonneg x y t

/-- The Gaussian upper bound of a V1 datum. -/
theorem gaussianUpperBound (D : HeatKernelDataV1 X) (x y : X) {t : ℝ} (ht : 0 < t) :
    D.kernel x y t ≤ D.C_up * t ^ (-(D.dim / 2)) * Real.exp (-(D.dist x y) ^ 2 / (D.c_up * t)) :=
  D.core.gaussianUpperBound x y t ht

/-- The Gaussian lower bound of a V1 datum. -/
theorem gaussianLowerBound (D : HeatKernelDataV1 X) (x y : X) {t : ℝ} (ht : 0 < t)
    (hxy : D.dist x y ≤ 1) :
    D.C_lo * t ^ (-(D.dim / 2)) * Real.exp (-(D.dist x y) ^ 2 / (D.c_lo * t)) ≤ D.kernel x y t :=
  D.core.gaussianLowerBound x y t ht hxy

/-- Symmetry of the kernel of a V1 datum. -/
theorem symmetry (D : HeatKernelDataV1 X) (x y : X) (t : ℝ) : D.kernel x y t = D.kernel y x t :=
  D.core.symmetry x y t

/-- The Chapman–Kolmogorov semigroup property of a V1 datum. -/
theorem semigroup (D : HeatKernelDataV1 X) (x y : X) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    D.kernel x y (s + t) = ∫ z, D.kernel x z s * D.kernel z y t ∂D.volume :=
  D.core.semigroup x y s t hs ht

/-- Normalization: the kernel of a V1 datum is a probability kernel for every `t > 0`. -/
theorem normalization (D : HeatKernelDataV1 X) (x : X) {t : ℝ} (ht : 0 < t) :
    ∫ y, D.kernel x y t ∂D.volume = 1 :=
  D.core.normalization x t ht

/-- The heat equation of a V1 datum: `∂_t K x y t = Δ_x K x y t`. -/
theorem heatEquation (D : HeatKernelDataV1 X) (x y : X) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => D.kernel x y s) (D.laplacian (fun z => D.kernel z y t) x) t :=
  D.core.heatEquation x y t ht

/-- The corrected (versioned) initial condition of a V1 datum, against its admissible class. -/
theorem initialConditionFor_apply (D : HeatKernelDataV1 X) (x : X) {f : X → ℝ}
    (hf : D.testClass.cls f) :
    Tendsto (fun t : ℝ => ∫ y, D.kernel x y t * f y ∂D.volume) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) :=
  D.initialConditionFor x f hf

/-! ## Legacy D7 data are corrected-domain data -/

/-- **Every legacy D7 heat-kernel datum is a V1 datum** for the continuous-integrable class: the
legacy literal initial condition quantifies over all continuous functions, in particular over the
members of the admissible class, so the corrected-domain interface is implied by the legacy one
with no further hypothesis. The converse (upgrade) holds in the compact finite-measure scope, see
`CompactUpgrade.lean`. Marked `reducible` so that typeclass synthesis (e.g. finite-measure
instances) sees through the wrapper to the original datum. -/
@[reducible]
def ofHeatKernelData (D : Poincare.D7.HeatKernel.HeatKernelData X) :
    HeatKernelDataV1 X where
  core := D.toCore
  testClass := AdmissibleTestClass.continuousIntegrableClass D.toCore.volume
  initialConditionFor := (WeakInitialConditionFor.iff_integrableClass (D := D.toCore)).mp
    (Poincare.D11.HeatKernelBridge.HeatKernelCore.WeakInitialCondition.of_full
      D.toCore_fullInitialCondition)

@[simp]
theorem ofHeatKernelData_core (D : Poincare.D7.HeatKernel.HeatKernelData X) :
    (ofHeatKernelData D).core = D.toCore := rfl

@[simp]
theorem ofHeatKernelData_toCore (D : Poincare.D7.HeatKernel.HeatKernelData X) :
    (ofHeatKernelData D).toCore = D.toCore := rfl

/-- The legacy-embedding is an integrable-class variant by construction. -/
theorem ofHeatKernelData_integrableClassVariant (D : Poincare.D7.HeatKernel.HeatKernelData X) :
    IsIntegrableClassVariant (ofHeatKernelData D) := rfl

/-! ## Tightness of the corrected-domain interface -/

/-- **Tightness of the bridge.** A V1 datum with a prescribed core and a prescribed admissible
class exists if and only if the core satisfies the versioned weak initial condition for that
class (the class equality is heterogeneous because the class type mentions the core's volume).
Thus the two fields added to `HeatKernelCore` by the D12 repair are exactly the difference
between the core and the corrected-domain D7 interface. -/
theorem exists_toCore_eq_iff (D₀ : Poincare.D11.HeatKernelBridge.HeatKernelCore X)
    (C : AdmissibleTestClass X D₀.volume) :
    (∃ D : HeatKernelDataV1 X, D.toCore = D₀ ∧ HEq D.testClass C) ↔
      WeakInitialConditionFor D₀ C := by
  constructor
  · rintro ⟨D, hcore, hC⟩
    subst hcore
    cases hC
    exact D.initialConditionFor
  · intro h
    exact ⟨⟨D₀, C, h⟩, rfl, HEq.rfl⟩

/-- For an integrable-class variant the corrected condition is exactly D11's weak initial
condition (this is the D12 equivalence `WeakInitialConditionFor.iff_integrableClass`, re-stated
for V1 data): the repair is an interface change, not a change of the proved mathematics. -/
theorem integrableClassVariant_weak_iff {D : HeatKernelDataV1 X} (hC : D.IsIntegrableClassVariant) :
    D.core.WeakInitialCondition ↔ WeakInitialConditionFor D.core
      (AdmissibleTestClass.continuousIntegrableClass D.core.volume) :=
  WeakInitialConditionFor.iff_integrableClass (D := D.core)

end HeatKernelDataV1

end Poincare.D13.HeatKernelBridge
