/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7); D7-namespaced consumer of the D13 bridge.
-/

import Poincare.D13.HeatKernelBridge.All
import Poincare.D7.HeatKernel.Blocked

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D7.HeatKernel.V1Interface

**D7 heat-kernel layer, downstream consumer of the D13 `HeatKernelBridge`.**

This is a *new* D7-side module (authored by the D13-heatkernel-bridge-d10-d7 task; no existing D7
file is edited) that consumes the corrected-domain bridge `Poincare.D13.HeatKernelBridge`:

* `IsHeatKernelV1`: the D7 heat-kernel predicate `IsHeatKernel` with its Dirac initial condition
  quantified over an admissible test-function class (the D12-corrected domain) instead of over all
  continuous functions;
* `HeatKernelExistenceStatementV1`: the blocked D7 manifold existence statement restated on the
  corrected domain;
* `heatKernelExistenceStatement_iff_v1`: the two statements are **equivalent** — on the intended
  closed (compact) manifold setting the corrected-domain quantifier is exactly as strong as the
  legacy literal quantifier, so restating the D7 blocked statement on the corrected domain loses
  nothing;
* `v1_flat_inhabited` / `v1_flat_no_legacy_of_pos`: the corrected-domain D7 interface is inhabited
  by the D10 Euclidean heat kernel in every dimension, while in every positive dimension no legacy
  `HeatKernelData` with that kernel exists — the D7-level summary of the bridge transport;
* `punit_v1_upgrade_eq`: the concrete round trip of the bridge on the existing D7 one-point
  instance (embedding into the corrected domain and upgrading back recovers the original datum).

`HeatKernelExistenceStatementV1` remains an unproved `Prop` exactly like the legacy
`HeatKernelExistenceStatement`; the equivalence proved here is a reduction of the blocked
statement, not a proof of existence. The companion D7 module `StatementStatus.lean` proves, from
the D13 refutation `Poincare.D13.HeatKernelBridge.StatementRefutation`, that both statements are in
fact **refutable as formalized**: the schematic `HeatSpacetime` does not constrain the analytic
operators `laplacian`/`timeDerivative`, and the one-point counterexample makes the shared `solves`
field contradictory. A manifold-side closure of the named blocker must therefore restate the
statement over a repaired interface (see `StatementStatus.lean` and `PDERepair.lean`).

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D7.HeatKernel

open Poincare.D11.HeatKernelBridge
open Poincare.D12.HeatDomain
open Poincare.D13.HeatKernelBridge
open Poincare.D13.HeatKernelBridge.HeatKernelDataV1

/-! ## The heat-kernel predicate on the corrected admissible-test-function domain -/

/-- **The defining properties of a heat kernel on the corrected admissible-test-function domain
(v1).** Identical to `IsHeatKernel` (positivity for positive times, the heat equation
`∂_t K = Δ K`, normalization `∫ K dV = 1`) except that the Dirac convergence is stated against an
admissible test-function class `C` — certified continuous and integrable — instead of against
every continuous function. -/
structure IsHeatKernelV1 {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (S : HeatSpacetime M) (C : Poincare.D12.HeatDomain.AdmissibleTestClass M S.volume)
    (K : M → M → ℝ → ℝ) : Prop where
  /-- The kernel is strictly positive for positive times. -/
  positive : ∀ x y t, 0 < t → 0 < K x y t
  /-- The kernel solves the heat equation in the forward variables. -/
  solves : ∀ y t, 0 < t → S.heatOperator (fun x => K x y t) = 0
  /-- The kernel is normalized: `∫_M K x y t dV = 1`. -/
  normalized : ∀ y t, 0 < t → ∫ x, K x y t ∂S.volume = 1
  /-- The kernel converges to the Dirac delta as `t → 0⁺`, against admissible test functions. -/
  dirac_limitFor : ∀ (f : M → ℝ), C.cls f → ∀ y : M,
    Tendsto (fun t : ℝ => ∫ x, K x y t * f x ∂S.volume) (𝓝[>] (0 : ℝ)) (𝓝 (f y))

/-! ## The blocked existence statement on the corrected domain -/

/-- **The heat-kernel existence statement on the corrected admissible-test-function domain**
(state-only, v1). The D7 `HeatKernelExistenceStatement` with the Dirac condition quantified over
the continuous-integrable admissible class. By `heatKernelExistenceStatement_iff_v1` this
statement is equivalent to the legacy one, so the corrected domain loses nothing on the intended
closed-manifold setting. -/
def HeatKernelExistenceStatementV1 : Prop :=
  ∀ (M : Type*) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (S : HeatSpacetime M), IsClosedRiemannianManifold S → ∀ y₀ : M,
      ∃ K : M → M → ℝ → ℝ,
        IsHeatKernelV1 S (AdmissibleTestClass.continuousIntegrableClass S.volume) K

/-! ## Equivalence of the legacy and corrected-domain statements -/

/-- **Per-kernel equivalence on a closed Riemannian manifold.** For a heat spacetime satisfying
`IsClosedRiemannianManifold` (in particular compact, with finite volume on compacts, over a Borel
space) the corrected-domain predicate for the continuous-integrable class and the legacy
`IsHeatKernel` predicate are equivalent for every kernel: compactness makes every continuous test
function bounded, finite volume makes it integrable (D12
`continuous_integrable_of_compactSpace_finiteMeasure`), so the extra integrability certificate of
the admissible class is automatic and the legacy literal quantifier is exactly the corrected one. -/
theorem isHeatKernelV1_integrable_iff_of_closed {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    [BorelSpace M] (S : HeatSpacetime M) (hclosed : IsClosedRiemannianManifold S)
    (K : M → M → ℝ → ℝ) :
    IsHeatKernelV1 S (AdmissibleTestClass.continuousIntegrableClass S.volume) K ↔
      IsHeatKernel S K := by
  constructor
  · intro h
    haveI : CompactSpace M := ⟨hclosed.compact_univ⟩
    haveI : IsFiniteMeasure S.volume := ⟨hclosed.volume_lt_top Set.univ hclosed.compact_univ⟩
    refine ⟨h.positive, h.solves, h.normalized, ?_⟩
    intro f hf y
    exact h.dirac_limitFor f
      ⟨hf, continuous_integrable_of_compactSpace_finiteMeasure S.volume hf⟩ y
  · intro h
    refine ⟨h.positive, h.solves, h.normalized, ?_⟩
    intro f hf y
    exact h.dirac_limit f hf.1 y

universe u

/-- **The blocked D7 existence statement is equivalent to its corrected-domain form.** Restating
the D7 `HeatKernelExistenceStatement` with the admissible-test-function initial condition loses
nothing: on every closed Riemannian manifold the two predicates coincide kernel by kernel. The
corrected-domain statement is therefore the legitimate form of the D7 blocked statement in which
the D10 Euclidean kernel can inhabit the interface (see `v1_flat_inhabited`). (Both sides are
ascribed the same universe so that the quantifier application typechecks at that level.) -/
theorem heatKernelExistenceStatement_iff_v1 :
    (HeatKernelExistenceStatement.{u} : Prop) ↔ (HeatKernelExistenceStatementV1.{u} : Prop) := by
  constructor
  · intro h M _ _ _ S hclosed y₀
    obtain ⟨K, hK⟩ := h M S hclosed y₀
    exact ⟨K, (isHeatKernelV1_integrable_iff_of_closed S hclosed K).mpr hK⟩
  · intro h M _ _ _ S hclosed y₀
    obtain ⟨K, hK⟩ := h M S hclosed y₀
    exact ⟨K, (isHeatKernelV1_integrable_iff_of_closed S hclosed K).mp hK⟩

/-! ## D7-level consumption of the D10 transport -/

/-- **The corrected-domain D7 interface is inhabited by the D10 Euclidean heat kernel in every
dimension.** A checked D7-level witness of the bridge transport: for every `n : ℕ` there is a
corrected-domain datum whose core is the explicit Euclidean core `flatHeatKernelCore n`. -/
theorem v1_flat_inhabited (n : ℕ) :
    ∃ D : HeatKernelDataV1 (EuclideanSpace ℝ (Fin n)),
      D.toCore = flatHeatKernelCore n ∧ D.IsIntegrableClassVariant :=
  ⟨flatHeatKernelDataV1_integrable n, rfl,
    flatHeatKernelDataV1_integrable_integrableClassVariant n⟩

/-- **In every positive dimension no legacy datum exists for the flat kernel** (D12
`Counterexample`), so the corrected-domain datum above is exactly the D7-level statement available
for the D10 Euclidean kernel in positive dimensions. -/
theorem v1_flat_no_legacy_of_pos (n : ℕ) (hn : 0 < n) :
    ¬ ∃ D : HeatKernelData (EuclideanSpace ℝ (Fin n)), D.toCore = flatHeatKernelCore n :=
  Poincare.D12.HeatDomain.not_exists_heatKernelData_flat_of_pos n hn

/-- **Concrete round trip on the existing D7 one-point instance.** The bridge embedding followed
by the compact finite-measure upgrade recovers the original legacy D7 datum: the corrected-domain
interface is lossless on the compact finite-measure scope where the legacy interface is correct.
(The finiteness instance is discharged inline through the definitional equality of the datum's
volume with the Dirac measure, following the D12 `punitHeatKernelData_core_weak_iff_full`
pattern.) -/
theorem punit_v1_upgrade_eq :
    @toHeatKernelData_of_integrableClass PUnit _ _ _ _
      (ofHeatKernelData punitHeatKernelData)
      (by
        change IsFiniteMeasure (Measure.dirac PUnit.unit)
        infer_instance)
      (ofHeatKernelData_integrableClassVariant punitHeatKernelData) = punitHeatKernelData := by
  haveI : IsFiniteMeasure punitHeatKernelData.toCore.volume := by
    change IsFiniteMeasure (Measure.dirac PUnit.unit)
    infer_instance
  exact ofHeatKernelData_upgrade_eq punitHeatKernelData

end Poincare.D7.HeatKernel
