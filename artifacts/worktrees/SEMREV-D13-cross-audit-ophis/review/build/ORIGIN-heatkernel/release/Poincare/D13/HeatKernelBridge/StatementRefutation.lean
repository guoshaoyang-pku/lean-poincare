/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D7.HeatKernel.V1Interface

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D13.HeatKernelBridge.StatementRefutation

**D13 heat-kernel bridge, companion note 3: the D7 `HeatKernelExistenceStatement` is refutable as
formalized.**

`PredicateSemantics.lean` records that the `solves` field shared by the D7 predicates
`Poincare.D7.HeatKernel.IsHeatKernel` and `Poincare.D7.HeatKernel.IsHeatKernelV1` is a
*time-snapshot operator identity*,

`solves : ∀ y t, 0 < t → S.timeDerivative (fun x => K x y t) = S.laplacian (fun x => K x y t)`,

rather than the heat equation `∂_t K(x,y,t) = Δ_x K(x,y,t)`. This file proves the corresponding
**statement-level** fact, which is strictly stronger than the flat-space refutation recorded there:

the D7 blocked existence statement `Poincare.D7.HeatKernel.HeatKernelExistenceStatement` — and its
corrected-domain restatement `HeatKernelExistenceStatementV1`, which shares the `solves` field — are
**false as formalized**, because `IsClosedRiemannianManifold` constrains only the volume measure and
the distance, and leaves the analytic operators `laplacian` and `timeDerivative` completely
unconstrained.

The counterexample is the one-point space `PUnit` with

* `volume = Measure.dirac PUnit.unit` (the unique nonempty open set has volume `1`, every compact
  set has volume at most `1`),
* `timeDerivative = 0` and `laplacian = LinearMap.id` (legitimate fields of the schematic
  `HeatSpacetime`, and *not* constrained by `IsClosedRiemannianManifold`),
* `dist = 0`, `dim = 0`.

The `solves` field then forces `K x y t = 0` for every `x y t` (the heat operator is
`u ↦ -u`), contradicting strict positivity. Hence no kernel inhabits the predicate on this closed
Riemannian spacetime, and the existential statement is refuted:

* `refutingSpacetime`, `refutingSpacetime_isClosedRiemannianManifold`: the counterexample spacetime
  and its closed-Riemannian certificate;
* `not_isHeatKernel_of_laplacian_id_timeDerivative_zero`: the general schema — on a nonempty space,
  any `HeatSpacetime` with `laplacian = id` and `timeDerivative = 0` admits no `IsHeatKernel`
  kernel (the PDE field is contradictory, independently of all integration theory);
* `not_isHeatKernelV1_of_laplacian_id_timeDerivative_zero`: the same for the corrected-domain
  predicate `IsHeatKernelV1`, with an arbitrary admissible test class;
* `not_heatKernelExistenceStatement` and `not_heatKernelExistenceStatementV1`: the two D7
  existence statements are refuted;
* `not_heatKernelExistenceStatement_of_refuting` / `...V1...`: the universe-polymorphic conditional
  forms, so the refutation is not an artefact of the lowest universe.

**Consequence for the named blocker.** `D7-HEAT-KERNEL-EXISTENCE` cannot be closed by proving the
statement as it currently stands: the statement is not merely unproved, it is refutable, so any
proof attempt must fail. The statement needs an interface repair that pins `laplacian` (and the
forward time derivative) to the geometric operators of a Riemannian metric — the repair direction
recorded in `PDERepair.lean`, whose `IsHeatKernelPDE` uses the genuine `HasDerivAt` field but is
still stated over the unconstrained schematic `HeatSpacetime`. The data-level bridge
`HeatKernelDataV1` is unaffected: its heat equation is the genuine `HasDerivAt` statement, and the
legacy `HeatKernelData` interface inherits it.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D13.HeatKernelBridge

open Poincare.D7.HeatKernel

/-! ## The counterexample spacetime -/

/-- **The refuting schematic heat spacetime** on the one-point space: Dirac volume at the unique
point, zero forward time derivative, and the identity operator as Laplacian. Both operator fields
are admissible values of the schematic `HeatSpacetime` structure, and `IsClosedRiemannianManifold`
does not constrain them. -/
noncomputable def refutingSpacetime : HeatSpacetime PUnit where
  volume := Measure.dirac PUnit.unit
  laplacian := LinearMap.id
  timeDerivative := 0
  dist := fun _ _ => 0
  dim := 0

@[simp]
theorem refutingSpacetime_volume :
    refutingSpacetime.volume = Measure.dirac PUnit.unit := rfl

@[simp]
theorem refutingSpacetime_laplacian :
    refutingSpacetime.laplacian = LinearMap.id := rfl

@[simp]
theorem refutingSpacetime_laplacian_apply (u : PUnit → ℝ) :
    refutingSpacetime.laplacian u = u := rfl

@[simp]
theorem refutingSpacetime_timeDerivative :
    refutingSpacetime.timeDerivative = 0 := rfl

@[simp]
theorem refutingSpacetime_timeDerivative_apply (u : PUnit → ℝ) :
    refutingSpacetime.timeDerivative u = 0 := rfl

/-- **The heat operator of the refuting spacetime is negation.** With `timeDerivative = 0` and
`laplacian = id`, the heat operator `∂_t - Δ` is the map `u ↦ -u` on functions of the space
variable. -/
theorem refutingSpacetime_heatOperator (u : PUnit → ℝ) :
    refutingSpacetime.heatOperator u = -u := by
  simp [HeatSpacetime.heatOperator]

/-- **The refuting spacetime is a closed Riemannian manifold** in the sense of the D7 predicate:
the one-point space is compact, the Dirac volume is positive on the unique nonempty open set and
finite on every compact set, and the zero distance satisfies the metric axioms on a subsingleton.
The analytic operator fields do not occur in the predicate. -/
theorem refutingSpacetime_isClosedRiemannianManifold :
    IsClosedRiemannianManifold refutingSpacetime where
  compact_univ := by
    rw [isCompact_iff_finite]
    exact Set.finite_univ
  volume_pos := by
    intro U _ hUne
    rw [Subsingleton.eq_univ_of_nonempty hUne]
    simp [refutingSpacetime]
  volume_lt_top := by
    intro K _
    exact (measure_mono (Set.subset_univ K)).trans_lt (by simp [refutingSpacetime])
  dist_self := fun _ => rfl
  dist_pos := fun x y h => (h (Subsingleton.elim x y)).elim
  dist_symm := fun _ _ => rfl
  dist_triangle := fun _ _ _ => by simp [refutingSpacetime]

/-! ## The general refutation schema -/

/-- **A `HeatSpacetime` with `laplacian = id` and `timeDerivative = 0` admits no `IsHeatKernel`
kernel.** On any nonempty space, the `solves` field of `IsHeatKernel` reads
`-(fun x => K x y t) = 0`, i.e. `K x y t = 0`, which contradicts strict positivity. Only the two
operator fields and the `positive`/`solves` fields are used; no measure theory, no integrability,
no test-function domain is involved. -/
theorem not_isHeatKernel_of_laplacian_id_timeDerivative_zero {M : Type*}
    [TopologicalSpace M] [MeasurableSpace M] [Nonempty M]
    (S : HeatSpacetime M) (hlapl : S.laplacian = LinearMap.id) (hT : S.timeDerivative = 0)
    (K : M → M → ℝ → ℝ) : ¬ IsHeatKernel S K := by
  intro h
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  have h0 := congr_fun (h.solves x 1 (by norm_num)) x
  have hK0 : K x x 1 = 0 := by
    simpa [HeatSpacetime.heatOperator, hlapl, hT] using h0
  have hpos := h.positive x x 1 (by norm_num)
  rw [hK0] at hpos
  exact lt_irrefl 0 hpos

/-- **A `HeatSpacetime` with `laplacian = id` and `timeDerivative = 0` admits no `IsHeatKernelV1`
kernel** for any admissible test-function class: the corrected-domain predicate shares the same
`solves` field, so the same contradiction applies; the class is not used. -/
theorem not_isHeatKernelV1_of_laplacian_id_timeDerivative_zero {M : Type*}
    [TopologicalSpace M] [MeasurableSpace M] [Nonempty M]
    (S : HeatSpacetime M) (hlapl : S.laplacian = LinearMap.id) (hT : S.timeDerivative = 0)
    (C : Poincare.D12.HeatDomain.AdmissibleTestClass M S.volume) (K : M → M → ℝ → ℝ) :
    ¬ IsHeatKernelV1 S C K := by
  intro h
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  have h0 := congr_fun (h.solves x 1 (by norm_num)) x
  have hK0 : K x x 1 = 0 := by
    simpa [HeatSpacetime.heatOperator, hlapl, hT] using h0
  have hpos := h.positive x x 1 (by norm_num)
  rw [hK0] at hpos
  exact lt_irrefl 0 hpos

/-! ## The D7 existence statements are refuted -/

/-- On the one-point space every measurable space has the same measurable sets (`∅` and `univ`), so
all measurable space structures on `PUnit` coincide. Mathlib does not register this instance; it is
proved here (for `PUnit` only) so that the universe-`0` counterexample can be instantiated. -/
theorem subsingleton_measurableSpace_punit : Subsingleton (MeasurableSpace PUnit) where
  allEq m₁ m₂ := by
    refine MeasurableSpace.ext (fun s => ?_)
    have hs : s = ∅ ∨ s = Set.univ := by
      rcases Set.eq_empty_or_nonempty s with h | ⟨x, hx⟩
      · exact Or.inl h
      · exact Or.inr (Subsingleton.eq_univ_of_nonempty ⟨x, hx⟩)
    rcases hs with rfl | rfl <;> simp

/-- **Universe-polymorphic conditional refutation of the legacy statement.** Any nonempty closed
Riemannian schematic spacetime whose Laplacian is the identity and whose forward time derivative is
zero refutes `HeatKernelExistenceStatement` at its own universe. The one-point counterexample is
the universe-`0` instance; the same schema applies at every universe. -/
theorem not_heatKernelExistenceStatement_of_refuting {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [Nonempty M] (S : HeatSpacetime M)
    (hclosed : IsClosedRiemannianManifold S) (hlapl : S.laplacian = LinearMap.id)
    (hT : S.timeDerivative = 0) : ¬ HeatKernelExistenceStatement.{u} := by
  intro h
  obtain ⟨K, hK⟩ := h M S hclosed (Classical.choice (inferInstance : Nonempty M))
  exact not_isHeatKernel_of_laplacian_id_timeDerivative_zero S hlapl hT K hK

/-- **Universe-polymorphic conditional refutation of the corrected-domain statement.** -/
theorem not_heatKernelExistenceStatementV1_of_refuting {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [Nonempty M] (S : HeatSpacetime M)
    (hclosed : IsClosedRiemannianManifold S) (hlapl : S.laplacian = LinearMap.id)
    (hT : S.timeDerivative = 0) : ¬ HeatKernelExistenceStatementV1.{u} := by
  intro h
  obtain ⟨K, hK⟩ := h M S hclosed (Classical.choice (inferInstance : Nonempty M))
  exact not_isHeatKernelV1_of_laplacian_id_timeDerivative_zero S hlapl hT
    (Poincare.D12.HeatDomain.AdmissibleTestClass.continuousIntegrableClass S.volume) K hK

/-- **The D7 `HeatKernelExistenceStatement` is refuted at universe `0`** by the one-point
counterexample spacetime. -/
theorem not_heatKernelExistenceStatement : ¬ HeatKernelExistenceStatement := by
  haveI : Subsingleton (MeasurableSpace PUnit) := subsingleton_measurableSpace_punit
  haveI : BorelSpace PUnit := ⟨Subsingleton.elim _ _⟩
  exact not_heatKernelExistenceStatement_of_refuting refutingSpacetime
    refutingSpacetime_isClosedRiemannianManifold rfl rfl

/-- **The corrected-domain D7 existence statement is refuted at universe `0`** by the same
counterexample: `HeatKernelExistenceStatementV1` shares the `solves` field of the legacy
predicate. -/
theorem not_heatKernelExistenceStatementV1 : ¬ HeatKernelExistenceStatementV1 := by
  haveI : Subsingleton (MeasurableSpace PUnit) := subsingleton_measurableSpace_punit
  haveI : BorelSpace PUnit := ⟨Subsingleton.elim _ _⟩
  exact not_heatKernelExistenceStatementV1_of_refuting refutingSpacetime
    refutingSpacetime_isClosedRiemannianManifold rfl rfl

end Poincare.D13.HeatKernelBridge
