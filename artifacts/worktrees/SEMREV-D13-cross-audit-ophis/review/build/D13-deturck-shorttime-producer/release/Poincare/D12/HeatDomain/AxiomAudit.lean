/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-heat-domain-repair)
-/

import Poincare.D12.HeatDomain.All

import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Axiom audit for the D12 heat-domain repair

Every declaration of the `Poincare.D12.HeatDomain` development is printed with `#print axioms` and
then re-checked programmatically with `Lean.collectAxioms`. The expected (and checked) outcome is
that every declaration depends only on the three standard Lean axioms `propext`,
`Classical.choice`, `Quot.sound` (or on none at all); in particular no `sorryAx`, no user axiom, no
`unsafe` declaration, no `Lean.ofReduceBool` from `native_decide`, and no `proof_wanted` may appear.
The `#print axioms` lines are informational transcripts; the *enforceable* fail-closed gate is the
programmatic `run_cmd` re-check at the end of this file, which aborts the build on any axiom outside
the approved cone.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open Lean Elab Command
open Poincare.D12.HeatDomain Poincare.D11.HeatKernelBridge

/-! ## Downstream use check (kernel-checked consumers of the v1 interface) -/

open MeasureTheory Filter
open scoped Topology

/-- A concrete downstream application: the versioned `C_c` condition applied to the bump test
function at `x = 0` yields the convergence to `1` through the core datum's own fields. -/
example (n : ℕ) :
    Tendsto (fun t : ℝ =>
        ∫ y : EuclideanSpace ℝ (Fin n),
          (flatHeatKernelCore n).kernel 0 y t * bump n y ∂(flatHeatKernelCore n).volume)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  simpa [flatHeatKernelCore_kernel, flatHeatKernelCore_volume, bump_zero n] using
    (flatHeatKernelCore_weakInitialConditionFor_ccClass n) 0 (bump n) (bump_mem_ccClass n)

/-- The versioned integrable-class condition is available for every dimension (re-exported use). -/
example (n : ℕ) :
    WeakInitialConditionFor (flatHeatKernelCore n)
      (AdmissibleTestClass.continuousIntegrableClass (flatHeatKernelCore n).volume) :=
  flatHeatKernelCore_weakInitialConditionFor_integrableClass n

/-! ## The versioned admissible-test-function interface -/

#print axioms Poincare.D12.HeatDomain.AdmissibleTestClass.v1
#print axioms Poincare.D12.HeatDomain.AdmissibleTestClass
#print axioms Poincare.D12.HeatDomain.AdmissibleTestClass.continuousCompactSupportClass
#print axioms Poincare.D12.HeatDomain.AdmissibleTestClass.continuousIntegrableClass
#print axioms Poincare.D12.HeatDomain.AdmissibleTestClass.continuousCompactSupportClass_subset_continuousIntegrableClass
#print axioms Poincare.D12.HeatDomain.AdmissibleTestClass.continuousIntegrableClass_inhabited
#print axioms Poincare.D12.HeatDomain.WeakInitialConditionFor
#print axioms Poincare.D12.HeatDomain.WeakInitialConditionFor.iff_integrableClass
#print axioms Poincare.D12.HeatDomain.WeakInitialConditionFor.of_integrableClass_of_ccClass

/-! ## The Euclidean core inhabits the interface in every dimension -/

#print axioms Poincare.D12.HeatDomain.flatHeatKernelCore_weakInitialConditionFor_integrableClass
#print axioms Poincare.D12.HeatDomain.flatHeatKernelCore_weakInitialConditionFor_ccClass
#print axioms Poincare.D12.HeatDomain.flatHeatKernelCore_weakInitialConditionFor_integrableClass'
#print axioms Poincare.D12.HeatDomain.bump
#print axioms Poincare.D12.HeatDomain.bump_continuous
#print axioms Poincare.D12.HeatDomain.bump_zero
#print axioms Poincare.D12.HeatDomain.bump_nontrivial
#print axioms Poincare.D12.HeatDomain.bump_support_subset_closedBall
#print axioms Poincare.D12.HeatDomain.bump_hasCompactSupport
#print axioms Poincare.D12.HeatDomain.bump_mem_ccClass
#print axioms Poincare.D12.HeatDomain.bump_weakInitialCondition
#print axioms Poincare.D12.HeatDomain.bump_weakInitialConditionFor_ccClass

/-! ## Compact finite-measure compatibility -/

#print axioms Poincare.D12.HeatDomain.continuous_integrable_of_compactSpace_finiteMeasure
#print axioms Poincare.D12.HeatDomain.weakInitialCondition_iff_full_of_compact_finiteMeasure
#print axioms Poincare.D12.HeatDomain.weakInitialConditionFor_integrableClass_iff_full_of_compact_finiteMeasure
#print axioms Poincare.D12.HeatDomain.ccClass_cls_iff_continuous_of_compactSpace
#print axioms Poincare.D12.HeatDomain.weakInitialConditionFor_ccClass_iff_full_of_compact_finiteMeasure
#print axioms Poincare.D12.HeatDomain.toHeatKernelData_of_weak_compact_finiteMeasure
#print axioms Poincare.D12.HeatDomain.toHeatKernelData_of_weak_compact_finiteMeasure_toCore
#print axioms Poincare.D12.HeatDomain.toHeatKernelData_of_weak_compact_finiteMeasure_initialCondition
#print axioms Poincare.D12.HeatDomain.punitHeatKernelData_core_weak_iff_full
#print axioms Poincare.D12.HeatDomain.punitHeatKernelData_toCore_weakInitialCondition

/-! ## The explicit fast-growing counterexample -/

#print axioms Poincare.D12.HeatDomain.volume_eq_volume_pi_image_ofLp
#print axioms Poincare.D12.HeatDomain.ofLp_image_halfspace
#print axioms Poincare.D12.HeatDomain.measurableSet_halfspace_fn
#print axioms Poincare.D12.HeatDomain.measurableSet_halfspace
#print axioms Poincare.D12.HeatDomain.halfspace_eq_box
#print axioms Poincare.D12.HeatDomain.volume_halfspace_eq_top
#print axioms Poincare.D12.HeatDomain.volume_set_norm_ge_eq_top
#print axioms Poincare.D12.HeatDomain.measurableSet_norm_ge
#print axioms Poincare.D12.HeatDomain.fastFunction
#print axioms Poincare.D12.HeatDomain.fastFunction_continuous
#print axioms Poincare.D12.HeatDomain.fastFunction_zero
#print axioms Poincare.D12.HeatDomain.fastFunction_nonneg
#print axioms Poincare.D12.HeatDomain.notIntegrable_fast_times_kernel
#print axioms Poincare.D12.HeatDomain.integral_fast_times_kernel_eq_zero
#print axioms Poincare.D12.HeatDomain.not_fullInitialCondition_flat_of_pos
#print axioms Poincare.D12.HeatDomain.not_fullInitialCondition_flat_one
#print axioms Poincare.D12.HeatDomain.flat_positive_dimension_weak_not_full
#print axioms Poincare.D12.HeatDomain.not_exists_heatKernelData_flat_of_pos
#print axioms Poincare.D12.HeatDomain.not_exists_heatKernelData_flat_one

/-! ## Programmatic re-check of every cone -/

/-- The full list of declarations of the D12 heat-domain repair. -/
private def heatDomainAuditedDeclarations : List Name :=
  [ ``Poincare.D12.HeatDomain.AdmissibleTestClass.v1,
    ``Poincare.D12.HeatDomain.AdmissibleTestClass,
    ``Poincare.D12.HeatDomain.AdmissibleTestClass.continuousCompactSupportClass,
    ``Poincare.D12.HeatDomain.AdmissibleTestClass.continuousIntegrableClass,
    ``Poincare.D12.HeatDomain.AdmissibleTestClass.continuousCompactSupportClass_subset_continuousIntegrableClass,
    ``Poincare.D12.HeatDomain.AdmissibleTestClass.continuousIntegrableClass_inhabited,
    ``Poincare.D12.HeatDomain.WeakInitialConditionFor,
    ``Poincare.D12.HeatDomain.WeakInitialConditionFor.iff_integrableClass,
    ``Poincare.D12.HeatDomain.WeakInitialConditionFor.of_integrableClass_of_ccClass,
    ``Poincare.D12.HeatDomain.flatHeatKernelCore_weakInitialConditionFor_integrableClass,
    ``Poincare.D12.HeatDomain.flatHeatKernelCore_weakInitialConditionFor_ccClass,
    ``Poincare.D12.HeatDomain.flatHeatKernelCore_weakInitialConditionFor_integrableClass',
    ``Poincare.D12.HeatDomain.bump,
    ``Poincare.D12.HeatDomain.bump_continuous,
    ``Poincare.D12.HeatDomain.bump_zero,
    ``Poincare.D12.HeatDomain.bump_nontrivial,
    ``Poincare.D12.HeatDomain.bump_support_subset_closedBall,
    ``Poincare.D12.HeatDomain.bump_hasCompactSupport,
    ``Poincare.D12.HeatDomain.bump_mem_ccClass,
    ``Poincare.D12.HeatDomain.bump_weakInitialCondition,
    ``Poincare.D12.HeatDomain.bump_weakInitialConditionFor_ccClass,
    ``Poincare.D12.HeatDomain.continuous_integrable_of_compactSpace_finiteMeasure,
    ``Poincare.D12.HeatDomain.weakInitialCondition_iff_full_of_compact_finiteMeasure,
    ``Poincare.D12.HeatDomain.weakInitialConditionFor_integrableClass_iff_full_of_compact_finiteMeasure,
    ``Poincare.D12.HeatDomain.ccClass_cls_iff_continuous_of_compactSpace,
    ``Poincare.D12.HeatDomain.weakInitialConditionFor_ccClass_iff_full_of_compact_finiteMeasure,
    ``Poincare.D12.HeatDomain.toHeatKernelData_of_weak_compact_finiteMeasure,
    ``Poincare.D12.HeatDomain.toHeatKernelData_of_weak_compact_finiteMeasure_toCore,
    ``Poincare.D12.HeatDomain.toHeatKernelData_of_weak_compact_finiteMeasure_initialCondition,
    ``Poincare.D12.HeatDomain.punitHeatKernelData_core_weak_iff_full,
    ``Poincare.D12.HeatDomain.punitHeatKernelData_toCore_weakInitialCondition,
    ``Poincare.D12.HeatDomain.volume_eq_volume_pi_image_ofLp,
    ``Poincare.D12.HeatDomain.ofLp_image_halfspace,
    ``Poincare.D12.HeatDomain.measurableSet_halfspace_fn,
    ``Poincare.D12.HeatDomain.measurableSet_halfspace,
    ``Poincare.D12.HeatDomain.halfspace_eq_box,
    ``Poincare.D12.HeatDomain.volume_halfspace_eq_top,
    ``Poincare.D12.HeatDomain.volume_set_norm_ge_eq_top,
    ``Poincare.D12.HeatDomain.measurableSet_norm_ge,
    ``Poincare.D12.HeatDomain.fastFunction,
    ``Poincare.D12.HeatDomain.fastFunction_continuous,
    ``Poincare.D12.HeatDomain.fastFunction_zero,
    ``Poincare.D12.HeatDomain.fastFunction_nonneg,
    ``Poincare.D12.HeatDomain.notIntegrable_fast_times_kernel,
    ``Poincare.D12.HeatDomain.integral_fast_times_kernel_eq_zero,
    ``Poincare.D12.HeatDomain.not_fullInitialCondition_flat_of_pos,
    ``Poincare.D12.HeatDomain.not_fullInitialCondition_flat_one,
    ``Poincare.D12.HeatDomain.flat_positive_dimension_weak_not_full,
    ``Poincare.D12.HeatDomain.not_exists_heatKernelData_flat_of_pos,
    ``Poincare.D12.HeatDomain.not_exists_heatKernelData_flat_one ]

/-- The approved axiom cone: exactly the three standard Lean axioms. -/
private def heatDomainApprovedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let mut unapprovedTotal : Array (Name × List Name) := #[]
  for d in heatDomainAuditedDeclarations do
    let axs ← Lean.collectAxioms d
    let bad := axs.toList.filter (fun a => !heatDomainApprovedAxioms.contains a)
    if !bad.isEmpty then
      unapprovedTotal := unapprovedTotal.push (d, bad)
  if unapprovedTotal.isEmpty then
    logInfo m!"D12HeatDomainAxiomCheck: PASS — all {heatDomainAuditedDeclarations.length} declarations \
      of the D12 heat-domain repair depend only on [propext, Classical.choice, Quot.sound]"
  else
    for (d, bad) in unapprovedTotal do
      logError m!"D12HeatDomainAxiomCheck: {d} depends on unapproved axioms {bad.map Name.toString}"
    throwError "D12HeatDomainAxiomCheck: FAIL — {unapprovedTotal.size} declaration(s) with unapproved axioms"
