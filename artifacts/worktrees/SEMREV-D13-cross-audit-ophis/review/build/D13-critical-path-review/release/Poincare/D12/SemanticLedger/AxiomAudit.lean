/-
Copyright (c) 2026 Poincare Longrun D12 semantic-ledger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-semantic-ledger)
-/

import Poincare.D12.SemanticLedger.Defect
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Poincare.D12.SemanticLedger.AxiomAudit

**Fail-closed programmatic axiom audit of every D12-semantic-ledger declaration.**

Every declaration of this D12 audit module is printed with `#print axioms`, and
then the same cones are re-checked programmatically with `Lean.collectAxioms`.
The build **fails** if any declaration depends on an axiom outside the approved
cone `{propext, Classical.choice, Quot.sound}` — in particular no `sorryAx`,
no user axiom, no `Lean.ofReduceBool` (from `native_decide`) and no
`proof_wanted` may appear.

The negative control that proves this predicate is not vacuous lives in
`negcontrol/NegativeControl.lean` at the worktree root (it detects `sorryAx`
and the private `native_decide` axiom); its exit-0 run is recorded in the
compile evidence of the ledger.

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs
in this file or in the files it imports.
-/

open Lean Elab Command

namespace Poincare.D12.SemanticLedger

/-! ## Kernel definition, observed interface and test function -/

#print axioms Poincare.D12.SemanticLedger.gaussianKernelXY
#print axioms Poincare.D12.SemanticLedger.D7InitialConditionAt
#print axioms Poincare.D12.SemanticLedger.testFunction
#print axioms Poincare.D12.SemanticLedger.testFunction_continuous
#print axioms Poincare.D12.SemanticLedger.testFunction_pos
#print axioms Poincare.D12.SemanticLedger.testFunction_zero
#print axioms Poincare.D12.SemanticLedger.tendsto_testFunction_atTop

/-! ## Domination of the Gaussian decay by the quartic test function -/

#print axioms Poincare.D12.SemanticLedger.R
#print axioms Poincare.D12.SemanticLedger.lowerConstant
#print axioms Poincare.D12.SemanticLedger.R_sq
#print axioms Poincare.D12.SemanticLedger.R_nonneg
#print axioms Poincare.D12.SemanticLedger.lowerConstant_pos
#print axioms Poincare.D12.SemanticLedger.integrand
#print axioms Poincare.D12.SemanticLedger.integrand_eq
#print axioms Poincare.D12.SemanticLedger.continuous_gaussianKernelXY_int
#print axioms Poincare.D12.SemanticLedger.integrand_continuous
#print axioms Poincare.D12.SemanticLedger.integrand_nonneg
#print axioms Poincare.D12.SemanticLedger.integrand_pos
#print axioms Poincare.D12.SemanticLedger.quartic_dominates
#print axioms Poincare.D12.SemanticLedger.lowerConstant_le_integrand

/-! ## Non-integrability and the defect theorem -/

#print axioms Poincare.D12.SemanticLedger.integrand_lintegral_eq_top
#print axioms Poincare.D12.SemanticLedger.integrand_not_integrable
#print axioms Poincare.D12.SemanticLedger.integral_undef_zero
#print axioms Poincare.D12.SemanticLedger.not_initialCondition_gaussian
#print axioms Poincare.D12.SemanticLedger.not_initialCondition_gaussian_quantified

/-! ## Programmatic re-check of every cone -/

/-- The full list of declarations authored by the D12 semantic-ledger audit. -/
private def d12AuditedDeclarations : List Name :=
  [ ``Poincare.D12.SemanticLedger.gaussianKernelXY,
    ``Poincare.D12.SemanticLedger.D7InitialConditionAt,
    ``Poincare.D12.SemanticLedger.testFunction,
    ``Poincare.D12.SemanticLedger.testFunction_continuous,
    ``Poincare.D12.SemanticLedger.testFunction_pos,
    ``Poincare.D12.SemanticLedger.testFunction_zero,
    ``Poincare.D12.SemanticLedger.tendsto_testFunction_atTop,
    ``Poincare.D12.SemanticLedger.R,
    ``Poincare.D12.SemanticLedger.lowerConstant,
    ``Poincare.D12.SemanticLedger.R_sq,
    ``Poincare.D12.SemanticLedger.R_nonneg,
    ``Poincare.D12.SemanticLedger.lowerConstant_pos,
    ``Poincare.D12.SemanticLedger.integrand,
    ``Poincare.D12.SemanticLedger.integrand_eq,
    ``Poincare.D12.SemanticLedger.continuous_gaussianKernelXY_int,
    ``Poincare.D12.SemanticLedger.integrand_continuous,
    ``Poincare.D12.SemanticLedger.integrand_nonneg,
    ``Poincare.D12.SemanticLedger.integrand_pos,
    ``Poincare.D12.SemanticLedger.quartic_dominates,
    ``Poincare.D12.SemanticLedger.lowerConstant_le_integrand,
    ``Poincare.D12.SemanticLedger.integrand_lintegral_eq_top,
    ``Poincare.D12.SemanticLedger.integrand_not_integrable,
    ``Poincare.D12.SemanticLedger.integral_undef_zero,
    ``Poincare.D12.SemanticLedger.not_initialCondition_gaussian,
    ``Poincare.D12.SemanticLedger.not_initialCondition_gaussian_quantified ]

/-- The approved axiom cone: exactly the three standard Lean axioms. -/
private def d12ApprovedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let mut unapprovedTotal : Array (Name × List Name) := #[]
  for d in d12AuditedDeclarations do
    let axs ← Lean.collectAxioms d
    let bad := axs.toList.filter (fun a => !d12ApprovedAxioms.contains a)
    if !bad.isEmpty then
      unapprovedTotal := unapprovedTotal.push (d, bad)
  if unapprovedTotal.isEmpty then
    logInfo m!"D12AxiomCheck: PASS — all {d12AuditedDeclarations.length} declarations \
      of the D12 semantic-ledger audit module depend only on \
      [propext, Classical.choice, Quot.sound]"
  else
    for (d, bad) in unapprovedTotal do
      logError m!"D12AxiomCheck: {d} depends on unapproved axioms {bad.map Name.toString}"
    throwError "D12AxiomCheck: FAIL — {unapprovedTotal.size} declaration(s) with unapproved axioms"

end Poincare.D12.SemanticLedger
