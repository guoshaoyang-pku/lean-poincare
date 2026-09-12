/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Fail-closed audit for `Poincare.L4.Compactness.RicciToDoublingHyperbolicClosedForm`

Prints the full signature of every declaration of the elementary hyperbolic closed-form
module (`#check`) and runs `Lean.collectAxioms` on each, failing closed (non-zero exit) if any
cone is not a subset of `{propext, Classical.choice, Quot.sound}`.  The declaration list is
literal, so a missing/renamed declaration fails the `#check` lines.
-/
import Poincare.L4.Compactness.RicciToDoublingHyperbolicClosedForm
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

namespace Poincare.L4.Compactness.Audit

#check @sinhPowIntegral
#check @sinhPowIntegral_zero
#check @sinhPowIntegral_one
#check @sinhPowIntegral_add_two
#check @sinhPowIntegral_apply_zero
#check @sinhPowIntegral_hasDerivAt
#check @sinhPowIntegral_integral
#check @sinhPowIntegral_two
#check @sinhPowIntegral_three
#check @hypModelA_volume_closedForm
#check @hypModel_volumeRatio_closedForm
#check @hypModelA_one_one_volume_closedForm
#check @hypModel_volumeRatio_d2_closedForm
#check @hyp_volume_ratio_le_of_ricci_ge_closedForm
#check @hyp_volume_doubling_closedForm

/-- The exact declaration list the audit must cover. -/
def auditedClosedFormDeclarations : List Name :=
  [ ``sinhPowIntegral
  , ``sinhPowIntegral_zero
  , ``sinhPowIntegral_one
  , ``sinhPowIntegral_add_two
  , ``sinhPowIntegral_apply_zero
  , ``sinhPowIntegral_hasDerivAt
  , ``sinhPowIntegral_integral
  , ``sinhPowIntegral_two
  , ``sinhPowIntegral_three
  , ``hypModelA_volume_closedForm
  , ``hypModel_volumeRatio_closedForm
  , ``hypModelA_one_one_volume_closedForm
  , ``hypModel_volumeRatio_d2_closedForm
  , ``hyp_volume_ratio_le_of_ricci_ge_closedForm
  , ``hyp_volume_doubling_closedForm ]

run_cmd do
  let approved : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : List (Name × List Name) := []
  for d in auditedClosedFormDeclarations do
    let axs ← Lean.collectAxioms d
    let axl := axs.toList
    logInfo m!"AXIOM-JSON {d}: {String.intercalate "," (axl.map Name.toString)}"
    let unapproved := axl.filter (fun a => !approved.contains a)
    if !unapproved.isEmpty then
      bad := (d, unapproved) :: bad
  if !bad.isEmpty then
    throwError m!"AXIOM-AUDIT FAIL-CLOSED: unapproved axiom cones: {bad.map (fun p => (p.1.toString, p.2.map Name.toString))}"
  logInfo m!"AXIOM-AUDIT PASS: {auditedClosedFormDeclarations.length} declarations, every cone is a subset of the approved classical trio (propext, Classical.choice, Quot.sound)"

end Poincare.L4.Compactness.Audit
