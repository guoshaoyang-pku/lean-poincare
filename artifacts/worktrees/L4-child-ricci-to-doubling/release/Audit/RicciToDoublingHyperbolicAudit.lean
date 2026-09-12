/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Fail-closed audit for `Poincare.L4.Compactness.RicciToDoublingHyperbolic`

Companion of `Audit/RicciToDoublingAudit.lean`: prints the full signature of every
declaration of the hyperbolic-model file (`#check`) and runs `Lean.collectAxioms` on each,
failing closed (non-zero exit) if any cone is not a subset of
`{propext, Classical.choice, Quot.sound}`.  The declaration list is literal, so a
missing/renamed declaration fails the `#check` lines.

`coth_sub_inv_abs_le_one` is a public theorem (used in `hypModelM_normalized`); its two
supporting private lemmas (`sinh_mul_cosh_sub_sinh_nonneg`, `sinh_mul_cosh_sub_sinh_le`) are
private and are audited indirectly through the public theorem's cone.
-/
import Poincare.L4.Compactness.RicciToDoublingHyperbolic
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

namespace Poincare.L4.Compactness.Audit

#check @hypModelK
#check @hypModelA
#check @hypModelM
#check @hypModelDm
#check @hypModelDA
#check @coth_sub_inv_abs_le_one
#check @hypModelM_hasDerivAt
#check @hypModelM_riccati
#check @hypModelM_contOn
#check @hypModelM_normalized
#check @hypModelA_hasDerivAt
#check @hypModelA_contOn
#check @hypModelA_pos
#check @hypModelA_zero
#check @hypModelA_logDeriv
#check @hyp_volume_ratio_le_of_ricci_ge
#check @hyp_volume_doubling_of_ricci_ge
#check @hypModel_doubling_witness
#check @hypModelA_one_one_volume
#check @hypModelA_one_one_doubling
#check @hyp_volume_doubling_d1_k1

/-- The exact declaration list the audit must cover. -/
def auditedHyperbolicDeclarations : List Name :=
  [ ``hypModelK
  , ``hypModelA
  , ``hypModelM
  , ``hypModelDm
  , ``hypModelDA
  , ``coth_sub_inv_abs_le_one
  , ``hypModelM_hasDerivAt
  , ``hypModelM_riccati
  , ``hypModelM_contOn
  , ``hypModelM_normalized
  , ``hypModelA_hasDerivAt
  , ``hypModelA_contOn
  , ``hypModelA_pos
  , ``hypModelA_zero
  , ``hypModelA_logDeriv
  , ``hyp_volume_ratio_le_of_ricci_ge
  , ``hyp_volume_doubling_of_ricci_ge
  , ``hypModel_doubling_witness
  , ``hypModelA_one_one_volume
  , ``hypModelA_one_one_doubling
  , ``hyp_volume_doubling_d1_k1 ]

run_cmd do
  let approved : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : List (Name × List Name) := []
  for d in auditedHyperbolicDeclarations do
    let axs ← Lean.collectAxioms d
    let axl := axs.toList
    logInfo m!"AXIOM-JSON {d}: {String.intercalate "," (axl.map Name.toString)}"
    let unapproved := axl.filter (fun a => !approved.contains a)
    if !unapproved.isEmpty then
      bad := (d, unapproved) :: bad
  if !bad.isEmpty then
    throwError m!"AXIOM-AUDIT FAIL-CLOSED: unapproved axiom cones: {bad.map (fun p => (p.1.toString, p.2.map Name.toString))}"
  logInfo m!"AXIOM-AUDIT PASS: {auditedHyperbolicDeclarations.length} declarations, every cone is a subset of the approved classical trio (propext, Classical.choice, Quot.sound)"

end Poincare.L4.Compactness.Audit
