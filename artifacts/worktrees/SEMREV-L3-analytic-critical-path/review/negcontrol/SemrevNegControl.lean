/-
SEMREV-L3 independent review — negative control for the *reviewer's* fail-closed predicate.

Declares an unapproved axiom, derives a theorem from it, and applies the same predicate used in
`SemrevAudit.lean`. Must exit 1 naming the bad axiom; certifies that the reviewer's PASS is not
vacuous.
-/

import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

/-- Intentional bad axiom for the reviewer's negative control. -/
axiom semrevBadAxiom : False

/-- A theorem whose cone contains the bad axiom. -/
theorem semrevBad : False := semrevBadAxiom

def approvedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let axs ← Lean.collectAxioms ``semrevBad
  let bad := axs.toList.filter (fun a => !approvedAxioms.contains a)
  if bad.isEmpty then
    logInfo "SEMREV-NEGCONTROL: UNEXPECTED PASS"
  else
    logInfo m!"SEMREV-NEGCONTROL: detected unapproved axioms {bad.map Name.toString}"
    throwError "SEMREV-NEGCONTROL: FAIL (expected) — the reviewer's predicate rejects this file"
