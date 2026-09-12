/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (L3-analytic-critical-path)

# Negative control for the L3 fail-closed axiom audit

This file is deliberately OUTSIDE the release package (`release/`), so the dispatcher's per-file
compile gate does not elaborate it. It declares an unapproved axiom (`l3NegControlBadAxiom`),
derives `l3NegControlBad : False` from it, and runs the *same* predicate as
`Poincare.L3.HeatTimeDeriv.Audit`: the check must detect the unapproved axiom and fail
(exit code 1). This certifies that the PASS verdict of the L3 audit is not vacuous.

Run from `release/`:  lake env lean ../audit-evidence/negcontrol/L3NegControl.lean
Expected: exit 1 with `L3NegControlAxiomCheck: FAIL (expected)`.
-/

import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

/-- The intentional bad axiom: not in the approved cone. -/
axiom l3NegControlBadAxiom : False

/-- A theorem whose axiom cone contains the bad axiom. -/
theorem l3NegControlBad : False := l3NegControlBadAxiom

/-- The same approved cone as the real audit. -/
private def l3NegControlApprovedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let axs ← Lean.collectAxioms ``l3NegControlBad
  let bad := axs.toList.filter (fun a => !l3NegControlApprovedAxioms.contains a)
  if bad.isEmpty then
    logInfo m!"L3NegControlAxiomCheck: UNEXPECTED PASS — the auditor did not detect the bad axiom"
  else
    logInfo m!"L3NegControlAxiomCheck: detected unapproved axioms {bad.map Name.toString}"
    throwError "L3NegControlAxiomCheck: FAIL (expected) — the fail-closed audit rejects this file"
