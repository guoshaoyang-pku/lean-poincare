/-
D5-clean-rebuild — negative control for the dependency audit.

This file is intentionally NOT part of the release package and is never imported by
ReleaseCheck.lean.  It proves that the audit machinery (`Lean.collectAxioms` + the
approved-axiom set) actually detects the forbidden trust primitives:

* `sorry`  -> `sorryAx`
* `native_decide` -> a private `..._native.native_decide.ax_...` axiom (in this Lean
  version `native_decide` does not route through `ofReduceBool`, so the audit's
  "unapproved axiom" rule is the one that catches it).

Run from the release directory:

    lake env lean ../negcontrol/NegativeControl.lean

Expected output: the sorry cone contains `sorryAx`; the native_decide cone contains an
axiom outside `{propext, Classical.choice, Quot.sound}`; the final line reports PASS.
-/
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

theorem negControl_sorry : True := by sorry

theorem negControl_nativeDecide : (2 + 2 = 4) := by native_decide

run_cmd do
  let approved : List Name :=
    ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let a1 ← Lean.collectAxioms ``negControl_sorry
  let a2 ← Lean.collectAxioms ``negControl_nativeDecide
  logInfo m!"NegativeControl: sorry cone = {a1.toList.map Name.toString}"
  logInfo m!"NegativeControl: native_decide cone = {a2.toList.map Name.toString}"
  if !a1.contains (Name.str .anonymous "sorryAx") then
    throwError "NegativeControl: sorryAx was NOT detected — audit predicate is broken"
  let unapproved := a2.filter (fun a => !approved.contains a)
  if unapproved.isEmpty then
    throwError "NegativeControl: native_decide produced no unapproved axiom — audit predicate is broken"
  logInfo m!"NegativeControl: PASS — audit detects sorryAx and native_decide \
    (unapproved axiom {unapproved.toList.map Name.toString})"
