/-
Copyright (c) 2026 D13-critical-path-review. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-critical-path-review)

# Task-local fail-closed axiom audit

Every declaration authored in `Poincare.D13.CriticalPathReview` is audited, together with
the load-bearing D7/D12 declarations this review relies on.  The audit fails closed:

* an exception while collecting a declaration's axioms is itself a failure (never a skip);
* every axiom cone must be contained in `{propext, Classical.choice, Quot.sound}`;
* `sorryAx`, the `native_decide` trust primitives and any project axiom are named and
  rejected;
* no audited declaration may be `unsafe`.

The intentional negative control lives in
`Poincare.D13.CriticalPathReview.NegControl` (never imported by any proof module); the
driver runs this same command against a root that *does* import it and requires the audit
to FAIL and to name the control axiom.

No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this module.
-/
import Poincare.D13.CriticalPathReview.UsageProbe
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option linter.unusedVariables false
set_option autoImplicit false

open Lean Elab Command

namespace Poincare.D13.CriticalPathReview

/-- The only axioms accepted in any audited dependency cone. -/
def approvedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `sorryAx` has a dedicated failure label. -/
def sorryAxiom : Name := ``sorryAx

/-- `native_decide` trust primitives. -/
def nativeAxioms : List Name := [``ofReduceBool, ``Lean.ofReduceBool]

/-- The namespace whose declarations are authored in this task. -/
def auditNamespace : Name := "Poincare.D13.CriticalPathReview".toName

/-- Load-bearing declarations from the snapshot that this review's evidence depends on.
They are audited here so that the review's claims do not rest on an unaudited cone. -/
def loadBearingDeclarations : List Name :=
  [ ``Poincare.D7.Recognition.stage6Target_of_certificates
  , ``Poincare.D12.SurgeryRecognition.stage6Target_of_v3hypotheses
  , ``Poincare.D12.SurgeryRecognition.deckTrivial_of_simplyConnected_quotient
  , ``Poincare.D12.SurgeryRecognition.sphericalPieceRecognition_of_spaceForm
  , ``Poincare.D12.TensorMaximumBochner.KernelTangent
  , ``Poincare.D12.TensorMaximumBochner.hamiltonField_kernelTangent
  , ``Poincare.D12.SemanticLedger.not_initialCondition_gaussian
  , ``Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2
  ]

/-- Declaration kind label. -/
def kindLabel : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo v => match v.safety with
    | .«unsafe» => "unsafe_def"
    | .«partial» => "partial_def"
    | .safe => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

/-- All declarations whose name is under `auditNamespace`, plus the load-bearing list. -/
def auditedDeclarations (env : Environment) : Array Name := Id.run do
  let mut acc : Array Name := #[]
  for (n, _) in env.constants.toList do
    if auditNamespace.isPrefixOf n && !n.toString.contains "_private" then
      acc := acc.push n
  for n in loadBearingDeclarations do
    if !acc.contains n then acc := acc.push n
  return acc

/-- Fail-closed axiom audit.  Emits `D13CPAUDIT*` lines and raises an elaboration error
unless every audited declaration is clean. -/
def runAxiomAudit : CommandElabM Unit := do
  let env ← getEnv
  let decls := auditedDeclarations env
  let mut projectAxioms : Array Name := #[]
  let mut unsafeDecls : Array Name := #[]
  let mut sorryDecls : Array Name := #[]
  let mut nativeDecls : Array Name := #[]
  let mut unapproved : Array (Name × Name) := #[]
  let mut collectFailures : Array (Name × String) := #[]
  for n in decls do
    match env.find? n with
    | none => collectFailures := collectFailures.push (n, "declaration not found")
    | some ci =>
      match ci with
      | .axiomInfo _ => projectAxioms := projectAxioms.push n
      | .defnInfo v => if v.safety == .«unsafe» then unsafeDecls := unsafeDecls.push n
      | _ => pure ()
      let axs ←
        try
          Lean.collectAxioms n
        catch _ =>
          collectFailures := collectFailures.push (n, "collectAxioms raised")
          pure #[]
      for a in axs do
        if a == sorryAxiom then sorryDecls := sorryDecls.push n
        else if nativeAxioms.contains a then nativeDecls := nativeDecls.push n
        else if !approvedAxioms.contains a then unapproved := unapproved.push (n, a)
      IO.println s!"D13CPAUDIT_DECL\t{n}\t{kindLabel ci}\t{";".intercalate (axs.toList.map Name.toString)}"
  let failed := !projectAxioms.isEmpty || !unsafeDecls.isEmpty || !sorryDecls.isEmpty ||
    !nativeDecls.isEmpty || !unapproved.isEmpty || !collectFailures.isEmpty
  IO.println s!"D13CPAUDIT\taudited_declarations\t{decls.size}"
  IO.println s!"D13CPAUDIT\tproject_axioms\t{projectAxioms.size}"
  IO.println s!"D13CPAUDIT\tunsafe\t{unsafeDecls.size}"
  IO.println s!"D13CPAUDIT\tsorryAx\t{sorryDecls.size}"
  IO.println s!"D13CPAUDIT\tnative_decide\t{nativeDecls.size}"
  IO.println s!"D13CPAUDIT\tunapproved_axioms\t{unapproved.size}"
  IO.println s!"D13CPAUDIT\tcollect_failures\t{collectFailures.size}"
  for n in projectAxioms do IO.println s!"D13CPAUDIT_FAIL\tproject_axiom\t{n}"
  for n in unsafeDecls do IO.println s!"D13CPAUDIT_FAIL\tunsafe\t{n}"
  for n in sorryDecls do IO.println s!"D13CPAUDIT_FAIL\tsorryAx\t{n}"
  for n in nativeDecls do IO.println s!"D13CPAUDIT_FAIL\tnative_decide\t{n}"
  for (n, a) in unapproved do IO.println s!"D13CPAUDIT_FAIL\tunapproved_axiom\t{n}\t{a}"
  for (n, e) in collectFailures do IO.println s!"D13CPAUDIT_FAIL\tcollect\t{n}\t{e}"
  if failed then
    IO.println "D13CPAUDIT_VERDICT\tFAIL"
    throwError "D13CriticalPathReview: axiom audit FAILED"
  else
    IO.println "D13CPAUDIT_VERDICT\tPASS"

/-- The fail-closed task-local axiom audit. -/
elab "#d13_axiom_audit" : command => runAxiomAudit

end Poincare.D13.CriticalPathReview

open Poincare.D13.CriticalPathReview

#d13_axiom_audit
