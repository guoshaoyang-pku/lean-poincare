/-
Copyright (c) 2026 D13-integrated-kernel-audit. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D13 integrated kernel audit — self-audit of the auditor's own declarations

The primary audit (`KernelAudit.lean`) covers the D11/D12 declarations of the snapshot.
This module audits the *auditor's own* declarations (every module under `Poincare.D13`),
with the same fail-closed rules, so the audit tooling cannot smuggle in an unapproved
axiom.  It also re-imports the statement scan (`StatementAudit.lean`) and the dependency
and usage probes so that a single `lake build` of this module rebuilds and re-checks the
whole D13 layer.
-/
import Poincare.D13.IntegratedAudit.KernelAudit
import Poincare.D13.IntegratedAudit.StatementAudit
import Poincare.D13.IntegratedAudit.DependencyProbe
import Poincare.D13.IntegratedAudit.UsageProbe
import Poincare.D13.IntegratedAudit.NonvacuityProbe
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

namespace Poincare.D13.IntegratedAudit

/-- Modules the D13 layer is expected to consist of. -/
def expectedD13Modules : List Name := [
  "Poincare.D13.IntegratedAudit.ExpectedModules".toName,
  "Poincare.D13.IntegratedAudit.SnapshotRoot".toName,
  "Poincare.D13.IntegratedAudit.AuditCore".toName,
  "Poincare.D13.IntegratedAudit.KernelAudit".toName,
  "Poincare.D13.IntegratedAudit.StatementAudit".toName,
  "Poincare.D13.IntegratedAudit.DependencyProbe".toName,
  "Poincare.D13.IntegratedAudit.UsageProbe".toName,
  "Poincare.D13.IntegratedAudit.NonvacuityProbe".toName
]

end Poincare.D13.IntegratedAudit

open Poincare.D13.IntegratedAudit in
run_cmd do
  let env ← getEnv
  let imported := env.header.moduleNames
  let mut missing : Array Name := #[]
  for m in expectedD13Modules do
    unless imported.contains m do
      missing := missing.push m
  let rows : Array (Name × ConstantInfo × Name) :=
    env.constants.fold (fun acc n ci =>
      match env.getModuleIdxFor? n with
      | some midx =>
          let m := imported.getD midx .anonymous
          if m.toString.startsWith "Poincare.D13" then acc.push (n, ci, m) else acc
      | none => acc) #[]
  let rows := rows.qsort (fun a b => a.1.toString < b.1.toString)
  let mut axioms : Array Name := #[]
  let mut unsafeDefs : Array Name := #[]
  let mut partialDefs : Array Name := #[]
  let mut sorryDecls : Array Name := #[]
  let mut otherAxiomDecls : Array (Name × Name) := #[]
  let mut failures : Array Name := #[]
  for (n, ci, _) in rows do
    match ci with
    | .axiomInfo _ => axioms := axioms.push n
    | .defnInfo v =>
        match v.safety with
        | .«unsafe» => unsafeDefs := unsafeDefs.push n
        | .«partial» => partialDefs := partialDefs.push n
        | .safe => pure ()
    | _ => pure ()
    let axs ←
      try
        Lean.collectAxioms n
      catch _ =>
        failures := failures.push n
        pure #[]
    for a in axs do
      if a == sorryAxiom then sorryDecls := sorryDecls.push n
      else if !approvedAxioms.contains a then otherAxiomDecls := otherAxiomDecls.push (n, a)
    IO.println s!"D13SELFDECL\t{n}\t{kindOf ci}\t{";".intercalate (axs.toList.map Name.toString)}"
  IO.println s!"D13SELFAUDIT\texpected_d13_modules\t{expectedD13Modules.length}"
  IO.println s!"D13SELFAUDIT\tmissing_modules\t{missing.size}"
  IO.println s!"D13SELFAUDIT\tdeclarations_audited\t{rows.size}"
  IO.println s!"D13SELFAUDIT\tproject_axioms\t{axioms.size}"
  IO.println s!"D13SELFAUDIT\tunsafe_declarations\t{unsafeDefs.size}"
  IO.println s!"D13SELFAUDIT\tpartial_declarations\t{partialDefs.size}"
  IO.println s!"D13SELFAUDIT\tsorry_declarations\t{sorryDecls.size}"
  IO.println s!"D13SELFAUDIT\tunapproved_axiom_declarations\t{otherAxiomDecls.size}"
  IO.println s!"D13SELFAUDIT\tcollect_failures\t{failures.size}"
  for m in missing do IO.println s!"D13SELFFAIL\tmissing_module\t{m}"
  for n in axioms do IO.println s!"D13SELFFAIL\tproject_axiom\t{n}"
  for n in unsafeDefs do IO.println s!"D13SELFFAIL\tunsafe\t{n}"
  for n in sorryDecls do IO.println s!"D13SELFFAIL\tsorryAx\t{n}"
  for (n, a) in otherAxiomDecls do IO.println s!"D13SELFFAIL\tunapproved_axiom\t{n}\t{a}"
  for n in failures do IO.println s!"D13SELFFAIL\tcollect_axioms_exception\t{n}"
  unless missing.isEmpty && axioms.isEmpty && unsafeDefs.isEmpty && sorryDecls.isEmpty
      && otherAxiomDecls.isEmpty && failures.isEmpty do
    IO.println "D13SELFVERDICT\tFAIL"
    throwError "D13IntegratedAudit: D13 layer self-audit FAILED"
  IO.println "D13SELFVERDICT\tPASS — the auditor's own declarations are kernel-clean"
