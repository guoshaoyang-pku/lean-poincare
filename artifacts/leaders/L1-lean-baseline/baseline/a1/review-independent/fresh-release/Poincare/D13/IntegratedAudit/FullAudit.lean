/-
Copyright (c) 2026 D13-integrated-kernel-audit. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D13 integrated kernel audit — full-package pass

The primary audit (`KernelAudit.lean`) covers the D11/D12/VKPort declarations added to the
release.  This module runs the same fail-closed checks over **every** declaration of the
integrated package (base D1–D10 modules, `Longrun`, `Stage*`, the drivers and the D13
layer), so that the kernel-trust statement covers the whole rebuilt snapshot, not only the
new layer.

The two intentional negative-control modules are imported by nothing and are excluded here
by name; they are audited separately by `audit-evidence/negcontrol/NegativeControlIncluded.lean`,
which must fail.
-/
import Poincare.D13.IntegratedAudit.SnapshotRoot
import Poincare.D13.IntegratedAudit.SelfAudit
import ReleaseCheck
import ReleaseAudit
import D6AuditReport
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

namespace Poincare.D13.IntegratedAudit

/-- Modules deliberately excluded from the full pass (their whole purpose is to declare a
forbidden axiom; see `NegativeControlIncluded.lean`). -/
def fullPassExcluded : List Name := [
  "Poincare.D12.TriangulationTopology.NegControl.NegControl".toName,
  "Poincare.D12.VolumeIBP.Audit".toName
]

/-- Module roots considered part of the integrated package. -/
def packageRoots : List Name := [
  "Poincare".toName, "Probe".toName, "Ledger".toName, "Audit".toName,
  "ReleaseCheck".toName, "ReleaseAudit".toName, "D6AuditReport".toName
]

end Poincare.D13.IntegratedAudit

open Poincare.D13.IntegratedAudit in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let inPackage (m : Name) : Bool :=
    packageRoots.any (fun r => r.isPrefixOf m) && !fullPassExcluded.contains m
  let rows : Array (Name × ConstantInfo × Name) :=
    env.constants.fold (fun acc n ci =>
      match env.getModuleIdxFor? n with
      | some midx =>
          let m := mods.getD midx .anonymous
          if inPackage m then acc.push (n, ci, m) else acc
      | none => acc) #[]
  let rows := rows.qsort (fun a b => a.1.toString < b.1.toString)
  let mut axioms : Array Name := #[]
  let mut unsafeDefs : Array Name := #[]
  let mut partialDefs : Array Name := #[]
  let mut sorryDecls : Array Name := #[]
  let mut nativeDecls : Array Name := #[]
  let mut otherAxiomDecls : Array (Name × Name) := #[]
  let mut failures : Array Name := #[]
  let mut moduleSet : Array Name := #[]
  for (n, ci, m) in rows do
    if !moduleSet.contains m then moduleSet := moduleSet.push m
    if n.toString.contains "proof_wanted" then
      otherAxiomDecls := otherAxiomDecls.push (n, "proof_wanted".toName)
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
      else if nativeAxioms.contains a then nativeDecls := nativeDecls.push n
      else if !approvedAxioms.contains a then otherAxiomDecls := otherAxiomDecls.push (n, a)
  IO.println s!"D13FULLAUDIT\tpackage_modules_with_declarations\t{moduleSet.size}"
  IO.println s!"D13FULLAUDIT\tdeclarations_audited\t{rows.size}"
  IO.println s!"D13FULLAUDIT\tpartial_declarations\t{partialDefs.size}"
  IO.println s!"D13FULLAUDIT\tproject_axioms\t{axioms.size}"
  IO.println s!"D13FULLAUDIT\tunsafe_declarations\t{unsafeDefs.size}"
  IO.println s!"D13FULLAUDIT\tsorry_declarations\t{sorryDecls.size}"
  IO.println s!"D13FULLAUDIT\tnative_decide_declarations\t{nativeDecls.size}"
  IO.println s!"D13FULLAUDIT\tunapproved_axiom_declarations\t{otherAxiomDecls.size}"
  IO.println s!"D13FULLAUDIT\tcollect_failures\t{failures.size}"
  for n in axioms do IO.println s!"D13FULLFAIL\tproject_axiom\t{n}"
  for n in unsafeDefs do IO.println s!"D13FULLFAIL\tunsafe\t{n}"
  for n in sorryDecls do IO.println s!"D13FULLFAIL\tsorryAx\t{n}"
  for (n, a) in otherAxiomDecls do IO.println s!"D13FULLFAIL\tunapproved_axiom\t{n}\t{a}"
  for n in failures do IO.println s!"D13FULLFAIL\tcollect_axioms_exception\t{n}"
  unless axioms.isEmpty && unsafeDefs.isEmpty && sorryDecls.isEmpty && nativeDecls.isEmpty
      && otherAxiomDecls.isEmpty && failures.isEmpty do
    IO.println "D13FULLVERDICT\tFAIL"
    throwError "D13IntegratedAudit: full-package kernel audit FAILED"
  IO.println "D13FULLVERDICT\tPASS — every package declaration depends only on {propext, Classical.choice, Quot.sound}"
