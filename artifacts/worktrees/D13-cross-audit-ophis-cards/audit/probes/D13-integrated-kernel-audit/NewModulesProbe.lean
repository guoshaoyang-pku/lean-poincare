/-
Independent cross-audit probe: import exactly the D13-integrated-kernel-audit roots and audit
EVERY package declaration reachable in that environment with an independently written detector.
Emits the reachable module list (D13XMOD) so coverage can be compared against the 456 source
modules on disk.
-/
import Poincare.D13.IntegratedAudit.SnapshotRoot
import Poincare.D13.IntegratedAudit.SelfAudit
import ReleaseCheck
import ReleaseAudit
import D6AuditReport
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace D13XFullClosure

def approvedAxioms : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]

def excluded : List Name := [
  "Poincare.D12.TriangulationTopology.NegControl.NegControl".toName,
  "Poincare.D12.VolumeIBP.Audit".toName]

def packageRoots : List Name := [
  "Poincare".toName, "Probe".toName, "Ledger".toName, "Audit".toName,
  "ReleaseCheck".toName, "ReleaseAudit".toName, "D6AuditReport".toName]

def kindOf : ConstantInfo → String
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

end D13XFullClosure

open D13XFullClosure in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let newRoots : List Name := ["Poincare.D11".toName, "Poincare.D12".toName, "Poincare.VKPort".toName]
  let inPackage (m : Name) : Bool :=
    newRoots.any (fun r => r.isPrefixOf m) && !excluded.contains m
  let allRows := env.constants.fold (fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some midx =>
        let m := mods.getD midx .anonymous
        if inPackage m then acc.push (n, ci, m) else acc
    | none => acc) #[]
  let mut moduleSet : Array Name := #[]
  for (_, _, m) in allRows do
    if !moduleSet.contains m then moduleSet := moduleSet.push m
  let sortedMods := moduleSet.qsort (fun a b => a.toString < b.toString)
  for m in sortedMods do
    IO.println s!"D13XMOD\t{m}"
  let mut nAxiom := 0
  let mut nUnsafe := 0
  let mut nSorry := 0
  let mut nNative := 0
  let mut nOther := 0
  let mut nFail := 0
  let mut nPartial := 0
  let mut nThm := 0
  for (name, ci, _m) in allRows do
    match ci with
    | .axiomInfo _ => nAxiom := nAxiom + 1
    | .defnInfo v =>
        match v.safety with
        | .«unsafe» => nUnsafe := nUnsafe + 1
        | .«partial» => nPartial := nPartial + 1
        | .safe => pure ()
    | .thmInfo _ => nThm := nThm + 1
    | _ => pure ()
    let axs ←
      try
        Lean.collectAxioms name
      catch _ =>
        nFail := nFail + 1
        pure #[]
    for a in axs do
      if a == ``sorryAx then nSorry := nSorry + 1
      else if a.toString.contains "native_decide" || a == ``ofReduceBool then nNative := nNative + 1
      else if !approvedAxioms.contains a then nOther := nOther + 1
  IO.println s!"D13XNEW\tmodules\t{sortedMods.size}"
  IO.println s!"D13XNEW\tdeclarations\t{allRows.size}"
  IO.println s!"D13XNEW\ttheorems\t{nThm}"
  IO.println s!"D13XNEW\tpartial_defs\t{nPartial}"
  IO.println s!"D13XNEW\tproject_axioms\t{nAxiom}"
  IO.println s!"D13XNEW\tunsafe\t{nUnsafe}"
  IO.println s!"D13XNEW\tsorry_cones\t{nSorry}"
  IO.println s!"D13XNEW\tnative_cones\t{nNative}"
  IO.println s!"D13XNEW\tunapproved_cones\t{nOther}"
  IO.println s!"D13XNEW\tcollect_failures\t{nFail}"
  if nAxiom + nUnsafe + nSorry + nNative + nOther + nFail > 0 then
    IO.println "D13XNEW\tVERDICT\tFAIL"
    throwError "D13XFullClosure: forbidden dependency found"
  else
    IO.println "D13XNEW\tVERDICT\tPASS"
