/-
SEMREV independent fail-closed census probe for D13-manifold-ibp-volume-form.
Written for longrun task SEMREV-D13-cross-audit-ophis; imports the transported snapshot only.
-/
import Poincare.D12.VolumeIBP.Audit
import Poincare.D13.Audit
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace SEMREV_D13_manifold_ibp_volume_form_neg

def approvedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def negativeControlModules : List Name := [
  ]

def auditedModules : List Name := [
  "Poincare.D12.VolumeIBP.Audit".toName,
  "Poincare.D13.Audit".toName]

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

end SEMREV_D13_manifold_ibp_volume_form_neg

open SEMREV_D13_manifold_ibp_volume_form_neg in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let auditedSet : Std.HashSet Name :=
    auditedModules.foldl (fun acc m => acc.insert m) ∅
  let rows := env.constants.fold (fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some midx =>
        let m := mods.getD midx .anonymous
        if auditedSet.contains m && !negativeControlModules.contains m then acc.push (n, ci, m)
        else acc
    | none => acc) #[]
  let mut nAxiom := 0
  let mut nUnsafe := 0
  let mut nSorry := 0
  let mut nNative := 0
  let mut nOther := 0
  let mut nFail := 0
  let mut nPartial := 0
  let mut nThm := 0
  let mut nOpaque := 0
  let mut nProofWanted := 0
  for (n, ci, m) in rows do
    if n.toString.contains "proof_wanted" then nProofWanted := nProofWanted + 1
    match ci with
    | .axiomInfo _ => nAxiom := nAxiom + 1
    | .opaqueInfo _ => nOpaque := nOpaque + 1
    | .defnInfo v =>
        match v.safety with
        | .«unsafe» => nUnsafe := nUnsafe + 1
        | .«partial» => nPartial := nPartial + 1
        | .safe => pure ()
    | .thmInfo _ => nThm := nThm + 1
    | _ => pure ()
    let axs ←
      try Lean.collectAxioms n
      catch _ => nFail := nFail + 1; pure #[]
    for a in axs do
      if a == ``sorryAx then nSorry := nSorry + 1
      else if a == ``ofReduceBool || a.toString.contains "native_decide" then nNative := nNative + 1
      else if !approvedAxioms.contains a then nOther := nOther + 1
    IO.println s!"XDECL\t{n}\t{kindOf ci}\t{m}\t{";".intercalate (axs.toList.map Name.toString)}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tdeclarations\t{rows.size}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\ttheorems\t{nThm}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tpartial_defs\t{nPartial}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\topaque\t{nOpaque}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tproject_axioms\t{nAxiom}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tunsafe\t{nUnsafe}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tsorry_cones\t{nSorry}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tnative_decide_cones\t{nNative}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tunapproved_axiom_cones\t{nOther}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tcollect_failures\t{nFail}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tproof_wanted\t{nProofWanted}"
  if nAxiom + nUnsafe + nSorry + nNative + nOther + nFail + nProofWanted > 0 then
    IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tVERDICT\tFAIL"
    throwError "SEMREV: forbidden dependency found (D13-manifold-ibp-volume-form)"
  else
    IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tVERDICT\tPASS"
