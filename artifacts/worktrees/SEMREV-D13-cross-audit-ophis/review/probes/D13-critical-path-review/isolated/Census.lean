/-
SEMREV independent fail-closed census probe for D13-critical-path-review-isolated.
Written for longrun task SEMREV-D13-cross-audit-ophis; imports the transported snapshot only.
-/
import Poincare.D7.Kappa.All
import Poincare.D7.Kappa.Audit
import Poincare.D7.Kappa.EntropyBridge
import Poincare.D7.Kappa.Nonvacuity
import Poincare.D7.Kappa.Probe
import Poincare.D7.Kappa.Statements
import Poincare.D7.Monotonicity.All
import Poincare.D7.Monotonicity.Blockers
import Poincare.D7.Monotonicity.BochnerGradientEstimate
import Poincare.D7.Monotonicity.FMonotonicity
import Poincare.D7.Monotonicity.Nonvacuity
import Poincare.D7.Monotonicity.WMuMonotonicity
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace SEMREV_D13_critical_path_review_isolated

def approvedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def negativeControlModules : List Name := [
  ]

def auditedModules : List Name := [
  "Poincare.D7.Kappa.All".toName,
  "Poincare.D7.Kappa.Audit".toName,
  "Poincare.D7.Kappa.EntropyBridge".toName,
  "Poincare.D7.Kappa.Nonvacuity".toName,
  "Poincare.D7.Kappa.Probe".toName,
  "Poincare.D7.Kappa.Statements".toName,
  "Poincare.D7.Monotonicity.All".toName,
  "Poincare.D7.Monotonicity.Blockers".toName,
  "Poincare.D7.Monotonicity.BochnerGradientEstimate".toName,
  "Poincare.D7.Monotonicity.FMonotonicity".toName,
  "Poincare.D7.Monotonicity.Nonvacuity".toName,
  "Poincare.D7.Monotonicity.WMuMonotonicity".toName]

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

end SEMREV_D13_critical_path_review_isolated

open SEMREV_D13_critical_path_review_isolated in
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
  IO.println s!"XAUDIT\tD13-critical-path-review-isolated\tdeclarations\t{rows.size}"
  IO.println s!"XAUDIT\tD13-critical-path-review-isolated\ttheorems\t{nThm}"
  IO.println s!"XAUDIT\tD13-critical-path-review-isolated\tpartial_defs\t{nPartial}"
  IO.println s!"XAUDIT\tD13-critical-path-review-isolated\topaque\t{nOpaque}"
  IO.println s!"XAUDIT\tD13-critical-path-review-isolated\tproject_axioms\t{nAxiom}"
  IO.println s!"XAUDIT\tD13-critical-path-review-isolated\tunsafe\t{nUnsafe}"
  IO.println s!"XAUDIT\tD13-critical-path-review-isolated\tsorry_cones\t{nSorry}"
  IO.println s!"XAUDIT\tD13-critical-path-review-isolated\tnative_decide_cones\t{nNative}"
  IO.println s!"XAUDIT\tD13-critical-path-review-isolated\tunapproved_axiom_cones\t{nOther}"
  IO.println s!"XAUDIT\tD13-critical-path-review-isolated\tcollect_failures\t{nFail}"
  IO.println s!"XAUDIT\tD13-critical-path-review-isolated\tproof_wanted\t{nProofWanted}"
  if nAxiom + nUnsafe + nSorry + nNative + nOther + nFail + nProofWanted > 0 then
    IO.println s!"XAUDIT\tD13-critical-path-review-isolated\tVERDICT\tFAIL"
    throwError "SEMREV: forbidden dependency found (D13-critical-path-review-isolated)"
  else
    IO.println s!"XAUDIT\tD13-critical-path-review-isolated\tVERDICT\tPASS"
