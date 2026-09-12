/-
Independent negative-control probe for D13-integrated-kernel-audit.
Imports ONLY the two modules that intentionally declare `axiom ... : False` and runs a
fail-closed detector.  Expected result: FAIL (nonzero exit) naming exactly those axioms —
i.e. the detector is not vacuous.
-/
import Poincare.D12.TriangulationTopology.NegControl.NegControl
import Poincare.D12.VolumeIBP.Audit
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace D13XNegControl

def approvedAxioms : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]

end D13XNegControl

open D13XNegControl in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let rows := env.constants.fold (fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some midx =>
        let m := mods.getD midx .anonymous
        if m == "Poincare.D12.TriangulationTopology.NegControl.NegControl".toName
            || m == "Poincare.D12.VolumeIBP.Audit".toName then acc.push (n, ci) else acc
    | none => acc) #[]
  let mut nAxiom := 0
  let mut nOther := 0
  for (n, _ci) in rows do
    match env.find? n with
    | some ci =>
        match ci with
        | .axiomInfo _ =>
            nAxiom := nAxiom + 1
            IO.println s!"D13XNEGFAIL\tproject_axiom\t{n}"
        | _ => pure ()
    | none => pure ()
    let axs ←
      try
        Lean.collectAxioms n
      catch _ => pure #[]
    for a in axs do
      if !approvedAxioms.contains a then
        nOther := nOther + 1
        IO.println s!"D13XNEGFAIL\tunapproved_axiom\t{n}\t{a}"
  IO.println s!"D13XNEG\tproject_axioms\t{nAxiom}"
  IO.println s!"D13XNEG\tunapproved_cones\t{nOther}"
  if nAxiom > 0 || nOther > 0 then
    IO.println "D13XNEG\tVERDICT\tFAIL (expected)"
    throwError "D13XNegControl: forbidden axiom detected (this failure is the expected control result)"
  else
    IO.println "D13XNEG\tVERDICT\tPASS (unexpected: control not detected)"
