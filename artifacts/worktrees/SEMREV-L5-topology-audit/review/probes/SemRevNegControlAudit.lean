/- SEMREV-L5 fail-closed negative control for the reviewer's own detector.

Expected behaviour: this file FAILS to elaborate (non-zero exit) and names
  * semrevFreshBadAxiom      (project axiom)
  * semrevFreshBadTheorem    (consumes the axiom)
  * semrevFreshSorry         (sorryAx cone)
  * semrevFreshNative        (Lean.ofReduceBool / native_decide cone)
Every one of these is outside the L5 release and outside the reviewer allow-list.
-/
import Lean.Util.CollectAxioms
import Lean.Elab.Command
import SemRevNegControl

open Lean Elab Command

namespace SemRevNegControlAudit

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def fresh : List Name := [
  `semrevFreshBadAxiom,
  `semrevFreshBadTheorem,
  `semrevFreshSorry,
  `semrevFreshNative,
]

run_cmd do
  let env ← getEnv
  let mut violations : Array String := #[]
  for n in fresh do
    match env.find? n with
    | none => violations := violations.push s!"missing {n}"
    | some _ =>
      let axs ←
        try Lean.collectAxioms n
        catch _ => pure #[`collectAxiomsException]
      IO.println s!"SEMREVNEGCONE\t{n}\t{";".intercalate (axs.toList.map Name.toString)}"
      let bad := axs.toList.filter (fun a => !allowedAxioms.contains a)
      if bad.isEmpty then
        violations := violations.push s!"CLEAN (should be dirty) {n}"
      else
        violations := violations.push s!"dirty {n} -> {bad.length} forbidden axiom(s)"
  for v in violations do IO.println s!"SEMREVNEGFAIL\t{v}"
  IO.println s!"SEMREVNEG\tviolations={violations.size}"
  if violations.isEmpty then
    throwError "SEMREV negative control did not fire"
  else
    throwError "SEMREV negative control fired as expected"
  pure ()

end SemRevNegControlAudit
