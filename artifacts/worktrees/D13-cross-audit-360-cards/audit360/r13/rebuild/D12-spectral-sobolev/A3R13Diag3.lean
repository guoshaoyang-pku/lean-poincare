import Poincare.D12.SpectralSobolev.Basic
open Lean Elab Command
open Lean Meta
namespace A3R13Diag3
def go (n : Name) : CommandElabM Unit := do
  liftTermElabM do
    let ci ← getConstInfo n
    match ci with | .defnInfo _ => logInfo "kind: def" | .thmInfo _ => logInfo "kind: thm" | _ => logInfo "kind: other"
    Lean.Meta.forallTelescope ci.type (fun args body => do
      logInfo m!"body={body} : {← inferType body}"
      for a in args do
        let ty ← inferType a
        logInfo m!"  hyp {a.fvarId!.name} : {ty}  defeq_body={← isDefEq ty body}")
end A3R13Diag3
run_cmd A3R13Diag3.go ``Poincare.D12.SpectralSobolev.heatWeight
