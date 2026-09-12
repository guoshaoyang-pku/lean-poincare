import Audit.CounterexampleAudit
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

run_cmd do
  let env ← getEnv
  for n in [`D4Audit.transfer_nonvacuous, `D4Audit.finiteMeshConvergence_nonvacuous,
            `Poincare.D7.Limit.finiteMeshConvergence_of_stability] do
    match env.find? n with
    | some ci => IO.println s!"FOUND {n}"
    | none => IO.println s!"MISSING {n}"
  IO.println "---- telescope heads ----"
  liftTermElabM do
    for n in [`D4Audit.transfer_nonvacuous, `D4Audit.finiteMeshConvergence_nonvacuous,
              `Poincare.D7.Limit.finiteMeshConvergence_of_stability] do
      match env.find? n with
      | some ci =>
        Meta.forallTelescopeReducing ci.type fun _ body => do
          IO.println s!"HEAD {n} = {body.getAppFn}"
      | none => pure ()
