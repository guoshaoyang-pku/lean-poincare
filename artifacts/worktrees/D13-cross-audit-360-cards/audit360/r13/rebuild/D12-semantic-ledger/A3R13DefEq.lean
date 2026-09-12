-- A3 round-13 definitional hyp-equals-conclusion screen (generated)
import Poincare.D12.SemanticLedger.AxiomAudit
import Poincare.D12.SemanticLedger.Defect
import Poincare.D12.SemanticLedger.LedgerProbe

open Lean Elab Command
open Lean Meta
namespace A3R13D

def claimed : List Name := [``Poincare.D12.SemanticLedger.integrand_lintegral_eq_top,
  ``Poincare.D12.SemanticLedger.integrand_not_integrable,
  ``Poincare.D12.SemanticLedger.lowerConstant_le_integrand,
  ``Poincare.D12.SemanticLedger.not_initialCondition_gaussian,
  ``Poincare.D12.SemanticLedger.not_initialCondition_gaussian_quantified,
  ``Poincare.D12.SemanticLedger.quartic_dominates,
  ``Poincare.D12.SemanticLedger.tendsto_testFunction_atTop]

/-- Only theorems with a Prop-valued hypothesis can commit the
assumption-as-conclusion defect; a plain function whose argument type equals
its result type (e.g. `def f (x : R) : R`) is benign. -/
def run : CommandElabM Unit := do
  liftTermElabM do
    let mut checked := 0
    for n in claimed do
      let ci ← getConstInfo n
      unless ci matches .thmInfo _ do continue
      checked := checked + 1
      Lean.Meta.forallTelescope ci.type (fun args body => do
        if ← isDefEq body (.const ``True []) then
          logInfo m!"A3R13D|TRIVIAL_TRUE|{n}"
        for a in args do
          let ty ← inferType a
          if ← isProp ty then
            if ← isDefEq ty body then
              let u := a.fvarId!.name
              logInfo m!"A3R13D|HYP_DEFEQ|{n}|{u}"
        )
    logInfo m!"A3R13D|CHECKED|{checked}"
  logInfo m!"A3R13D|DONE"

end A3R13D
run_cmd A3R13D.run
