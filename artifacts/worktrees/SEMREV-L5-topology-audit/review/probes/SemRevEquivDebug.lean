/- SEMREV-L5: debug/verification of the whole-package conclusion-equivalence scan.
   Prints, for each flagged declaration, the telescope local contexts and the body,
   marking the local whose type is definitionally equal to the conclusion. -/
import Poincare.D9.DeTurck.StatementOnly
import Poincare.D7.Compactness.ManifoldStatements
import Poincare.D10.MaximumPrincipleRN.WeakMaximumPrinciple
import Poincare.D11.MaximumPrincipleTensor.Euler
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Lean Elab Command

namespace SemRevEquivDebug

def targets : List Name := [
  `Poincare.Longrun.DeTurck.FlowInterface.toy_ricciFlowUniqueness,
  `Poincare.Longrun.DeTurck.FlowInterface.toy_ricciFlowUniqueness_of_deturck,
  `Poincare.Longrun.DeTurck.FlowInterface.toy_uniqueness,
  `Poincare.D7.Compactness.cheegerGromov_of_ghSubsequence,
  `Poincare.D10.MaximumPrincipleRN.weak_maximum_principle_const,
  `Poincare.D11.MaximumPrincipleTensor.PositivityPreserving.id,
  `Poincare.Longrun.Topology.stage6Target_of_sphereRecognition,
  `Poincare.Longrun.Topology.stage6Target_of_compactThreeManifold,
  `Poincare.D7.SurgeryFlow.realLineProcedureChain_simplyConnected,
]

run_cmd do
  let env ← getEnv
  liftTermElabM do
    for n in targets do
      match env.find? n with
      | none => IO.println s!"EQUIVDBG\t{n}\tMISSING"
      | some ci =>
          try
            Meta.forallTelescopeReducing ci.type fun _ body => do
              let lctx ← getLCtx
              let mut idx := 0
              for x in lctx do
                if !x.isLet && !x.isImplementationDetail then
                  let same := Expr.equal x.type body
                  let deq ← try Meta.isDefEq x.type body catch _ => pure false
                  if same || deq then
                    let ht ← Meta.ppExpr x.type
                    let bt ← Meta.ppExpr body
                    IO.println s!"EQUIVDBG\t{n}\thyp#{idx}\t{x.userName}\tsyntactic={same}\tdefeq={deq}"
                    IO.println s!"EQUIVDBG\thypType\t{(" ".intercalate (ht.pretty.splitOn "\n")).take 300}"
                    IO.println s!"EQUIVDBG\tconcl\t{(" ".intercalate (bt.pretty.splitOn "\n")).take 300}"
                  idx := idx + 1
          catch _ => IO.println s!"EQUIVDBG\t{n}\tERROR"

end SemRevEquivDebug
