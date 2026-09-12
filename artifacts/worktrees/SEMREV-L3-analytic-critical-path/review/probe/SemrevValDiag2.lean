import Poincare.L3.HeatTimeDeriv.All
import Lean

open Lean

namespace SemrevValDiag2

theorem localThm : True := trivial

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo v => if v.safety == .unsafe then "unsafe-def" else "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

run_cmd do
  let env ← getEnv
  let names : List Name :=
    [ ``SemrevValDiag2.localThm,
      ``Nat.add_comm, ``List.append_nil, ``Nat.zero_le,
      ``Poincare.L3.HeatTimeDeriv.timeDerivIntegral,
      ``Poincare.L3.HeatTimeDeriv.heatConv_classicalHeatSolution,
      ``Poincare.L3.HeatTimeDeriv.KernelClassicalHeatSolution.T,
      ``Poincare.L3.HeatTimeDeriv.KernelClassicalHeatSolution.isSolution,
      ``Poincare.L3.HeatTimeDeriv.timeCoeff,
      ``Poincare.D12.ParabolicLocal.heatConv ]
  for n in names do
    match env.find? n with
    | none => logInfo s!"SEMREV-VALDIAG2|{n}|MISSING"
    | some ci =>
      logInfo s!"SEMREV-VALDIAG2|{n}|{kindOf ci}|value-present|{ci.value?.isSome}"

end SemrevValDiag2
