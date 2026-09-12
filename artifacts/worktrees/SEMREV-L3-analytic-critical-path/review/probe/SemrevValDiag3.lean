import Poincare.L3.HeatTimeDeriv.All
import Lean

open Lean Meta Elab Command

namespace SemrevValDiag3

theorem localThm : True := trivial

partial def constsIn (acc : Std.HashSet Name) : Expr → Std.HashSet Name
  | .const n _ => acc.insert n
  | .app f a => constsIn (constsIn acc f) a
  | .lam _ d b _ => constsIn (constsIn acc d) b
  | .forallE _ d b _ => constsIn (constsIn acc d) b
  | .letE _ d v b _ => constsIn (constsIn (constsIn acc d) v) b
  | .mdata _ b => constsIn acc b
  | .proj _ _ b => constsIn acc b
  | _ => acc

run_cmd liftTermElabM do
  let env ← getEnv
  for n in [``SemrevValDiag3.localThm, ``Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_holds,
            ``Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_BCF] do
    match env.find? n with
    | none => logInfo s!"SEMREV-VALDIAG3|{n}|MISSING"
    | some ci =>
      match ci.value? (allowOpaque := true) with
      | none => logInfo s!"SEMREV-VALDIAG3|{n}|no-value"
      | some v =>
        let cs := (constsIn {} v).toList
        let heat := cs.filter (fun c => (c.toString.splitOn "HeatTimeDeriv").length > 1)
        let pp ← ppExpr v
        let ppS := pp.pretty
        let short := if ppS.length > 300 then (ppS.take 300).toString ++ "..." else ppS
        logInfo s!"SEMREV-VALDIAG3|{n}|nconsts|{cs.length}|heat-consts|{String.intercalate "," (heat.map Name.toString)}"
        logInfo s!"SEMREV-VALDIAG3|{n}|pp|{short}"

end SemrevValDiag3
