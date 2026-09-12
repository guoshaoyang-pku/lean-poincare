import Poincare.D12.ConnectionCurvature.ChartLeviCivitaSmooth
open Lean Elab Command
namespace A3R13Diag2
partial def peel (e : Expr) (acc : Array Expr) : Array Expr × Expr :=
  match e with
  | .forallE _ d b _ => peel b (acc.push d)
  | _ => (acc, e)
def go (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  match env.find? n with
  | none => logInfo "NOT FOUND"
  | some ci =>
    let (_, body) := peel ci.type #[]
    if body.isAppOfArity ``Eq 3 then
      let a := body.getArg! 1
      let b := body.getArg! 2
      logInfo m!"BEq={a == b} equal={a.equal b} hashEq={a.hash == b.hash}"
      logInfo m!"aHash={a.hash} bHash={b.hash}"
end A3R13Diag2
run_cmd A3R13Diag2.go ``Poincare.D12.ConnectionCurvature.sum_three_cycle
