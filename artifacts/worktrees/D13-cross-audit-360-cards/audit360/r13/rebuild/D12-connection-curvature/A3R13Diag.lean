import Poincare.D12.ConnectionCurvature.ChartLeviCivitaSmooth
open Lean Elab Command
namespace A3R13Diag
partial def peel (e : Expr) (acc : Array Expr) : Array Expr × Expr :=
  match e with
  | .forallE _ d b _ => peel b (acc.push d)
  | _ => (acc, e)
def go (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  match env.find? n with
  | none => logInfo "NOT FOUND"
  | some ci =>
    let (hyps, body) := peel ci.type #[]
    logInfo m!"hyps={hyps.size}"
    logInfo m!"body={body}"
    logInfo m!"isEq3={body.isAppOfArity ``Eq 3}"
    if body.isAppOfArity ``Eq 3 then
      let a := body.getArg! 1
      let b := body.getArg! 2
      logInfo m!"a={a}"
      logInfo m!"b={b}"
      logInfo m!"eq={a == b}"
end A3R13Diag
run_cmd A3R13Diag.go ``Poincare.D12.ConnectionCurvature.sum_three_cycle
