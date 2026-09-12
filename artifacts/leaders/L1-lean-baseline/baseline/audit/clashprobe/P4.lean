import Poincare.D11.BochnerManifold.ModelSpace
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  IO.println s!"mods.size={mods.size}"
  for n in [`Poincare.D10.jacobiSolFlat.eq_1, `Poincare.D11.BochnerManifold.modelRicciTerm.eq_1, `Poincare.D10.jacobiSolFlat] do
    match env.getModuleIdxFor? n with
    | some idx => IO.println s!"{n} -> idx={idx} name={mods.getD idx .anonymous}"
    | none => IO.println s!"{n} -> none"
