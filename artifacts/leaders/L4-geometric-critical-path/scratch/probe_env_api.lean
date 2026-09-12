import Poincare.L4.Compactness.MeasureGrowthChainCircle
import Lean

open Lean

run_cmd do
  let env ← getEnv
  IO.println s!"numModules = {env.header.moduleNames.size}"
  let idx? := env.getModuleIdxFor? `Poincare.L4.Compactness.circleEquiv
  IO.println s!"idxForCircleEquiv = {idx?}"
  IO.println s!"moduleNames[idx] = {idx?.map (fun i => env.header.moduleNames[i]!)}"
  let names := env.constants.toList.filter (fun (n, _) =>
    n.toString.contains "MeasureGrowthChainCircle")
  IO.println s!"names containing module string: {names.length}"
  for (n, _) in names.take 40 do
    IO.println s!"  {n}"
