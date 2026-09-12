import Poincare.L4.Compactness.MeasureGrowthChainCircleFamily
import Lean

open Lean

run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? `Poincare.L4.Compactness.circleEquivT
    | throwError "circleEquivT not found"
  let modNames := env.constants.toList.filterMap (fun (n, _) =>
    if env.getModuleIdxFor? n == some idx then some n else none)
  IO.println s!"FAMILY MODULE DECLS ({modNames.length}):"
  for n in modNames do
    IO.println s!"{n}"
