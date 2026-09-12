import Poincare.L4.Compactness.FamilyCovers
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let n := ``Poincare.L4.Compactness.totallyBounded_of_uniformDoubling
  logInfo ("find?.isSome = " ++ toString (env.find? n).isSome)
  match env.find? n with
  | none => logInfo "none"
  | some ci =>
    logInfo ("value?.isSome = " ++ toString ci.value?.isSome)
    match ci.value? with
    | none => logInfo "value none"
    | some v => logInfo ("used constants = " ++ toString (v.getUsedConstants.map Name.toString))
