import Poincare.D11.ReducedVolume.All

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let ns := `Poincare.D11.ReducedVolume
  let mut rows : Array (Name × String) := #[]
  for (c, ci) in env.constants.toList do
    if ns.isPrefixOf c && c != ns then
      let k := match ci with
        | .thmInfo _ => "thm"
        | .defnInfo _ => "def"
        | .inductInfo _ => "induct"
        | .ctorInfo _ => "ctor"
        | .recInfo _ => "rec"
        | .opaqueInfo _ => "opaque"
        | .axiomInfo _ => "AXIOM"
        | .quotInfo _ => "quot"
      rows := rows.push (c, k)
  logInfo m!"ENVCOUNT {rows.size}"
  for (c, k) in rows.qsort (fun a b => a.1.toString < b.1.toString) do
    logInfo m!"{k} {c}"
