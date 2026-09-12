import Lean.Elab.Command
import Poincare.D7.EvolutionSharp.Implications

open Lean Elab Command

run_cmd do
  let env ← getEnv
  for n in [`Poincare.D7.EvolutionSharp.perelmanF_step_lt_old_recovered,
            `Poincare.D7.EvolutionSharp.perelmanF_step_lt_old_of_sharp,
            `Poincare.D7.EvolutionSharp.perelmanF_step_lt_of_one_le,
            `Poincare.D7.EvolutionSharp.gibbsTerm_strictAnti_of_one_le] do
    match env.find? n with
    | none => IO.println s!"DEPCHK {n} MISSING"
    | some ci =>
      let v := ci.value?
      IO.println s!"DEPCHK {n} value?={v.isSome}"
      match v with
      | none => pure ()
      | some e =>
        let used := e.getUsedConstants
        IO.println s!"DEPCHK {n} value_used={used.size}"
        for d in used do
          if d.toString.contains "perelmanF" || d.toString.contains "gibbsTerm" then
            IO.println s!"DEPCHK {n} VALUE_DEP {d}"
      let tu := ci.type.getUsedConstants
      IO.println s!"DEPCHK {n} type_used={tu.size}"
      for d in tu do
        if d.toString.contains "perelmanF" || d.toString.contains "gibbsTerm" then
          IO.println s!"DEPCHK {n} TYPE_DEP {d}"
