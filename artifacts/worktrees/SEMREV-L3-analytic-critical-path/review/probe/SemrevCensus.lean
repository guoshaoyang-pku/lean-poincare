/-
SEMREV-L3 independent review — Stage C: declaration census with exact types.

Prints `SEMREV-DECL|<name>|<kind>|` followed by the exact type of *every* constant in the
environment whose name mentions `HeatTimeDeriv`. This is the per-declaration semantic-class
census for the review card (types are printed by the standard `#check` formatter).
-/

import Poincare.L3.HeatTimeDeriv.All
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

namespace SemrevL3

def kindOfC : ConstantInfo → String
  | .axiomInfo _ => "AXIOM"
  | .defnInfo v => if v.safety == .unsafe then "UNSAFE-DEF" else "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

run_cmd do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if (n.toString.splitOn "HeatTimeDeriv").length > 1 then
      count := count + 1
      logInfo s!"SEMREV-DECL|{n}|{kindOfC ci}"
      try
        elabCommand (← `(command| #check $(mkIdent n)))
      catch _ =>
        logInfo s!"SEMREV-DECL-TYPEFAIL|{n}"
  logInfo s!"SEMREV-DECL-SUMMARY|{count} constants mentioning HeatTimeDeriv"

end SemrevL3
