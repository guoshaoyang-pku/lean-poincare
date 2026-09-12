import Poincare.D7.Limit.Convergence

open Lean Elab Command

namespace Probe0291

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo v =>
      if v.safety == .unsafe then "unsafe_def"
      else if v.safety == .partial then "partial_def" else "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "recursor"

end Probe0291

open Probe0291 in
run_cmd do
  let env ← getEnv
  let target : Name := `Poincare.D7.Limit.Convergence
  let mut out : Array (Name × String) := #[]
  for (n, ci) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some idx =>
        if env.header.moduleNames.getD idx .anonymous == target then
          out := out.push (n, kindOf ci)
    | none => pure ()
  for (n, k) in out do
    IO.println s!"MD\t{target}\t{n}\t{k}"
