/-
SEMREV-L3 review — round 3, Stage E-diagnostic: are theorem *values* present in the imported
environment? The single-pass consumer search reported zero value-level references, which
contradicts the source text of `mildToClassicalBridge_holds` (it visibly calls
`mildToClassicalBridge_pointwise`). This diagnostic decides whether that is a real finding (proof
terms are stored with the reference) or an instrumentation failure (`value?` empty / proofs
elided).
-/

import Poincare.L3.HeatTimeDeriv.All
import Lean

open Lean

namespace SemrevValDiag

partial def countConst (t : Name) : Nat → Expr → Nat
  | acc, .const n _ => if n == t then acc + 1 else acc
  | acc, .app f a => countConst t (countConst t acc f) a
  | acc, .lam _ d b _ => countConst t (countConst t acc d) b
  | acc, .forallE _ d b _ => countConst t (countConst t acc d) b
  | acc, .letE _ d v b _ => countConst t (countConst t (countConst t acc d) v) b
  | acc, .mdata _ b => countConst t acc b
  | acc, .proj _ _ b => countConst t acc b
  | acc, _ => acc

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo v => if v.safety == .unsafe then "unsafe-def" else "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

run_cmd do
  let env ← getEnv
  let checks : List (Name × Name) :=
    [ (``Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_holds,
       ``Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_pointwise),
      (``Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_BCF,
       ``Poincare.L3.HeatTimeDeriv.uniformMildToClassicalBridge_holds),
      (``Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_holds,
       ``Poincare.L3.HeatTimeDeriv.timeDerivIntegral),
      (``Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_BCF,
       ``Poincare.L3.HeatTimeDeriv.timeDerivBCF) ]
  for (owner, ref) in checks do
    match env.find? owner with
    | none => logInfo s!"SEMREV-VALDIAG|MISSING|{owner}"
    | some ci =>
      let hasVal := ci.value? (allowOpaque := true) |>.isSome
      let c := match ci.value? with
        | some v => countConst ref 0 v
        | none => 0
      logInfo s!"SEMREV-VALDIAG|{owner}|kind|{kindOf ci}|value-present|{hasVal}|refs-to|{ref}|{c}"

end SemrevValDiag
