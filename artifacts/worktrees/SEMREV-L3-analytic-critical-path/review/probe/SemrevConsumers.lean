/-
SEMREV-L3 independent review — round 3, Stage E: whole-environment consumer search (single pass).

Round 2 established "no compiled consumer of the L3 deliverables outside
`Poincare/L3/HeatTimeDeriv`" by *textual grep* (F2). This probe replaces that with an exact
environment-level search:

  * one pass over every constant in the compiled environment; for each constant it checks
    whether the constant's **type** mentions any deliverable (all 800k+ constants) and — for
    constants in a **local module namespace**, the only place a consumer can live since mathlib
    cannot mention these names — whether the constant's **value** (proof term / definition body)
    mentions any deliverable.

A `#check`-style use creates no constant, so every row reported here is a real compiled
reference. Rows are `SEMREV-CONSUMER|<consumer>|<kind>|<targets>|<type|value>|<scope>`, where
scope is `internal` inside `Poincare.L3.HeatTimeDeriv` and `EXTERNAL` otherwise. Summary lines
give per-target totals and, decisively, the count of **external** consumers. The probe aborts if
any target is absent from the environment (a rename cannot silently produce "0 consumers").
-/

import Poincare.L3.HeatTimeDeriv.All
import Lean

open Lean

namespace SemrevConsumers

/-- The L3 deliverables whose downstream use is at issue. -/
def targets : List Name :=
  [ ``Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_holds,
    ``Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_pointwise,
    ``Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_of_uniform,
    ``Poincare.L3.HeatTimeDeriv.uniformMildToClassicalBridge_holds,
    ``Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_BCF,
    ``Poincare.L3.HeatTimeDeriv.heatConv_classicalHeatSolution,
    ``Poincare.L3.HeatTimeDeriv.KernelClassicalHeatSolution,
    ``Poincare.L3.HeatTimeDeriv.SpatialLaplacianBridge,
    ``Poincare.L3.HeatTimeDeriv.timeDerivBCF,
    ``Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_apply,
    ``Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_apply_kernelLaplacian,
    ``Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_const,
    ``Poincare.L3.HeatTimeDeriv.timeDerivBCF_apply ]

/-- Local-module prefixes: a consumer outside these namespaces cannot exist (mathlib is compiled
against an environment that does not contain `Poincare.L3`). -/
def localPrefixes : List String :=
  ["Poincare.", "Audit.", "Ledger.", "Probe.", "D6", "Release"]

def isLocal (n : Name) : Bool :=
  localPrefixes.any (fun p => n.toString.startsWith p)

/-- Which of `s` occur in `e`? -/
partial def mentionsAny (s : Std.HashSet Name) (acc : Array Name) : Expr → Array Name
  | .const n _ => if s.contains n then acc.push n else acc
  | .app f a => mentionsAny s (mentionsAny s acc f) a
  | .lam _ d b _ => mentionsAny s (mentionsAny s acc d) b
  | .forallE _ d b _ => mentionsAny s (mentionsAny s acc d) b
  | .letE _ d v b _ => mentionsAny s (mentionsAny s (mentionsAny s acc d) v) b
  | .mdata _ b => mentionsAny s acc b
  | .proj _ _ b => mentionsAny s acc b
  | _ => acc

/-- Short kind tag. -/
def kindOf : ConstantInfo → String
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
  for t in targets do
    if !env.contains t then
      throwError "SEMREV-L3 consumer search: target {t} is absent from the environment"
  let s : Std.HashSet Name := targets.foldl (fun acc t => acc.insert t) {}
  let consts := env.constants.toList
  logInfo s!"SEMREV-CONSUMER|ENV|constants|{consts.length}"
  let mut total := 0
  let mut ext := 0
  -- per-target tallies
  let mut tTotal : Std.HashMap Name Nat := {}
  let mut tExt : Std.HashMap Name Nat := {}
  for t in targets do
    tTotal := tTotal.insert t 0
    tExt := tExt.insert t 0
  for (n, ci) in consts do
    let inType := mentionsAny s #[] ci.type
    let inVal :=
      if isLocal n then
        match ci.value? (allowOpaque := true) with
        | some v => mentionsAny s #[] v
        | none => #[]
      else #[]
    if !inType.isEmpty || !inVal.isEmpty then
      total := total + 1
      let external := !(n.toString.startsWith "Poincare.L3.HeatTimeDeriv")
      if external then ext := ext + 1
      let where_ :=
        if !inType.isEmpty && !inVal.isEmpty then "type+value"
        else if !inType.isEmpty then "type"
        else "value"
      let names := (inType ++ inVal).toList.eraseDups
      for t in names do
        tTotal := tTotal.insert t (tTotal.getD t 0 + 1)
        if external then tExt := tExt.insert t (tExt.getD t 0 + 1)
      logInfo s!"SEMREV-CONSUMER|{n}|{kindOf ci}|{String.intercalate "," (names.map Name.toString)}|{where_}|{if external then "EXTERNAL" else "internal"}"
  for t in targets do
    logInfo s!"SEMREV-CONSUMER-SUMMARY|{t}|{tTotal.getD t 0}|external|{tExt.getD t 0}"
  logInfo s!"SEMREV-CONSUMER-TOTAL|{total}|external|{ext}"

end SemrevConsumers
