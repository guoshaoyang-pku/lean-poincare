/-
SEMREV-L3 independent review — Stage B: fail-closed axiom audit and declaration census.

This file is NOT part of the reviewed package. It is compiled by the reviewer against the
reviewed package's environment. Unlike the parent audit it does not use a hand-written list of
declarations: it enumerates *every* constant in the environment whose name mentions
`HeatTimeDeriv` (so private helpers and automatically generated declarations are covered),
plus the nine snapshot declarations the parent audit names as consumed, and applies the
fail-closed predicate to all of them. Any axiom outside `{propext, Classical.choice,
Quot.sound}`, any `sorryAx`, any axiom declaration, and any unsafe declaration aborts the file.

The per-declaration rows are printed as `SEMREV|...` lines for the review card.
-/

import Poincare.L3.HeatTimeDeriv.All
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

namespace SemrevL3

/-- The approved axiom cone. -/
def approvedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The nine load-bearing snapshot declarations named by the parent audit. -/
def snapshotDecls : List Name :=
  [ ``Poincare.D12.ParabolicLocal.mildToClassicalBridge,
    ``Poincare.D12.ParabolicLocal.heatConv,
    ``Poincare.D12.ParabolicLocal.heatConv_apply,
    ``Poincare.D12.ParabolicLocal.heatConv_tendsto_self_BUC,
    ``Poincare.D10.HeatKernelEuclidean.hasDerivAt_gaussianKernel,
    ``Poincare.D10.HeatKernelEuclidean.laplacian_gaussianKernel,
    ``Poincare.D12.HeatSemigroup.heatOperator,
    ``Poincare.D12.HeatSemigroup.gaussianKernel_interval_bound,
    ``Poincare.D12.HeatSemigroup.gaussianKernel_interval_bound_le ]

/-- A short kind tag for a constant. -/
def kindOf : ConstantInfo → String
  | .axiomInfo _ => "AXIOM"
  | .defnInfo v => if v.safety == .unsafe then "UNSAFE-DEF" else "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

/-- Row for one declaration: kind, axiom cone, verdict. -/
def row (n : Name) (ci : ConstantInfo) (axs : Array Name) : String :=
  let bad := axs.toList.filter (fun a => !approvedAxioms.contains a)
  let verdict :=
    if kindOf ci == "AXIOM" || kindOf ci == "UNSAFE-DEF" then "VIOLATION-KIND"
    else if axs.contains ``sorryAx then "VIOLATION-SORRY"
    else if bad.isEmpty then "ok"
    else "VIOLATION-AXIOM"
  s!"SEMREV|{n}|{kindOf ci}|{String.intercalate "," (axs.toList.map Name.toString)}|{verdict}"

run_cmd do
  let env ← getEnv
  let mut l3Count := 0
  let mut snapCount := 0
  let mut violations : Array String := #[]
  -- (1) every constant mentioning HeatTimeDeriv (catches private/auxiliary declarations)
  for (n, ci) in env.constants.toList do
    if (n.toString.splitOn "HeatTimeDeriv").length > 1 then
      l3Count := l3Count + 1
      let axs ← Lean.collectAxioms n
      let r := row n ci axs
      logInfo r
      if !(r.endsWith "|ok") then violations := violations.push r
  -- (2) the nine snapshot declarations
  for n in snapshotDecls do
    match (← getEnv).find? n with
    | none =>
      violations := violations.push s!"SEMREV|{n}|MISSING||VIOLATION-MISSING"
      logError m!"SEMREV: snapshot declaration {n} is absent from the environment"
    | some ci =>
      snapCount := snapCount + 1
      let axs ← Lean.collectAxioms n
      let r := row n ci axs
      logInfo r
      if !(r.endsWith "|ok") then violations := violations.push r
  logInfo s!"SEMREV|SUMMARY|HeatTimeDeriv constants: {l3Count}, snapshot decls: {snapCount}, violations: {violations.size}"
  if !violations.isEmpty then
    for v in violations do logError m!"{v}"
    throwError "SEMREV-L3 axiom audit: FAIL — {violations.size} violation(s)"
  else
    logInfo "SEMREV-L3 axiom audit: PASS — all enumerated declarations depend only on [propext, Classical.choice, Quot.sound]"

end SemrevL3
