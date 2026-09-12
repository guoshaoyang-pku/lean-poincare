/-
SEMREV-L3 independent review — round 4, Stage G: audit-completeness cross-check.

The independent fail-closed audit (`SemrevAudit.lean`) enumerates every environment constant
whose *name* mentions `HeatTimeDeriv`. That filter is complete only if the six authored files
contribute no declaration with a different name. This probe closes that methodological gap
machine-checkably: it enumerates every constant whose *declaring module* is one of the six
`Poincare.L3.HeatTimeDeriv.*` modules (via `Environment.getModuleIdxFor?` and
`Environment.header.moduleNames`), reports how many there are, and fails closed if any such
constant is missed by the name-substring filter used by the audit.

The per-declaration rows are printed as `SEMREV-COMPLETE-DECL|...` lines so the round-4 card
can diff the module-attributed population against the audit population.
-/

import Poincare.L3.HeatTimeDeriv.All
import Lean

open Lean Elab Command

namespace SemrevComplete

/-- The six authored modules of the reviewed artifact. -/
def authoredModules : List Name :=
  [ `Poincare.L3.HeatTimeDeriv.All,
    `Poincare.L3.HeatTimeDeriv.Audit,
    `Poincare.L3.HeatTimeDeriv.BanachDeriv,
    `Poincare.L3.HeatTimeDeriv.Basic,
    `Poincare.L3.HeatTimeDeriv.ClassicalBridge,
    `Poincare.L3.HeatTimeDeriv.UniformBridge ]

run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut fromAuthored : Array Name := #[]
  let mut missed : Array Name := #[]
  for (n, _) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := mods[idx.toNat]!
      if authoredModules.contains m then
        fromAuthored := fromAuthored.push n
        if (n.toString.splitOn "HeatTimeDeriv").length <= 1 then
          missed := missed.push n
    | none => pure ()
  logInfo s!"SEMREV-COMPLETE|authored-module constants: {fromAuthored.size}, missed by name filter: {missed.size}"
  for n in fromAuthored do
    logInfo s!"SEMREV-COMPLETE-DECL|{n}"
  if !missed.isEmpty then
    for n in missed do logError m!"SEMREV-COMPLETE-MISSED|{n}"
    throwError "SEMREV-L3 audit completeness: FAIL — {missed.size} declaration(s) from the authored modules are not covered by the name filter"
  else
    logInfo "SEMREV-L3 audit completeness: PASS — every constant declared by the six authored modules is covered by the name-substring filter used by SemrevAudit.lean"

end SemrevComplete
