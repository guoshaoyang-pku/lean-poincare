/-
# A1 downstream-use probe (run inside `baseline/a1/patched-release`)

Prints the *proof-level* direct dependencies (`ConstantInfo.getUsedConstants`, which
includes proof bodies for theorems in Lean v4.34.0-rc2 only when `value?` is forced) of the
restated promoted theorems and of the sharp-only consumers, so that the downstream checked
use is machine-readable rather than asserted.

    cd baseline/a1/patched-release
    lake env lean ../../../baseline/a1/verify/ConsumerCone.lean
-/

import Poincare.D7.EvolutionSharp.AxiomAudit
import Audit.CounterexampleAudit

open Lean Elab Command

namespace A1UseProbe

/-- Direct proof-level dependencies of a declaration, one `A1USE` line each. -/
def report (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  match env.find? n with
  | none => logInfo m!"A1USE {n} MISSING"
  | some ci =>
      -- proof-level edges: type plus proof body (allowOpaque := true includes theorem bodies)
      let used := ci.type.getUsedConstants
        ++ ((ConstantInfo.value? ci (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
      logInfo m!"A1USEN {n} {used.size}"
      for d in used do
        logInfo m!"A1USE {n} {d}"

end A1UseProbe

open A1UseProbe in
run_cmd do
  -- the three restated promoted theorems
  report ``Poincare.Longrun.Evolution.gibbsTerm_strictAnti
  report ``Poincare.Longrun.Evolution.gibbsTerm_step_lt
  report ``Poincare.Longrun.Evolution.perelmanF_step_lt
  -- sharp-only consumers added by the restatement
  report ``Poincare.D7.EvolutionSharp.gibbsTerm_strictAnti_at_threshold_one
  report ``Poincare.D7.EvolutionSharp.perelmanF_step_lt_at_threshold_one
  report ``Poincare.D7.EvolutionSharp.perelmanF_step_lt_sharp_of_lt
  -- pre-existing consumers that now receive the sharp statement
  report ``Poincare.D7.EvolutionSharp.perelmanF_step_lt_of_one_le
  report ``Poincare.D7.EvolutionSharp.perelmanF_step_lt_old_recovered
  report ``Poincare.D7.EvolutionSharp.gibbsTerm_strictAnti_of_one_le
  report ``Poincare.D7.EvolutionSharp.gibbsTerm_step_lt_promoted
  report ``Poincare.D7.EvolutionSharp.perelmanF_step_lt_promoted
  report ``D4Audit.gibbsTerm_strictAnti_of_one_le
  report ``D4Audit.perelmanF_step_lt_of_one_le
