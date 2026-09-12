/-
Targeted cone check for the three generated declarations that the grouped partition
audit did not enumerate (they appear in the per-module probe inventory but their
`const2ModIdx` attribution in the whole-partition environment resolves to a
non-target module).  See baseline/audit/probe-inventory-crosscheck.json.

Run from release/:  lake env lean ../baseline/audit/depcheck/MissedDeclConeCheck.lean
-/
import Poincare.D12.ParabolicLocal.GaussianConv
import Poincare.D12.TensorMaximumBochner.So3Model
import Poincare.D9.DeTurck.SymbolModel
import Poincare.VKPort.HatcherLib.Ch1.BasicConstructions

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `BoundedContinuousFunction.mkOfBound.congr_simp,
    `LinearMap.mk₂.congr_simp,
    `ContinuousMap.Homotopy.affine.congr_simp
  ]
  let approved : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Nat := 0
  for n in targets do
    match env.find? n with
    | none => IO.println s!"MISSEDCONE\t{n}\tABSENT"
    | some _ =>
      let axs ← Lean.collectAxioms n
      let extra := axs.filter (fun a => !approved.contains a)
      IO.println s!"MISSEDCONE\t{n}\t{String.intercalate "," (axs.toList.map toString)}\tunexpected={extra.size}"
      if !extra.isEmpty then bad := bad + 1
  if bad == 0 then
    IO.println "MISSEDCONEVERDICT\tPASS"
  else
    IO.println "MISSEDCONEVERDICT\tFAIL"
    throwError "missed-declaration cone check FAILED"
