/-
Copyright (c) 2026 D13-integrated-kernel-audit. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D13 integrated kernel audit — reusable fail-closed detector

`runNewModuleAudit` is the detector used both by the positive audit root
(`Poincare.D13.IntegratedAudit.KernelAudit`, expected to pass) and by the intentional
negative-control root `audit-evidence/negcontrol/NegativeControlIncluded.lean`, which adds
the two negative-control modules of the snapshot and must therefore FAIL the build.

It is fail-closed: every expected clean module must be imported, and any exception raised
while collecting a declaration's axioms is itself a failure.
-/
import Poincare.D13.IntegratedAudit.ExpectedModules
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

namespace Poincare.D13.IntegratedAudit

/-- The only axioms accepted in a released dependency cone. -/
def approvedAxioms : List Name :=
  ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]

/-- `sorryAx` has a dedicated message. -/
def sorryAxiom : Name := "sorryAx".toName

/-- `native_decide` trust primitives. -/
def nativeAxioms : List Name :=
  ["ofReduceBool".toName, "Lean.ofReduceBool".toName]

/-- Modules added in this snapshot: D11 (preliminary dependencies), D12 (terminal releases)
and VKPort (relay-gap recovery of the ported van Kampen cluster, audited with a distinct
origin tag in the provenance manifest). -/
def newModuleRoots : List Name :=
  ["Poincare.D11".toName, "Poincare.D12".toName, "Poincare.VKPort".toName]

def isNewModule (m : Name) : Bool :=
  newModuleRoots.any (fun r => r.isPrefixOf m)

/-- Declaration kind for the report. -/
def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo v =>
      match v.safety with
      | .«unsafe» => "unsafe_def"
      | .«partial» => "partial_def"
      | .safe => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

/-- Order-preserving duplicate removal. -/
def dedupNames (xs : Array Name) : Array Name :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]

/-- Fail-closed audit of every declaration attributed to a D11/D12 module of the
imported environment.  Emits `D13DECL`/`D13TYPE`/`D13AUDIT` lines and raises an
elaboration error unless every check passes. -/
def runNewModuleAudit : CommandElabM Unit := do

let env ← getEnv
-- ---- fail-closed: every expected clean module must be imported -------------------
let imported := env.header.moduleNames
let mut missing : Array Name := #[]
for m in expectedCleanModules do
  unless imported.contains m do
    missing := missing.push m
-- duplicate module names would mean a corrupted environment
let mut dupModules : Array Name := #[]
let mut seen : Array Name := #[]
for m in imported do
  if seen.contains m then dupModules := dupModules.push m else seen := seen.push m
-- ---- collect declarations attributed to D11/D12 modules ---------------------------
let rows : Array (Name × ConstantInfo × Name) :=
  env.constants.fold (fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some midx =>
        let m := imported.getD midx .anonymous
        if isNewModule m then acc.push (n, ci, m) else acc
    | none => acc) #[]
let rows := rows.qsort (fun a b => a.1.toString < b.1.toString)
let mut projectAxioms : Array Name := #[]
let mut unsafeDefs : Array Name := #[]
let mut partialDefs : Array Name := #[]
let mut proofWantedNames : Array Name := #[]
let mut sorryDecls : Array Name := #[]
let mut nativeDecls : Array Name := #[]
let mut otherAxiomDecls : Array (Name × Name) := #[]
let mut collectFailures : Array (Name × String) := #[]
let mut moduleCounts : Array (Name × Nat) := #[]
let mut theoremCount := 0
for (n, ci, m) in rows do
  if n.toString.contains "proof_wanted" then
    proofWantedNames := proofWantedNames.push n
  match ci with
  | .axiomInfo _ => projectAxioms := projectAxioms.push n
  | .defnInfo v =>
      match v.safety with
      | .«unsafe» => unsafeDefs := unsafeDefs.push n
      | .«partial» => partialDefs := partialDefs.push n
      | .safe => pure ()
  | .thmInfo _ => theoremCount := theoremCount + 1
  | _ => pure ()
  -- axiom-cone collection, fail-closed
  let axs ←
    try
      Lean.collectAxioms n
    catch _ =>
      collectFailures := collectFailures.push (n, "collectAxioms raised an exception")
      pure #[]
  for a in axs do
    if a == sorryAxiom then
      sorryDecls := sorryDecls.push n
    else if nativeAxioms.contains a then
      nativeDecls := nativeDecls.push n
    else if !approvedAxioms.contains a then
      otherAxiomDecls := otherAxiomDecls.push (n, a)
  -- per-module declaration count
  let mut found := false
  let mut newCounts : Array (Name × Nat) := #[]
  for (k, c) in moduleCounts do
    if k == m then
      found := true
      newCounts := newCounts.push (k, c + 1)
    else
      newCounts := newCounts.push (k, c)
  if !found then newCounts := newCounts.push (m, 1)
  moduleCounts := newCounts
  IO.println s!"D13DECL\t{n}\t{kindOf ci}\t{m}\t{";".intercalate (axs.toList.map Name.toString)}"
-- ---- full type inventory (all audited declarations) -------------------------------
for (n, ci, m) in rows do
  let ty ← liftTermElabM (Meta.ppExpr ci.type)
  let tyStr := " ".intercalate (ty.pretty.splitOn "\n")
  IO.println s!"D13TYPE\t{n}\t{kindOf ci}\t{m}\t{tyStr}"
-- ---- expected module declaration counts -------------------------------------------
let zeroModules := expectedCleanModules.filter (fun m =>
  !(moduleCounts.any (fun (k, c) => k == m && c > 0)))
-- ---- summary ----------------------------------------------------------------------
IO.println s!"D13AUDIT\texpected_clean_modules\t{expectedCleanModules.length}"
IO.println s!"D13AUDIT\tmissing_modules\t{missing.size}"
IO.println s!"D13AUDIT\tduplicate_module_names\t{dupModules.size}"
IO.println s!"D13AUDIT\tdeclarations_audited\t{rows.size}"
IO.println s!"D13AUDIT\ttheorems\t{theoremCount}"
IO.println s!"D13AUDIT\tproject_axioms\t{projectAxioms.size}"
IO.println s!"D13AUDIT\tunsafe_declarations\t{unsafeDefs.size}"
IO.println s!"D13AUDIT\tpartial_declarations\t{partialDefs.size}"
IO.println s!"D13AUDIT\tsorry_declarations\t{sorryDecls.size}"
IO.println s!"D13AUDIT\tnative_decide_declarations\t{nativeDecls.size}"
IO.println s!"D13AUDIT\tunapproved_axiom_declarations\t{otherAxiomDecls.size}"
IO.println s!"D13AUDIT\tproof_wanted_declarations\t{proofWantedNames.size}"
IO.println s!"D13AUDIT\tcollect_axioms_failures\t{collectFailures.size}"
IO.println s!"D13AUDIT\tmodules_with_zero_declarations\t{zeroModules.length}"
IO.println s!"D13AUDIT\tnegative_control_modules_excluded\t{negativeControlModules.length}"
for m in dedupNames missing do
  IO.println s!"D13FAIL\tmissing_module\t{m}"
for m in dedupNames dupModules do
  IO.println s!"D13FAIL\tduplicate_module\t{m}"
for (n, e) in collectFailures do
  IO.println s!"D13FAIL\tcollect_axioms_exception\t{n}\t{e}"
for n in dedupNames projectAxioms do
  IO.println s!"D13FAIL\tproject_axiom\t{n}"
for n in dedupNames unsafeDefs do
  IO.println s!"D13FAIL\tunsafe\t{n}"
for n in dedupNames sorryDecls do
  IO.println s!"D13FAIL\tsorryAx\t{n}"
for n in dedupNames nativeDecls do
  IO.println s!"D13FAIL\tnative_decide\t{n}"
for (n, a) in otherAxiomDecls do
  IO.println s!"D13FAIL\tunapproved_axiom\t{n}\t{a}"
for n in dedupNames proofWantedNames do
  IO.println s!"D13FAIL\tproof_wanted\t{n}"
for m in zeroModules do
  IO.println s!"D13NOTE\tzero_declarations\t{m}"
let failed :=
  !missing.isEmpty || !dupModules.isEmpty || !projectAxioms.isEmpty || !unsafeDefs.isEmpty ||
  !sorryDecls.isEmpty || !nativeDecls.isEmpty || !otherAxiomDecls.isEmpty ||
  !proofWantedNames.isEmpty || !collectFailures.isEmpty
if failed then
  IO.println "D13VERDICT\tFAIL"
  throwError "D13IntegratedAudit: forbidden kernel dependency — integrated snapshot gate FAILED"
else
  IO.println "D13VERDICT\tPASS — every D11/D12/VKPort declaration depends only on {propext, Classical.choice, Quot.sound}"

end Poincare.D13.IntegratedAudit
