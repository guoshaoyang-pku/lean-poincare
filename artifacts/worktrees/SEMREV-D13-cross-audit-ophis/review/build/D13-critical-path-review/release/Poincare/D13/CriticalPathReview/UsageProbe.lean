/-
Copyright (c) 2026 D13-critical-path-review. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-critical-path-review)

# Downstream-use probe (retained consumers of the claimed closures)

For a list of constructors that the D12/D13 cards claim to be *used downstream*, this
module computes the number of retained consumers in the compiled snapshot, by building the
reverse of the direct-dependency graph over project declarations (`Poincare.*`) and running
a BFS from each constructor.

"Retained consumer" means: a declaration in the olean environment whose type or proof term
mentions the constructor, directly or transitively.  Anonymous `example` commands are not
stored in oleans and therefore do not count (this is exactly the D13-integrated-audit §6.3
finding about constructors whose only uses were `example`s).

The probe is a report, not a gate: `#d13_usage_probe` prints `D13CP_USE` lines and a
`D13CP_USE_VERDICT` line, and fails only if a constructor listed as *required to be
consumed* has zero consumers.

No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
import Poincare.D13.CriticalPathReview.StatementAudit
import Lean.Elab.Command
import Std.Data.HashMap

set_option linter.unusedVariables false
set_option autoImplicit false

open Lean Elab Command

namespace Poincare.D13.CriticalPathReview

/-- Constructors whose retained-consumer count is reported together with whether a
non-zero count is required. -/
def usageTargets : List (Name × Bool) :=
  [ (``Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2, true)
  , (``Poincare.D12.SurgeryRecognition.iteratedSphereSum, true)
  , (``Poincare.D12.SurgeryRecognition.iteratedSphereSum_homeo_sphere, false)
  , (``Poincare.D12.SurgeryRecognition.sphereConnectSum_homeo_sphere, true)
  , (``Poincare.D12.SurgeryRecognition.sphericalPieceRecognition_of, true)
  , (``Poincare.D12.SurgeryRecognition.sphericalPieceRecognition_of_spaceForm, true)
  , (``Poincare.D12.SurgeryRecognition.deckTrivial_of_simplyConnected_quotient, true)
  , (``Poincare.D12.TensorMaximumBochner.hamiltonField_kernelTangent, true)
  , (``Poincare.D13.CriticalPathReview.scalar_forward_invariance, true)
  , (``Poincare.D13.CriticalPathReview.exists_last_zero, true)
  ]

/-- Direct dependencies of `n`: constants in its statement plus constants in its
(immediate) proof term. -/
def directDependencies (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let tys := statementConstants env n
    let prf := match ci.value? true with
      | some v => v.getUsedConstants
      | none => #[]
    tys ++ prf

/-- All project declarations (names under `Poincare.`) that are not private. -/
def projectDeclarations (env : Environment) : Array Name :=
  env.constants.fold (fun acc n _ =>
    if n.toString.startsWith "Poincare." && !n.toString.contains "_private" then
      acc.push n
    else acc) #[]

/-- Reverse direct-dependency graph restricted to project declarations. -/
def buildReverseGraph (env : Environment) : Std.HashMap Name (Array Name) := Id.run do
  let mut graph : Std.HashMap Name (Array Name) := {}
  for n in projectDeclarations env do
    for d in directDependencies env n do
      if d.toString.startsWith "Poincare." && !d.toString.contains "_private" then
        graph := graph.insert d ((graph.getD d #[]).push n)
  return graph

/-- Number of retained consumers of `target` (BFS over the reverse graph; the target itself
is excluded). -/
def consumerCount (graph : Std.HashMap Name (Array Name)) (target : Name) : Nat := Id.run do
  let mut visited : Std.HashSet Name := {}
  let mut count : Nat := 0
  let mut todo : List Name := (graph.getD target #[]).toList
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if visited.contains n then continue
    visited := visited.insert n
    count := count + 1
    for m in graph.getD n #[] do
      if !visited.contains m then todo := m :: todo
  return count

/-- Report retained-consumer counts for `usageTargets`. -/
def runUsageProbe : CommandElabM Unit := do
  let env ← getEnv
  let graph := buildReverseGraph env
  let mut failures : Array String := #[]
  for (t, required) in usageTargets do
    if (env.find? t).isNone then
      failures := failures.push s!"missing declaration {t}"
      IO.println s!"D13CP_USE\t{t}\tMISSING"
    else
      let c := consumerCount graph t
      IO.println s!"D13CP_USE\t{t}\t{c}"
      if required && c == 0 then
        failures := failures.push s!"{t} has zero retained consumers but is required to be used"
  if failures.isEmpty then
    IO.println "D13CP_USE_VERDICT\tPASS"
  else
    IO.println "D13CP_USE_VERDICT\tFAIL"
    for f in failures do
      IO.println s!"D13CP_USE_FAIL\t{f}"
    throwError "D13CriticalPathReview: usage probe FAILED ({failures.size} failures)"

/-- Retained-consumer probe for the claimed critical-path closures. -/
elab "#d13_usage_probe" : command => runUsageProbe

end Poincare.D13.CriticalPathReview

open Poincare.D13.CriticalPathReview

#d13_usage_probe
