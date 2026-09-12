/-
# Poincare.D7.EvolutionSharp.ReleaseAudit

**D7 evolution sharp restatement: environment-wide kernel release gate.**

The D6 `ReleaseAudit.lean` walks the environment of `ReleaseCheck`, which does **not**
import the new D7 modules. This driver imports the D7 audit root
(`Poincare.D7.EvolutionSharp.AxiomAudit`, hence every authored D7 module and the whole
promoted `Poincare.Longrun` cone) and re-runs the same environment-wide check over every
constant declared in a `Poincare.*` module:

* no `sorryAx` in any dependency cone,
* no project `axiom` declaration,
* no `unsafe` declaration,
* no `native_decide` / `ofReduceBool` trust primitive,
* no axiom outside `{propext, Classical.choice, Quot.sound}`,
* no declaration name containing `proof_wanted`.

The check is exhaustive over the imported environment, not just over the `#print axioms`
list of `AxiomAudit.lean`. A successful elaboration (exit 0) is the release gate for the D7
modules. This file is an audit driver, not mathematical content. No `sorry`, `axiom`,
`unsafe`, `native_decide`, or `proof_wanted` occurs in this file.
-/

import Poincare.D7.EvolutionSharp.AxiomAudit
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace Poincare
namespace D7
namespace EvolutionSharp

/-! Namespaced helpers for the D7 environment-wide audit. -/
namespace SharpAudit

/-- The only axioms accepted in a released dependency cone. -/
def approvedAxioms : List Name :=
  ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]

/-- `sorryAx` has a dedicated message. -/
def sorryAxiom : Name := "sorryAx".toName

/-- `native_decide` trust primitives (`ofReduceBool`, root and `Lean`-qualified spellings). -/
def nativeAxioms : List Name := ["ofReduceBool".toName, "Lean.ofReduceBool".toName]

/-- Module roots owned by this package cone: every `Poincare.*` module. -/
def projectModuleRoots : List Name := ["Poincare".toName]

/-- A module name belongs to the audited project cone. -/
def isProjectModule (m : Name) : Bool :=
  projectModuleRoots.any (fun r => r.isPrefixOf m)

/-- Every constant declared in a module of the audited project cone. -/
def projectConstants (env : Environment) : Array (Name × ConstantInfo) :=
  let mods := env.header.moduleNames
  env.constants.fold (fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some midx =>
        if isProjectModule (mods.getD midx .anonymous) then acc.push (n, ci) else acc
    | none => acc) #[]

/-- Format an axiom cone as `[a, b, c]`. -/
def coneString (axs : Array Name) : String :=
  "[" ++ ", ".intercalate (axs.toList.map Name.toString) ++ "]"

/-- Order-preserving duplicate removal. -/
def dedupNames (xs : Array Name) : Array Name :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]

/-- Order-preserving duplicate removal for `(declaration, axiom)` pairs. -/
def dedupPairs (xs : Array (Name × Name)) : Array (Name × Name) :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]

end SharpAudit

open SharpAudit in
run_cmd do
  let env ← getEnv
  let cs := projectConstants env
  let mut projectAxioms : Array Name := #[]
  let mut unsafeDefs : Array Name := #[]
  let mut partialDefs : Array Name := #[]
  let mut proofWantedNames : Array Name := #[]
  let mut cones : Array (Name × Array Name) := #[]
  for (n, ci) in cs do
    if n.toString.contains "proof_wanted" then
      proofWantedNames := proofWantedNames.push n
    match ci with
    | .axiomInfo _ => projectAxioms := projectAxioms.push n
    | .defnInfo v =>
        match v.safety with
        | .«unsafe» => unsafeDefs := unsafeDefs.push n
        | .«partial» => partialDefs := partialDefs.push n
        | .safe => pure ()
    | _ => pure ()
    let axs ← Lean.collectAxioms n
    cones := cones.push (n, axs)
  let mut sorryDecls : Array Name := #[]
  let mut nativeDecls : Array Name := #[]
  let mut otherAxiomDecls : Array (Name × Name) := #[]
  for (n, axs) in cones do
    for a in axs do
      if a == sorryAxiom then
        sorryDecls := sorryDecls.push n
      else if nativeAxioms.contains a then
        nativeDecls := nativeDecls.push n
      else if !approvedAxioms.contains a then
        otherAxiomDecls := otherAxiomDecls.push (n, a)
  let mut distinctCones : Array String := #[]
  for (_, axs) in cones do
    let s := coneString axs
    if !distinctCones.contains s then
      distinctCones := distinctCones.push s
  logInfo m!"D7SharpReleaseAudit: project declarations audited: {cs.size}"
  logInfo m!"D7SharpReleaseAudit: project axiom declarations: {projectAxioms.size}"
  logInfo m!"D7SharpReleaseAudit: unsafe declarations: {unsafeDefs.size}"
  logInfo m!"D7SharpReleaseAudit: partial declarations: {partialDefs.size}"
  logInfo m!"D7SharpReleaseAudit: declarations depending on sorryAx: {sorryDecls.size}"
  logInfo m!"D7SharpReleaseAudit: declarations depending on native_decide/ofReduceBool: {nativeDecls.size}"
  logInfo m!"D7SharpReleaseAudit: declarations with unapproved axioms: {otherAxiomDecls.size}"
  logInfo m!"D7SharpReleaseAudit: declaration names containing 'proof_wanted': {proofWantedNames.size}"
  logInfo m!"D7SharpReleaseAudit: distinct axiom cones: {distinctCones.size}"
  for s in distinctCones do
    logInfo m!"D7SharpReleaseAudit:   cone {s}"
  let failed :=
    !projectAxioms.isEmpty || !unsafeDefs.isEmpty || !sorryDecls.isEmpty ||
    !nativeDecls.isEmpty || !otherAxiomDecls.isEmpty || !proofWantedNames.isEmpty
  if failed then
    for n in dedupNames projectAxioms do
      logError m!"D7SharpReleaseAudit FAIL: project axiom declaration {n}"
    for n in dedupNames unsafeDefs do
      logError m!"D7SharpReleaseAudit FAIL: unsafe declaration {n}"
    for n in dedupNames sorryDecls do
      logError m!"D7SharpReleaseAudit FAIL: sorryAx in dependency cone of {n}"
    for n in dedupNames nativeDecls do
      logError m!"D7SharpReleaseAudit FAIL: native_decide/ofReduceBool in dependency cone of {n}"
    for (n, a) in dedupPairs otherAxiomDecls do
      logError m!"D7SharpReleaseAudit FAIL: unapproved axiom {a} in dependency cone of {n}"
    for n in dedupNames proofWantedNames do
      logError m!"D7SharpReleaseAudit FAIL: proof_wanted-derived declaration {n}"
    throwError "D7SharpReleaseAudit: forbidden dependency found — release gate FAILED"
  else
    logInfo m!"D7SharpReleaseAudit: PASS — no sorryAx, no project axiom, no unsafe, no native_decide, no proof_wanted in any dependency cone"

end EvolutionSharp
end D7
end Poincare
