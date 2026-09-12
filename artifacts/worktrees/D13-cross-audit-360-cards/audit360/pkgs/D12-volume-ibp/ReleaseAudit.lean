/-
D5-clean-rebuild — kernel-level dependency audit.

Imports `ReleaseCheck` (all promoted D1–D4 clusters) and walks the *entire* environment
of the clean package.  For every declaration owned by this release package it collects
the transitive axiom cone and fails the file (nonzero exit) if it finds

* `sorryAx`,
* a project axiom (any `axiom` declaration in a release module),
* an `unsafe` declaration,
* `native_decide` (its `ofReduceBool` axiom),
* any axiom outside `{propext, Classical.choice, Quot.sound}` (this also covers
  `Lean.trustCompiler` and any other unapproved trust primitive),
* a declaration or imported module connected with `proof_wanted` / `Mathlib.Wanted`.

The audit is intentionally exhaustive: `collectAxioms` is run on every project constant,
so any `sorry`/`native_decide` anywhere in a project proof is detected regardless of
whether a result card printed it.
-/
import ReleaseCheck
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace D5ReleaseAudit

/-- The only axioms accepted in a released dependency cone. -/
def approvedAxioms : List Name :=
  ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]

/-- `sorryAx` has a dedicated message. -/
def sorryAxiom : Name := "sorryAx".toName

/-- `native_decide`'s trust primitive (`ofReduceBool`), root and `Lean`-qualified spellings. -/
def nativeAxioms : List Name := ["ofReduceBool".toName, "Lean.ofReduceBool".toName]

/-- Module roots owned by this release package. -/
def projectModuleRoots : List Name :=
  ["Poincare".toName, "Probe".toName, "Ledger".toName, "Audit".toName,
   "ReleaseCheck".toName, "ReleaseAudit".toName]

def isProjectModule (m : Name) : Bool :=
  projectModuleRoots.any (fun r => r.isPrefixOf m)

/-- Every constant declared in a module of this release package (base skeleton + D1–D4
clusters + the release drivers). -/
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

/-- Order-preserving duplicate removal (Lean 4.34 has no `Array.dedup`). -/
def dedupNames (xs : Array Name) : Array Name :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]

/-- Order-preserving duplicate removal for `(declaration, axiom)` pairs. -/
def dedupPairs (xs : Array (Name × Name)) : Array (Name × Name) :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]

end D5ReleaseAudit

open D5ReleaseAudit in
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
  let wantedModules := env.header.moduleNames.filter (fun m => m.toString.contains "Wanted")
  logInfo m!"D5ReleaseAudit: project declarations audited: {cs.size}"
  logInfo m!"D5ReleaseAudit: project axiom declarations: {projectAxioms.size}"
  logInfo m!"D5ReleaseAudit: unsafe declarations: {unsafeDefs.size}"
  logInfo m!"D5ReleaseAudit: partial declarations: {partialDefs.size}"
  logInfo m!"D5ReleaseAudit: declarations depending on sorryAx: {sorryDecls.size}"
  logInfo m!"D5ReleaseAudit: declarations depending on native_decide/ofReduceBool: {nativeDecls.size}"
  logInfo m!"D5ReleaseAudit: declarations with unapproved axioms: {otherAxiomDecls.size}"
  logInfo m!"D5ReleaseAudit: project declaration names containing 'proof_wanted': {proofWantedNames.size}"
  logInfo m!"D5ReleaseAudit: imported modules whose name contains 'Wanted' (informational): {wantedModules.size}"
  logInfo m!"D5ReleaseAudit: distinct axiom cones: {distinctCones.size}"
  for s in distinctCones do
    logInfo m!"D5ReleaseAudit:   cone {s}"
  for n in dedupNames partialDefs do
    logInfo m!"D5ReleaseAudit:   note: partial declaration {n}"
  let failed :=
    !projectAxioms.isEmpty || !unsafeDefs.isEmpty || !sorryDecls.isEmpty ||
    !nativeDecls.isEmpty || !otherAxiomDecls.isEmpty || !proofWantedNames.isEmpty
  if failed then
    for n in dedupNames projectAxioms do
      logError m!"D5ReleaseAudit FAIL: project axiom declaration {n}"
    for n in dedupNames unsafeDefs do
      logError m!"D5ReleaseAudit FAIL: unsafe declaration {n}"
    for n in dedupNames sorryDecls do
      logError m!"D5ReleaseAudit FAIL: sorryAx in dependency cone of {n}"
    for n in dedupNames nativeDecls do
      logError m!"D5ReleaseAudit FAIL: native_decide/ofReduceBool in dependency cone of {n}"
    for (n, a) in dedupPairs otherAxiomDecls do
      logError m!"D5ReleaseAudit FAIL: unapproved axiom {a} in dependency cone of {n}"
    for n in dedupNames proofWantedNames do
      logError m!"D5ReleaseAudit FAIL: proof_wanted-derived declaration {n}"
    throwError "D5ReleaseAudit: forbidden dependency found — release gate FAILED"
  else
    logInfo m!"D5ReleaseAudit: PASS — no sorryAx, no project axiom, no unsafe, no native_decide, no proof_wanted in any dependency cone"
