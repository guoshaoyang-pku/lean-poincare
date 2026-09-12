/-
D6-weekly-release — per-declaration axiom report (integrator's independent audit).

This file is a D6 addition.  It imports the accepted D5 `ReleaseCheck` root (all promoted
D1–D4 clusters) and emits one machine-parsable line per project declaration:

    D6DECL<TAB><declaration><TAB><kind><TAB><module><TAB><axiom cone, ';'-separated>

plus a `D6AUDIT<TAB>...` summary block.  It also enforces the same release rule as the
accepted D5 `ReleaseAudit.lean` (no `sorryAx`, no project axiom, no `unsafe`, no
`native_decide`, no unapproved axiom, no `proof_wanted`), so a successful run is both the
per-declaration axiom report and the release gate for the D6 package.
-/
import ReleaseCheck
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace D6AuditReport

/-- The only axioms accepted in a released dependency cone. -/
def approvedAxioms : List Name :=
  ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]

/-- `sorryAx` has a dedicated message. -/
def sorryAxiom : Name := "sorryAx".toName

/-- `native_decide` trust primitives.  In Lean 4.34.0-rc2 `native_decide` emits a private
`<decl>._native.native_decide.ax_*` axiom, which the unapproved-axiom rule catches; the
`ofReduceBool` spellings are retained for older toolchains. -/
def nativeAxioms : List Name :=
  ["ofReduceBool".toName, "Lean.ofReduceBool".toName]

/-- Module roots owned by this release package (accepted D1–D4 clusters, base skeleton,
D5 release drivers, and this D6 report driver). -/
def projectModuleRoots : List Name :=
  ["Poincare".toName, "Probe".toName, "Ledger".toName, "Audit".toName,
   "ReleaseCheck".toName, "ReleaseAudit".toName, "D6AuditReport".toName]

def isProjectModule (m : Name) : Bool :=
  projectModuleRoots.any (fun r => r.isPrefixOf m)

/-- Every constant declared in a release module, together with its owning module. -/
def projectConstants (env : Environment) : Array (Name × ConstantInfo × Name) :=
  let mods := env.header.moduleNames
  env.constants.fold (fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some midx =>
        let m := mods.getD midx .anonymous
        if isProjectModule m then acc.push (n, ci, m) else acc
    | none => acc) #[]

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

/-- Order-preserving duplicate removal (Lean 4.34 has no `Array.dedup`). -/
def dedupNames (xs : Array Name) : Array Name :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]

def coneString (axs : Array Name) : String :=
  ";".intercalate (axs.toList.map Name.toString)

end D6AuditReport

open D6AuditReport in
run_cmd do
  let env ← getEnv
  let cs := projectConstants env
  -- deterministic order by fully-qualified name
  let cs := cs.qsort (fun a b => a.1.toString < b.1.toString)
  let mut projectAxioms : Array Name := #[]
  let mut unsafeDefs : Array Name := #[]
  let mut partialDefs : Array Name := #[]
  let mut proofWantedNames : Array Name := #[]
  let mut sorryDecls : Array Name := #[]
  let mut nativeDecls : Array Name := #[]
  let mut otherAxiomDecls : Array (Name × Name) := #[]
  let mut coneCounts : Array (String × Nat) := #[]
  let mut theoremCount := 0
  for (n, ci, m) in cs do
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
    let axs ← Lean.collectAxioms n
    for a in axs do
      if a == sorryAxiom then
        sorryDecls := sorryDecls.push n
      else if nativeAxioms.contains a then
        nativeDecls := nativeDecls.push n
      else if !approvedAxioms.contains a then
        otherAxiomDecls := otherAxiomDecls.push (n, a)
    let s := coneString axs
    let mut found := false
    let mut newCounts : Array (String × Nat) := #[]
    for (k, c) in coneCounts do
      if k == s then
        found := true
        newCounts := newCounts.push (k, c + 1)
      else
        newCounts := newCounts.push (k, c)
    if !found then newCounts := newCounts.push (s, 1)
    coneCounts := newCounts
    IO.println s!"D6DECL\t{n}\t{kindOf ci}\t{m}\t{s}"
  IO.println s!"D6AUDIT\tproject_declarations\t{cs.size}"
  IO.println s!"D6AUDIT\ttheorems\t{theoremCount}"
  IO.println s!"D6AUDIT\tproject_axioms\t{projectAxioms.size}"
  IO.println s!"D6AUDIT\tunsafe_declarations\t{unsafeDefs.size}"
  IO.println s!"D6AUDIT\tpartial_declarations\t{partialDefs.size}"
  IO.println s!"D6AUDIT\tsorry_declarations\t{sorryDecls.size}"
  IO.println s!"D6AUDIT\tnative_decide_declarations\t{nativeDecls.size}"
  IO.println s!"D6AUDIT\tunapproved_axiom_declarations\t{otherAxiomDecls.size}"
  IO.println s!"D6AUDIT\tproof_wanted_declarations\t{proofWantedNames.size}"
  IO.println s!"D6AUDIT\tdistinct_cones\t{coneCounts.size}"
  for (k, c) in coneCounts do
    IO.println s!"D6AUDIT\tcone\t{c}\t{k}"
  let wantedModules := env.header.moduleNames.filter (fun m => m.toString.contains "Wanted")
  IO.println s!"D6AUDIT\twanted_modules\t{wantedModules.size}"
  for n in dedupNames partialDefs do
    IO.println s!"D6AUDIT\tpartial_decl\t{n}"
  let failed :=
    !projectAxioms.isEmpty || !unsafeDefs.isEmpty || !sorryDecls.isEmpty ||
    !nativeDecls.isEmpty || !otherAxiomDecls.isEmpty || !proofWantedNames.isEmpty
  if failed then
    for n in dedupNames projectAxioms do
      IO.println s!"D6AUDIT\tFAIL\tproject axiom declaration {n}"
    for n in dedupNames unsafeDefs do
      IO.println s!"D6AUDIT\tFAIL\tunsafe declaration {n}"
    for n in dedupNames sorryDecls do
      IO.println s!"D6AUDIT\tFAIL\tsorryAx in dependency cone of {n}"
    for n in dedupNames nativeDecls do
      IO.println s!"D6AUDIT\tFAIL\tnative_decide in dependency cone of {n}"
    for (n, a) in otherAxiomDecls do
      IO.println s!"D6AUDIT\tFAIL\tunapproved axiom {a} in dependency cone of {n}"
    for n in dedupNames proofWantedNames do
      IO.println s!"D6AUDIT\tFAIL\tproof_wanted-derived declaration {n}"
    IO.println "D6AUDIT\tVERDICT\tFAIL"
    throwError "D6AuditReport: forbidden dependency found — D6 release gate FAILED"
  else
    IO.println "D6AUDIT\tVERDICT\tPASS — no sorryAx, no project axiom, no unsafe, no native_decide, no unapproved axiom, no proof_wanted"
