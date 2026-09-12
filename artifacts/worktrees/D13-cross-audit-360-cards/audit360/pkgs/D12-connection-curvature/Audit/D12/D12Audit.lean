import Poincare.D12
import Lean.Util.CollectAxioms

/-
D12-connection-curvature — per-declaration axiom audit (fail-closed).

This file imports the full `Poincare.D12` module tree and emits one machine-parsable
line per D12 declaration:

    D12DECL<TAB><declaration><TAB><kind><TAB><module><TAB><axiom cone, ';'-separated>

plus a `D12AUDIT<TAB>...` summary block. It enforces the release rules: no `sorryAx`,
no project axiom, no `unsafe`, no `native_decide`, no unapproved axiom, no
`proof_wanted`. Only `propext`, `Classical.choice`, `Quot.sound` are approved in a
dependency cone. The audit THROWS on any violation (fail-closed): a passing run is the
kernel-trust evidence for every new declaration.

Run from the release directory:

    lake env lean Audit/D12/D12Audit.lean

Negative control: `negcontrol/D12NegativeControl.lean` (not imported by the package)
proves the predicate catches `sorryAx` and `native_decide`.
-/

open Lean Elab Command

namespace D12Audit

/-- The only axioms accepted in a released dependency cone. -/
def approvedAxioms : List Name :=
  ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]

/-- `sorryAx` has a dedicated message. -/
def sorryAxiom : Name := "sorryAx".toName

/-- `native_decide` trust primitives (private `._native.native_decide.ax_*` axioms are
caught by the unapproved-axiom rule; `ofReduceBool` retained for older toolchains). -/
def nativeAxioms : List Name :=
  ["ofReduceBool".toName, "Lean.ofReduceBool".toName]

/-- The D12 module root under audit. -/
def projectModuleRoots : List Name :=
  ["Poincare.D12".toName]

def isProjectModule (m : Name) : Bool :=
  projectModuleRoots.any (fun r => r.isPrefixOf m)

/-- Every constant declared in a D12 module, together with its owning module. -/
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

/-- Order-preserving duplicate removal. -/
def dedupNames (xs : Array Name) : Array Name :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]

def coneString (axs : Array Name) : String :=
  ";".intercalate (axs.toList.map Name.toString)

end D12Audit

open D12Audit in
run_cmd do
  let env ← getEnv
  let cs := projectConstants env
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
    IO.println s!"D12DECL\t{n}\t{kindOf ci}\t{m}\t{s}"
  IO.println s!"D12AUDIT\tproject_declarations\t{cs.size}"
  IO.println s!"D12AUDIT\ttheorems\t{theoremCount}"
  IO.println s!"D12AUDIT\tproject_axioms\t{projectAxioms.size}"
  IO.println s!"D12AUDIT\tunsafe_declarations\t{unsafeDefs.size}"
  IO.println s!"D12AUDIT\tpartial_declarations\t{partialDefs.size}"
  IO.println s!"D12AUDIT\tsorry_declarations\t{sorryDecls.size}"
  IO.println s!"D12AUDIT\tnative_decide_declarations\t{nativeDecls.size}"
  IO.println s!"D12AUDIT\tunapproved_axiom_declarations\t{otherAxiomDecls.size}"
  IO.println s!"D12AUDIT\tproof_wanted_declarations\t{proofWantedNames.size}"
  IO.println s!"D12AUDIT\tdistinct_cones\t{coneCounts.size}"
  for (k, c) in coneCounts do
    IO.println s!"D12AUDIT\tcone\t{c}\t{k}"
  let failed :=
    !projectAxioms.isEmpty || !unsafeDefs.isEmpty || !sorryDecls.isEmpty ||
    !nativeDecls.isEmpty || !otherAxiomDecls.isEmpty || !proofWantedNames.isEmpty
  if failed then
    for n in dedupNames projectAxioms do
      IO.println s!"D12AUDIT\tFAIL\tproject axiom declaration {n}"
    for n in dedupNames unsafeDefs do
      IO.println s!"D12AUDIT\tFAIL\tunsafe declaration {n}"
    for n in dedupNames sorryDecls do
      IO.println s!"D12AUDIT\tFAIL\tsorryAx in dependency cone of {n}"
    for n in dedupNames nativeDecls do
      IO.println s!"D12AUDIT\tFAIL\tnative_decide in dependency cone of {n}"
    for (n, a) in otherAxiomDecls do
      IO.println s!"D12AUDIT\tFAIL\tunapproved axiom {a} in dependency cone of {n}"
    for n in dedupNames proofWantedNames do
      IO.println s!"D12AUDIT\tFAIL\tproof_wanted-derived declaration {n}"
    IO.println "D12AUDIT\tVERDICT\tFAIL"
    throwError "D12Audit: forbidden dependency found — D12 audit FAILED (fail-closed)"
  else
    IO.println "D12AUDIT\tVERDICT\tPASS — no sorryAx, no project axiom, no unsafe, no native_decide, no unapproved axiom, no proof_wanted"
