/-
D9-adversarial-audit-release — independent declaration census (auditor-written).

Re-derives from the compiled environment, without trusting
`manifest/verified-declarations.json`:

* every constant declared in a release module + its owning module, kind, safety, and
  kernel axiom cone (`Lean.collectAxioms`);
* for every theorem: used-constant count, directly-referenced module set, the binder
  census (all / explicit / Prop), the hypothesis type list, the conclusion, and
  vacuity / circularity screens:
    - conclusion is literally `True`
    - an explicit hypothesis is literally `False`
    - an explicit hypothesis type is syntactically equal to the conclusion
      (statement of the form `(h : P) → P`)
* proof-shape summary: head of the proof term (hypothesis fvar / constant / projection /
  lambda / other) and proof-term node count.

Release modules are enumerated from the source tree, so the auditor's own files under
`Audit/D9/` are labelled (`d9=<bool>`) but nothing is silently dropped.

Output lines (TSV) are consumed by `IndepCones.py`:
  D9BCONST  <name> <module> <kind> <safety> <axioms> <d9>
  D9BTHM    <name> <module> <used> <directMods> <hyps> <expHyps> <propHyps>
            <falseHyps> <trueConcl> <hypEqConcl> <proofHead> <proofNodes>
            <axioms> <d9> <hypTypes ;; ...> <conclusion>
-/
import ReleaseCheck
import Lean.Util.CollectAxioms
import Lean.Meta.InferType
import Lean.Meta.Tactic.Simp

open Lean Elab Command Meta

namespace D9BCensus

/-- Release modules enumerated from the source tree rooted at the cwd (skips `.lake`). -/
def releaseModules : IO (Array Name) := do
  let root ← IO.currentDir
  let paths ← System.FilePath.walkDir root
    (enter := fun p => pure (p.fileName != some ".lake"))
  let rootStr := root.toString
  let mut out : Array Name := #[]
  for p in paths do
    if p.extension == some "lean" then
      let s := p.toString
      let rel :=
        if s.startsWith (rootStr ++ "/") then (s.drop (rootStr.length + 1)).toString
        else s
      let stem : String := (rel.dropEnd 5).toString
      out := out.push (stem.replace "/" ".").toName
  return out

def moduleOf (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | some i => some (env.header.moduleNames.getD i .anonymous)
  | none => none

def sanitize (s : String) : String :=
  ((s.replace "\n" " ").replace "\r" " ").replace "\t" " "

/-- Dedup preserving order. -/
def dedup (xs : Array Name) : Array Name :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]

/-- Head shape of a proof term. -/
def proofHead (e : Expr) : String :=
  let rec go (e : Expr) : String :=
    match e with
    | .app f _ => go f
    | .lam _ _ b _ => "lam->" ++ go b
    | .forallE _ _ b _ => "forall->" ++ go b
    | .mdata _ b => go b
    | .proj _ _ _ => "proj"
    | .fvar id => "hyp:" ++ (toString (id.name))
    | .const n _ => "const:" ++ (toString n)
    | .sort _ => "sort"
    | .lit _ => "lit"
    | .letE _ _ _ b _ => "let->" ++ go b
    | .bvar _ => "bvar"
    | .mvar _ => "mvar"
  go e

/-- Node count of an expression (rough proof-size proxy). -/
partial def nodeCount (e : Expr) : Nat :=
  match e with
  | .app f a => 1 + nodeCount f + nodeCount a
  | .lam _ t b _ => 1 + nodeCount t + nodeCount b
  | .forallE _ t b _ => 1 + nodeCount t + nodeCount b
  | .letE _ t v b _ => 1 + nodeCount t + nodeCount v + nodeCount b
  | .mdata _ b => 1 + nodeCount b
  | .proj _ _ b => 1 + nodeCount b
  | _ => 1

/-- Statement census for a theorem type. -/
def stmtCensus (e : Expr) : MetaM (Nat × Nat × Nat × Nat × Bool × Bool
    × Array String × String) := do
  forallTelescope e fun xs body => do
    let mut allHyps := 0
    let mut expHyps := 0
    let mut propHyps := 0
    let mut falseHyps := 0
    let mut doms : Array String := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      allHyps := allHyps + 1
      if decl.binderInfo == .default then
        expHyps := expHyps + 1
        doms := doms.push (sanitize (toString decl.type))
        if decl.type.isConstOf ``False then falseHyps := falseHyps + 1
        if ← isProp decl.type then propHyps := propHyps + 1
    let trueConcl := body.isConstOf ``True
    -- syntactic hypothesis-equals-conclusion screen (up to expression equality)
    let mut hypEq := false
    for x in xs do
      let decl ← x.fvarId!.getDecl
      if decl.binderInfo == .default then
        if Expr.equal decl.type body then hypEq := true
    return (allHyps, expHyps, propHyps, falseHyps, trueConcl, hypEq, doms,
            sanitize (toString body))

end D9BCensus

open D9BCensus in
run_cmd do
  let relMods ← releaseModules
  let d9mods := relMods.filter (fun m => ("Audit.D9.").isPrefixOf m.toString)
  IO.println s!"D9BHEAD\trelease_modules\t{relMods.size}\td9_modules\t{d9mods.size}"
  let env ← getEnv
  let cs := (env.constants.fold (fun acc n ci =>
      match env.getModuleIdxFor? n with
      | some midx =>
          let m := env.header.moduleNames.getD midx .anonymous
          if relMods.contains m then acc.push (n, ci, m) else acc
      | none => acc) #[]).qsort (fun a b => a.1.toString < b.1.toString)
  let mut thmCount := 0
  for (n, ci, m) in cs do
    let axs ← Lean.collectAxioms n
    let cone := ";".intercalate (axs.toList.map Name.toString)
    let d9 := if ("Audit.D9.").isPrefixOf m.toString then "1" else "0"
    match ci with
    | .thmInfo v =>
        thmCount := thmCount + 1
        let used := ci.getUsedConstantsAsSet
        let usedArr := used.toArray
        let mods := dedup (usedArr.filterMap (fun c => moduleOf env c))
        let (hyps, expHyps, propHyps, falseHyps, trueConcl, hypEq, doms, concl) ←
          liftTermElabM (stmtCensus v.type)
        let (head, nodes) ←
          liftTermElabM do
            let val ← instantiateMVars v.value
            forallTelescope val fun _ b => do
              pure (proofHead b, nodeCount b)
        let modList := " ".intercalate (mods.toList.map Name.toString)
        let domList := " ;; ".intercalate doms.toList
        IO.println s!"D9BTHM\t{n}\t{m}\t{usedArr.size}\t{mods.size}\t{hyps}\t{expHyps}\t{propHyps}\t{falseHyps}\t{trueConcl}\t{hypEq}\t{head}\t{nodes}\t{cone}\t{d9}\t{domList}\t{concl}"
    | _ => pure ()
    match ci with
    | .axiomInfo _ => IO.println s!"D9BCONST\t{n}\t{m}\taxiom\taxiom\t{cone}\t{d9}"
    | .defnInfo v =>
        let safety := match v.safety with
          | .safe => "safe" | .«unsafe» => "unsafe" | .«partial» => "partial"
        IO.println s!"D9BCONST\t{n}\t{m}\tdef\t{safety}\t{cone}\t{d9}"
    | .opaqueInfo _ => IO.println s!"D9BCONST\t{n}\t{m}\topaque\topaque\t{cone}\t{d9}"
    | .thmInfo _ => IO.println s!"D9BCONST\t{n}\t{m}\tthm\tsafe\t{cone}\t{d9}"
    | .ctorInfo _ => IO.println s!"D9BCONST\t{n}\t{m}\tctor\tsafe\t{cone}\t{d9}"
    | .inductInfo _ => IO.println s!"D9BCONST\t{n}\t{m}\tinduct\tsafe\t{cone}\t{d9}"
    | .recInfo _ => IO.println s!"D9BCONST\t{n}\t{m}\trec\tsafe\t{cone}\t{d9}"
    | .quotInfo _ => IO.println s!"D9BCONST\t{n}\t{m}\tquot\tsafe\t{cone}\t{d9}"
  IO.println s!"D9BHEAD\ttheorems\t{thmCount}"
  IO.println s!"D9BHEAD\tproject_constants\t{cs.size}"
