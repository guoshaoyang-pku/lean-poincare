/-
D9-adversarial-audit-release — independent per-theorem dependency census.

This file is written by the D9 auditor, *not* by the D6 release builder.  It re-derives,
from the compiled environment alone (no trust in `manifest/verified-declarations.json`):

* every constant declared in a release module, with its owning module;
* for every `theorem`, the set of *directly* referenced constants (type + proof term)
  and, via their owning modules, the directly referenced module set;
* the kernel axiom cone from `Lean.collectAxioms` (the engine behind `#print axioms`);
* a binder census of the statement: explicit `∀` binders, explicit `Prop` binders, and
  the domain type of every explicit binder (i.e. the hypothesis list);
* a vacuity screen: whether the conclusion is literally `True`, and how many explicit
  hypotheses are literally `False`.

Ownership rule.  The release modules are enumerated from the **source tree** rooted at the
current working directory (the package root under `lake env lean`).  An earlier draft of
this census used a name-prefix whitelist (`Poincare`, `Probe`, `Ledger`, `Audit`) and
silently dropped module `ReleaseCheck` — which holds `D5ReleaseCheck.release_check_compiles`,
the theorem attached to the module that imports every other release module.  The
filesystem-derived rule cannot have that failure mode.

Output is tab-separated `D9THEOREM` / `D9THMEX` lines consumed by `analyze_cones.py`,
which unions the per-module import closures to obtain a genuine per-theorem import cone.
-/
import ReleaseCheck
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Meta.InferType

open Lean Elab Command

namespace D9TheoremConeAudit

/-- Module names of the release package, enumerated from the source tree at the current
working directory.  `.lake` is skipped, so no dependency package leaks in. -/
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

/-- Every constant declared in a release module, with its owning module. -/
def projectConstants (env : Environment) (relMods : Array Name) :
    Array (Name × ConstantInfo × Name) :=
  let mods := env.header.moduleNames
  env.constants.fold (fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some midx =>
        let m := mods.getD midx .anonymous
        if relMods.contains m then acc.push (n, ci, m) else acc
    | none => acc) #[]

/-- Owning module of a constant, if it is an imported/defined constant. -/
def moduleOf (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | some i => some (env.header.moduleNames.getD i .anonymous)
  | none => none

/-- Flatten a string so it can live on one TSV line. -/
def sanitize (s : String) : String :=
  ((s.replace "\n" " ").replace "\r" " ").replace "\t" " "

/-- Binder census plus vacuity screen.  Returns
(explicit binder count, explicit `Prop` binder count, explicit binder domains,
 conclusion, conclusion-is-`True`, number of explicit hypotheses that are `False`). -/
def binderCensus (e : Expr) : MetaM (Nat × Nat × Array String × String × Bool × Nat) := do
  Meta.forallTelescope e fun xs body => do
    let mut hyps := 0
    let mut propHyps := 0
    let mut doms : Array String := #[]
    let mut falseHyps := 0
    for x in xs do
      let decl ← x.fvarId!.getDecl
      if decl.binderInfo == .default then
        hyps := hyps + 1
        doms := doms.push (sanitize (toString decl.type))
        if decl.type.isConstOf ``False then falseHyps := falseHyps + 1
        if ← Meta.isProp decl.type then propHyps := propHyps + 1
    let conclusion := sanitize (toString body)
    let isTrueConcl := body.isConstOf ``True
    return (hyps, propHyps, doms, conclusion, isTrueConcl, falseHyps)

/-- Order-preserving dedup for module lists. -/
def dedup (xs : Array Name) : Array Name :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]

end D9TheoremConeAudit

open D9TheoremConeAudit in
run_cmd do
  let relMods ← releaseModules
  IO.println s!"D9CONE\trelease_modules\t{relMods.size}"
  for m in relMods.qsort (fun a b => a.toString < b.toString) do
    IO.println s!"D9CONE\tmodule\t{m}"
  let env ← getEnv
  let cs := (projectConstants env relMods).qsort (fun a b => a.1.toString < b.1.toString)
  let mut theoremCount := 0
  let mut defCount := 0
  for (n, ci, m) in cs do
    -- Independent replication of the central D6 kernel claim: the axiom cone of *every*
    -- release declaration, not only of the theorems.
    let axs ← Lean.collectAxioms n
    let cone := ";".intercalate (axs.toList.map Name.toString)
    IO.println s!"D9AXIOM\t{n}\t{m}\t{cone}"
    match ci with
    | .thmInfo _ =>
        theoremCount := theoremCount + 1
        let used := ci.getUsedConstantsAsSet
        let usedArr := used.toArray
        let mods := dedup (usedArr.filterMap (fun c => moduleOf env c))
        let (hyps, propHyps, doms, concl, isTrueConcl, falseHyps) ←
          liftTermElabM (binderCensus ci.type)
        let modList := " ".intercalate (mods.toList.map Name.toString)
        let domList := " ;; ".intercalate doms.toList
        IO.println s!"D9THEOREM\t{n}\t{m}\t{usedArr.size}\t{mods.size}\t{hyps}\t{propHyps}\t{axs.size}\t{cone}\t{modList}\t{domList}\t{sanitize (toString ci.type)}"
        IO.println s!"D9THMEX\t{n}\t{isTrueConcl}\t{falseHyps}\t{concl}"
    | .defnInfo _ => defCount := defCount + 1
    | _ => pure ()
  IO.println s!"D9CONE\ttheorems\t{theoremCount}"
  IO.println s!"D9CONE\tdefs\t{defCount}"
  IO.println s!"D9CONE\tproject_constants\t{cs.size}"
  let shapes := cs.filterMap (fun (n, ci, _) =>
    match ci with
    | .axiomInfo _ => some s!"axiomInfo\t{n}"
    | .defnInfo v =>
        match v.safety with
        | .«unsafe» => some s!"unsafe_def\t{n}"
        | .«partial» => some s!"partial_def\t{n}"
        | .safe => none
    | .opaqueInfo _ => some s!"opaqueInfo\t{n}"
    | _ => none)
  IO.println s!"D9CONE\taxiom_or_unsafe_or_opaque\t{shapes.size}"
  for s in shapes do
    IO.println s!"D9CONE\tSHAPE\t{s}"
