/-
D9-adversarial-audit-release — fast per-theorem *module* census (auditor-written).

Companion to `IndepCensus.lean`: that file emits the full statement/proof census but (because
of a printing slip) not the direct-module list.  This file emits, for every theorem declared
in a release module, the sorted set of modules owning the constants used in its type and
proof term — the input needed to compute a genuine per-theorem import cone.

  D9BMOD <name> <module> <usedCount> <directModuleCount> <axioms> <module list>
-/
import ReleaseCheck
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace D9BModCensus

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

def dedup (xs : Array Name) : Array Name :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]

end D9BModCensus

open D9BModCensus in
run_cmd do
  let relMods ← releaseModules
  let env ← getEnv
  let cs := (env.constants.fold (fun acc n ci =>
      match env.getModuleIdxFor? n with
      | some midx =>
          let m := env.header.moduleNames.getD midx .anonymous
          if relMods.contains m then acc.push (n, ci, m) else acc
      | none => acc) #[]).qsort (fun a b => a.1.toString < b.1.toString)
  for (n, ci, _) in cs do
    match ci with
    | .thmInfo v =>
        let axs ← Lean.collectAxioms n
        let cone := ";".intercalate (axs.toList.map Name.toString)
        let used := ci.getUsedConstantsAsSet
        let usedArr := used.toArray
        let mods := dedup (usedArr.filterMap (fun c => moduleOf env c))
        let modList := " ".intercalate (mods.toList.map Name.toString)
        IO.println s!"D9BMOD\t{n}\t{mods.size}\t{usedArr.size}\t{cone}\t{modList}"
    | _ => pure ()
