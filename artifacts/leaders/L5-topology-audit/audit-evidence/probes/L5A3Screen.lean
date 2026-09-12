/-
L5-topology-audit — A3 partial screen over the D2/D3 clusters.

Blocker A3 (`audit-residual-finding`) says: no false statement was found, but the
adversarial counterexample search covers only the D4 evolution cluster; the earlier D2/D3
clusters have axiom audits but **no counterexample search**.

This probe does the mechanically checkable part of such a search over the D2/D3 modules
present in the release (`Poincare.Longrun.CurvatureODE.*`, `Poincare.Longrun.Entropy.*`,
`Poincare.Longrun.PDE.*`, `Poincare.Stage1.*`):

* `L5A3TRIV`  — theorem whose conclusion is definitionally `True` (vacuous/trivial wrapper);
* `L5A3VAC`   — theorem with a hypothesis definitionally `False` (vacuous statement);
* `L5A3CIRC`  — theorem with a hypothesis definitionally equal to the conclusion
                (conclusion-equivalent assumption = circular statement);
* `L5A3UNUSED`— hypothesis not occurring in the proof term (candidate overstrong/irrelevant
                hypothesis; reported for review, not by itself a defect);
* `L5A3TAUT`  — `def`/`opaque` of type `Prop` whose value is definitionally `True`
                (tautological interface);
* `L5A3NTYPE` — per-theorem hypothesis count, for the residual-scope bookkeeping.

It is a *screen*, not a proof of A3's closure: absence of hits does not establish absence
of false statements.  A3 therefore remains OPEN with the exact residual scope recorded in
the result card and split into child tasks.
-/
import Poincare.Longrun.CurvatureODE
import Poincare.Longrun.Entropy
import Poincare.Longrun.PDE.ContinuousInterface
import Poincare.Longrun.PDE.DiscreteMaximumPrinciple
import Poincare.Longrun.PDE.Energy
import Poincare.Longrun.PDE.HeatGrid
import Poincare.Longrun.PDE.AxiomAudit
import Poincare.Stage1.RiemannAdapter
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option autoImplicit false
set_option maxHeartbeats 0

open Lean Elab Command Meta

namespace L5A3

def a3Roots : List Name :=
  ["Poincare.Longrun.CurvatureODE".toName,
   "Poincare.Longrun.Entropy".toName,
   "Poincare.Longrun.PDE".toName,
   "Poincare.Stage1".toName]

def isUnder (roots : List Name) (m : Name) : Bool := roots.any (fun r => r.isPrefixOf m)

/-- Analyse one declaration; returns the report lines for it. -/
def analyse (n : Name) (m : Name) (ci : ConstantInfo) : TermElabM (Array String) := do
  let mut out : Array String := #[]
  match ci with
  | .thmInfo _ =>
      let lines ← forallTelescopeReducing ci.type fun xs body => do
        let mut out : Array String := #[]
        let pf := match ci.value? true with
          | some v => mkAppN v xs
          | none => mkConst ``True.intro
        let mut hypCount := 0
        for x in xs do
          let ty ← inferType x
          if ← Meta.isProp ty then
            hypCount := hypCount + 1
            if !pf.hasAnyFVar (fun fv => fv == x.fvarId!) then
              out := out.push s!"L5A3UNUSED\t{n}\t{m}\t{x.fvarId!.name}"
            if ← (try Meta.isDefEq ty (mkConst ``False) catch _ => pure false) then
              out := out.push s!"L5A3VAC\t{n}\t{m}\t{x.fvarId!.name}"
            if ← (try Meta.isDefEq ty body catch _ => pure false) then
              out := out.push s!"L5A3CIRC\t{n}\t{m}\t{x.fvarId!.name}"
        if ← (try Meta.isDefEq body (mkConst ``True) catch _ => pure false) then
          out := out.push s!"L5A3TRIV\t{n}\t{m}"
        out := out.push s!"L5A3NTYPE\t{n}\t{m}\t{hypCount}"
        return out
      out := out ++ lines
  | .defnInfo _ | .opaqueInfo _ =>
      if ← Meta.isProp ci.type then
        let v := match ci.value? true with
          | some v => v
          | none => .const ``True []
        let v ← whnf v
        if ← (try Meta.isDefEq v (mkConst ``True) catch _ => pure false) then
          out := out.push s!"L5A3TAUT\t{n}\t{m}"
  | _ => pure ()
  return out

def runScreen : CommandElabM Unit := do
  let env ← getEnv
  let imported := env.header.moduleNames
  let moduleOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some i => imported.getD i .anonymous
    | none => .anonymous
  let rows : Array (Name × ConstantInfo × Name) :=
    env.constants.fold (fun acc n ci =>
      let m := moduleOf n
      if isUnder a3Roots m then acc.push (n, ci, m) else acc) #[]
  let rows := rows.qsort (fun a b => a.1.toString < b.1.toString)
  let mut theorems := 0
  let mut hypotheses := 0
  let mut unused := 0
  let mut trivial := 0
  let mut vacuous := 0
  let mut circular := 0
  let mut taut := 0
  let mut errors := 0
  for (n, ci, m) in rows do
    if let .thmInfo _ := ci then theorems := theorems + 1
    let ls ←
      try liftTermElabM (analyse n m ci)
      catch _ =>
        errors := errors + 1
        pure #[s!"L5A3ERR\t{n}\t{m}"]
    for l in ls do
      if l.startsWith "L5A3UNUSED" then unused := unused + 1
      else if l.startsWith "L5A3TRIV" then trivial := trivial + 1
      else if l.startsWith "L5A3VAC" then vacuous := vacuous + 1
      else if l.startsWith "L5A3CIRC" then circular := circular + 1
      else if l.startsWith "L5A3TAUT" then taut := taut + 1
      else if l.startsWith "L5A3NTYPE" then
        hypotheses := hypotheses + ((l.splitOn "\t").getD 3 "0").toNat!
      IO.println l
  IO.println s!"L5A3\tdeclarations\t{rows.size}"
  IO.println s!"L5A3\ttheorems\t{theorems}"
  IO.println s!"L5A3\thypotheses\t{hypotheses}"
  IO.println s!"L5A3\tunused_hypotheses\t{unused}"
  IO.println s!"L5A3\ttrivial_conclusions\t{trivial}"
  IO.println s!"L5A3\tvacuous_false_hypotheses\t{vacuous}"
  IO.println s!"L5A3\tcircular_hypotheses\t{circular}"
  IO.println s!"L5A3\ttautological_prop_defs\t{taut}"
  IO.println s!"L5A3\tanalysis_errors\t{errors}"
  IO.println "L5A3VERDICT\tSCREEN_COMPLETE — no counterexample search; A3 remains open"

end L5A3

run_cmd L5A3.runScreen
