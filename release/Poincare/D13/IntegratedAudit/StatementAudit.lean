/-
Copyright (c) 2026 D13-integrated-kernel-audit. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D13 integrated kernel audit — statement-level adversarial scan

Independent (auditor-authored) scan of every theorem of the integrated snapshot for the
*shape* defects named in the task acceptance rules:

* `HYP_EQ_CONCL` — a hypothesis whose type is syntactically equal to the conclusion
  (the `(h : P) → P` pattern, i.e. a hypothesis equivalent to the conclusion);
* `HYP_DEFEQ_CONCL` — a hypothesis whose type is *definitionally* equal to the conclusion;
* `CONCL_IN_HYP` — the conclusion occurs as a subterm of one of the hypothesis types
  (weaker structural warning, e.g. `(h : P ∧ Q) → P`).

The scan reports; it does not fail the build by itself.  The driver reviews the reported
names and records the verdict in the result card.  Genuine instances of these patterns are
legitimate (e.g. `And.left`-style projections), so a hit is a *flag*, not a proof of
cheating; the flag list is short enough for manual review.
-/
import Poincare.D13.IntegratedAudit.SnapshotRoot
import Lean.Elab.Command
import Lean.Meta.Tactic.Simp

open Lean Elab Command Meta

namespace Poincare.D13.IntegratedAudit

/-- Syntactic subterm test. -/
partial def occursSyntactic (sub e : Expr) : Bool :=
  if e == sub then true
  else
    match e with
    | .app f a => occursSyntactic sub f || occursSyntactic sub a
    | .lam _ t b _ => occursSyntactic sub t || occursSyntactic sub b
    | .forallE _ t b _ => occursSyntactic sub t || occursSyntactic sub b
    | .letE _ t v b _ => occursSyntactic sub t || occursSyntactic sub v || occursSyntactic sub b
    | .mdata _ b => occursSyntactic sub b
    | .proj _ _ b => occursSyntactic sub b
    | _ => false

/-- Scan one declaration's type. Returns `(syntacticHits, defeqHits, occursHits)`. -/
def scanType (ty : Expr) : MetaM (Array Name × Array Name × Array Name) := do
  let ty ← instantiateMVars ty
  forallTelescopeReducing ty fun xs concl => do
    let mut syn : Array Name := #[]
    let mut deq : Array Name := #[]
    let mut occ : Array Name := #[]
    if concl.isProp then
      for x in xs do
        let d ← inferType x
        if d.isProp then
          if d == concl then syn := syn.push x.fvarId!.name
          else if occursSyntactic concl d then occ := occ.push x.fvarId!.name
          else
            let r ← observing? (withNewMCtxDepth <| isDefEq d concl)
            if r == some true then deq := deq.push x.fvarId!.name
    return (syn, deq, occ)

end Poincare.D13.IntegratedAudit

open Poincare.D13.IntegratedAudit in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut rows : Array (Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.fold (fun acc n ci => acc.push (n, ci)) #[] do
    match env.getModuleIdxFor? n with
    | some midx =>
        let m := mods.getD midx .anonymous
        if (m.toString.startsWith "Poincare.D11" || m.toString.startsWith "Poincare.D12"
            || m.toString.startsWith "Poincare.VKPort") && ci matches .thmInfo _ then
          rows := rows.push (n, ci)
    | none => pure ()
  let sorted := rows.qsort (fun a b => a.1.toString < b.1.toString)
  let mut nSyn := 0
  let mut nDeq := 0
  let mut nOcc := 0
  let mut suspects : Array (String × Name × Name) := #[]
  for (n, ci) in sorted do
    let (syn, deq, occ) ← liftTermElabM (scanType ci.type)
    if !syn.isEmpty then
      nSyn := nSyn + 1
      for h in syn do
        IO.println s!"D13SUSPECT\tHYP_EQ_CONCL\t{n}\t{h}"
        suspects := suspects.push ("HYP_EQ_CONCL", n, h)
    if !deq.isEmpty then
      nDeq := nDeq + 1
      for h in deq do
        IO.println s!"D13SUSPECT\tHYP_DEFEQ_CONCL\t{n}\t{h}"
        suspects := suspects.push ("HYP_DEFEQ_CONCL", n, h)
    if !occ.isEmpty then
      nOcc := nOcc + 1
      for h in occ do
        IO.println s!"D13SUSPECT\tCONCL_IN_HYP\t{n}\t{h}"
  IO.println s!"D13STMT\ttheorems_scanned\t{sorted.size}"
  IO.println s!"D13STMT\thyp_eq_concl\t{nSyn}"
  IO.println s!"D13STMT\thyp_defeq_concl\t{nDeq}"
  IO.println s!"D13STMT\tconcl_in_hyp\t{nOcc}"
