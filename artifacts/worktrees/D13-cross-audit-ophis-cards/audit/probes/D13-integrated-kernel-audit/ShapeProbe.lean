/-
Independent statement-shape scan for the D13-integrated-kernel-audit new layer.
For every theorem of Poincare.D11.*, Poincare.D12.*, Poincare.VKPort.* it telescopes the type and
counts hypotheses whose type is syntactically equal to the conclusion, definitionally equal to it,
or contains it as a syntactic subterm.  This is an independent re-implementation of the shape check;
it reports and does not fail the build.
-/
import Poincare.D13.IntegratedAudit.SnapshotRoot
import Lean.Elab.Command

open Lean Elab Command Meta

namespace D13XShape

partial def occurs (sub e : Expr) : Bool :=
  if e == sub then true
  else
    match e with
    | .app f a => occurs sub f || occurs sub a
    | .lam _ t b _ => occurs sub t || occurs sub b
    | .forallE _ t b _ => occurs sub t || occurs sub b
    | .letE _ t v b _ => occurs sub t || occurs sub v || occurs sub b
    | .mdata _ b => occurs sub b
    | .proj _ _ b => occurs sub b
    | _ => false

def scan (ty : Expr) : MetaM (Nat × Nat × Nat × Array String) := do
  let ty ← instantiateMVars ty
  forallTelescopeReducing ty fun xs concl => do
    let mut nSyn := 0
    let mut nDeq := 0
    let mut nOcc := 0
    let mut names : Array String := #[]
    if concl.isProp then
      for x in xs do
        let d ← inferType x
        if d.isProp then
          if d == concl then
            nSyn := nSyn + 1
            names := names.push s!"SYN:{x.fvarId!.name}"
          else if occurs concl d then
            nOcc := nOcc + 1
            names := names.push s!"OCC:{x.fvarId!.name}"
          else
            let r ← observing? (withNewMCtxDepth <| isDefEq d concl)
            if r == some true then
              nDeq := nDeq + 1
              names := names.push s!"DEQ:{x.fvarId!.name}"
    return (nSyn, nDeq, nOcc, names)

end D13XShape

open D13XShape in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut rows : Array (Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.fold (fun acc n ci => acc.push (n, ci)) #[] do
    match env.getModuleIdxFor? n with
    | some midx =>
        let m := mods.getD midx .anonymous
        let s := m.toString
        if (s.startsWith "Poincare.D11" || s.startsWith "Poincare.D12"
            || s.startsWith "Poincare.VKPort") && ci matches .thmInfo _ then
          rows := rows.push (n, ci)
    | none => pure ()
  let sorted := rows.qsort (fun a b => a.1.toString < b.1.toString)
  let mut nSyn := 0
  let mut nDeq := 0
  let mut nOcc := 0
  let mut suspects : Array String := #[]
  for (n, ci) in sorted do
    let (a, b, c, ns) ← liftTermElabM (scan ci.type)
    nSyn := nSyn + a
    nDeq := nDeq + b
    nOcc := nOcc + c
    for s in ns do
      suspects := suspects.push s!"{n}\t{s}"
  IO.println s!"D13XSHAPE\ttheorems\t{sorted.size}"
  IO.println s!"D13XSHAPE\thyp_eq_concl_syntactic\t{nSyn}"
  IO.println s!"D13XSHAPE\thyp_eq_concl_defeq\t{nDeq}"
  IO.println s!"D13XSHAPE\tconcl_in_hyp\t{nOcc}"
  for s in suspects do
    IO.println s!"D13XSHAPEFLAG\t{s}"
  IO.println "D13XSHAPE_DONE"
