/-
A3 round-9 kernel assumption-as-conclusion screen over the D2/D3/D6 namespace.

This is the same kernel criterion used for the seven D12 card packages
(`audit360/pkgs/*/A3TautFull.lean`), applied to the D2/D3/D6 release environment
(`import ReleaseCheck`, roots `Poincare`, `Audit`, `Ledger` — the same namespace
set as `A3UnusedHypD6.lean`):

  * `hypothesis-eq-conclusion:<binder>` — a forall-binder's type is
    definitionally equal to the conclusion;
  * `conclusion-defeq-True` — the conclusion is definitionally `True`;
  * `proof-is-hypothesis:<binder>` — the proof body is an assumption-like term
    whose type is the flagged conclusion binder.

Only Prop-valued conclusions are considered.  The local control
`A3TautD2D3Ctl.a3ctlTaut` must be flagged; the known round-3 finding
A3-D2D3-8 (`stage6Target_of_compactThreeManifold`, whose proof is the hypothesis
`hrec`) is expected to be flagged with both reasons.
-/
import ReleaseCheck

open Lean Meta Elab Command

namespace A3TautD2D3Ctl

theorem a3ctlTaut (P : Prop) (h : P) : P := h

end A3TautD2D3Ctl

open Lean Meta Elab Command in
run_cmd do
  let env ← getEnv
  let roots : List Name := [`Poincare, `Audit, `Ledger]
  let mut checked : Nat := 0
  let mut propChecked : Nat := 0
  let mut flags : Nat := 0
  match env.find? ``A3TautD2D3Ctl.a3ctlTaut with
  | none => logError m!"A3TAUTD2D3-CONTROL-MISSING"
  | some ctl =>
    let ctlV? := match ctl with
      | .thmInfo v => some v.value
      | .defnInfo v => some v.value
      | _ => none
    match ctlV? with
    | none => logError m!"A3TAUTD2D3-CONTROL-MISSING"
    | some v =>
      let outs ← liftTermElabM do
        let ty ← instantiateMVars ctl.type
        forallTelescopeReducing ty fun xs concl => do
          let concl ← instantiateMVars concl
          if !(← isProp concl) then return #[]
          let mut res : Array String := #[]
          let mut idxs : Array Nat := #[]
          for h : i in [0:xs.size] do
            let d ← instantiateMVars (← xs[i].fvarId!.getType)
            if ← isDefEq d concl then
              idxs := idxs.push i
              let nm ← xs[i].fvarId!.getUserName
              res := res.push s!"hypothesis-eq-conclusion:{nm}"
          let bodyRes ← lambdaTelescope v fun ys body => do
            let mut out : Array String := #[]
            let body ← instantiateMVars body
            if let .fvar fid := body.getAppFn then
              if body.getAppArgs.all (fun a => a.isFVar) then
                for i in idxs do
                  if h : i < ys.size then
                    if ys[i].fvarId! == fid then
                      let nm ← ys[i].fvarId!.getUserName
                      out := out.push s!"proof-is-hypothesis:{nm}"
            return out
          return res ++ bodyRes
      if outs.size == 0 then logError m!"A3TAUTD2D3-CONTROL-MISSING"
      else logInfo m!"A3TAUTD2D3-CONTROL-FLAGGED: {outs.toList}"
  for (n, ci) in env.constants.toList do
    if !roots.any (fun r => r.isPrefixOf n) then continue
    checked := checked + 1
    let v? := match ci with
      | .thmInfo v => some v.value
      | .defnInfo v => some v.value
      | _ => none
    match v? with
    | none => pure ()
    | some v =>
      let outs ← liftTermElabM do
        let ty ← instantiateMVars ci.type
        forallTelescopeReducing ty fun xs concl => do
          let concl ← instantiateMVars concl
          if !(← isProp concl) then return #[]
          let mut res : Array String := #[]
          let mut idxs : Array Nat := #[]
          if ← isDefEq concl (mkConst ``True) then
            res := res.push "conclusion-defeq-True"
          for h : i in [0:xs.size] do
            let d ← instantiateMVars (← xs[i].fvarId!.getType)
            if ← isDefEq d concl then
              idxs := idxs.push i
              let nm ← xs[i].fvarId!.getUserName
              res := res.push s!"hypothesis-eq-conclusion:{nm}"
          let bodyRes ← lambdaTelescope v fun ys body => do
            let mut out : Array String := #[]
            let body ← instantiateMVars body
            if let .fvar fid := body.getAppFn then
              if body.getAppArgs.all (fun a => a.isFVar) then
                for i in idxs do
                  if h : i < ys.size then
                    if ys[i].fvarId! == fid then
                      let nm ← ys[i].fvarId!.getUserName
                      out := out.push s!"proof-is-hypothesis:{nm}"
            return out
          return res ++ bodyRes
      propChecked := propChecked + 1
      if outs.size > 0 then
        flags := flags + 1
        logInfo m!"A3TAUTD2D3-FLAG: {n} {outs.toList}"
  logInfo m!"A3TAUTD2D3: checked {checked} constants, {propChecked} with proof values, flags {flags}"
