#!/usr/bin/env python3
"""Round-9b full-namespace, Prop-gated assumption-as-conclusion screen generator.

`gen_taut_screen.py` screens only the card-declared names and (round 9a) showed
that the raw criterion over-fires on data/type declarations whose result type
coincides with a binder type.  This generator emits `A3TautFull.lean` per package
which

  * enumerates **every** constant of the package's own namespace in the kernel
    environment (same enumeration as `A3FullAudit.lean`, i.e. the 1103-declaration
    full-namespace set),
  * restricts the criterion to **Prop-valued** conclusions, where vacuity is
    meaningful, and
  * flags a declaration iff a forall-binder's type is definitionally equal to the
    conclusion, or the conclusion is definitionally `True`, or the proof body is
    an assumption-like term whose type is the flagged conclusion binder.

A local positive control `A3TautFullScreen.a3TautFullCtl (P : Prop) (h : P) : P := h`
must be flagged; the summary script fails-closed otherwise.

Usage: python3 audit360/gen_taut_full.py [card ...]
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PKGS = os.path.join(HERE, "pkgs")
CARDS = ["D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
         "D12-semantic-ledger", "D12-comparison-geodesics", "D12-geometric-compactness",
         "D12-surgery-recognition"]

BODY = r'''
open Lean Meta Elab Command

namespace A3TautFullScreen

/-- Positive control for the full-namespace screen. -/
theorem a3TautFullCtl (P : Prop) (h : P) : P := h

/-- Flag strings for one declaration value/type; empty means clean. -/
def checkOne (v ty : Expr) : MetaM (Array String) := do
  let ty ← instantiateMVars ty
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

end A3TautFullScreen

open Lean Meta Elab Command in
run_cmd do
  let env ← getEnv
  let root : Name := `Poincare.D12
  let mut checked : Nat := 0
  let mut propChecked : Nat := 0
  let mut flags : Nat := 0
  match env.find? ``A3TautFullScreen.a3TautFullCtl with
  | none => logError m!"A3TAUTFULL-CONTROL-MISSING"
  | some ctl =>
    let ctlV? := match ctl with
      | .thmInfo v => some v.value
      | .defnInfo v => some v.value
      | _ => none
    match ctlV? with
    | none => logError m!"A3TAUTFULL-CONTROL-MISSING"
    | some v =>
      let outs ← liftTermElabM (A3TautFullScreen.checkOne v ctl.type)
      if outs.size == 0 then
        logError m!"A3TAUTFULL-CONTROL-MISSING"
      else
        logInfo m!"A3TAUTFULL-CONTROL-FLAGGED: {outs.toList}"
  for (n, ci) in env.constants.toList do
    if !root.isPrefixOf n then continue
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
        logInfo m!"A3TAUTFULL-FLAG: {n} {outs.toList}"
  logInfo m!"A3TAUTFULL: checked {checked} constants, {propChecked} with proof values, flags {flags}"
'''


def gen(card):
    pkg = os.path.join(PKGS, card)
    imports = []
    full = os.path.join(pkg, "A3UnusedHypFull.lean")
    if os.path.exists(full):
        for line in open(full):
            if line.startswith("import "):
                imports.append(line.rstrip("\n"))
    if not imports:
        imports = ["import Mathlib"]
    text = ("-- A3 round-9 full-namespace Prop-gated assumption-as-conclusion screen for %s\n"
            "-- generated by audit360/gen_taut_full.py; do not edit\n" % card)
    text += "\n".join(imports) + "\n" + BODY
    out = os.path.join(pkg, "A3TautFull.lean")
    open(out, "w").write(text)
    return out


def main():
    cards = sys.argv[1:] or CARDS
    for card in cards:
        print("generated", gen(card))
    return 0


if __name__ == "__main__":
    sys.exit(main())
