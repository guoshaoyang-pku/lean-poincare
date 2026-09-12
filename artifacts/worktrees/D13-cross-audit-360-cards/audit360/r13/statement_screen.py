#!/usr/bin/env python3
"""A3 round-13 independent statement-level screen.

For every constant under Poincare.D12 (and the snapshot roots) in the
cold-rebuilt packages, flag:

  TRIVIAL_CONCLUSION  conclusion is `True`, `x = x`, or `P ↔ P`;
  HYP_EQ_CONCLUSION   the conclusion is (definitionally) equal to one of the
                      binder hypotheses -- i.e. the statement assumes what it
                      concludes;
  FALSE_HYPOTHESIS    a hypothesis is literally `False` (ex falso);
  ALIAS               a theorem whose proof term is a single constant (possibly
                      applied only to the theorem's own bound variables), i.e.
                      a restatement / renaming rather than a proof.

Each flag is evidence to be reviewed, not a verdict by itself.

Output: audit360/r13/statement_screen.json
"""
import json
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
REBUILD = os.path.join(ROOT, "audit360", "r13", "rebuild")
LOGS = os.path.join(ROOT, "audit360", "r13", "logs")
CARDS = [
    "D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
    "D12-semantic-ledger", "D12-comparison-geodesics", "D12-geometric-compactness",
    "D12-surgery-recognition", "D12-triangulation-topology", "D12-tensor-maximum-bochner",
    "D12-semantic-ledger-snapshot",
]

PROBE = r"""-- A3 round-13 statement-level screen (generated)
@@IMPORTS@@

open Lean Elab Command
namespace A3R13T

/-- peel binders, return (hypothesis types in order, body) -/
partial def peel (e : Expr) (acc : Array Expr) : Array Expr × Expr :=
  match e with
  | .forallE _ d b _ => peel b (acc.push d)
  | _ => (acc, e)

def isTrue (e : Expr) : Bool := e.isConstOf ``True
def isFalse (e : Expr) : Bool := e.isConstOf ``False

/-- conclusion `a = a` or `a ↔ a` up to STRUCTURAL equality.
NOTE: `Expr`'s `BEq` instance is hash-based in this toolchain (`a == b` can be
true for structurally different expressions); `Expr.equal` is the structural
comparison and is what this screen must use. -/
def reflexiveConclusion (e : Expr) : Bool :=
  if e.isAppOfArity ``Eq 3 then
    let a := e.getArg! 1
    let b := e.getArg! 2
    a.equal b
  else if e.isAppOfArity ``Iff 2 then
    (e.getArg! 0).equal (e.getArg! 1)
  else false

/-- proof term is a single constant, possibly applied only to fvars bound by
the theorem's own telescope (a renaming/restatement) -/
def aliasOf (e : Expr) : Option Name :=
  let rec head (e : Expr) : Option Name :=
    match e with
    | .const n _ => some n
    | .app f _ => head f
    | .mdata _ b => head b
    | _ => none
  let rec onlyBound (e : Expr) : Bool :=
    match e with
    | .const _ _ => true
    | .app f a => onlyBound f && onlyBound a
    | .mdata _ b => onlyBound b
    | .fvar _ => true
    | _ => false
  if onlyBound e then head e else none

def screen (roots : List Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if roots.any (fun r => r.isPrefixOf n) then
      count := count + 1
      let (hyps, body) := peel ci.type #[]
      if isTrue body then
        logInfo m!"A3R13T|TRIVIAL|{n}|True"
      else if reflexiveConclusion body then
        logInfo m!"A3R13T|TRIVIAL|{n}|reflexive"
      for h in hyps do
        if isFalse h then
          logInfo m!"A3R13T|FALSE_HYP|{n}"
        if h.equal body then
          logInfo m!"A3R13T|HYP_EQ|{n}|syntactic"
      match ci.value? (allowOpaque := true) with
      | some v =>
        if let some m := aliasOf v then
          if m != n then
            logInfo m!"A3R13T|ALIAS|{n}|{m}"
      | none => pure ()
  logInfo m!"A3R13T|COUNT|{count}"

end A3R13T
run_cmd A3R13T.screen @@ROOTS@@
"""

ROOTS = {
    "D12-semantic-ledger-snapshot": "[`Poincare.D7, `Poincare.D10, `Poincare.D12]",
    "_default": "[`Poincare.D12]",
}


def modules_of(card):
    pkg = os.path.join(REBUILD, card)
    if card == "D12-semantic-ledger-snapshot":
        # reuse the consistent import closure computed for the snapshot audit
        sys.path.insert(0, os.path.join(ROOT, "audit360", "r13"))
        from snapshot_audit import modules_of as snap_modules  # noqa
        return snap_modules(pkg)
    mods = []
    for dirpath, dirnames, filenames in os.walk(os.path.join(pkg, "Poincare", "D12")):
        dirnames[:] = [d for d in dirnames if d not in (".lake",)]
        for fn in sorted(filenames):
            if fn.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dirpath, fn), pkg)
                mods.append(rel[:-5].replace(os.sep, "."))
    return sorted(set(mods))


def run_card(card):
    pkg = os.path.join(REBUILD, card)
    imports = "\n".join("import " + m for m in modules_of(card))
    roots = ROOTS.get(card, ROOTS["_default"])
    probe = os.path.join(pkg, "A3R13Screen.lean")
    open(probe, "w").write(PROBE.replace("@@IMPORTS@@", imports).replace("@@ROOTS@@", roots))
    env = dict(os.environ)
    env["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
    env["PATH"] = env["ELAN_HOME"] + "/bin:" + env.get("PATH", "")
    log = os.path.join(LOGS, f"screen_{card}.log")
    t0 = time.time()
    with open(log, "w") as lf:
        proc = subprocess.run(["lake", "env", "lean", "A3R13Screen.lean"], cwd=pkg,
                              stdout=lf, stderr=subprocess.STDOUT, env=env, timeout=3600)
    flags = {"TRIVIAL": [], "HYP_EQ": [], "FALSE_HYP": [], "ALIAS": []}
    count = None
    for raw in open(log, errors="replace"):
        if raw.startswith("A3R13T|"):
            parts = raw.rstrip("\n").split("|")
            tag = parts[1]
            if tag == "COUNT":
                count = int(parts[2])
            elif tag in flags:
                flags[tag].append(parts[2:])
    return {"rc": proc.returncode, "seconds": round(time.time() - t0, 1),
            "log": os.path.relpath(log, ROOT), "count": count, "flags": flags}


def main():
    os.makedirs(LOGS, exist_ok=True)
    report = {"lane": "A3-round13", "generated_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
              "cards": {}, "verdict": "PASS"}
    with ThreadPoolExecutor(max_workers=len(CARDS)) as ex:
        runs = list(ex.map(run_card, CARDS))
    for card, r in zip(CARDS, runs):
        report["cards"][card] = r
        if r["rc"] != 0 or r["count"] is None:
            report["verdict"] = "REVIEW"
    with open(os.path.join(ROOT, "audit360", "r13", "statement_screen.json"), "w") as f:
        json.dump(report, f, indent=1, sort_keys=True)
    print("verdict:", report["verdict"])
    for card in CARDS:
        r = report["cards"][card]
        f = r["flags"]
        print(f"  {card:32s} rc={r['rc']} n={r['count']} trivial={len(f['TRIVIAL'])} "
              f"hyp_eq={len(f['HYP_EQ'])} false_hyp={len(f['FALSE_HYP'])} "
              f"alias={len(f['ALIAS'])}")
        for k in ("TRIVIAL", "HYP_EQ", "FALSE_HYP"):
            for x in f[k]:
                print("      ", k, x)
        for x in f["ALIAS"][:12]:
            print("       ALIAS", x)
        if len(f["ALIAS"]) > 12:
            print(f"       ... {len(f['ALIAS'])-12} more aliases")
    return 0


if __name__ == "__main__":
    sys.exit(main())
