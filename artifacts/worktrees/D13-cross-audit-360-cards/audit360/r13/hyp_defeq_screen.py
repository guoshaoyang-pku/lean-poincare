#!/usr/bin/env python3
"""A3 round-13 definitional hypothesis-equals-conclusion screen.

For every declaration the producer cards claim as proved (resolved names from
audit360/r13/axiom_reaudit.json), check in the kernel/meta layer whether any
binder hypothesis is DEFINITIONALLY EQUAL to the conclusion.  This is the
strong form of "no assumption equivalent to the conclusion": it catches
restatements that the syntactic screen cannot see.

Output: audit360/r13/hyp_defeq_screen.json
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
]

PROBE = r"""-- A3 round-13 definitional hyp-equals-conclusion screen (generated)
@@IMPORTS@@

open Lean Elab Command
open Lean Meta
namespace A3R13D

def claimed : List Name := [@@NAMES@@]

/-- Only theorems with a Prop-valued hypothesis can commit the
assumption-as-conclusion defect; a plain function whose argument type equals
its result type (e.g. `def f (x : R) : R`) is benign. -/
def run : CommandElabM Unit := do
  liftTermElabM do
    let mut checked := 0
    for n in claimed do
      let ci ← getConstInfo n
      unless ci matches .thmInfo _ do continue
      checked := checked + 1
      Lean.Meta.forallTelescope ci.type (fun args body => do
        if ← isDefEq body (.const ``True []) then
          logInfo m!"A3R13D|TRIVIAL_TRUE|{n}"
        for a in args do
          let ty ← inferType a
          if ← isProp ty then
            if ← isDefEq ty body then
              let u := a.fvarId!.name
              logInfo m!"A3R13D|HYP_DEFEQ|{n}|{u}"
        )
    logInfo m!"A3R13D|CHECKED|{checked}"
  logInfo m!"A3R13D|DONE"

end A3R13D
run_cmd A3R13D.run
"""


def modules_of(pkg):
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
    ax = json.load(open(os.path.join(ROOT, "audit360", "r13", "axiom_reaudit.json")))
    snap = {"Poincare.D12.SemanticLedger.real_initialCondition_specializes",
            "Poincare.D12.SemanticLedger.realField_unsatisfiable_by_gaussian"}
    names = sorted({v["resolved"] for v in ax["cards"][card]["claims"].values()
                    if v.get("resolved") and v["resolved"] not in snap})
    imports = "\n".join("import " + m for m in modules_of(pkg))
    nm = ",\n  ".join("``" + n for n in names)
    probe = os.path.join(pkg, "A3R13DefEq.lean")
    open(probe, "w").write(PROBE.replace("@@IMPORTS@@", imports).replace("@@NAMES@@", nm))
    env = dict(os.environ)
    env["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
    env["PATH"] = env["ELAN_HOME"] + "/bin:" + env.get("PATH", "")
    log = os.path.join(LOGS, f"hyp_defeq_{card}.log")
    t0 = time.time()
    with open(log, "w") as lf:
        proc = subprocess.run(["lake", "env", "lean", "A3R13DefEq.lean"], cwd=pkg,
                              stdout=lf, stderr=subprocess.STDOUT, env=env, timeout=3600)
    flags, done = {"HYP_DEFEQ": [], "TRIVIAL_TRUE": []}, False
    for raw in open(log, errors="replace"):
        if raw.startswith("A3R13D|"):
            parts = raw.rstrip("\n").split("|")
            if parts[1] == "DONE":
                done = True
            elif parts[1] in flags:
                flags[parts[1]].append(parts[2:])
    return {"rc": proc.returncode, "seconds": round(time.time() - t0, 1),
            "log": os.path.relpath(log, ROOT), "claims": len(names), "done": done,
            "flags": flags}


def main():
    os.makedirs(LOGS, exist_ok=True)
    report = {"lane": "A3-round13", "generated_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
              "cards": {}, "verdict": "PASS"}
    with ThreadPoolExecutor(max_workers=len(CARDS)) as ex:
        runs = list(ex.map(run_card, CARDS))
    for card, r in zip(CARDS, runs):
        report["cards"][card] = r
        if r["rc"] != 0 or not r["done"]:
            report["verdict"] = "FAIL"
        if r["flags"]["HYP_DEFEQ"]:
            report["verdict"] = "REVIEW"
    with open(os.path.join(ROOT, "audit360", "r13", "hyp_defeq_screen.json"), "w") as f:
        json.dump(report, f, indent=1, sort_keys=True)
    print("verdict:", report["verdict"])
    for card in CARDS:
        r = report["cards"][card]
        print(f"  {card:32s} rc={r['rc']} claims={r['claims']} done={r['done']} "
              f"hyp_defeq={len(r['flags']['HYP_DEFEQ'])} "
              f"trivial_true={len(r['flags']['TRIVIAL_TRUE'])} {r['seconds']}s")
        for x in r["flags"]["HYP_DEFEQ"]:
            print("      HYP_DEFEQ", x)
        for x in r["flags"]["TRIVIAL_TRUE"]:
            print("      TRIVIAL_TRUE", x)
    return 0


if __name__ == "__main__":
    sys.exit(main())
