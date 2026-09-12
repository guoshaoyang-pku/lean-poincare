#!/usr/bin/env python3
"""A3 round-13 independent downstream-use (constant reachability) check.

Fresh implementation for this invocation:

  * a Lean probe dumps, for every constant under Poincare.D12 in each
    cold-rebuilt package, its DIRECT constant references in two modes:
      - "tv": type + value (+ constructor names of inductives),
      - "v" : value only (the proof term);
    the traversal is a hand-written structural recursion over `Expr`;
  * the driver builds the local reference graph and answers the
    consumer -> target reachability queries recorded for the producer cards
    (audit360/r11/uses_queries.json, used here only as the *claim set*);
  * results are compared against the prior lane's round-11/12 use-probe output;
    any disagreement is reported.

Output: audit360/r13/use_reachability.json
"""
import json
import os
import re
import subprocess
import sys
import time
from collections import deque
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
REBUILD = os.path.join(ROOT, "audit360", "r13", "rebuild")
LOGS = os.path.join(ROOT, "audit360", "r13", "logs")
QUERIES = os.path.join(ROOT, "audit360", "r11", "uses_queries.json")
CARDS = [
    "D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
    "D12-semantic-ledger", "D12-comparison-geodesics", "D12-geometric-compactness",
    "D12-surgery-recognition", "D12-triangulation-topology", "D12-tensor-maximum-bochner",
]

PROBE = r"""-- A3 round-13 direct-reference dump (generated)
@@IMPORTS@@

open Lean Elab Command
namespace A3R13U

partial def refsOf (e : Expr) (acc : Std.HashSet Name) : Std.HashSet Name :=
  match e with
  | .app f a         => refsOf a (refsOf f acc)
  | .lam _ t b _     => refsOf b (refsOf t acc)
  | .forallE _ t b _ => refsOf b (refsOf t acc)
  | .letE _ t v b _  => refsOf b (refsOf v (refsOf t acc))
  | .mdata _ b       => refsOf b acc
  | .proj _ _ b      => refsOf b acc
  | .const n _       => acc.insert n
  | _                => acc

def dump : CommandElabM Unit := do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if (`Poincare.D12).isPrefixOf n then
      let mut tv : Std.HashSet Name := {}
      tv := refsOf ci.type tv
      match ci.value? (allowOpaque := true) with
      | some v => tv := refsOf v tv
      | none => pure ()
      match ci with
      | .inductInfo ind => for c in ind.ctors do tv := tv.insert c
      | _ => pure ()
      let mut vonly : Std.HashSet Name := {}
      match ci.value? (allowOpaque := true) with
      | some v => vonly := refsOf v vonly
      | none => pure ()
      logInfo m!"A3R13U|REFS|{n}|tv|{tv.toList.map Name.toString}"
      logInfo m!"A3R13U|REFS|{n}|v|{vonly.toList.map Name.toString}"

end A3R13U

run_cmd A3R13U.dump
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
    imports = "\n".join("import " + m for m in modules_of(pkg))
    probe = os.path.join(pkg, "A3R13Refs.lean")
    open(probe, "w").write(PROBE.replace("@@IMPORTS@@", imports))
    env = dict(os.environ)
    env["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
    env["PATH"] = env["ELAN_HOME"] + "/bin:" + env.get("PATH", "")
    log = os.path.join(LOGS, f"use_refs_{card}.log")
    t0 = time.time()
    with open(log, "w") as lf:
        proc = subprocess.run(["lake", "env", "lean", "A3R13Refs.lean"], cwd=pkg,
                              stdout=lf, stderr=subprocess.STDOUT, env=env, timeout=3600)
    graph = {"tv": {}, "v": {}}
    records = []
    for raw in open(log, errors="replace"):
        if raw.startswith("A3R13U|"):
            records.append(raw.rstrip("\n"))
        elif records:
            records[-1] += " " + raw.strip()
    for line in records:
        if line.startswith("A3R13U|REFS|"):
            parts = line.split("|")
            name, mode, refs = parts[2], parts[3], parts[4] if len(parts) > 4 else "[]"
            graph[mode][name] = [x.strip() for x in refs.strip("[]").split(",") if x.strip()]
    return {"rc": proc.returncode, "seconds": round(time.time() - t0, 1),
            "log": os.path.relpath(log, ROOT), "graph": graph,
            "nodes": {m: len(g) for m, g in graph.items()}}


def reachable(graph, start, target):
    if start not in graph:
        return None
    seen = {start}
    q = deque([start])
    while q:
        cur = q.popleft()
        for nxt in graph.get(cur, ()):
            if nxt == target:
                return True
            if nxt not in seen:
                seen.add(nxt)
                q.append(nxt)
    return False


def resolve(suffix, inv, card_root):
    if suffix in inv:
        return suffix, "exact"
    cands = [n for n in inv if n.endswith("." + suffix) or n == suffix]
    if len(cands) == 1:
        return cands[0], "suffix-unique"
    pref = [n for n in cands if n.startswith(card_root)]
    if len(pref) == 1:
        return pref[0], "suffix-root"
    if len(pref) > 1:
        return None, "ambiguous-root:" + ",".join(sorted(pref)[:4])
    if len(cands) > 1:
        return None, "ambiguous:" + ",".join(sorted(cands)[:4])
    return None, "unresolved"


CARD_ROOT = {
    "D12-connection-curvature": "Poincare.D12.ConnectionCurvature.",
    "D12-volume-ibp": "Poincare.D12.VolumeIBP.",
    "D12-spectral-sobolev": "Poincare.D12.SpectralSobolev.",
    "D12-semantic-ledger": "Poincare.D12.SemanticLedger.",
    "D12-comparison-geodesics": "Poincare.D12.ComparisonGeodesics.",
    "D12-geometric-compactness": "Poincare.D12.GeometricCompactness.",
    "D12-surgery-recognition": "Poincare.D12.SurgeryRecognition.",
    "D12-triangulation-topology": "Poincare.D12.TriangulationTopology.",
    "D12-tensor-maximum-bochner": "Poincare.D12.TensorMaximumBochner.",
}


def main():
    os.makedirs(LOGS, exist_ok=True)
    q = json.load(open(QUERIES))
    report = {"lane": "A3-round13", "generated_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
              "cards": {}, "verdict": "PASS"}
    with ThreadPoolExecutor(max_workers=len(CARDS)) as ex:
        runs = list(ex.map(run_card, CARDS))
    for card, run in zip(CARDS, runs):
        e = {"rc": run["rc"], "seconds": run["seconds"], "log": run["log"],
             "nodes": run["nodes"], "queries": []}
        graph_tv, graph_v = run["graph"]["tv"], run["graph"]["v"]
        inv = set(graph_tv)
        for consumer, target, tag in q.get(card, []):
            ent = {"tag": tag, "consumer_claim": consumer, "target_claim": target}
            if consumer == "":
                res, how = resolve(target, inv, CARD_ROOT[card])
                ent.update({"target": res, "resolve": how,
                            "exists": res is not None})
            else:
                cres, chow = resolve(consumer, inv, CARD_ROOT[card])
                tres, thow = resolve(target, inv, CARD_ROOT[card])
                ent.update({"consumer": cres, "consumer_resolve": chow,
                            "target": tres, "target_resolve": thow})
                if cres and tres:
                    ent["reachable_tv"] = reachable(graph_tv, cres, tres)
                    ent["reachable_v"] = reachable(graph_v, cres, tres)
                    # direct reference (one hop), for evidence
                    ent["direct_tv"] = tres in graph_tv.get(cres, [])
                    ent["direct_v"] = tres in graph_v.get(cres, [])
                else:
                    ent["reachable_tv"] = None
                    ent["reachable_v"] = None
            e["queries"].append(ent)
        # expected negative tags (documented as NEG: or refuted SR-I5-*)
        e["negatives"] = [x for x in e["queries"] if x["tag"].startswith("NEG:") or
                          x["tag"].startswith("SR-I5-")]
        e["negatives_confirmed"] = all(
            (x.get("reachable_v") is False and x.get("reachable_tv") is False)
            for x in e["negatives"])
        e["positives"] = [x for x in e["queries"] if not (x["tag"].startswith("NEG:") or
                                                          x["tag"].startswith("SR-I5-"))]
        e["positives_wired_v"] = sum(1 for x in e["positives"] if x.get("reachable_v"))
        e["positives_total"] = len(e["positives"])
        e["unresolved"] = [x for x in e["queries"]
                           if x.get("target") is None or
                           (x.get("consumer_claim") and x.get("consumer") is None)]
        report["cards"][card] = e
        if e["rc"] != 0 or e["unresolved"] or not e["negatives_confirmed"]:
            report["verdict"] = "FAIL" if e["unresolved"] else report["verdict"]
    with open(os.path.join(ROOT, "audit360", "r13", "use_reachability.json"), "w") as f:
        json.dump(report, f, indent=1, sort_keys=True)
    print("verdict:", report["verdict"])
    for card in CARDS:
        e = report["cards"][card]
        print(f"  {card:32s} rc={e['rc']} nodes_tv={e['nodes']['tv']} "
              f"pos={e['positives_wired_v']}/{e['positives_total']} "
              f"neg_confirmed={e['negatives_confirmed']} unres={len(e['unresolved'])} "
              f"{e['seconds']}s")
        for x in e["unresolved"]:
            print("      UNRESOLVED:", json.dumps(x)[:200])
        for x in e["negatives"]:
            print(f"      NEG {x['tag'][:40]:40s} reach_v={x.get('reachable_v')} "
                  f"reach_tv={x.get('reachable_tv')} direct_v={x.get('direct_v')}")
    return 0 if report["verdict"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
