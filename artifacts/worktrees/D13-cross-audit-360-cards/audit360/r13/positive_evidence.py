#!/usr/bin/env python3
"""A3 round-13: targeted evidence for the four positive queries that the local
D12 reference graph could not answer.

  * CC-I1-e1: `leviCivitaExists` is typed by `LeviCivitaExistenceStatement`,
    which lives in Poincare.Longrun.Geometry.LeviCivitaBlocked (outside D12);
    confirmed by a `#check` probe.
  * C8-node9b / C8-node14: the three F23 "reversed pair" claims -- the card
    names the component lemma as consumer of the main theorem it is derived
    from.  The local graph is re-read here and the REVERSED direction is tested.

Output: audit360/r13/positive_evidence.json
"""
import json
import os
import subprocess
import sys
from collections import deque

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LOGS = os.path.join(ROOT, "audit360", "r13", "logs")
REBUILD = os.path.join(ROOT, "audit360", "r13", "rebuild")
TRI = "Poincare.D12.TriangulationTopology."


def load_graph(log, mode="tv"):
    g = {}
    records = []
    for raw in open(log, errors="replace"):
        if raw.startswith("A3R13U|"):
            records.append(raw.rstrip("\n"))
        elif records:
            records[-1] += " " + raw.strip()
    for line in records:
        if line.startswith("A3R13U|REFS|"):
            parts = line.split("|")
            if parts[3] != mode:
                continue
            g[parts[2]] = [x.strip() for x in (parts[4] if len(parts) > 4 else "[]").strip("[]").split(",") if x.strip()]
    return g


def reach(g, s, t):
    if s not in g:
        return None
    seen, q = {s}, deque([s])
    while q:
        c = q.popleft()
        for n in g.get(c, ()):
            if n == t:
                return True
            if n not in seen:
                seen.add(n)
                q.append(n)
    return False


def main():
    out = {"lane": "A3-round13", "reversed_pairs": {}, "cc_type_check": {}}
    g = load_graph(os.path.join(LOGS, "use_refs_D12-triangulation-topology.log"), "tv")
    gv = load_graph(os.path.join(LOGS, "use_refs_D12-triangulation-topology.log"), "v")
    pairs = [
        ("alexanderHomeo_sphereToDisk", "alexanderHomeo",
         "C8-node14 Alexander trick boundary restriction"),
        ("alexanderHomeo_eq_refl_iff", "alexanderHomeo",
         "C8-node14 Alexander trick nondegeneracy"),
        ("simplexHomeoBoundaryConeStd", "simplexHomeoBoundaryCone",
         "C8-node9b literal radial boundary-cone form"),
    ]
    for a, b, tag in pairs:
        A, B = TRI + a, TRI + b
        out["reversed_pairs"][tag] = {
            "reversed_consumer": A, "reversed_target": B,
            "reachable_tv": reach(g, A, B), "reachable_v": reach(gv, A, B),
            "direct_tv": B in g.get(A, []), "direct_v": B in gv.get(A, []),
        }
    # CC type check via lean
    pkg = os.path.join(REBUILD, "D12-connection-curvature")
    probe = os.path.join(pkg, "A3R13Check.lean")
    open(probe, "w").write(
        "import Poincare.D12.ConnectionCurvature.MilnorLeviCivita\n"
        "import Poincare.Longrun.Geometry.LeviCivitaBlocked\n"
        "set_option pp.all true\n"
        "#check Poincare.D12.ConnectionCurvature.leviCivitaExists\n"
        "#check Poincare.Longrun.Geometry.LeviCivitaExistenceStatement\n")
    env = dict(os.environ)
    env["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
    env["PATH"] = env["ELAN_HOME"] + "/bin:" + env.get("PATH", "")
    log = os.path.join(LOGS, "cc_type_check.log")
    with open(log, "w") as lf:
        proc = subprocess.run(["lake", "env", "lean", "A3R13Check.lean"], cwd=pkg,
                              stdout=lf, stderr=subprocess.STDOUT, env=env, timeout=900)
    txt = open(log, errors="replace").read()
    out["cc_type_check"] = {
        "rc": proc.returncode, "log": os.path.relpath(log, ROOT),
        "mentions_statement": "LeviCivitaExistenceStatement" in txt,
        "mentions_prop_witness": "milnorConnection" in txt,
        "head": txt[:1200],
    }
    out["verdict"] = "PASS" if (
        all(v["reachable_tv"] and v["reachable_v"] for v in out["reversed_pairs"].values())
        and out["cc_type_check"]["rc"] == 0
        and out["cc_type_check"]["mentions_statement"]) else "FAIL"
    with open(os.path.join(ROOT, "audit360", "r13", "positive_evidence.json"), "w") as f:
        json.dump(out, f, indent=1, sort_keys=True)
    print(json.dumps(out, indent=1)[:2500])
    return 0 if out["verdict"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
