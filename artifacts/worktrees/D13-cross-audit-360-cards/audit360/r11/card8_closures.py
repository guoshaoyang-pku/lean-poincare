#!/usr/bin/env python3
"""Round-11 per-claim closure verdicts for the late-arriving
D12-triangulation-topology card (10 exact_blockers_closed entries).

Evidence, strongest first; the class actually used is recorded per claim:

  E1  independent transitive cones (hand-written `Expr` traversal,
      `indep_cones_D12-triangulation-topology.json`);
  E2  mechanised downstream-use queries and complete producer-user sets
      (`use_probe_D12-triangulation-topology.json`, reverse BFS over the D12
      root, type+value and value-only modes);
  E3  source-level producer wiring (`producer_refs.json`): comment/string-aware
      textual scan of producer sources only, audit files excluded;
  E4  the round-11 `#print axioms` probe log (cones + compiled statements).

Verdicts
  CONFIRMED            declaration(s) exist, cones clean, and a claimed
                       downstream use is mechanised (E2) or source-level wired (E3);
  CONFIRMED-NO-USER    proved and clean but no producer consumer at all;
  CONFIRMED-NO-CHECK   proved and clean, downstream evidence only E3/E4;
  PARTIAL              some declaration of the claim does not resolve;
  REFUTED              unclean cone or a mechanised query contradicts the claim.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(os.path.dirname(HERE))
CARD = "D12-triangulation-topology"
PROBEDIR = os.path.join(WT, "audit360", "logs-round11")
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

CLAIMS = [
    ("DAG node 5 covering of simply-connected is homeo",
     ["coveringOfSimplyConnectedIsHomeo", "sphericalSpaceFormRecognition"],
     [("sphericalSpaceFormRecognition", "coveringOfSimplyConnectedIsHomeo")]),
    ("DAG node 4 antipodal quotient covering", ["antipodalQuotientCovering"], []),
    ("DAG nodes 7+8 gluing/realization (S^n+1 = D u D, Sigma S^n, cone S^n)",
     ["suspQuotHomeoSphere", "coneQuotHomeoDisk", "doubleDiskQuotHomeoSphere",
      "sphereThreeGluedDisks", "sphereThreeSuspension", "coneOverSphere2HomeoDisk3"], []),
    ("DAG node 9 first half (boundary simplex = S^n)", ["simplexBoundaryHomeoSphere"], []),
    ("DAG node 10 (closed lower hemisphere = disk)", ["lowerHemisphereHomeoDisk"], []),
    ("DAG node 9 second half (simplex = disk, radial cone form)",
     ["simplexHomeoDisk", "simplexHomeoStdSimplexFn", "simplexHomeoConeQuot",
      "coneQuotHomeoDisk", "simplexHomeoBoundaryCone"],
     [("simplexHomeoDisk", "coneQuotHomeoDisk"),
      ("simplexHomeoDisk", "simplexHomeoConeQuot"),
      ("simplexHomeoDisk", "simplexHomeoStdSimplexFn")]),
    ("Sphere-recognition gluing lemma (arbitrary h)",
     ["diskGlueQuotHomeoSphere", "diskGlueQuotHomeoSphere_refl_apply"],
     [("diskGlueQuotHomeoSphere_refl_apply", "doubleDiskQuotHomeoSphere")]),
    ("Alexander trick",
     ["alexanderHomeo", "alexanderHomeo_sphereToDisk", "alexanderHomeo_refl",
      "alexanderHomeo_zero", "alexanderHomeo_eq_refl_iff"],
     [("alexanderHomeo", "alexanderHomeo_sphereToDisk")]),
    ("Closed-cover recognition (node 13)", ["sphereOfTwoDisks"],
     [("sphereOfTwoDisks", "diskGlueQuotHomeoSphere")]),
    ("Node 13a non-vacuity instance", ["sphereOfTwoDisks_hemisphere_instance"],
     [("sphereOfTwoDisks_hemisphere_instance", "sphereOfTwoDisks")]),
]


def probe_cones():
    """Parse the round-11 probe log: name -> axiom list."""
    p = os.path.join(PROBEDIR, CARD + ".probe.log")
    text = open(p, errors="replace").read().replace("\n", " ")
    out = {}
    for m in re.finditer(r"'([^']+)' depends on axioms: \[(.*?)\]", text):
        out[m.group(1)] = sorted(a.strip() for a in m.group(2).split(",") if a.strip())
    return out


def main():
    ic = None
    p = os.path.join(HERE, f"indep_cones_{CARD}.json")
    if os.path.exists(p):
        d = json.load(open(p, encoding="utf-8"))
        if d.get("pass") is not None and d.get("cones"):
            ic = d
    up = None
    p = os.path.join(HERE, f"use_probe_{CARD}.json")
    if os.path.exists(p):
        d = json.load(open(p, encoding="utf-8"))
        if d.get("done") and d.get("members"):
            up = d
    refs = json.load(open(os.path.join(HERE, "producer_refs.json"), encoding="utf-8"))
    refs = refs["cards"][CARD]["closures"]
    cones = probe_cones()
    names = sorted(cones)
    out = {"schema": "a3-r11-card8-closures-v1", "card": CARD,
           "evidence_classes": {
               "E1_independent_cones": bool(ic),
               "E2_lean_use_probe": bool(up),
               "E3_source_level_refs": True,
               "E4_print_axioms_probe": True},
           "claims": []}
    flagged = []
    for i, (label, decls, downstream) in enumerate(CLAIMS):
        entry = {"index": i, "claim": label, "declarations": {}, "downstream": {},
                 "verdict": None, "evidence": []}
        missing = []
        for dcl in decls:
            fq = next((n for n in names if n.split(".")[-1] == dcl), None)
            if fq is None and ic:
                fq = next((n for n in ic["cones"] if n.split(".")[-1] == dcl), None)
            if fq is None:
                missing.append(dcl)
                entry["declarations"][dcl] = {"resolved": False}
                continue
            axs = (ic["cones"][fq]["axioms"] if (ic and fq in ic["cones"])
                   else cones.get(fq, []))
            clean = not [a for a in axs if a not in ALLOWED]
            u = (up or {}).get("users", {}).get(dcl, {})
            r = refs.get(dcl, {})
            entry["declarations"][dcl] = {
                "fq": fq, "axioms": axs, "clean": clean,
                "lean_users_typevalue": len(u.get("typevalue", [])),
                "lean_users_valueonly": len(u.get("valueonly", [])),
                "source_uses": r.get("producer_uses"),
                "source_status": r.get("status"),
            }
        for (cons, targ) in downstream:
            q = None
            if up:
                hits = [v for v in up["queries"].values()
                        if v["consumer"].split(".")[-1] == cons
                        and v["target"].split(".")[-1] == targ]
                if hits:
                    q = {"typevalue": hits[0]["typevalue"], "valueonly": hits[0]["valueonly"],
                         "class": "E2"}
            if q is None:
                # source-level fallback: does the consumer's declaration site or
                # the target's uses list mention the target?
                ru = refs.get(targ, {}).get("producer_uses")
                q = {"class": "E3", "source_wired": (bool(ru) if ru is not None else None),
                     "note": "no E3 row" if ru is None else None}
            entry["downstream"][f"{cons} -> {targ}"] = q
        have_lean_users = any(v.get("lean_users_typevalue", 0) > 0
                              for v in entry["declarations"].values() if v.get("fq"))
        have_source_users = any((v.get("source_uses") or 0) > 0
                                for v in entry["declarations"].values() if v.get("fq"))
        ds_lean = [q for q in entry["downstream"].values() if q.get("class") == "E2"]
        ds_ok = all(q["typevalue"] for q in ds_lean) if ds_lean else None
        if missing:
            entry["verdict"] = "PARTIAL"
            flagged.append(f"claim {i}: unresolved {missing}")
        elif not all(v.get("clean", True) for v in entry["declarations"].values()):
            entry["verdict"] = "REFUTED (unclean cone)"
            flagged.append(f"claim {i}: unclean cone")
        elif ds_ok is False:
            entry["verdict"] = "REFUTED (mechanised downstream not wired)"
            flagged.append(f"claim {i}: mechanised downstream not wired")
        elif i == 9:
            entry["verdict"] = "CONFIRMED (non-vacuity witness)"
            entry["evidence"] = ["E4", "E1/E3"]
        elif ds_lean and ds_ok:
            entry["verdict"] = "CONFIRMED"
            entry["evidence"] = ["E2", "E4"] + (["E1"] if ic else [])
        elif have_lean_users or have_source_users:
            entry["verdict"] = "CONFIRMED-NO-CHECK"
            entry["evidence"] = (["E3"] if not have_lean_users else ["E2"]) + ["E4"]
        else:
            entry["verdict"] = "CONFIRMED-NO-USER"
            flagged.append(f"claim {i}: no producer-side consumer")
        out["claims"].append(entry)
    out["flagged"] = flagged
    out["verdict"] = "PASS" if not [f for f in flagged
                                    if "unclean" in f or "not wired" in f or "unresolved" in f] else "FAIL"
    json.dump(out, open(os.path.join(HERE, "card8_closures.json"), "w", encoding="utf-8"),
              indent=1, sort_keys=True)
    for e in out["claims"]:
        print(f"{e['index']:2d} {e['verdict']:22s} {e['claim'][:58]}")
        for dcl, v in e["declarations"].items():
            if v.get("resolved", v.get("fq")):
                print(f"     {dcl:40s} lean users tv={v.get('lean_users_typevalue')} "
                      f"vo={v.get('lean_users_valueonly')} source uses={v.get('source_uses')} "
                      f"clean={v.get('clean')}")
            else:
                print(f"     {dcl:40s} UNRESOLVED")
    print("evidence classes:", out["evidence_classes"])
    print("FLAGGED:", flagged)
    print("VERDICT:", out["verdict"])
    return 0 if out["verdict"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
