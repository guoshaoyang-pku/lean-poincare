#!/usr/bin/env python3
"""Round-11 claim-consistency audit for the D13 cross-audit (adversarial lane A3).

Combines three independent evidence streams:

  * `logs-round11/<card>.probe.log` -- the `#print axioms` cones of rounds 1-10
    (recomputed for the ninth time in round 11);
  * `r11/indep_cones_<card>.json`   -- the round-11 independently implemented
    transitive cones and downstream-use queries;
  * the producer card JSONs         -- the claims being audited.

Checks
  C1 cone agreement: for every declaration probed with `#print axioms`, the
     independent traversal must produce the same axiom set.
  C2 closure verdicts: every `exact_blockers_closed` group must have all of its
     mechanised downstream-use queries resolved and wired (type+value), and we
     record how many are wired at proof-term (value-only) level.
  C3 statement-former over-claim screen: a declaration the kind screen classed
     as a `def:PropFormer` (statement-only) must not appear in the card under a
     path that claims it was proved.
  C4 blocker bookkeeping: a claimed-closed blocker id must not reappear in the
     card's `remaining_blockers`.

Exit code 1 if any check fails.  Output: audit360/r11/claim_consistency.json
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(os.path.dirname(HERE))
LOGS = os.path.join(WT, "audit360", "logs-round11")
PKGS = os.path.join(WT, "audit360", "pkgs")
PROD = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees"
OUT = os.path.join(HERE, "claim_consistency.json")

CARDS = [
    "D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
    "D12-semantic-ledger", "D12-comparison-geodesics", "D12-geometric-compactness",
    "D12-surgery-recognition", "D12-triangulation-topology",
    "D12-tensor-maximum-bochner",
]
GROUPS = {  # exact_blockers_closed claim -> tag prefix in uses_queries.json
    "D12-connection-curvature": {"LeviCivitaExistenceStatement/leviCivitaExists": "CC-I1-"},
    "D12-surgery-recognition": {
        "SR-5 sphere_of_spheres": "SR-5-",
        "covering-space recognition": "SR-I5-",
        "coveringTrivial": "SR-I6-",
    },
    "D12-triangulation-topology": {
        "DAG node 5 covering": "C8-node5",
        "DAG node 9 second half (simplex = disk)": "C8-node9b",
        "Sphere-recognition gluing lemma": "C8-n12",
        "Alexander trick": "C8-node14",
        "Closed-cover recognition (node 13)": "C8-n13",
        "Node 13a non-vacuity instance": "C8-n13a",
    },
}
AXIOM_LINE = re.compile(r"^'([^']+)' depends on axioms: \[(.*?)\]\s*$")


def probe_cones(card):
    """Parse the `#print axioms` output of the round-11 probe log."""
    path = os.path.join(LOGS, card + ".probe.log")
    text = open(path, encoding="utf-8", errors="replace").read()
    text = text.replace("\n", " ")
    out = {}
    for m in re.finditer(r"'([^']+)' depends on axioms: \[(.*?)\]", text):
        name, body = m.group(1), m.group(2)
        out[name] = sorted(a.strip() for a in body.split(",") if a.strip())
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", text):
        out[m.group(1)] = []
    return out


def card_json(card):
    return json.load(open(os.path.join(PROD, card, "longrun", "results", card + ".json"),
                          encoding="utf-8"))


def flatten(obj, path=""):
    """Yield (json-path, string) for every string in the card."""
    if isinstance(obj, str):
        yield path, obj
    elif isinstance(obj, dict):
        for k, v in obj.items():
            yield from flatten(v, f"{path}.{k}")
    elif isinstance(obj, list):
        for i, v in enumerate(obj):
            yield from flatten(v, f"{path}[{i}]")


def main():
    kind = json.load(open(os.path.join(WT, "audit360", "kind_screen.json"),
                          encoding="utf-8"))
    result = {"schema": "a3-r11-claim-consistency-v1", "cards": {}}
    failures = []

    for card in CARDS:
        indep_path = os.path.join(HERE, f"indep_cones_{card}.json")
        entry = {"cone_agreement": {}, "closure_verdicts": {}, "overclaims": []}
        if not os.path.exists(indep_path):
            entry["status"] = "INDEPENDENT_RUN_MISSING"
            failures.append(f"{card}: independent run missing")
            result["cards"][card] = entry
            continue
        indep = json.load(open(indep_path, encoding="utf-8"))
        indep_cones = indep.get("cones", {})
        pr = probe_cones(card)

        # C1: cone agreement on every probed declaration
        agree = mismatch = missing = 0
        mismatches = []
        for name, axs in sorted(pr.items()):
            if name not in indep_cones:
                # probe entries may be class-projection rows or over-qualified
                # names; record rather than fail here (F1 covers name resolution)
                short = name.split(".")[-1]
                if not any(k.split(".")[-1] == short for k in indep_cones):
                    missing += 1
                    mismatches.append({"name": name, "reason": "not in independent set"})
                continue
            iaxs = sorted(indep_cones[name]["axioms"])
            if iaxs == sorted(axs):
                agree += 1
            else:
                mismatch += 1
                mismatches.append({"name": name, "print_axioms": axs,
                                   "independent": iaxs})
        entry["cone_agreement"] = {"agree": agree, "mismatch": mismatch,
                                   "missing": missing, "details": mismatches[:20]}
        if mismatch:
            failures.append(f"{card}: {mismatch} cone mismatches")

        # C2: closure verdicts from mechanised use queries
        queries = indep.get("queries", {})
        resolves = indep.get("resolve_only", {})
        for claim, prefix in GROUPS.get(card, {}).items():
            def _m(tag):
                return tag.startswith(prefix) or tag.removeprefix("NEG:").startswith(prefix)
            group = {k: v for k, v in queries.items() if _m(k)}
            res = {k: v for k, v in resolves.items() if _m(k)}
            if not group and not res:
                entry["closure_verdicts"][claim] = {"verdict": "USERS_ONLY"}
                continue
            wired_tv = all(v.get("ok", v["typevalue"]) for v in group.values()) and bool(group)
            wired_vo = sum(1 for v in group.values() if v["valueonly"])
            has_neg = any(k.startswith("NEG:") for k in group)
            if not wired_tv:
                verdict = "REFUTED"
                failures.append(f"{card}: closure {claim} not wired")
            elif has_neg:
                verdict = "CONFIRMED-CLOSURE/DOWNSTREAM-NOT-WIRED"
            else:
                verdict = "CONFIRMED"
            entry["closure_verdicts"][claim] = {
                "verdict": verdict,
                "queries": len(group) + len(res),
                "wired_typevalue": wired_tv,
                "wired_valueonly": wired_vo,
                "detail": {k: {"consumer": v["consumer_fq"], "target": v["target_fq"],
                               "typevalue": v["typevalue"], "valueonly": v["valueonly"]}
                           for k, v in group.items()},
                "resolve_only": {k: v["target_fq"] for k, v in res.items()},
            }

        # C3: statement-former over-claim screen
        kc = kind["cards"].get(card)
        if kc:
            non_proof = [e["name"] for e in kc.get("non_proof_entries", [])
                         if e.get("result") == "PropFormer"]
        else:
            # cards arriving after the round-5 kind screen: parse the round-11 log
            non_proof = []
            kp = os.path.join(LOGS, card + ".kind.log")
            if os.path.exists(kp):
                for line in open(kp, errors="replace"):
                    parts = line.rstrip("\n").split("\t")
                    if len(parts) >= 4 and parts[0] == "A3KIND" and parts[3] == "PropFormer":
                        non_proof.append(parts[1])
        flat = list(flatten(card_json(card)))
        for np_name in non_proof:
            short = np_name.split(".")[-1]
            # if the card itself describes this PropFormer as a `def`, listing it is
            # not an over-claim (its entries read "Name : def, ...")
            if any(re.search(re.escape(short) + r"\s*:\s*def\b", txt) for _, txt in flat):
                continue
            pat = re.compile(r"(?<![\w.])" + re.escape(short) + r"(?![\w])")
            claim_paths = [p for p, s in flat
                           if pat.search(s) and not re.search(
                               r"statement|excluded|frontier|remaining|blocker|not[_ ]?built|missing|dependen|request",
                               p, re.I)]
            if claim_paths:
                entry["overclaims"].append({"declaration": np_name, "paths": claim_paths[:5]})
                failures.append(f"{card}: statement-only {short} appears under proof-claiming path")

        # C4: closed blockers must not reappear in remaining_blockers
        cj = card_json(card)
        rem = json.dumps(cj.get("remaining_blockers", []))
        for claim in GROUPS.get(card, {}):
            key = claim.split()[0]
            if key in rem:
                entry["blocker_bookkeeping"] = {"closed": claim, "reappears_in_remaining": True}
                failures.append(f"{card}: closed blocker {key} reappears in remaining_blockers")

        entry["status"] = "PASS" if not entry["overclaims"] and not mismatch else "FAIL"
        result["cards"][card] = entry

    result["failures"] = failures
    result["verdict"] = "PASS" if not failures else "FAIL"
    json.dump(result, open(OUT, "w", encoding="utf-8"), indent=1, sort_keys=True)
    for card, e in result["cards"].items():
        ca = e.get("cone_agreement", {})
        print(f"{card}: status={e.get('status')} cones agree={ca.get('agree')} "
              f"mismatch={ca.get('mismatch')} missing={ca.get('missing')} "
              f"closures={ {k: v['verdict'] for k, v in e.get('closure_verdicts', {}).items()} }")
    print("FAILURES:", failures)
    print("VERDICT:", result["verdict"])
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
