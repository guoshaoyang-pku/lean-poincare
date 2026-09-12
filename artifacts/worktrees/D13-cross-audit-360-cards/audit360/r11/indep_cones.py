#!/usr/bin/env python3
"""Round-11 independent transitive axiom-cone checker (adversarial lane A3).

Generates `A3ExtraR11/IndepCones.lean` inside each audited package from the
round-11 template and runs it.  The Lean program walks `Expr` by hand and
closes transitively over constant values, so it is an implementation that is
independent of `#print axioms`/`CollectAxioms` (used by rounds 1-10).

Usage: python3 audit360/r11/indep_cones.py [card ...]
Outputs: audit360/r11/indep_cones_<card>.log, audit360/r11/indep_cones.json
"""
import hashlib
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(os.path.dirname(HERE))
PKGS = os.path.join(WT, "audit360", "pkgs")
TEMPLATE = os.path.join(HERE, "IndepConesTemplate.lean")

CARDS = [
    "D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
    "D12-semantic-ledger", "D12-comparison-geodesics", "D12-geometric-compactness",
    "D12-surgery-recognition",
]

CONE = re.compile(r"A3R11CONE\|([^|]+)\|([^|]*)\|(\d+)")
QUERY = re.compile(r"A3R11QUERY\|([^|]*)\|([^|]*)\|([^|]*)\|([^|]*)\|([^|]*)\|typevalue=(\w+)\|valueonly=(\w+)\|expected=(\w+)\|ok=(\w+)")
RESOLVE = re.compile(r"A3R11RESOLVE\|([^|]*)\|([^|]*)\|([^|]*)")
QUERIES = os.path.join(HERE, "uses_queries.json")
MARKER = "def a3r11Queries : List (String × String × String) := []"

ENV = dict(os.environ)
ENV["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
ENV["PATH"] = ENV["ELAN_HOME"] + "/bin:" + ENV.get("PATH", "")


def imports_of(pkg):
    out = []
    path = os.path.join(pkg, "A3FullAudit.lean")
    for line in open(path, encoding="utf-8"):
        if line.startswith("import "):
            out.append(line.rstrip("\n"))
    return out


def main():
    cards = sys.argv[1:] or CARDS
    results = {}
    for card in cards:
        pkg = os.path.join(PKGS, card)
        imports = imports_of(pkg)
        template = open(TEMPLATE, encoding="utf-8").read()
        queries = json.load(open(QUERIES, encoding="utf-8")).get(card, [])
        rendered = "def a3r11Queries : List (String × String × String) := [\n" + "".join(
            "  (%s, %s, %s),\n" % (json.dumps(q[0]), json.dumps(q[1]), json.dumps(q[2]))
            for q in queries) + "]"
        assert MARKER in template, "query marker missing from template"
        template = template.replace(MARKER, rendered)
        src = "\n".join(imports) + "\n\n" + template
        outdir = os.path.join(pkg, "A3ExtraR11")
        os.makedirs(outdir, exist_ok=True)
        path = os.path.join(outdir, "IndepCones.lean")
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(src)
        sha = hashlib.sha256(src.encode()).hexdigest()
        log = os.path.join(HERE, f"indep_cones_{card}.log")
        with open(log, "w", encoding="utf-8") as fh:
            proc = subprocess.run(
                ["lake", "env", "lean", "A3ExtraR11/IndepCones.lean"],
                cwd=pkg, stdout=fh, stderr=subprocess.STDOUT, env=ENV, timeout=10800)
        text = open(log, encoding="utf-8", errors="replace").read()
        cones = {}
        for m in CONE.finditer(text):
            name, axs, visited = m.group(1), m.group(2), int(m.group(3))
            cones[name] = {"axioms": [a for a in axs.split(",") if a], "visited": visited}
        queries = {}
        for m in QUERY.finditer(text):
            tag, cs, ts, cf, tf, tv, vo, exp, ok = m.groups()
            queries[tag] = {"consumer_suffix": cs, "target_suffix": ts,
                            "consumer_fq": cf, "target_fq": tf,
                            "typevalue": tv == "true", "valueonly": vo == "true",
                            "expected": exp == "true", "ok": ok == "true"}
        resolves = {}
        for m in RESOLVE.finditer(text):
            tag, ts, tf = m.groups()
            resolves[tag] = {"target_suffix": ts, "target_fq": tf}
        qmiss = 0
        mm = re.search(r"A3R11 QUERIES (\d+) total, (\d+) missing", text)
        if mm:
            qmiss = int(mm.group(2))
        selftest = "A3R11 SELFTEST PASS" in text
        passed = "A3R11 PASS" in text
        total = re.search(r"A3R11 TOTAL (\d+) declarations, (\d+) reachable", text)
        results[card] = {
            "lean_file": os.path.relpath(path, WT),
            "lean_sha256": sha,
            "log": os.path.relpath(log, WT),
            "rc": proc.returncode,
            "selftest_pass": selftest,
            "pass": passed,
            "declarations": int(total.group(1)) if total else None,
            "reachable_visits": int(total.group(2)) if total else None,
            "cone_count": len(cones),
            "queries": queries,
            "resolve_only": resolves,
            "query_missing": qmiss,
            "all_queries_wired": qmiss == 0 and bool(queries or resolves),
        }
        with open(os.path.join(HERE, f"indep_cones_{card}.json"), "w", encoding="utf-8") as fh:
            json.dump({"card": card, "rc": proc.returncode, "selftest_pass": selftest,
                       "pass": passed, "queries": queries, "resolve_only": resolves,
                       "cones": cones}, fh, indent=1, sort_keys=True)
        print(f"{card}: rc={proc.returncode} selftest={selftest} pass={passed} "
              f"decls={results[card]['declarations']} cones={len(cones)} "
              f"queries={len(queries)}+{len(resolves)} qmiss={qmiss}")
    with open(os.path.join(HERE, "indep_cones.json"), "w", encoding="utf-8") as fh:
        json.dump(results, fh, indent=1, sort_keys=True)
    bad = [c for c, r in results.items() if r["rc"] != 0 or not r["pass"] or not r["selftest_pass"]]
    print("VERDICT:", "FAIL " + str(bad) if bad else "PASS all cards")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
