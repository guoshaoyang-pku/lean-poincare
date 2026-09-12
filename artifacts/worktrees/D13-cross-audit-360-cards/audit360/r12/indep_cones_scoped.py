#!/usr/bin/env python3
"""Round-12 SCOPED independent axiom-cone checker (adversarial lane A3).

v2 of the round-11 tool (audit360/r11/indep_cones.py): same hand-written `Expr`
traversal, hardened so the two topology-heavy cards (`D12-triangulation-topology`,
`D12-surgery-recognition`) that timed out in round 11 can complete.  Emits
`A3R12SCONE` / `A3R12SPROGRESS` / `A3R12S TOTAL` lines.

Usage: python3 audit360/r12/indep_cones.py [card ...]
Outputs: audit360/r12/indep_cones_scoped_<card>.log/.json, indep_cones.json
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
TEMPLATE = os.path.join(HERE, "IndepConesScopedTemplate.lean")

CARDS = [
    "D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
    "D12-semantic-ledger", "D12-comparison-geodesics", "D12-geometric-compactness",
    "D12-surgery-recognition", "D12-triangulation-topology",
    "D12-tensor-maximum-bochner",
]

CONE = re.compile(r"A3R12SCONE\|([^|]+)\|([^|]*)\|(\d+)")
PROG = re.compile(r"A3R12SPROGRESS\|(\d+)\|(\d+)\|(\d+)")
ENV = dict(os.environ)
ENV["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
ENV["PATH"] = ENV["ELAN_HOME"] + "/bin:" + ENV.get("PATH", "")


def imports_of(pkg):
    out = []
    for line in open(os.path.join(pkg, "A3FullAudit.lean"), encoding="utf-8"):
        if line.startswith("import "):
            out.append(line.rstrip("\n"))
    return out


def main():
    cards = sys.argv[1:] or CARDS
    timeout = int(os.environ.get("A3R12_TIMEOUT", "10800"))
    results = {}
    for card in cards:
        pkg = os.path.join(PKGS, card)
        src = "\n".join(imports_of(pkg)) + "\n\n" + open(TEMPLATE, encoding="utf-8").read()
        outdir = os.path.join(pkg, "A3ExtraR12")
        os.makedirs(outdir, exist_ok=True)
        path = os.path.join(outdir, "IndepConesScoped.lean")
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(src)
        sha = hashlib.sha256(src.encode()).hexdigest()
        log = os.path.join(HERE, f"indep_cones_scoped_{card}.log")
        rc = None
        with open(log, "w", encoding="utf-8") as fh:
            try:
                proc = subprocess.run(
                    ["lake", "env", "lean", "A3ExtraR12/IndepConesScoped.lean"],
                    cwd=pkg, stdout=fh, stderr=subprocess.STDOUT, env=ENV, timeout=timeout)
                rc = proc.returncode
            except subprocess.TimeoutExpired:
                rc = -99
        text = open(log, encoding="utf-8", errors="replace").read()
        cones = {}
        for m in CONE.finditer(text):
            name, axs, visited = m.group(1), m.group(2), int(m.group(3))
            cones[name] = {"axioms": [a for a in axs.split(",") if a], "visited": visited}
        last_prog = None
        progs = PROG.findall(text)
        if progs:
            last_prog = {"roots_done": int(progs[-1][0]), "roots_total": int(progs[-1][1]),
                         "memo": int(progs[-1][2])}
        selftest = "A3R12S SELFTEST PASS" in text
        passed = "A3R12S PASS" in text
        total = re.search(r"A3R12S TOTAL (\d+) declarations, memo size (\d+)", text)
        results[card] = {
            "lean_file": os.path.relpath(path, WT),
            "lean_sha256": sha,
            "log": os.path.relpath(log, WT),
            "rc": rc,
            "selftest_pass": selftest,
            "pass": passed,
            "declarations": int(total.group(1)) if total else None,
            "memo_size": int(total.group(2)) if total else (last_prog["memo"] if last_prog else None),
            "cone_count": len(cones),
            "last_progress": last_prog,
        }
        with open(os.path.join(HERE, f"indep_cones_scoped_{card}.json"), "w", encoding="utf-8") as fh:
            json.dump({"card": card, "rc": rc, "selftest_pass": selftest, "pass": passed,
                       "cones": cones, "last_progress": last_prog},
                      fh, indent=1, sort_keys=True)
        print(f"{card}: rc={rc} selftest={selftest} pass={passed} "
              f"decls={results[card]['declarations']} cones={len(cones)} "
              f"memo={results[card]['memo_size']} last_progress={last_prog}")
        sys.stdout.flush()
    with open(os.path.join(HERE, os.environ.get("A3R12S_OUT", "indep_cones_scoped.json")), "w",
              encoding="utf-8") as fh:
        json.dump(results, fh, indent=1, sort_keys=True)
    bad = [c for c, r in results.items() if r["rc"] != 0 or not r["pass"] or not r["selftest_pass"]]
    print("VERDICT:", "FAIL " + str(bad) if bad else "PASS all cards")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
