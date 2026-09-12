#!/usr/bin/env python3
"""Probe-root-scoped independent transitive cone run (round-12 fallback/insurance).

Same hand-written traversal as `IndepConesTemplate.lean`, but the roots are exactly the
declarations listed in the card's `A3Probe.lean` `#print axioms` lines (read from the
round-12 probe log) instead of every constant under the D12 root.  This is the evidence
the `claim_consistency` cone-agreement check consumes, and it is cheaper than the full
namespace closure for the two topology-heavy late cards.

Usage: A3R12P_OUT=... python3 audit360/r12/indep_cones_probe.py <card> [...]
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
LOGS = os.path.join(WT, "audit360", "logs-round12")
TEMPLATE = os.path.join(HERE, "IndepConesProbeTemplate.lean")
MARKER = "def a3r12Roots : List String := []"
PRINT = re.compile(r"^'([^']+)' (?:depends on axioms|does not depend on any axioms)")
CONE = re.compile(r"A3R12PCONE\|([^|]+)\|([^|]*)\|(\d+)")
ENV = dict(os.environ)
ENV["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
ENV["PATH"] = ENV["ELAN_HOME"] + "/bin:" + ENV.get("PATH", "")


def probe_names(card):
    path = os.path.join(LOGS, card + ".probe.log")
    names = []
    for line in open(path, errors="replace"):
        m = PRINT.match(line.strip())
        if m and m.group(1).startswith("Poincare.D12"):
            names.append(m.group(1))
    # de-dup preserving order
    seen, out = set(), []
    for n in names:
        if n not in seen:
            seen.add(n)
            out.append(n)
    return out


def main():
    cards = sys.argv[1:]
    results = {}
    for card in cards:
        names = probe_names(card)
        pkg = os.path.join(PKGS, card)
        imports = [l.rstrip("\n") for l in open(os.path.join(pkg, "A3FullAudit.lean"),
                                                encoding="utf-8") if l.startswith("import ")]
        tpl = open(TEMPLATE, encoding="utf-8").read()
        assert MARKER in tpl
        rendered = "def a3r12Roots : List String := [\n" + "".join(
            "  %s,\n" % json.dumps(n) for n in names) + "]"
        src = "\n".join(imports) + "\n\n" + tpl.replace(MARKER, rendered)
        outdir = os.path.join(pkg, "A3ExtraR12")
        os.makedirs(outdir, exist_ok=True)
        path = os.path.join(outdir, "IndepConesProbe.lean")
        open(path, "w", encoding="utf-8").write(src)
        sha = hashlib.sha256(src.encode()).hexdigest()
        log = os.path.join(HERE, f"indep_cones_probe_{card}.log")
        rc = None
        with open(log, "w", encoding="utf-8") as fh:
            try:
                proc = subprocess.run(["lake", "env", "lean", "A3ExtraR12/IndepConesProbe.lean"],
                                      cwd=pkg, stdout=fh, stderr=subprocess.STDOUT, env=ENV,
                                      timeout=int(os.environ.get("A3R12P_TIMEOUT", "10800")))
                rc = proc.returncode
            except subprocess.TimeoutExpired:
                rc = -99
        text = open(log, errors="replace").read()
        cones = {}
        for m in CONE.finditer(text):
            cones[m.group(1)] = {"axioms": [a for a in m.group(2).split(",") if a], "visited": 0}
        total = re.search(r"A3R12P TOTAL (\d+) declarations, memo size (\d+)", text)
        res = {"card": card, "roots": len(names), "rc": rc,
               "selftest_pass": "A3R12P SELFTEST PASS" in text,
               "pass": "A3R12P PASS" in text,
               "declarations": int(total.group(1)) if total else None,
               "memo_size": int(total.group(2)) if total else None,
               "cones": cones, "lean_sha256": sha,
               "lean_file": os.path.relpath(path, WT)}
        with open(os.path.join(HERE, os.environ.get("A3R12P_OUT", f"indep_cones_probe_{card}.json")),
                  "w", encoding="utf-8") as fh:
            json.dump(res, fh, indent=1, sort_keys=True)
        results[card] = {k: v for k, v in res.items() if k != "cones"}
        print(f"{card}: roots={len(names)} rc={rc} pass={res['pass']} cones={len(cones)} memo={res['memo_size']}")
        sys.stdout.flush()
    print("VERDICT:", "PASS" if all(r["pass"] for r in results.values()) else "FAIL")
    return 0 if all(r["pass"] for r in results.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
