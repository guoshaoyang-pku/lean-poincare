#!/usr/bin/env python3
"""Parse `lake env lean Audit.lean` output into a structured axiom report (session 21)."""
import json
import re
import sys

LOG = sys.argv[1]
OUT = sys.argv[2]

text = open(LOG, encoding="utf-8").read()
# Join continuation lines: a record starts with a quoted name.
text = re.sub(r"\n\s+", " ", text)
lines = [l.strip() for l in text.splitlines() if l.strip()]

STD = {"propext", "Classical.choice", "Quot.sound"}
dep = re.compile(r"^'([^']+)' depends on axioms: \[(.*)\]$")
nodep = re.compile(r"^'([^']+)' does not depend on any axioms$")

details = {}
order = []
for l in lines:
    m = dep.match(l)
    if m:
        name = m.group(1)
        ax = [a.strip() for a in m.group(2).split(",") if a.strip()]
        details[name] = sorted(set(ax))
        order.append(name)
        continue
    m = nodep.match(l)
    if m:
        details[m.group(1)] = []
        order.append(m.group(1))

cones = {}
for v in details.values():
    key = str(sorted(set(v)))
    cones[key] = cones.get(key, 0) + 1

nonstandard = {k: v for k, v in details.items() if not set(v) <= STD}

report = {
    "total": len(details),
    "cones": cones,
    "nonstandard": sorted(nonstandard.items()),
    "details": {k: details[k] for k in order},
}
json.dump(report, open(OUT, "w"), indent=1)

print("total", report["total"])
for k, v in sorted(cones.items()):
    print(" ", k, "->", v)
print("nonstandard:", len(nonstandard))
for k, v in sorted(nonstandard.items()):
    print("  BAD", k, v)
