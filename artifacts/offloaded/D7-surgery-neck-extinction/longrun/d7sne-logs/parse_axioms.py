#!/usr/bin/env python3
"""Parse the `#print axioms` output of `Poincare/D7/SurgeryFlow/Audit.lean`.

Reads `longrun/d7sne-logs/axioms-print.out` and writes a JSON cone summary.  The
expected cones are exactly `[]`, `[propext]`, `[Quot.sound, propext]` and
`[Classical.choice, Quot.sound, propext]`; anything else is reported under
`nonstandard` (this catches `sorryAx`, project axioms, `native_decide`, ...).
"""
import collections
import json
import re
import sys

SRC = "longrun/d7sne-logs/axioms-print.out"
txt = open(SRC).read()

dep_re = re.compile(r"'([^']+)' depends on axioms: \[(.*?)\]", re.S)
nodep_re = re.compile(r"'([^']+)' does not depend on any axioms")

entries = []
for m in dep_re.finditer(txt):
    name = m.group(1)
    ax = [a.strip() for a in m.group(2).split(",") if a.strip()]
    entries.append({"name": name, "axioms": sorted(ax)})
for m in nodep_re.finditer(txt):
    entries.append({"name": m.group(1), "axioms": []})

cones = collections.Counter(tuple(e["axioms"]) for e in entries)
standard = {"[]", "['propext']", "['Quot.sound', 'propext']",
            "['Classical.choice', 'Quot.sound', 'propext']"}
nonstandard = [e for e in entries if str(e["axioms"]) not in standard]

out = {
    "schema": "d7-surgery-neck-extinction/axioms-v1",
    "source": SRC,
    "declarations_audited": len(entries),
    "cones": {str(list(c)): n for c, n in cones.most_common()},
    "nonstandard": nonstandard,
    "entries": sorted(entries, key=lambda e: e["name"]),
}
json.dump(out, sys.stdout, indent=1)
print()
sys.exit(1 if nonstandard else 0)
