#!/usr/bin/env python3
"""Parse the `#print axioms` output of the D7-sphere-recognition audit.

Reads `longrun/d7sr-logs/axioms-print.out` and writes a JSON summary of the axiom cones
to stdout.  Nonstandard axioms (anything outside {propext, Classical.choice, Quot.sound})
are reported separately so that verification can fail loudly.
"""
import json
import re
import sys
from collections import Counter

PRINT = "longrun/d7sr-logs/axioms-print.out"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}

text = open(PRINT).read()
flat = re.sub(r"\s+", " ", text)
pat = re.compile(
    r"'(\S+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
entries = []
for m in pat.finditer(flat):
    name = m.group(1)
    ax = m.group(3)
    axs = tuple(sorted(a.strip() for a in ax.split(","))) if ax is not None else ()
    entries.append({"name": name, "axioms": list(axs)})

cones = Counter(tuple(e["axioms"]) for e in entries)
nonstandard = [e for e in entries if any(a not in STANDARD for a in e["axioms"])]
out = {
    "schema": "d7-sphere-recognition/axioms-v1",
    "source": PRINT,
    "declarations_audited": len(entries),
    "cones": {str(list(k)): v for k, v in sorted(cones.items(), key=lambda kv: -kv[1])},
    "nonstandard": nonstandard,
    "entries": entries,
}
print(json.dumps(out, indent=1))
if nonstandard:
    sys.exit(1)
