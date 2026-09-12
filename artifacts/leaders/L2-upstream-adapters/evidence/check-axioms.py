#!/usr/bin/env python3
"""Fail-closed parser for `#print axioms` output.

Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.  Anything else
(notably `sorryAx`, `Lean.trustCompiler`, project axioms) makes the audit fail
with a non-zero exit code.

Lean wraps long axiom lists over several lines:

    'Foo.bar' depends on axioms: [propext,
     Classical.choice,
     Quot.sound]

so records are matched with a multi-line regex.  The number of record starts is
also compared against the number of parsed records, and any leftover line that
begins a quoted record is a failure: a mangled or truncated log can never be
mistaken for success.

Usage: check-axioms.py <audit-output-file>
"""
import re
import sys
from collections import Counter
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
RECORD = re.compile(
    r"'([^']+)' (does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",
    re.S,
)
START = re.compile(r"^'", re.M)


def main():
    path = Path(sys.argv[1])
    text = path.read_text(errors="replace")
    records = []
    for m in RECORD.finditer(text):
        name = m.group(1)
        if m.group(2).startswith("does not depend"):
            records.append((name, []))
        else:
            axioms = [a.strip() for a in m.group(3).split(",") if a.strip()]
            records.append((name, axioms))
    starts = len(START.findall(text))
    checked, failures, cones = 0, [], Counter()
    for name, axioms in records:
        checked += 1
        for a in axioms:
            cones[a] += 1
        bad = [a for a in axioms if a not in ALLOWED]
        if bad:
            failures.append((name, bad))
    if starts != len(records):
        failures.append((f"<{starts - len(records)} unparsed audit record start(s)>",
                         ["<unparsed-audit-line>"]))
    print(f"axiom audit: parsed {checked} declaration cones "
          f"(record starts in log: {starts})")
    for a, n in sorted(cones.items()):
        print(f"  cone contains {a}: {n}")
    if failures:
        print("AXIOM AUDIT FAILED (fail-closed):")
        for name, bad in failures:
            print(f"  {name}: disallowed {bad}")
        return 1
    if checked == 0:
        print("AXIOM AUDIT FAILED: no audit records found")
        return 1
    print("AXIOM AUDIT PASSED: all cones within {propext, Classical.choice, Quot.sound}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
