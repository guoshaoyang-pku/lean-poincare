#!/usr/bin/env python3
"""Extract and check the upstream packages' own `#print axioms` self-audits.

MorganTianLib and Topping annotate hundreds of declarations with
`#print axioms`.  Lake replays those `info:` lines into the build log.  This
script re-parses them with a multi-line-aware matcher (Lean wraps long cones),
summarises the axiom cones, and reports any cone outside
`{propext, Classical.choice, Quot.sound}` — in particular `sorryAx`.

Usage: extract-upstream-self-audits.py <build-log> <out-txt>
"""
import re
import sys
from collections import Counter
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
RECORD = re.compile(
    r"(?:info: )?([^\s:]+\.lean:\d+:\d+: )?'([^']+)' "
    r"(does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",
    re.S,
)


def main():
    log = Path(sys.argv[1]).read_text(errors="replace")
    out = Path(sys.argv[2])
    records, bad = [], []
    lines = []
    for m in RECORD.finditer(log):
        loc, name, shape, body = m.group(1) or "", m.group(2), m.group(3), m.group(4)
        if name.startswith("UpstreamAdapters") or "UpstreamAdapters/" in loc:
            continue
        if shape.startswith("does not"):
            axes = []
        else:
            axes = [a.strip() for a in body.split(",") if a.strip()]
        records.append((name, axes))
        lines.append(f"{loc.strip()}'{name}' depends on axioms: [{', '.join(axes)}]")
        if any(a not in ALLOWED for a in axes):
            bad.append((name, axes))
    cones = Counter(a for _, axes in records for a in axes)
    out.write_text("\n".join(sorted(set(lines))) + "\n")
    print(f"upstream self-audit records: {len(records)}")
    print("cone contents:", dict(cones))
    print(f"disallowed cones: {len(bad)}")
    for name, axes in bad[:10]:
        print("  DISALLOWED", name, axes)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
