#!/usr/bin/env python3
"""Compare round-4 probe logs against round-3 logs modulo timing lines.

Round-3 logs were captured under `time` (trailing real/user/sys lines) and some
carry leading timing markers; strip those, then require byte-identity of the
Lean output. Reports SAME/DIFF per pair and exits 1 on any unexpected DIFF.
"""
import re
import sys
from pathlib import Path

E = Path(__file__).resolve().parent.parent / "evidence"

PAIRS = [
    ("r3-semrev-audit.log", "r4-semrev-audit.log"),
    ("r3-semrev-census.log", "r4-semrev-census.log"),
    ("r3-domains.log", "r4-domains.log"),
    ("r3-consumers.log", "r4-consumers.log"),
    ("r3-inhabitants.log", "r4-inhabitants.log"),
    ("r3-semrev-semantics.log", "r4-semantics.log"),
    ("r3-banach.log", "r4-banach.log"),
    ("r3-stageA3.log", "r4-stageA3.log"),
    ("r3-synthfail.log", "r4-synthfail.log"),
    ("r3-negcontrol-parent.log", "r4-negcontrol-parent.log"),
    ("r3-negcontrol-reviewer.log", "r4-negcontrol-reviewer.log"),
    ("r3-perfile-gate.log", "r4-perfile-gate.log"),
    ("r3-forbidden-scan.log", "r4-forbidden-scan.log"),
]
TIMING = re.compile(r"^\s*(real|user|sys)\s+\d")


def norm(p: Path) -> str:
    """Non-empty lines, timing stripped, sorted: environment enumeration order is
    not stable across two builds, so compare content as a multiset."""
    out = []
    for line in p.read_text(errors="replace").splitlines():
        if TIMING.match(line):
            continue
        if line.strip() in {"real", "user", "sys"}:
            continue
        if "seconds=" in line and line.startswith("perfile-"):
            continue
        if not line.strip():
            continue
        out.append(line)
    return "\n".join(sorted(out))


bad = 0
for old, new in PAIRS:
    po, pn = E / old, E / new
    if not pn.exists():
        print(f"MISSING  {new}")
        bad += 1
        continue
    so, sn = norm(po), norm(pn)
    same = so == sn
    print(f"{'SAME' if same else 'DIFF'}  {new}  (vs {old})")
    if not same:
        bad += 1
print("ALL SAME modulo timing" if bad == 0 else f"{bad} difference(s)")
sys.exit(1 if bad else 0)
