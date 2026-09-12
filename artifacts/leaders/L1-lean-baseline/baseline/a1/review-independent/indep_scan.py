#!/usr/bin/env python3
"""Independent semantic scan for the A1 review.

1. Forbidden-token scan of the patch's added lines (comments stripped).
2. Declaration-name comparison for the changed files.
3. Signature comparison of the three promoted declarations.
"""
import re
import subprocess
import sys

WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L1-lean-baseline"
PATCH = f"{WT}/baseline/a1/a1-restatement.patch"
REL = f"{WT}/release"
PAT = f"{WT}/baseline/a1/patched-release"

FORBIDDEN = ["sorry", "admit", "axiom", "unsafe", "native_decide", "proof_wanted"]


def strip_comments(text: str) -> str:
    """Remove /- -/ block comments (nested) and -- line comments."""
    out = []
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if text.startswith("-/", i) and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth > 0:
            i += 1
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


print("=" * 72)
print("1) FORBIDDEN TOKENS IN ADDED PATCH LINES (comments stripped)")
print("=" * 72)
added_by_file = {}
cur = None
for line in open(PATCH, encoding="utf-8"):
    if line.startswith("+++ "):
        cur = line.strip().split(None, 1)[1]
        added_by_file.setdefault(cur, [])
    elif line.startswith("+") and not line.startswith("+++"):
        if cur is not None:
            added_by_file[cur].append(line[1:])
hits = 0
for f, lines in added_by_file.items():
    code = strip_comments("".join(lines))
    for tok in FORBIDDEN:
        for m in re.finditer(r"(?<![A-Za-z0-9_'])" + tok + r"(?![A-Za-z0-9_'])", code):
            hits += 1
            print(f"  HIT {f}: token {tok!r} in added code")
if hits == 0:
    print("  no forbidden token in any added line (comments/docstrings stripped)")

print()
print("=" * 72)
print("2) FULL-FILE TOKEN SCAN OF CHANGED/NEW FILES (comments stripped)")
print("=" * 72)
files = [
    "Audit/CounterexampleAudit.lean",
    "Poincare/D7/EvolutionSharp/AxiomAudit.lean",
    "Poincare/D7/EvolutionSharp/GibbsSharp.lean",
    "Poincare/D7/EvolutionSharp/Implications.lean",
    "Poincare/D7/EvolutionSharp/SharpOnlyConsumers.lean",
    "Poincare/Longrun/Evolution/Discrete.lean",
    "Poincare/Longrun/Evolution/Gibbs.lean",
    "Poincare/Longrun/Evolution.lean",
]
for f in files:
    code = strip_comments(open(f"{PAT}/{f}", encoding="utf-8").read())
    found = [t for t in FORBIDDEN if re.search(r"(?<![A-Za-z0-9_'])" + t + r"(?![A-Za-z0-9_'])", code)]
    print(f"  {f}: {'CLEAN' if not found else 'FOUND ' + str(found)}")

print()
print("=" * 72)
print("3) DECLARATION NAMES: release vs patched")
print("=" * 72)
decl_re = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|class)\s+([A-Za-z0-9_'.]+)",
    re.M,
)
for f in files:
    try:
        a = open(f"{REL}/{f}", encoding="utf-8").read()
    except FileNotFoundError:
        print(f"  {f}: absent in release (new file)")
        continue
    b = open(f"{PAT}/{f}", encoding="utf-8").read()
    na = set(m.group(2) for m in decl_re.finditer(a))
    nb = set(m.group(2) for m in decl_re.finditer(b))
    removed = sorted(na - nb)
    added = sorted(nb - na)
    print(f"  {f}: removed={removed} added={added}")

print()
print("=" * 72)
print("4) SIGNATURE OF THE THREE PROMOTED DECLARATIONS (raw source)")
print("=" * 72)


def sig(path, name):
    lines = open(path, encoding="utf-8").read().splitlines()
    for i, line in enumerate(lines):
        if re.match(r"\s*theorem\s+" + re.escape(name) + r"\b", line):
            body = []
            for ln in lines[i:]:
                body.append(ln.strip())
                if ":=" in ln:
                    break
            return " ".join(body)
    return "<not found>"


for name in ["gibbsTerm_strictAnti", "gibbsTerm_step_lt"]:
    print(f"  [release] {name}: {sig(f'{REL}/Poincare/Longrun/Evolution/Gibbs.lean', name)}")
    print(f"  [patched] {name}: {sig(f'{PAT}/Poincare/Longrun/Evolution/Gibbs.lean', name)}")
    print()
print(f"  [release] perelmanF_step_lt: {sig(f'{REL}/Poincare/Longrun/Evolution/Discrete.lean', 'perelmanF_step_lt')}")
print(f"  [patched] perelmanF_step_lt: {sig(f'{PAT}/Poincare/Longrun/Evolution/Discrete.lean', 'perelmanF_step_lt')}")
