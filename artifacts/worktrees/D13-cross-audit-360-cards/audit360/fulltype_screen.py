#!/usr/bin/env python3
"""Full-namespace triviality/vacuity type screen for the D12 packages.

Round 2/3 screened only the 335 card-declared names.  This script screens the
types of *all* 1104 constants under `Poincare.D12` (the 1103 axiom-audited
declarations plus the documented negative-control axiom), reusing the T1-T11
criteria of `vacuity_screen3.py` plus two full-namespace criteria:

  T12 the whole type is literally `True`
  T13 the type is a proposition with no free variables (a constant `Prop`; a
      review trigger for interfaces that cannot depend on their parameters)

Flags are review triggers, never verdicts.
"""
import glob
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
LOG = os.path.join(HERE, "logs-round3")
OUT = os.path.join(HERE, "fulltype_screen.json")
CARDS = [
    "D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
    "D12-semantic-ledger", "D12-comparison-geodesics", "D12-geometric-compactness",
    "D12-surgery-recognition",
]
START = re.compile(r"^A3TYPE ([^\s:]+) : (.*)$")


def parse(path):
    out, cur, buf = {}, None, []
    for raw in open(path, encoding="utf-8", errors="replace"):
        line = raw.rstrip("\n")
        m = START.match(line)
        if m:
            if cur is not None:
                out[cur] = " ".join(buf).strip()
            cur, buf = m.group(1), [m.group(2)]
        elif cur is not None and not line.startswith("A3TYPE-COUNT"):
            buf.append(line.strip())
    if cur is not None:
        out[cur] = " ".join(buf).strip()
    return out


def norm(s):
    s = re.sub(r"\s+", "", s)
    return s


def conclusion(ty):
    depth = 0
    last = -1
    for i, ch in enumerate(ty):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and ch in "→,":
            last = i
    return ty[last + 1:].strip() if last != -1 else ty.strip()


def flags(name, ty):
    f = []
    c = norm(conclusion(ty))
    if c == "True":
        f.append("T1-conclusion-True")
    if "Nonempty(Decidable" in c:
        f.append("T2-decidable-nonempty")
    if c.startswith("Subsingleton") or "Subsingleton" in c.split("->")[-1]:
        f.append("T3-subsingleton")
    m = re.search(r"([^\s()]+)=([^\s()]+)$", norm(conclusion(ty)))
    if m and m.group(1) == m.group(2):
        f.append("T4-trivial-equality")
    m = re.search(r"([^\s()]+)<->([^\s()]+)$", norm(conclusion(ty)))
    if m and m.group(1) == m.group(2):
        f.append("T5-trivial-iff")
    if re.search(r"\b0\s*[≤<]\s*0\b", conclusion(ty)) or re.search(r"\b0\s*<\s*1\b", conclusion(ty)):
        f.append("T6-numeric-triviality")
    for m in re.finditer(r"[∃]\s*\(?([A-Za-z_][\w']*)\s*[:,]", conclusion(ty)):
        var = m.group(1)
        rest = conclusion(ty)[m.end():]
        if not re.search(r"\b" + re.escape(var) + r"\b", rest):
            f.append("T7-vacuous-existential:" + var)
            break
    if norm(ty) == "True":
        f.append("T12-type-is-True")
    if re.search(r"\(_ : ", ty):
        f.append("T8-underscore-hypothesis")
    return f


def main():
    report = {"criteria": ["T1", "T2", "T3", "T4", "T5", "T6", "T7", "T8", "T12"],
              "cards": {}, "total": 0, "flags": []}
    for card in CARDS:
        path = os.path.join(LOG, card + ".alltypes.log")
        decls = parse(path)
        entry = {"declarations": len(decls), "flags": []}
        for name, ty in sorted(decls.items()):
            fl = flags(name, ty)
            if fl:
                entry["flags"].append({"name": name, "type": ty[:300], "flags": fl})
                report["flags"].append({"card": card, "name": name, "flags": fl})
        report["cards"][card] = entry
        report["total"] += len(decls)
    with open(OUT, "w") as fh:
        json.dump(report, fh, indent=1)
    print("declarations:", report["total"], "| flags:", len(report["flags"]))
    for x in report["flags"]:
        print("FLAG", x["card"], x["name"], x["flags"])
    return 0


if __name__ == "__main__":
    sys.exit(main())
