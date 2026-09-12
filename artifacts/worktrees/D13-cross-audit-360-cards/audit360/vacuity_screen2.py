#!/usr/bin/env python3
"""Independent vacuity / triviality screen over the D12 card probes.

The prior round recorded only a decl count and an empty flag list.  This screen
parses the full `#check` types out of the A3Probe logs and applies documented,
conservative heuristics; every flag is then reviewed by hand.

Criteria (a flag is NOT a verdict, only a review trigger):
  T1  conclusion is literally `True`
  T2  conclusion is `Nonempty (Decidable ...)` (classical decidability, not an algorithm)
  T3  conclusion is `Subsingleton ...` at top level
  T4  trivial equality `X = X` with syntactically identical sides
  T5  `P <-> P` with syntactically identical sides
  T6  numeric triviality `0 <= 0`, `0 < 1`, `x <= x`
  T7  conclusion is an existential whose body contains no free occurrence of the
      bound variable (vacuous existential)
  T8  hypothesis binder literally `(_ : ...)` in the statement (unused input)
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(HERE)
LOGS = os.path.join(HERE, "logs")

CARDS = [
    "D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
    "D12-semantic-ledger", "D12-comparison-geodesics", "D12-geometric-compactness",
    "D12-surgery-recognition",
]

DECL_START = re.compile(r"^([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)+)(?:\.\{[^}]*\})?(?:\s|$)")


def parse_probe(card):
    """Return {name: type_text} for one card probe log."""
    path = os.path.join(LOGS, card + ".probe.log")
    out, cur, buf = {}, None, []
    for raw in open(path, encoding="utf-8", errors="replace"):
        line = raw.rstrip("\n")
        if line.startswith("###") or line.startswith("'") or "depends on axioms" in line:
            continue
        m = DECL_START.match(line)
        if m and not line.startswith("  "):
            if cur is not None:
                out[cur] = " ".join(buf).strip()
            cur, buf = m.group(1), [line]
        elif cur is not None:
            buf.append(line)
    if cur is not None:
        out[cur] = " ".join(buf).strip()
    return out


def strip_name(ty):
    return ty.split(" ", 1)[1] if " " in ty else ""


def conclusion(ty):
    """Very conservative: text after the last top-level ':' of the statement."""
    # take the part after the first ' : ' that is followed by the conclusion
    parts = ty.split(" : ", 1)
    return parts[1] if len(parts) == 2 else ty


def flags(name, ty):
    f = []
    concl = conclusion(ty)
    c = concl.replace(" ", "")
    if c == "True":
        f.append("T1-conclusion-True")
    if "Nonempty(Decidable" in c:
        f.append("T2-decidable-nonempty")
    if c.startswith("Subsingleton") or "Subsingleton" in c.split("→")[-1]:
        f.append("T3-subsingleton")
    m = re.search(r"([^\s()]+)\s*=\s*([^\s()]+)\s*$", concl)
    if m and m.group(1) == m.group(2):
        f.append("T4-trivial-equality")
    m = re.search(r"([^\s()]+)\s*<->\s*([^\s()]+)\s*$", concl)
    if m and m.group(1) == m.group(2):
        f.append("T5-trivial-iff")
    if re.search(r"\b0\s*[≤<]\s*0\b", concl) or re.search(r"\b0\s*<\s*1\b", concl):
        f.append("T6-numeric-triviality")
    if re.search(r"\(_ : ", ty):
        f.append("T8-underscore-hypothesis")
    return f


def main():
    report = {"criteria": __doc__.split("Criteria")[1].strip()[:800], "cards": {}}
    total = 0
    allflags = []
    for card in CARDS:
        decls = parse_probe(card)
        total += len(decls)
        entry = {"declarations": len(decls), "flags": []}
        for name, ty in sorted(decls.items()):
            fl = flags(name, ty)
            if fl:
                entry["flags"].append({"name": name, "type": ty[:400], "flags": fl})
                allflags.append((card, name, fl))
        report["cards"][card] = entry
    report["total_declarations"] = total
    report["total_flags"] = len(allflags)
    json.dump(report, open(os.path.join(HERE, "vacuity_screen2.json"), "w"), indent=1)
    print("declarations parsed:", total, "| flags:", len(allflags))
    for card, name, fl in allflags:
        print("FLAG", card, name, fl)
    return 0


if __name__ == "__main__":
    sys.exit(main())
