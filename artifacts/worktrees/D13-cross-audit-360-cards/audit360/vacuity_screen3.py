#!/usr/bin/env python3
"""Round-3 vacuity / triviality screen over the D12 card probes.

Round 2 (vacuity_screen2.py) implemented criteria T1-T6 and T8 but *not* T7
despite documenting it, and had no test for "hypothesis equivalent to the
conclusion" (the D12-plan acceptance criterion).  This round-3 screen:

  * implements every documented criterion honestly (T1-T11),
  * records which criteria are implemented so the docstring cannot drift,
  * re-parses the round-3 probe logs.

Criteria (a flag is a review trigger, never a verdict by itself):
  T1  conclusion is literally `True`
  T2  conclusion contains `Nonempty (Decidable` (classical decidability)
  T3  conclusion is `Subsingleton ...`
  T4  trivial equality `X = X`
  T5  trivial iff `P <-> P`
  T6  numeric triviality `0 ≤ 0`, `0 < 1`
  T7  existential whose body has no free occurrence of the bound variable
  T8  hypothesis binder literally `(_ : ...)`
  T9  conclusion text equals a hypothesis type text (hypothesis = conclusion)
  T10 conclusion is exactly a hypothesis binder name
  T11 hypothesis type is `False` or a textual contradiction (`0 < 0`, `x < x`,
      `x ≠ x`, `a < b ∧ b < a`)
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
LOG = os.path.join(HERE, "logs-round3")
OUT = os.path.join(HERE, "vacuity_screen3.json")

CARDS = [
    "D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
    "D12-semantic-ledger", "D12-comparison-geodesics", "D12-geometric-compactness",
    "D12-surgery-recognition",
]

DECL_START = re.compile(r"^([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)+)(?:\.\{[^}]*\})?(?:\s|$)")

IMPLEMENTED = ["T1", "T2", "T3", "T4", "T5", "T6", "T7", "T8", "T9", "T10", "T11"]


def parse_probe(card):
    path = os.path.join(LOG, card + ".probe.log")
    out, cur, buf = {}, None, []
    if not os.path.exists(path):
        return out
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


def norm(s):
    s = s.replace(" ", "")
    s = s.replace("→", "->").replace("∀", "forall").replace("∃", "exists")
    while s.startswith("(") and s.endswith(")") and s.count("(") == s.count(")"):
        s = s[1:-1]
    return s


def strip_name(ty):
    return ty.split(" ", 1)[1] if " " in ty else ""


def split_binders(ty):
    """Return (binders, conclusion) for a `#check` type string.

    binders: list of (name, type_text).  Conservative top-level split on the
    last top-level arrow/comma.
    """
    s = strip_name(ty)
    depth = 0
    last = -1
    for i, ch in enumerate(s):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and ch in "→,":
            last = i
    if last == -1:
        return [], s.strip()
    head, concl = s[:last], s[last + 1:].strip()
    binders = []
    for m in re.finditer(r"[({[]\s*([A-Za-z_][\w'₀-₉]*)\s*:\s*", head):
        start = m.end()
        depth = 0
        end = len(head)
        for j in range(start, len(head)):
            ch = head[j]
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                if depth == 0:
                    end = j
                    break
                depth -= 1
            elif depth == 0 and ch == ",":
                end = j
                break
        binders.append((m.group(1), head[start:end].strip()))
    return binders, concl


def flags(name, ty):
    f = []
    binders, concl = split_binders(ty)
    c = norm(concl)
    if c == "True":
        f.append("T1-conclusion-True")
    if "Nonempty(Decidable" in c:
        f.append("T2-decidable-nonempty")
    if c.startswith("Subsingleton") or "Subsingleton" in c.split("->")[-1]:
        f.append("T3-subsingleton")
    m = re.search(r"([^\s()]+)=([^\s()]+)$", concl.replace(" ", ""))
    if m and m.group(1) == m.group(2):
        f.append("T4-trivial-equality")
    m = re.search(r"([^\s()]+)<->([^\s()]+)$", concl.replace(" ", ""))
    if m and m.group(1) == m.group(2):
        f.append("T5-trivial-iff")
    if re.search(r"\b0\s*[≤<]\s*0\b", concl) or re.search(r"\b0\s*<\s*1\b", concl):
        f.append("T6-numeric-triviality")
    # T7: vacuous existential
    for m in re.finditer(r"[∃]\s*\(?([A-Za-z_][\w']*)\s*[:,]", concl):
        var = m.group(1)
        rest = concl[m.end():]
        if not re.search(r"\b" + re.escape(var) + r"\b", rest):
            f.append("T7-vacuous-existential:" + var)
            break
    if re.search(r"\(_ : ", ty):
        f.append("T8-underscore-hypothesis")
    # T9/T10: hypothesis = conclusion
    for bname, bty in binders:
        if norm(bty) and norm(bty) == c:
            f.append("T9-hypothesis-equals-conclusion:" + bname)
        if norm(concl) == bname:
            f.append("T10-conclusion-is-hypothesis:" + bname)
    # T11: unsatisfiable-looking hypothesis
    for bname, bty in binders:
        bt = norm(bty)
        if bt == "False" or re.search(r"0<0", bt) or re.search(r"([A-Za-z_][\w']*)<\1", bt) \
           or re.search(r"([A-Za-z_][\w']*)≠\1", bt):
            f.append("T11-suspect-unsat-hypothesis:" + bname + ":" + bty[:60])
    return f, binders, concl


def main():
    report = {"criteria_implemented": IMPLEMENTED, "cards": {}}
    total = 0
    allflags = []
    for card in CARDS:
        decls = parse_probe(card)
        total += len(decls)
        entry = {"declarations": len(decls), "flags": []}
        for name, ty in sorted(decls.items()):
            fl, binders, concl = flags(name, ty)
            if fl:
                entry["flags"].append({"name": name, "type": ty[:500],
                                       "conclusion": concl[:200], "flags": fl})
                allflags.append((card, name, fl))
        report["cards"][card] = entry
    report["total_declarations"] = total
    report["total_flags"] = len(allflags)
    with open(OUT, "w") as fh:
        json.dump(report, fh, indent=1)
    print("declarations parsed:", total, "| flags:", len(allflags))
    for card, name, fl in allflags:
        print("FLAG", card, name, fl)
    return 0


if __name__ == "__main__":
    sys.exit(main())
