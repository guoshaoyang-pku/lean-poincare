#!/usr/bin/env python3
"""Round-7 vacuity-screen self-control follow-up (finding F18).

The round-7 audit-of-the-auditor control C3 injected

    theorem a3CtlTauto (P : Prop) (h : P) : P := h

and the round-3 vacuity screen (`vacuity_screen3.flags`) did NOT flag it,
although the type is literally "hypothesis = conclusion".  Root cause: Lean's
`#check` prints a theorem whose type is a forall in signature form

    name (P : Prop) (h : P) : P

and `vacuity_screen3.split_binders` only splits on top-level `→`/`,`, never on
the signature colon, so `binders = []` and `conclusion` becomes the whole
signature string.  Every criterion that needs the binders or the conclusion
(T1, T3-T7, T9, T10, T11) is then blind for such declarations.

This script:
  1. reproduces the blind spot on the control type (old parser: no flag);
  2. implements an honest fixed splitter (signature binders + colon) and shows
     the control is flagged;
  3. re-screens all real round-7 card declarations with the fixed splitter and
     diffs the flags against the round-7 re-run of the old screen.

Output: `audit360/vacuity_screen8_fixed.json`.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import vacuity_screen3 as vs  # noqa: E402

LOG = os.path.join(HERE, "logs-round8")
CARDS = [
    "D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
    "D12-semantic-ledger", "D12-comparison-geodesics", "D12-geometric-compactness",
    "D12-surgery-recognition",
]


def parse_binder_groups(head):
    """Parse `(x : A) {y : B} [C] ...` at top level; None if not all binders."""
    s = head.strip()
    binders = []
    i = 0
    n = len(s)
    while i < n:
        while i < n and s[i] == " ":
            i += 1
        if i >= n:
            break
        if s[i] not in "([{":
            return None
        close = {"(": ")", "[": "]", "{": "}"}[s[i]]
        depth = 0
        j = i
        while j < n:
            if s[j] in "([{":
                depth += 1
            elif s[j] in ")]}":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        if j >= n:
            return None
        inner = s[i + 1:j]
        m = re.match(r"\s*([A-Za-z_][\w'₀-₉]*)\s*:\s*(.*)$", inner, re.S)
        if m:
            binders.append((m.group(1), m.group(2).strip()))
        i = j + 1
    return binders


def split_binders_fixed(ty):
    """Signature-aware split: `name (b1 : T1) (b2 : T2) : concl` or old style."""
    s = vs.strip_name(ty)
    depth = 0
    last_colon = -1
    for i, ch in enumerate(s):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and ch == ":":
            last_colon = i
    if last_colon != -1 and s.strip().startswith(("(", "{", "[")):
        head, concl = s[:last_colon], s[last_colon + 1:].strip()
        binders = parse_binder_groups(head)
        if binders is not None:
            return binders, concl, True
    binders, concl = vs.split_binders(ty)
    return binders, concl, False


def flags_fixed(ty):
    """Same criteria as vacuity_screen3.flags but with the signature-aware split."""
    f = []
    binders, concl, sig = split_binders_fixed(ty)
    c = vs.norm(concl)
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
    for m in re.finditer(r"[∃]\s*\(?([A-Za-z_][\w']*)\s*[:,]", concl):
        var = m.group(1)
        rest = concl[m.end():]
        if not re.search(r"\b" + re.escape(var) + r"\b", rest):
            f.append("T7-vacuous-existential:" + var)
            break
    if re.search(r"\(_ : ", ty):
        f.append("T8-underscore-hypothesis")
    for bname, bty in binders:
        if vs.norm(bty) and vs.norm(bty) == c:
            f.append("T9-hypothesis-equals-conclusion:" + bname)
        if vs.norm(concl) == bname:
            f.append("T10-conclusion-is-hypothesis:" + bname)
    for bname, bty in binders:
        bt = vs.norm(bty)
        if bt == "False" or re.search(r"0<0", bt) or re.search(r"([A-Za-z_][\w']*)<\1", bt) \
           or re.search(r"([A-Za-z_][\w']*)≠\1", bt):
            f.append("T11-suspect-unsat-hypothesis:" + bname + ":" + bty[:60])
    return f, binders, concl, sig


def main():
    ctl = ("Poincare.D12.SemanticLedger.a3CtlTauto (P : Prop) (h : P) : P")
    old_ctl, _, _ = vs.flags("ctl", ctl)
    new_ctl, _, _, _ = flags_fixed(ctl)
    report = {
        "finding": "F18",
        "control_type": ctl,
        "old_screen_flags_on_control": old_ctl,
        "fixed_screen_flags_on_control": new_ctl,
        "blind_spot_reproduced": not old_ctl,
        "fixed_control_flagged": any(x.startswith(("T9-", "T10-")) for x in new_ctl),
        "cards": {},
    }
    total = sig_total = 0
    new_flags = []
    for card in CARDS:
        decls = vs.parse_probe(card)
        entry = {"declarations": len(decls), "signature_binder_decls": 0,
                 "old_flags": [], "fixed_flags": [], "new_flags": []}
        for name, ty in sorted(decls.items()):
            total += 1
            old, _, _ = vs.flags(name, ty)
            fixed, binders, concl, sig = flags_fixed(ty)
            if sig:
                entry["signature_binder_decls"] += 1
                sig_total += 1
            if old:
                entry["old_flags"].append({"name": name, "flags": old})
            if fixed:
                entry["fixed_flags"].append({"name": name, "flags": fixed,
                                             "conclusion": concl[:200]})
            if set(fixed) - set(old):
                entry["new_flags"].append({"name": name, "flags": sorted(set(fixed) - set(old)),
                                           "type": ty[:300]})
                new_flags.append((card, name, sorted(set(fixed) - set(old))))
        report["cards"][card] = entry
    report["total_declarations"] = total
    report["signature_binder_declarations"] = sig_total
    report["total_new_flags"] = len(new_flags)
    report["new_flags"] = [{"card": c, "name": n, "flags": f} for c, n, f in new_flags]
    with open(os.path.join(HERE, "vacuity_screen8_fixed.json"), "w") as fh:
        json.dump(report, fh, indent=1)
    print("control old flags:", old_ctl, "| fixed flags:", new_ctl)
    print(f"declarations: {total} | signature-binder declarations: {sig_total}")
    print("new flags under fixed splitter:", len(new_flags))
    for c, n, f in new_flags:
        print("  NEW", c, n, f)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
