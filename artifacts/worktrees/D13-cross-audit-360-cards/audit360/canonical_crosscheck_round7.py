#!/usr/bin/env python3
"""Round-7 canonical-blocker cross-check.

The nine D12 cards are audited against the 31-entry blocker register published by
the `D12-semantic-ledger` card (`longrun/results/D12-semantic-ledger.json`,
field `blockers_recounted`).  For every `exact_blockers_closed` claim in a card
this script answers three questions:

  1. which canonical register id (if any) does the claimed blocker correspond to;
  2. is the claimed closure a proof of the *identical* statement (Lean-level
     evidence recorded separately in A3ExtraR7/CanonicalClosure.lean), a
     construction of a *different* local statement, or a scope-restricted proof;
  3. does the register entry remain open after the closure, i.e. is the canonical
     blocker fully closed, partially closed, or untouched.

It also matches each card's `remaining_blockers` prose to register ids so the
report cannot silently drop an unresolved canonical item.  Output:
`audit360/canonical_crosscheck_round7.json`.
"""
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees"
LEDGER = "/data3/guoshaoyang/workdir/lean_poincare/longrun/results/D12-semantic-ledger.json"

CARDS = [
    "D12-connection-curvature",
    "D12-volume-ibp",
    "D12-spectral-sobolev",
    "D12-semantic-ledger",
    "D12-comparison-geodesics",
    "D12-geometric-compactness",
    "D12-surgery-recognition",
]

# Hand-curated mapping: (card, substring of the claimed blocker) -> canonical ids
CLAIM_MAP = {
    ("D12-connection-curvature", "LeviCivitaExistenceStatement"): {
        "canonical_ids": ["I1"],
        "canonical_text": ("I1: 'LeviCivitaExistenceStatement and "
                           "CovariantDerivativeCurvatureStatement are explicit BLOCKED "
                           "Props with no proof.'"),
        "verdict": "CONFIRMED-PARTIAL",
        "detail": (
            "The closure proves the *identical* Prop "
            "Poincare.Longrun.Geometry.LeviCivitaExistenceStatement (imported from the D2 "
            "module), not a local look-alike; kernel-checked by type ascription in "
            "A3ExtraR7/CanonicalClosure.lean and by six independent consumers. The second "
            "conjunct of I1, CovariantDerivativeCurvatureStatement, is untouched and is "
            "still listed by the card itself as an open dependency, so I1 is only "
            "partially closed. Side finding: the D2 docstring's claim that the statement "
            "is 'false without extra hypotheses' is refuted (Milnor connection)."),
    },
    ("D12-surgery-recognition", "SR-5"): {
        "canonical_ids": ["SR-5"],
        "canonical_text": ("SR-5 (register prose, D12-semantic-ledger.md): "
                           "'ConnectedSumDecomposition.sphere_of_spheres: connected sum of "
                           "S^3 summands is S^3, UNPROVED'."),
        "verdict": "CONFIRMED",
        "detail": (
            "SR-5 is the ledger's own id for the field consumed by "
            "stage6Target_of_v2decomposition; the closure constructs "
            "ConnectedSumDecomposition.mkV2 with a proved sphere_of_spheres field. "
            "Independently re-consumed in rounds 3 and 5 (empty and nonempty piece "
            "lists, A3ExtraR3/ClosureUse.lean and A3ExtraR5/ClosureUseNonempty.lean)."),
    },
    ("D12-surgery-recognition", "covering-space recognition"): {
        "canonical_ids": ["I5"],
        "canonical_text": ("I5: 'kappa-noncollapsing K1-K7 and sphere-recognition S1-S5 are "
                           "statement-only' (the recognition half)."),
        "verdict": "CONFIRMED-LOCAL",
        "detail": (
            "The constructed covering-space recognition is a genuine point-set/algebraic "
            "topology theorem (finiteFreeOrbit_isQuotientCoveringMap + explicit "
            "trivializing neighbourhoods + antipodal model), but it closes a specific "
            "local bridge (the spherical-half hypotheses the SR card carries), not the "
            "canonical I5 item, whose register status stays open because the "
            "spaceForm/Ricci-flow inputs remain hypotheses."),
    },
    ("D12-surgery-recognition", "coveringTrivial"): {
        "canonical_ids": ["I5", "I6"],
        "canonical_text": ("I5/I6: sphere-recognition and neck/extinction inputs are "
                           "statement-only."),
        "verdict": "CONFIRMED-LOCAL",
        "detail": (
            "deckTrivial_of_simplyConnected_quotient is proved from mathlib's covering "
            "monodromy (no van Kampen); it removes one local hypothesis of the "
            "recognition bridge, while the canonical I5/I6 entries stay open."),
    },
}

# prose fragments in remaining_blockers that must be traceable to a register id
RESIDUAL_MAP = {
    "CovariantDerivativeCurvatureStatement": ["I1"],
    "Manifold-level CovariantDerivative curvature API": ["I1"],
    "van Kampen": ["SR-4"],
    "SR-4": ["SR-4"],
    "spaceForm": ["I5"],
    "SR-6": ["SR-6"],
    "Moise": ["SR-1"],
    "D9 tensor algebra": ["(local snapshot gap, not in register)"],
    "heat": ["U6"],
    "Bochner": ["I4", "U10"],
    "D9": ["(local)"],
}


def load_register():
    d = json.load(open(LEDGER))
    reg = d["blockers_recounted"]
    return {b["id"]: b for b in reg}, d


def main():
    reg, ledger = load_register()
    out = {
        "schema": "d13-canonical-crosscheck-v1",
        "register_source": LEDGER,
        "register_ids": sorted(reg.keys()),
        "register_open_ids": sorted(k for k, v in reg.items() if v.get("status") == "open"),
        "cards": {},
    }
    for card in CARDS:
        p = os.path.join(WT, card, "longrun", "results", card + ".json")
        if not os.path.exists(p):
            out["cards"][card] = {"source_absent": True}
            continue
        cj = json.load(open(p))
        closed = cj.get("exact_blockers_closed") or []
        residual = cj.get("remaining_blockers") or []
        claims = []
        for c in closed:
            text = json.dumps(c)
            key = None
            for (cc, sub), info in CLAIM_MAP.items():
                if cc == card and sub in text:
                    key = (cc, sub)
                    break
            entry = {"claim": c if isinstance(c, dict) else str(c)[:400]}
            if key:
                entry.update(CLAIM_MAP[key])
            else:
                entry.update({"canonical_ids": [], "verdict": "UNMAPPED",
                              "detail": "no canonical-register mapping recorded"})
            claims.append(entry)
        residual_mapped = []
        for r in residual:
            ids = sorted({i for frag, lst in RESIDUAL_MAP.items() if frag in r for i in lst})
            residual_mapped.append({"text": r[:300],
                                    "canonical_ids": ids,
                                    "register_status": {i: reg.get(i, {}).get("status", "?")
                                                        for i in ids if i in reg}})
        out["cards"][card] = {
            "closure_claims": claims,
            "remaining_blockers_mapped": residual_mapped,
        }
    # register entries touched by this milestone
    touched = {}
    for card, e in out["cards"].items():
        for c in e.get("closure_claims", []):
            for i in c.get("canonical_ids", []):
                touched.setdefault(i, []).append({"card": card, "verdict": c["verdict"]})
    out["register_entries_touched"] = touched

    # I1 second conjunct: mechanical scan that nothing in the A3-verified package
    # proves `CovariantDerivativeCurvatureStatement` (it stays a def + hypotheses).
    pkg = os.path.join(HERE, "pkgs", "D12-connection-curvature")
    occ, proofs = [], []
    for dirpath, dirnames, filenames in os.walk(pkg):
        dirnames[:] = [d for d in dirnames if d not in (".lake", "A3Extra", "A3ExtraR3",
                                                        "A3ExtraR6", "A3ExtraR7", "A3ExtraD2")]
        for fn in filenames:
            if not fn.endswith(".lean"):
                continue
            rel = os.path.relpath(os.path.join(dirpath, fn), pkg)
            if rel.startswith("A3"):
                continue
            lines = open(os.path.join(dirpath, fn), errors="replace").read().splitlines()
            for i, line in enumerate(lines, 1):
                if "CovariantDerivativeCurvatureStatement" not in line:
                    continue
                stripped = line.strip()
                kind = "reference"
                if re.match(r"(noncomputable\s+)?def\s+CovariantDerivativeCurvatureStatement", stripped):
                    kind = "definition"
                elif re.match(r"#(check|print)", stripped):
                    kind = "audit-probe"
                elif stripped.startswith("--") or stripped.startswith("*"):
                    kind = "comment"
                else:
                    # continuation of a theorem/lemma statement?
                    prev = next((l for l in reversed(lines[:i - 1]) if l.strip()), "")
                    if re.match(r".*\b(theorem|lemma)\b.*:\s*$", prev):
                        kind = "theorem-statement"
                        proofs.append(f"{rel}:{i}")
                    elif ":" in stripped or stripped.startswith("CovariantDerivative"):
                        kind = "hypothesis-or-field"
                occ.append({"loc": f"{rel}:{i}", "kind": kind, "text": stripped[:140]})
    out["I1_second_conjunct_scan"] = {
        "meaning": ("I1 = 'LeviCivitaExistenceStatement AND CovariantDerivativeCurvatureStatement "
                    "are explicit BLOCKED Props with no proof.' The first conjunct is proved by the "
                    "D12 closure; this scan checks the second is untouched."),
        "theorem_with_that_type": proofs,
        "occurrences": occ[:20],
        "verdict": "SECOND CONJUNCT UNTOUCHED" if not proofs else "REVIEW",
    }
    with open(os.path.join(HERE, "canonical_crosscheck_round7.json"), "w") as f:
        json.dump(out, f, indent=1)
    for card, e in out["cards"].items():
        if e.get("source_absent"):
            print(f"{card:32s} SOURCE-ABSENT")
            continue
        for c in e["closure_claims"]:
            print(f"{card:32s} {c['verdict']:18s} ids={c['canonical_ids']}")
    print("register ids touched:", {k: v for k, v in touched.items()})
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
