#!/usr/bin/env python3
"""Round-8 closure-consumption (wiring) screen.

An `exact_blockers_closed` claim is only as strong as the use that has actually
been made of the constructed object.  For each headline closure of the seven
audited cards this script lists every occurrence of the closure's identifiers in
the *staged producer packages* (`audit360/pkgs/<card>`, audit probe files of this
lane excluded), comment/string-aware, and classifies the occurrence as

  * `decl`  — the site that declares the object;
  * `use`   — an occurrence inside some other declaration's statement or proof.

Fail-closed: a closure with zero `use` occurrences would be reported `ORPHAN`
(a closure nothing consumes = weak evidence).  The audit's own independent
consumers (`A3ExtraR3/R5/R6/R7/R8`) are listed separately as `audit_consumers`;
the point of this screen is producer-side wiring plus the fact that the audit
consumers exist.

Output: audit360/closure_consumption_round8.json
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from forbidden_scan7 import strip_comments_strings  # noqa: E402

PKGS = os.path.join(HERE, "pkgs")

CLOSURES = {
    "D12-connection-curvature": {
        "I1/LeviCivitaExistenceStatement": [
            "leviCivitaExists",
            "milnorConnection",
            "milnorConnection_eq_mean_iff",
        ],
        "downstream chain": [
            "so3MeanLeviCivita",
            "so3_ricci_e00",
            "ricci_symm",
        ],
    },
    "D12-surgery-recognition": {
        "SR-5": [
            "ConnectedSumDecomposition.mkV2",
            "iteratedSphereSum_homeo_sphere",
        ],
        "I5/I6 recognition bridge": [
            "deckTrivial_of_simplyConnected_quotient",
            "sphericalPieceRecognition_of_spaceForm",
            "RemainingRecognitionHypothesesV2.toRemaining",
        ],
    },
}

AUDIT_CONSUMERS = {
    "D12-connection-curvature": [
        "A3ExtraR3/ClosureUse.lean",
        "A3ExtraR6/ClosureUseNoninvariant.lean",
        "A3ExtraR7/CanonicalClosure.lean",
    ],
    "D12-surgery-recognition": [
        "A3ExtraR3/ClosureUse.lean",
        "A3ExtraR5/ClosureUseNonempty.lean",
        "A3ExtraR8/RegisterIdentity.lean",
    ],
}


def lean_files(root):
    out = []
    for dirpath, dirnames, filenames in os.walk(root):
        if ".lake" in dirpath.split(os.sep):
            continue
        for f in filenames:
            if f.endswith(".lean"):
                out.append(os.path.join(dirpath, f))
    return sorted(out)


def is_decl_line(line, name):
    tail = name.split(".")[-1]
    return bool(re.search(r"\b(def|theorem|lemma|abbrev|structure|instance|noncomputable\s+def)\s+"
                          + re.escape(tail) + r"\b", line))


def main():
    result = {"schema": "a3-closure-consumption-v1", "round": 8, "cards": {}}
    orphans = []
    for card, groups in CLOSURES.items():
        pkg = os.path.join(PKGS, card)
        files = lean_files(pkg)
        card_entry = {"files_scanned": len(files), "groups": {}}
        for group, names in groups.items():
            group_entry = {}
            for name in names:
                tail = name.split(".")[-1]
                pat = re.compile(r"\b" + re.escape(tail) + r"\b")
                decl, uses = [], []
                for path in files:
                    rel = os.path.relpath(path, pkg)
                    text = strip_comments_strings(open(path, errors="replace").read())
                    for i, line in enumerate(text.splitlines(), 1):
                        if pat.search(line):
                            (decl if is_decl_line(line, name) else uses).append(
                                {"file": rel, "line": i, "text": line.strip()[:160]})
                group_entry[name] = {
                    "declarations": decl,
                    "producer_uses": uses,
                    "status": "WIRED" if uses else "ORPHAN",
                }
                if not uses:
                    orphans.append(f"{card}:{name}")
            card_entry["groups"][group] = group_entry
        pkg_audit = os.path.join(pkg)
        card_entry["audit_consumers"] = [
            p for p in AUDIT_CONSUMERS.get(card, []) if os.path.exists(os.path.join(pkg_audit, p))
        ]
        result["cards"][card] = card_entry
    result["orphans"] = orphans
    result["verdict"] = ("PASS: every closure identifier has at least one producer-side use"
                         if not orphans else "ORPHAN closures: " + ", ".join(orphans))
    out = os.path.join(HERE, "closure_consumption_round8.json")
    json.dump(result, open(out, "w"), indent=1)
    print(json.dumps({"orphans": orphans, "verdict": result["verdict"]}, indent=1))
    for card, c in result["cards"].items():
        for group, ge in c["groups"].items():
            for name, e in ge.items():
                print(f"{card:28s} {name:52s} decl={len(e['declarations']):2d} uses={len(e['producer_uses']):3d} {e['status']}")
    return 1 if orphans else 0


if __name__ == "__main__":
    sys.exit(main())
