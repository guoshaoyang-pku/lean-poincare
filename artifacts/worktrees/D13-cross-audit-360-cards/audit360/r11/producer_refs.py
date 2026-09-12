#!/usr/bin/env python3
"""Fast source-level producer-wiring scan (round-11 fallback / cross-check).

Counts occurrences of each closure identifier in the *producer* sources only:
this lane's own `A3Extra*`/`A3*.lean` files and comments/strings are excluded.
Unlike the Lean reverse-BFS instrument this is a textual screen (it sees
statements and proofs alike, and is blind to notation aliases), so it is
reported as corroboration, never as the primary evidence.

Output: audit360/r11/producer_refs.json
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(os.path.dirname(HERE))
PKGS = os.path.join(WT, "audit360", "pkgs")
sys.path.insert(0, os.path.join(WT, "audit360"))
from forbidden_scan7 import strip_comments_strings  # noqa: E402

CLOSURES = {
    "D12-connection-curvature": ["leviCivitaExists", "milnorConnection_eq_mean_iff",
                                 "so3MeanLeviCivita", "so3_ricci_symm", "so3_ricci_e00"],
    "D12-surgery-recognition": ["ConnectedSumDecomposition.mkV2",
                                "deckTrivial_of_simplyConnected_quotient",
                                "sphericalPieceRecognition_of_spaceForm",
                                "finiteFreeOrbit_isQuotientCoveringMap"],
    "D12-tensor-maximum-bochner": ["KernelTangent", "hamiltonField",
                                   "kernelTangent_of_feasibleDirection",
                                   "kernelTangent_not_feasible",
                                   "hamiltonField_kernelTangent",
                                   "hamiltonField_not_strengthened",
                                   "adjugate_posSemidef", "staysPosSemidef_of_tangent",
                                   "staysPosSemidef_of_field"],
    "D12-triangulation-topology": ["coveringOfSimplyConnectedIsHomeo",
                                   "sphericalSpaceFormRecognition",
                                   "antipodalQuotientCovering",
                                   "simplexBoundaryHomeoSphere", "lowerHemisphereHomeoDisk",
                                   "simplexHomeoDisk", "simplexHomeoStdSimplexFn",
                                   "simplexHomeoConeQuot", "simplexHomeoBoundaryCone",
                                   "diskGlueQuotHomeoSphere",
                                   "diskGlueQuotHomeoSphere_refl_apply",
                                   "alexanderHomeo", "alexanderHomeo_sphereToDisk",
                                   "alexanderHomeo_refl", "alexanderHomeo_zero",
                                   "alexanderHomeo_eq_refl_iff", "sphereOfTwoDisks",
                                   "sphereOfTwoDisks_hemisphere_instance",
                                   "suspQuotHomeoSphere", "coneQuotHomeoDisk",
                                   "doubleDiskQuotHomeoSphere", "sphereThreeGluedDisks",
                                   "sphereThreeSuspension", "coneOverSphere2HomeoDisk3"],
}
def is_decl(line, tail):
    return bool(re.search(r"\b(def|theorem|lemma|abbrev|structure|instance|opaque|"
                          r"noncomputable\s+def|protected\s+def|private\s+def)\s+"
                          + re.escape(tail) + r"\b", line))


def scan(card, names):
    root = os.path.join(PKGS, card)
    files = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d != ".lake" and not d.startswith("A3Extra")
                       and d != "A3Extra"]
        for f in filenames:
            if f.endswith(".lean") and not f.startswith("A3"):
                files.append(os.path.join(dirpath, f))
    out = {}
    for name in names:
        tail = name.split(".")[-1]
        pat = re.compile(r"\b" + re.escape(tail) + r"\b")
        decl, uses = [], []
        for path in sorted(files):
            rel = os.path.relpath(path, root)
            text = strip_comments_strings(open(path, errors="replace").read())
            for i, line in enumerate(text.splitlines(), 1):
                if pat.search(line):
                    isdecl = is_decl(line, tail)
                    (decl if isdecl else uses).append(
                        {"file": rel, "line": i, "text": line.strip()[:140]})
        out[name] = {"declarations": decl, "uses": uses,
                     "producer_uses": len(uses),
                     "status": "WIRED" if uses else "NO-PRODUCER-USE"}
    return {"files_scanned": len(files), "closures": out}


def main():
    res = {"schema": "a3-r11-producer-refs-v1",
           "method": "comment/string-aware textual scan of producer sources only "
                     "(A3*.lean audit files excluded); corroboration for the Lean "
                     "reverse-BFS instrument",
           "cards": {}}
    for card, names in CLOSURES.items():
        res["cards"][card] = scan(card, names)
    json.dump(res, open(os.path.join(HERE, "producer_refs.json"), "w", encoding="utf-8"),
              indent=1, sort_keys=True)
    for card, e in res["cards"].items():
        print(f"== {card} ({e['files_scanned']} files)")
        for n, v in e["closures"].items():
            print(f"   {n:48s} decls={len(v['declarations']):2d} uses={v['producer_uses']:3d} {v['status']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
