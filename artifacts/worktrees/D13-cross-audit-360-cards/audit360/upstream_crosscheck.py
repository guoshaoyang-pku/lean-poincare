#!/usr/bin/env python3
"""Upstream (pinned Frenzymath snapshot, commit bb91a091) cross-check for the
nine D12 cards.

For each D12 card this records the nearest artefact in the pinned snapshot and
classifies it as one of:

  upstream-lean-proof-candidate : a Lean declaration exists in the snapshot
      (sorry/axiom-free statically); NOT compiled by this audit (snapshot pins
      Lean v4.32.1 / mathlib 520045ab, this host has v4.34.0-rc2), so the
      strongest honest label is "upstream source claim".
  upstream-blueprint-contract : a blueprint node exists but is marked
      \\notready (statement/contract only, pending expert review).
  none : no counterpart found in the snapshot.

The check is mechanical: each cited file must exist and contain the cited
declaration/label string; otherwise the entry fails closed and is reported.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(HERE)
SNAP = os.path.join(WT, "third_party", "frenzymath", "Poincare-Conjecture")

ENTRIES = [
    {
        "card": "D12-connection-curvature",
        "question": "Is LeviCivitaExistenceStatement (claimed BLOCKED, 'false without invariance') really blocked?",
        "artefacts": [
            {"kind": "upstream-lean-proof-candidate",
             "file": "formalized-sources/DoCarmo/DoCarmoLib/Riemannian/Manifold/DoCarmoCh2.lean",
             "decl": "RiemannianMetric.exists_unique_isLeviCivita",
             "note": "unconditional existence+uniqueness of the Levi-Civita connection "
                     "on finite-dim, sigma-compact, Hausdorff Riemannian manifolds"},
            {"kind": "upstream-lean-proof-candidate",
             "file": "formalized-sources/DoCarmo/DoCarmoLib/Riemannian/Manifold/DoCarmoCh2.lean",
             "decl": "AffineConnection.isLeviCivita_of_koszulDual",
             "note": "algebraic verification half"},
        ],
        "verdict": "corroborates the CONFIRMED closure: an independent upstream development "
                   "proves existence unconditionally; the historical 'false without invariance' "
                   "note is not supported by upstream.",
    },
    {
        "card": "D12-comparison-geodesics",
        "question": "Do the comparison statements have an upstream counterpart, and at what level?",
        "artefacts": [
            {"kind": "upstream-lean-proof-candidate",
             "file": "formalized-sources/MorganTian/MorganTianLib/Ch01/BishopGromovBall.lean",
             "decl": "bishop_gromov_ball",
             "note": "relative volume comparison (cross-multiplied)"},
            {"kind": "upstream-lean-proof-candidate",
             "file": "formalized-sources/MorganTian/MorganTianLib/Ch01/BishopGromovBall.lean",
             "decl": "bishop_gromov_ball_ratio",
             "note": "ratio monotonicity + explicit non-vacuity theorem "
                     "bishop_gromov_ball_ratio_model"},
            {"kind": "upstream-lean-proof-candidate",
             "file": "formalized-sources/MorganTian/MorganTianLib/Ch01/BishopGromov.lean",
             "decl": "bishop_gromov_radial",
             "note": "radial Jacobi comparison core"},
            {"kind": "upstream-lean-proof-candidate",
             "file": "formalized-sources/MorganTian/MorganTianLib/Ch01/BishopGromovManifold.lean",
             "decl": "bishop_gromov_manifold_ratio",
             "note": "manifold-level ratio comparison"},
        ],
        "verdict": "upstream has a substantive Bishop-Gromov engine (sorry/axiom-free statically); "
                   "it corroborates the family but is not the local card and is not compiled here.",
    },
    {
        "card": "D12-volume-ibp",
        "question": "Is there an upstream manifold integration-by-parts/Green development?",
        "artefacts": [
            {"kind": "upstream-lean-proof-candidate",
             "file": "formalized-sources/MorganTian/MorganTianLib/Ch02/GreenIdentity.lean",
             "decl": "integral_coordinateGreen_eq_zero",
             "note": "coordinate Green identity on a Riemannian manifold"},
            {"kind": "upstream-lean-proof-candidate",
             "file": "formalized-sources/MorganTian/MorganTianLib/Ch02/GreenIdentity.lean",
             "decl": "integral_mul_coordinateDivergence_comm",
             "note": "divergence integration-by-parts on model space"},
        ],
        "verdict": "same mathematical family exists upstream; no statement-level diff performed.",
    },
    {
        "card": "D12-spectral-sobolev",
        "question": "Does upstream formalize the Poincare-Wirtinger/spectral gap results?",
        "artefacts": [],
        "verdict": "none. A grep over formalized-sources/**/*.lean for "
                   "wirtinger/poincareInequality/spectralGap returns zero files: the pinned "
                   "snapshot has no counterpart.",
    },
    {
        "card": "D12-geometric-compactness",
        "question": "Does upstream formalize Cheeger-Gromov/Hamilton compactness?",
        "artefacts": [
            {"kind": "upstream-blueprint-contract",
             "file": "PoincareConjecture/blueprint/src/chapters/analytic-control-and-noncollapsing.tex",
             "decl": "thm:hamilton-compactness-generalized-flows",
             "note": "blueprint node marked \\notready (contract only, pending expert review)"},
            {"kind": "none",
             "file": "formalized-sources/CheegerGromovTaylor/CheegerGromovTaylor/Basic.lean",
             "decl": "(empty namespace)",
             "note": "the CheegerGromovTaylor project in the snapshot contains only an empty "
                     "namespace module - no compactness theorem"},
        ],
        "verdict": "no compiled upstream compactness theorem; the blueprint node is a "
                   "statement/contract, not a proof.",
    },
    {
        "card": "D12-surgery-recognition",
        "question": "Do the connected-sum/sphere-recognition/covering closures have upstream counterparts?",
        "artefacts": [
            {"kind": "none",
             "file": "PoincareConjecture/blueprint/src/chapters/extinction-and-component-topology.tex",
             "decl": "lem:hempel-essential-sphere-input",
             "note": "the upstream route keeps the topological input as an imported source "
                     "boundary (registered Morgan-Tian Theorem 18.20)"},
        ],
        "verdict": "no Lean counterpart in the snapshot for connected sum / sphere recognition; "
                   "upstream treats the topological input as an imported classical boundary.",
    },
    {
        "card": "D12-triangulation-topology",
        "question": "Does upstream formalize 3-manifold triangulation?",
        "artefacts": [],
        "verdict": "none in Lean. 'triangulation' appears only in other projects' blueprint TeX "
                   "(Petersen Ch07, Thurston Ch04/Ch13, LeeRiemannian ch9) and the local "
                   "extinction chapter; no formalization.",
    },
    {
        "card": "D12-tensor-maximum-bochner",
        "question": "Does upstream formalize the strong tensor maximum principle?",
        "artefacts": [
            {"kind": "upstream-blueprint-contract",
             "file": "PoincareConjecture/blueprint/src/chapters/analytic-control-and-noncollapsing.tex",
             "decl": "thm:strong-curvature-tensor-maximum-principle",
             "note": "full contract text present, marked \\notready; grep over "
                     "formalized-sources/**/*.lean for tensorMaximumPrinciple/maximumPrinciple "
                     "returns zero files"},
        ],
        "verdict": "statement-only upstream (blueprint contract, \\notready). This is relevant "
                   "context for the unauditable card but is not the 360 card and is not a proof.",
    },
    {
        "card": "D12-semantic-ledger",
        "question": "Is there an upstream ledger counterpart?",
        "artefacts": [],
        "verdict": "none - the semantic ledger is a local audit artefact with no upstream analogue.",
    },
]


def check(entry):
    results = []
    for a in entry["artefacts"]:
        p = os.path.join(SNAP, a["file"])
        exists = os.path.exists(p)
        found = False
        sorry = axiom = None
        if exists:
            txt = open(p, encoding="utf-8", errors="replace").read()
            found = a["decl"] in txt if a["decl"] != "(empty namespace)" else "namespace" in txt
            if p.endswith(".lean"):
                sorry = len(re.findall(r"\bsorry\b", txt))
                axiom = len(re.findall(r"^\s*axiom\s", txt, re.M))
        results.append({"file": a["file"], "decl": a["decl"], "kind": a["kind"],
                        "exists": exists, "decl_found": found,
                        "sorry_hits": sorry, "axiom_hits": axiom, "note": a["note"]})
    return results


def main():
    out = {"snapshot": SNAP,
           "snapshot_commit_claimed": "bb91a091f0b968f8bbe8d861e025a88d82b161be",
           "compiled_here": False,
           "reason_not_compiled": "snapshot pins leanprover/lean4:v4.32.1 / mathlib "
                                  "520045ab14e26149ee970e2e617ca04b09bde5d6; this host's "
                                  "pinned toolchain is v4.34.0-rc2 with mathlib 7974e751",
           "cards": {}}
    ok = True
    for e in ENTRIES:
        res = check(e)
        for r in res:
            if not r["exists"] or not r["decl_found"]:
                ok = False
        out["cards"][e["card"]] = {"question": e["question"], "artefacts": res,
                                   "verdict": e["verdict"]}
    out["mechanical_check"] = "PASS" if ok else "FAIL"
    with open(os.path.join(HERE, "upstream_crosscheck.json"), "w") as fh:
        json.dump(out, fh, indent=1)
    print("mechanical check:", out["mechanical_check"])
    for c, v in out["cards"].items():
        for r in v["artefacts"]:
            print(f"  {c:34s} {r['kind']:32s} exists={r['exists']} found={r['decl_found']} "
                  f"sorry={r['sorry_hits']} axiom={r['axiom_hits']}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
