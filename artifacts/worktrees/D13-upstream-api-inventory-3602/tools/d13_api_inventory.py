#!/usr/bin/env python3
"""D13 API inventory over the scanned upstream modules.

Reads manifest/upstream-modules.json and produces

  manifest/upstream-api-inventory.json   - topic-tagged declaration inventory
  manifest/upstream-api-highlights.json  - curated per-topic entry points

Classification vocabulary used for every declaration:

  model        structure / class / inductive / def / abbrev / instance / opaque
               (a definitional object, not a mathematical claim);
  claim        theorem / lemma / example (a mathematical assertion);
  assumption   axiom (admitted assumption, no proof);
  admitted     claim whose own body contains `sorry`/`admit` (statement-only
               upstream); this flag is orthogonal to model/claim/assumption.

Whether a declaration is *compiled in our environment* is decided separately
by the adapter-probe build (manifest/d13-probe-results.json), never here.
"""

from __future__ import annotations

import datetime as _dt
import json
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
MANI = REPO / "manifest"

MODEL_KINDS = {"structure", "class", "inductive", "def", "abbrev", "instance", "opaque"}
CLAIM_KINDS = {"theorem", "lemma", "example"}
ASSUMPTION_KINDS = {"axiom"}

# Curated entry points: (package, topic, module regex, label)
HIGHLIGHTS = [
    ("shared", "geometry", r"Shared/MetricGeometry/LengthSpace", "length-space infrastructure"),
    ("shared", "geometry", r"Shared/Algebraic/BilinearForm/Basic", "bilinear forms on real vector spaces"),
    ("shared", "geometry", r"Shared/Algebraic/BilinearForm/Riesz", "Riesz representation for bilinear forms"),
    ("shared", "geometry", r"Shared/Algebraic/Auxiliary/OrthonormalBasisDiagonal", "orthonormal-basis diagonalisation"),
    ("shared", "topology", r"Shared/Topology/FiberBundleT2", "T2 total space of a fibre bundle"),
    ("DoCarmo", "geometry", r"Riemannian/Manifold/DoCarmoCh0", "do Carmo Ch0: differentiable manifolds"),
    ("DoCarmo", "geometry", r"Riemannian/Manifold/DoCarmoCh1", "do Carmo Ch1: Riemannian metrics"),
    ("DoCarmo", "geometry", r"Riemannian/Manifold/DoCarmoCh2", "do Carmo Ch2: affine connections"),
    ("DoCarmo", "geometry", r"Riemannian/Connection/CurvaturePointwise", "curvature tensor (pointwise)"),
    ("DoCarmo", "geometry", r"Riemannian/Connection/ChristoffelBridge", "Christoffel symbols bridge"),
    ("DoCarmo", "geometry", r"Riemannian/Connection/CovariantDerivativeAlongLeviCivita", "covariant derivative along a curve (Levi-Civita)"),
    ("DoCarmo", "geometry", r"Riemannian/Connection/ParallelAlong", "parallel transport along a curve"),
    ("DoCarmo", "geometry", r"Riemannian/Connection/MetricCompatibilityAlong", "metric compatibility"),
    ("DoCarmo", "geometry", r"Riemannian/Geodesic/Equation", "geodesic equation"),
    ("DoCarmo", "geometry", r"Riemannian/Geodesic/Completeness", "geodesic completeness / Hopf-Rinow ingredients"),
    ("DoCarmo", "geometry", r"Riemannian/Exponential/GaussLemma", "Gauss lemma"),
    ("DoCarmo", "geometry", r"Riemannian/Exponential/Minimizing", "minimising geodesics"),
    ("DoCarmo", "geometry", r"Riemannian/Exponential/NormalBallEDist", "normal ball / exponential distance"),
    ("DoCarmo", "geometry", r"Riemannian/Jacobi/JacobiField", "Jacobi fields"),
    ("DoCarmo", "geometry", r"Riemannian/Jacobi/JacobiEquationODE", "Jacobi equation (ODE form)"),
    ("DoCarmo", "geometry", r"Riemannian/Variation/BonnetMyers", "Bonnet-Myers theorem"),
    ("DoCarmo", "geometry", r"Riemannian/TensorBundle/MusicalIso", "musical isomorphisms"),
    ("MorganTian", "geometry", r"Ch01/BishopGromov$", "Bishop-Gromov volume comparison"),
    ("MorganTian", "geometry", r"Ch01/BishopGromovManifold$", "Bishop-Gromov on manifolds"),
    ("MorganTian", "geometry", r"Ch01/ComparisonGeometric", "geometric comparison theorems"),
    ("MorganTian", "geometry", r"Ch01/Chapter1VolumeRemaining", "volume comparison frontier"),
    ("MorganTian", "geometry", r"Ch01/Chapter1CutLocusRemaining", "cut-locus frontier"),
    ("MorganTian", "geometry", r"Ch02/", "Ch2: Ricci flow basics"),
    ("MorganTian", "geometry", r"Ch03/", "Ch3: curvature evolution / maximum principle"),
    ("MorganTian", "geometry", r"Ch04/", "Ch4: noncollapsing"),
    ("MorganTian", "geometry", r"Ch05/", "Ch5: canonical neighbourhoods / surgery"),
    ("Topping", "pde_heat", r"ParabolicPDE/Scalar$", "scalar parabolic PDE"),
    ("Topping", "pde_heat", r"ParabolicPDE/Vector$", "vector-valued parabolic PDE"),
    ("Topping", "pde_heat", r"ParabolicPDE/Contraction", "parabolic contraction estimates"),
    ("Topping", "pde_heat", r"ParabolicPDE/HolderSpace", "Hölder spaces"),
    ("Topping", "pde_heat", r"ParabolicPDE/VariableSectionNemytskii", "Nemytskii operators for variable coefficients"),
    ("Topping", "pde_heat", r"MaximumPrinciple/Riemannian", "maximum principle (Riemannian)"),
    ("Topping", "pde_heat", r"MaximumPrinciple/ScalarConsequences", "scalar maximum-principle consequences"),
    ("Topping", "pde_heat", r"MaximumPrinciple/HigherDerivativeEstimate", "higher-derivative estimates"),
    ("Topping", "geometry", r"Riemannian/CurvatureMultilinear", "curvature multilinear algebra"),
    ("Topping", "geometry", r"Riemannian/CurvatureRicciTrace", "Ricci trace"),
    ("Topping", "geometry", r"Riemannian/Einstein", "Einstein metrics"),
    ("Topping", "geometry", r"RicciFlow/CurvatureVariationFromFlow", "curvature evolution under Ricci flow"),
    ("Topping", "geometry", r"RicciFlow/ScalarEvolutionFromFlow", "scalar curvature evolution"),
    ("Topping", "geometry", r"RicciFlow/Existence/DeTurckPicard", "DeTurck trick / Picard iteration"),
    ("Topping", "geometry", r"RicciFlow/Existence/GaugeFlow", "gauge (DeTurck) flow"),
    ("Evans", "pde_heat", r"Ch02/Heat$", "heat equation: fundamental solution"),
    ("Evans", "pde_heat", r"Ch02/HeatIVP", "heat equation: initial value problem"),
    ("Evans", "pde_heat", r"Ch02/HeatIVPSmooth", "heat IVP smoothness"),
    ("Evans", "pde_heat", r"Ch02/HeatMaxPrinciple", "heat maximum principle"),
    ("Evans", "pde_heat", r"Ch02/HeatCauchyMaxPrinciple", "Cauchy maximum principle"),
    ("Evans", "pde_heat", r"Ch02/HeatMeanValue", "mean-value formula for the heat equation"),
    ("Evans", "pde_heat", r"Ch02/MeanValue", "harmonic mean-value property"),
    ("Evans", "pde_heat", r"Ch02/Regularity", "elliptic regularity"),
    ("Evans", "pde_heat", r"Ch02/Laplace$", "Laplace equation"),
    ("Evans", "pde_heat", r"Ch01/PDE", "PDE vocabulary"),
    ("Hatcher", "topology", r"Ch1/CoveringSpaces", "covering spaces"),
    ("Hatcher", "topology", r"Ch1/CoveringClassification", "covering classification"),
    ("Hatcher", "topology", r"Ch1/UniversalCoverConstruction", "universal cover construction"),
    ("Hatcher", "topology", r"Ch1/VanKampen$", "van Kampen theorem"),
    ("Hatcher", "topology", r"Ch1/Sphere", "spheres and simply-connectedness"),
    ("Hatcher", "topology", r"Ch1/Circle", "the circle"),
    ("Hatcher", "topology", r"Ch1/AlgebraicConstructions", "algebraic constructions on groups"),
    ("Hatcher", "topology", r"Ch0/CellComplexes", "CW complexes"),
    ("Hatcher", "topology", r"Ch0/HomotopyTheory", "homotopy theory"),
    ("Hatcher", "topology", r"Ch0/AttachingSpace", "attaching spaces"),
    ("KleinerLott", "geometry", r"RicciFlow/Noncollapsing", "noncollapsing"),
    ("KleinerLott", "geometry", r"RicciFlow/HopfRinow", "Hopf-Rinow"),
    ("KleinerLott", "geometry", r"RicciFlow/PointSelection", "point selection"),
    ("KleinerLott", "geometry", r"RicciFlow/CompleteGeometry", "complete geometry"),
    ("KleinerLott", "geometry", r"RicciFlow/SmoothRicciFlow", "smooth Ricci flow"),
    ("ChowKnopf", "geometry", r"AppendixA/", "Chow-Knopf Appendix A"),
    ("ChowKnopf", "geometry", r"AppendixB/", "Chow-Knopf Appendix B"),
    ("GilbargTrudinger", "pde_heat", r"Ch05/", "Gilbarg-Trudinger Ch5 (elliptic PDE)"),
    ("HanLinLectureNotes", "pde_heat", r"Ch0[12]/", "Han-Lin elliptic PDE chapters"),
    ("LeeRiemannian", "geometry", r"Ch0[1246]/", "Lee, Riemannian manifolds"),
    ("LeeRiemannian", "geometry", r"Ch1[012]/", "Lee, curvature and comparison"),
    ("Petersen", "geometry", r"Riemannian/", "Petersen, Riemannian geometry core"),
    ("Petersen", "geometry", r"Foundations/", "Petersen, foundations"),
    ("Petersen", "geometry", r"Ch0[1-6]/", "Petersen, chapters 1-6"),
    ("LeeSmooth", "geometry", r"Ch0[1-4]/", "Lee, smooth manifolds (may contain admitted statements)"),
]


def main() -> int:
    modules = json.loads((MANI / "upstream-modules.json").read_text())["modules"]
    stamp = _dt.datetime.now().astimezone().isoformat(timespec="seconds")

    def pkg_of(f: str) -> str:
        return f.split("/")[1] if f.startswith("formalized-sources/") else f.split("/")[0]

    inv = {}
    for f, m in modules.items():
        if not m.get("topics"):
            continue
        pkg = pkg_of(f)
        p = inv.setdefault(
            pkg,
            {"modules": 0, "decls": 0, "kinds": {}, "admitted_claims": 0,
             "assumptions": 0, "no_name_decls": 0, "by_topic": {}},
        )
        p["modules"] += 1
        p["decls"] += m["decl_count"]
        for d in m["decls"]:
            k = d["kind"]
            p["kinds"][k] = p["kinds"].get(k, 0) + 1
            if not d["name"]:
                p["no_name_decls"] += 1
            if k in ASSUMPTION_KINDS:
                p["assumptions"] += 1
            if k in CLAIM_KINDS and d["admitted"]:
                p["admitted_claims"] += 1
        for t in m["topics"]:
            p["by_topic"][t] = p["by_topic"].get(t, 0) + 1

    (MANI / "upstream-api-inventory.json").write_text(
        json.dumps(
            {
                "schema": "d13-upstream-api-inventory-v1",
                "generated_at": stamp,
                "source": "third_party/frenzymath/Poincare-Conjecture",
                "classification_vocabulary": {
                    "model": sorted(MODEL_KINDS),
                    "claim": sorted(CLAIM_KINDS),
                    "assumption": sorted(ASSUMPTION_KINDS),
                    "admitted": "claim body contains an admitted step (upstream statement-only)",
                },
                "packages": inv,
            },
            indent=1,
        )
        + "\n"
    )

    # curated highlights
    highlights = []
    for pkg, topic, rx, label in HIGHLIGHTS:
        pat = re.compile(rx)
        sel = [
            (f, m)
            for f, m in modules.items()
            if pkg_of(f) == pkg and pat.search(f)
        ]
        if not sel:
            continue
        decls = []
        for f, m in sorted(sel):
            for d in m["decls"]:
                if not d["name"]:
                    continue
                decls.append(
                    {
                        "name": d["name"],
                        "kind": d["kind"],
                        "module": d["module"],
                        "line": d["line"],
                        "statement": d["statement_head"],
                        "admitted": d["admitted"],
                        "classification": (
                            "assumption"
                            if d["kind"] in ASSUMPTION_KINDS
                            else ("model" if d["kind"] in MODEL_KINDS else "claim")
                        ),
                    }
                )
        highlights.append(
            {
                "package": pkg,
                "topic": topic,
                "label": label,
                "module_regex": rx,
                "modules": [f for f, _ in sorted(sel)],
                "module_count": len(sel),
                "decl_count": len(decls),
                "admitted_decl_count": sum(1 for d in decls if d["admitted"]),
                "declarations": decls,
            }
        )

    (MANI / "upstream-api-highlights.json").write_text(
        json.dumps(
            {
                "schema": "d13-upstream-api-highlights-v1",
                "generated_at": stamp,
                "groups": highlights,
            },
            indent=1,
        )
        + "\n"
    )
    print(f"packages={len(inv)} highlight_groups={len(highlights)}")
    for h in highlights:
        print(f"  {h['package']:18} {h['topic']:9} {h['module_count']:4} mod "
              f"{h['decl_count']:5} decl {h['admitted_decl_count']:4} admitted  {h['label']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
