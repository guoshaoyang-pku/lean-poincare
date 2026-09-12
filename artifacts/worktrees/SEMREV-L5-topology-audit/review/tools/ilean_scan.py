#!/usr/bin/env python3
"""SEMREV-L5 independent scan of the compiled union release via .ilean files.

Independent of the L5 tools (own parser / own definitions):
  * declaration inventory per module,
  * duplicate (colliding) declaration names across modules,
  * import closure per module,
  * per-declaration consumer sets (referencing modules + referencing declarations),
  * two collision-free import passes covering every module.
"""
import json
import os
import sys
from collections import defaultdict

REL = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L5-topology-audit/release"
LIB = os.path.join(REL, ".lake/build/lib/lean")
OUT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "evidence")

GENERATED_SUFFIXES = (
    "._proof_", "._sunfold", "._unsafe_rec", ".eq_", ".match_", ".recOn", ".casesOn",
    ".noConfusion", "._flat_ctor", ".mk", ".rec", ".below", ".brecOn", ".ibelow",
)


def is_generated(name: str) -> bool:
    return any(s in name for s in GENERATED_SUFFIXES)


def load():
    mods = {}
    for root, _dirs, files in os.walk(LIB):
        for f in files:
            if not f.endswith(".ilean"):
                continue
            p = os.path.join(root, f)
            with open(p) as fh:
                d = json.load(fh)
            mods[d["module"]] = d
    return mods


def main():
    mods = load()
    print(f"modules with ilean: {len(mods)}")

    decl2mods = defaultdict(list)
    for m, d in mods.items():
        for name in d.get("decls", {}):
            decl2mods[name].append(m)

    dup = {n: sorted(ms) for n, ms in decl2mods.items() if len(ms) > 1}
    pair_counts = defaultdict(int)
    for n, ms in dup.items():
        pair_counts[tuple(ms)] += 1

    # import closure
    closure = {}

    def close(m, seen=None):
        if m in closure:
            return closure[m]
        if seen is None:
            seen = set()
        if m in seen:
            return set()
        seen.add(m)
        out = {m}
        for imp in mods.get(m, {}).get("directImports", []):
            im = imp[0]
            out |= close(im, seen)
        closure[m] = out
        return out

    for m in mods:
        close(m)

    # collision sides
    pair_list = sorted(pair_counts.items(), key=lambda kv: -kv[1])
    print("colliding module sets:")
    for pair, cnt in pair_list:
        print(f"  {cnt:3d} names: {pair}")

    # choose sides: first module of each colliding set = original side
    original_side, duplicate_side = set(), set()
    for pair, _cnt in pair_list:
        original_side.add(pair[0])
        for x in pair[1:]:
            duplicate_side.add(x)

    conflicts = original_side | duplicate_side

    def side_of(m):
        cl = closure[m]
        has_o = bool(cl & original_side)
        has_d = bool(cl & duplicate_side)
        if has_o and has_d:
            return "BOTH"
        if has_d:
            return "B"
        if has_o:
            return "A"
        return "neutral"

    sides = {m: side_of(m) for m in mods}
    counts = defaultdict(int)
    for m, s in sides.items():
        counts[s] += 1
    print("pass assignment:", dict(counts))
    both = [m for m, s in sides.items() if s == "BOTH"]
    if both:
        print("MODULES IMPORTING BOTH SIDES (cannot be covered):", both)

    passA = sorted(m for m, s in sides.items() if s in ("A", "neutral"))
    passB = sorted(m for m, s in sides.items() if s in ("B", "neutral"))
    covered = set(passA) | set(passB)
    print(f"passA={len(passA)} passB={len(passB)} union={len(covered)} of {len(mods)}")

    # consumer index: target -> set of (module, declaring decl)
    consumers = defaultdict(set)
    for m, d in mods.items():
        refs = d.get("references", {})
        for key, r in refs.items():
            try:
                dec = json.loads(key)
                tname = dec["c"]["n"]
            except Exception:
                tname = key
            for u in r.get("usages", []):
                owner = u[4] if len(u) > 4 else None
                if owner == tname:
                    continue
                consumers[tname].add((m, owner))

    cited = [
        "Poincare.D12.SurgeryRecognition.doubleBallHomeoSphere",
        "Poincare.D12.SurgeryRecognition.sphereConnectSum_homeo_sphere",
        "Poincare.D12.SurgeryRecognition.sphereConnectSum_transported",
        "Poincare.D12.SurgeryRecognition.iteratedSphereSum_homeo_sphere",
        "Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2",
        "Poincare.D12.SurgeryRecognition.finiteFreeOrbit_isQuotientCoveringMap",
        "Poincare.D12.SurgeryRecognition.deckTrivial_of_simplyConnected_quotient",
        "Poincare.D12.SurgeryRecognition.stage6Target_of_v2decomposition",
        "Poincare.D12.SurgeryRecognition.stage6Target_of_v2hypotheses",
        "Poincare.D12.SurgeryRecognition.stage6Target_of_v3hypotheses",
        "Poincare.D12.SurgeryRecognition.AntipodalGroup",
        "Poincare.D7.Recognition.stage6Target_of_certificates",
        "Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere",
        "Poincare.D12.TriangulationTopology.alexanderHomeo",
        "Poincare.D12.TriangulationTopology.alexanderHomeo_eq_refl_iff",
        "Poincare.D12.TriangulationTopology.sphereOfTwoDisks",
        "Poincare.D12.TriangulationTopology.sphereOfTwoDisks_hemisphere_instance",
        "Poincare.D7.SurgeryFlow.realLineProcedureChain_simplyConnected",
        "Poincare.Longrun.Topology.stage6Target_of_sphereRecognition",
        "Poincare.Longrun.Topology.stage6Target_of_compactThreeManifold",
        "Poincare.D7.Limit.HeatMeshConvergence",
    ]
    consumer_rows = {}
    for t in cited:
        allc = sorted(consumers.get(t, set()))
        user = [(m, o) for (m, o) in allc if not is_generated(o or "")]
        nonaudit = [
            (m, o)
            for (m, o) in user
            if not any(k in m for k in ("Audit", "Probe", "Release", "Report"))
        ]
        consumer_rows[t] = {
            "raw_consumer_decls": len(allc),
            "raw_consumer_modules": len({m for m, _ in allc}),
            "user_consumer_decls": len(user),
            "user_consumer_modules": len({m for m, _ in user}),
            "nonaudit_user_consumer_decls": len(nonaudit),
            "nonaudit_user_consumers": [f"{m}::{o}" for m, o in nonaudit][:40],
            "user_consumers": [f"{m}::{o}" for m, o in user][:40],
            "raw_sample": [f"{m}::{o}" for m, o in allc][:40],
        }
        print(
            f"{t}: raw={len(allc)} user={len(user)} "
            f"nonaudit_user={len(nonaudit)} modules={len({m for m, _ in allc})}"
        )

    # declaration counts per module prefix for the cited lanes
    prefix_counts = defaultdict(int)
    for n, ms in decl2mods.items():
        for m in ms:
            for p in (
                "Poincare.D12.SurgeryRecognition",
                "Poincare.D12.TriangulationTopology",
                "Poincare.D10.TriangulationLowDim",
                "Poincare.Longrun.Topology",
                "Poincare.D7.SurgeryFlow",
                "Poincare.D7.Limit",
                "Poincare.D7.Recognition",
                "Poincare.Longrun.Surgery",
                "Poincare.Longrun.Evolution",
                "Poincare.VKPort",
            ):
                if m == p or m.startswith(p + "."):
                    prefix_counts[p] += 1
                    break

    with open(os.path.join(OUT, "collisions-replay.json"), "w") as f:
        json.dump(
            {
                "modules": len(mods),
                "duplicate_declaration_names": len(dup),
                "colliding_module_sets": [
                    {"modules": list(pair), "names": cnt} for pair, cnt in pair_list
                ],
                "duplicate_names_full": dup,
                "pass_A_modules": len(passA),
                "pass_B_modules": len(passB),
                "union_covers_all": len(covered) == len(mods),
                "modules_importing_both_sides": both,
            },
            f,
            indent=1,
        )
    with open(os.path.join(OUT, "consumers-replay.json"), "w") as f:
        json.dump(
            {
                "method": "ilean references; raw counts include compiler-generated auxiliaries",
                "cited": consumer_rows,
                "declaration_counts_by_prefix": dict(prefix_counts),
            },
            f,
            indent=1,
        )
    with open(os.path.join(OUT, "passes.json"), "w") as f:
        json.dump({"passA": passA, "passB": passB}, f, indent=1)
    print("wrote collisions-replay.json, consumers-replay.json, passes.json")


if __name__ == "__main__":
    main()
