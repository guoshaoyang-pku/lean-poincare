#!/usr/bin/env python3
"""SEMREV-L5: build the per-declaration semantic-class table from the reviewer's evidence."""
import json
import os
import re

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EV = os.path.join(ROOT, "evidence")
LOGS = os.path.join(ROOT, "logs")

# independent semantic class assigned by the reviewer, from the compiled evidence
CLASS = {
    "Poincare.D12.SurgeryRecognition.doubleBallHomeoSphere": "proved-unconditional",
    "Poincare.D12.SurgeryRecognition.sphereConnectSum_homeo_sphere": "proved-unconditional",
    "Poincare.D12.SurgeryRecognition.sphereConnectSum_transported": "proved-unconditional",
    "Poincare.D12.SurgeryRecognition.iteratedSphereSum_homeo_sphere": "proved-unconditional-unconsumed",
    "Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2": "constructed-bridge",
    "Poincare.D12.SurgeryRecognition.finiteFreeOrbit_isQuotientCoveringMap": "proved-unconditional",
    "Poincare.D12.SurgeryRecognition.deckTrivial_of_simplyConnected_quotient": "proved-unconditional",
    "Poincare.D12.SurgeryRecognition.stage6Target_of_v2decomposition": "conditional-implication",
    "Poincare.D12.SurgeryRecognition.stage6Target_of_v2hypotheses": "conditional-implication",
    "Poincare.D12.SurgeryRecognition.stage6Target_of_v3hypotheses": "conditional-implication-terminal",
    "Poincare.D12.SurgeryRecognition.AntipodalGroup": "abbrev-used-46",
    "Poincare.D7.Recognition.stage6Target_of_certificates": "conditional-implication",
    "HatcherLib.vanKampenMap": "upstream-proved",
    "HatcherLib.vanKampenMap_surjective": "upstream-proved",
    "HatcherLib.vanKampen_ker_eq_normalSubgroup_of_factorizationsConnected": "upstream-proved",
    "Poincare.D12.TriangulationTopology.alexanderHomeo": "proved-unconditional",
    "Poincare.D12.TriangulationTopology.alexanderHomeo_eq_refl_iff": "proved-unconditional-unconsumed",
    "Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere": "proved-unconditional",
    "Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere_refl_apply": "proved-unconditional",
    "Poincare.D12.TriangulationTopology.sphereOfTwoDisks": "proved-unconditional",
    "Poincare.D12.TriangulationTopology.sphereOfTwoDisks_hemisphere_instance": "proved-unconditional-nonvacuity",
    "Poincare.D10.TriangulationLowDim.MoiseTriangulationTheorem": "statement-only-prop",
    "Poincare.D10.TriangulationLowDim.FiniteAbstractSimplicialComplex": "structure",
    "Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses": "statement-only-structure",
    "Poincare.D7.SurgeryFlow.missingFullNeckAnalysis": "statement-only-prop",
    "Poincare.D7.SurgeryFlow.missingExtinctionTheorem": "statement-only-prop",
    "Poincare.D7.SurgeryFlow.missingSurgeryFlowTheorem": "statement-only-prop",
    "Poincare.D7.SurgeryFlow.ExtinctionData": "structure",
    "Poincare.Longrun.Surgery.ExtinctionTheorem": "statement-only-structure",
    "Poincare.Longrun.Surgery.MissingInputs": "statement-only-structure",
    "Poincare.D7.SurgeryFlow.realLineProcedureChain_simplyConnected": "vacuous-P-implies-P",
    "Poincare.Longrun.Evolution.FiniteRepresentsContinuousPerelman": "inhabited-at-parameters-model-boundary",
    "Poincare.Longrun.Evolution.FiniteMeshConvergence": "inhabited-at-parameters-model-boundary",
    "Poincare.Longrun.Evolution.PerelmanEvolutionBoundary": "statement-only-structure",
    "Poincare.Longrun.Evolution.PerelmanApproximation": "inhabited-degenerate-witness",
    "Poincare.Longrun.Evolution.ContinuousPerelmanFMonotonicity": "inhabited-at-toy-parameters",
    "Poincare.D7.Limit.HeatMeshConvergence": "model-conditional-conclusion",
    "Poincare.D7.Limit.heatMeshConvergence_of_stability": "model-conditional-theorem",
    "Poincare.D7.Limit.finiteMeshConvergence_of_stability": "model-conditional-theorem",
    "Poincare.D7.Limit.HeatMeshConvergenceTheorem": "statement-only-prop",
    "Poincare.D7.Limit.IsRefiningMesh": "hypothesis-predicate",
    "Poincare.D7.Limit.HasVanishingError": "hypothesis-predicate",
    "Poincare.Longrun.Topology.stage6Target_of_sphereRecognition": "circular-conclusion-equivalent",
    "Poincare.Longrun.Topology.stage6Target_of_compactThreeManifold": "circular-conclusion-equivalent",
    "Poincare.Longrun.Topology.stage6Target_iff_sphereRecognition": "proved-defeq-bridge",
    "Poincare.Stage6.poincareConjectureTopologicalThree": "statement-only-alias",
    "d12NegControlBadAxiom": "registered-negative-control",
    "d12NegControlBadTheorem": "registered-negative-control",
    "Poincare.D12.VolumeIBP.Audit.negativeControl": "registered-negative-control",
    "Poincare.D13.CriticalPathReview.NegControl.negControlBadAxiom": "registered-negative-control",
    "Poincare.D13.CriticalPathReview.NegControl.negControlBadTheorem": "registered-negative-control",
}


def parse_cones_and_kinds():
    cones, kinds = {}, {}
    for line in open(os.path.join(LOGS, "SemRevAxioms.log")):
        if line.startswith("SEMREVCONE"):
            _, name, cone = line.rstrip("\n").split("\t")
            cones[name] = cone
        elif line.startswith("SEMREVKIND"):
            parts = line.rstrip("\n").split("\t")
            kinds[parts[1]] = {"kind": parts[2], "details": parts[3:]}
    return cones, kinds


def parse_uses():
    use = {}
    for p in ("PassA.log", "PassB.log"):
        for line in open(os.path.join(LOGS, p)):
            if line.startswith("SEMREVUSE"):
                _, name, count, _rest = line.rstrip("\n").split("\t", 3)
                use.setdefault(name, {})[p[0]] = int(count)
    return {k: max(v.values()) for k, v in use.items()}


def parse_types():
    types, cur = {}, None
    for line in open(os.path.join(LOGS, "SemRevTypes.log")):
        if line.startswith("-- card-class:"):
            continue
        if line.startswith("@"):
            cur = line.split(" : ", 1)[0][1:]
            types[cur] = line.rstrip("\n")
        elif line.startswith("Poincare.") or line.startswith("HatcherLib.") or line.startswith("d12"):
            name = line.split(" : ", 1)[0]
            if " : " in line:
                cur = name
                types[cur] = line.rstrip("\n")
        elif cur and (line.startswith(" ") or line.startswith("\t")) and cur in types:
            types[cur] += " " + line.strip()
    return types


def main():
    cited = json.load(open(os.path.join(EV, "cited-declarations.json")))["cited"]
    cones, kinds = parse_cones_and_kinds()
    uses = parse_uses()
    types = parse_types()
    ilean = json.load(open(os.path.join(EV, "consumers-replay.json")))["cited"]
    rows = []
    for c in cited:
        n = c["name"]
        rows.append(
            {
                "name": n,
                "card_section": c["card_section"],
                "card_semantic_class": c["card_semantic_class"],
                "review_semantic_class": CLASS.get(n, "UNCLASSIFIED"),
                "kind": kinds.get(n, {}).get("kind"),
                "declares_prop": any("declaresProp=true" in d for d in kinds.get(n, {}).get("details", [])),
                "axiom_cone": cones.get(n),
                "env_consumers": uses.get(n),
                "ilean_raw": (ilean.get(n) or {}).get("raw_consumer_decls"),
                "ilean_user": (ilean.get(n) or {}).get("user_consumer_decls"),
                "ilean_nonaudit_user": (ilean.get(n) or {}).get("nonaudit_user_consumer_decls"),
                "type": types.get(n, "")[:600],
            }
        )
    with open(os.path.join(EV, "semantic-class-table.json"), "w") as f:
        json.dump(rows, f, indent=1)
    with open(os.path.join(EV, "semantic-class-table.md"), "w") as f:
        f.write("| declaration | kind | cone | env consumers | review class | card class |\n")
        f.write("|---|---|---|---:|---|---|\n")
        for r in rows:
            f.write(
                f"| `{r['name']}` | {r['kind']} | `{r['axiom_cone']}` | {r['env_consumers']} | "
                f"{r['review_semantic_class']} | {r['card_semantic_class']} |\n"
            )
    print(f"wrote semantic-class-table.json/md with {len(rows)} rows")
    unclassified = [r["name"] for r in rows if r["review_semantic_class"] == "UNCLASSIFIED"]
    print("unclassified:", unclassified)


if __name__ == "__main__":
    main()
