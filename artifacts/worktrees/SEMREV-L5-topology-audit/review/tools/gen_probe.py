#!/usr/bin/env python3
"""SEMREV-L5 generator: build replay probes for the L5-topology-audit review.

Emits:
  review/probes/SemRevTypes.lean    -- #check of every cited declaration (exact type replay)
  review/probes/SemRevShapes.lean   -- #print of the semantic-class-critical declarations
  review/probes/SemRevAxioms.lean   -- independent, fail-closed axiom/trust audit
  review/evidence/cited-declarations.json -- the exact list reviewed, with card semantic class
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# (full name, semantic class claimed in the L5 card, card section, module to import)
CITED = [
    # --- §5 recognition -------------------------------------------------------
    ("Poincare.D12.SurgeryRecognition.doubleBallHomeoSphere", "proved_unconditional", "5", "Poincare.D12.SurgeryRecognition.All"),
    ("Poincare.D12.SurgeryRecognition.sphereConnectSum_homeo_sphere", "proved_unconditional", "5", "Poincare.D12.SurgeryRecognition.All"),
    ("Poincare.D12.SurgeryRecognition.sphereConnectSum_transported", "proved_unconditional", "5", "Poincare.D12.SurgeryRecognition.All"),
    ("Poincare.D12.SurgeryRecognition.iteratedSphereSum_homeo_sphere", "proved_but_unconsumed", "5", "Poincare.D12.SurgeryRecognition.All"),
    ("Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2", "constructed_bridge", "5", "Poincare.D12.SurgeryRecognition.All"),
    ("Poincare.D12.SurgeryRecognition.finiteFreeOrbit_isQuotientCoveringMap", "proved_unconditional", "5", "Poincare.D12.SurgeryRecognition.All"),
    ("Poincare.D12.SurgeryRecognition.deckTrivial_of_simplyConnected_quotient", "proved_unconditional", "5", "Poincare.D12.SurgeryRecognition.All"),
    ("Poincare.D12.SurgeryRecognition.stage6Target_of_v2decomposition", "conditional_implication", "5", "Poincare.D12.SurgeryRecognition.All"),
    ("Poincare.D12.SurgeryRecognition.stage6Target_of_v2hypotheses", "conditional_implication", "5", "Poincare.D12.SurgeryRecognition.All"),
    ("Poincare.D12.SurgeryRecognition.stage6Target_of_v3hypotheses", "conditional_implication_terminal", "5", "Poincare.D12.SurgeryRecognition.All"),
    ("Poincare.D12.SurgeryRecognition.AntipodalGroup", "abbrev_empty_cone", "5", "Poincare.D12.SurgeryRecognition.All"),
    ("Poincare.D7.Recognition.stage6Target_of_certificates", "conditional_implication", "5", "Poincare.D7.Recognition.All"),
    ("HatcherLib.vanKampenMap", "upstream_proved", "5", "Poincare.VKPort.HatcherLib.Ch1.VanKampen"),
    ("HatcherLib.vanKampenMap_surjective", "upstream_proved", "5", "Poincare.VKPort.HatcherLib.Ch1.VanKampen"),
    ("HatcherLib.vanKampen_ker_eq_normalSubgroup_of_factorizationsConnected", "upstream_proved", "5", "Poincare.VKPort.HatcherLib.Ch1.VanKampen"),
    # --- §6 triangulation -----------------------------------------------------
    ("Poincare.D12.TriangulationTopology.alexanderHomeo", "proved_unconditional", "6", "Poincare.D12.TriangulationTopology.DiskGluing"),
    ("Poincare.D12.TriangulationTopology.alexanderHomeo_eq_refl_iff", "proved_unconditional", "6", "Poincare.D12.TriangulationTopology.DiskGluing"),
    ("Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere", "proved_unconditional", "6", "Poincare.D12.TriangulationTopology.DiskGluing"),
    ("Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere_refl_apply", "proved_unconditional", "6", "Poincare.D12.TriangulationTopology.DiskGluing"),
    ("Poincare.D12.TriangulationTopology.sphereOfTwoDisks", "proved_unconditional", "6", "Poincare.D12.TriangulationTopology.TwoHemisphereInstance"),
    ("Poincare.D12.TriangulationTopology.sphereOfTwoDisks_hemisphere_instance", "proved_unconditional", "6", "Poincare.D12.TriangulationTopology.TwoHemisphereInstance"),
    ("Poincare.D10.TriangulationLowDim.MoiseTriangulationTheorem", "statement_only_prop", "6", "Poincare.D10.TriangulationLowDim.Moise"),
    ("Poincare.D10.TriangulationLowDim.FiniteAbstractSimplicialComplex", "structure", "6", "Poincare.D10.TriangulationLowDim.Complex"),
    # --- §7 surgery / I6 ------------------------------------------------------
    ("Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses", "statement_only_structure", "7", "Poincare.D7.SurgeryFlow.Statements"),
    ("Poincare.D7.SurgeryFlow.missingFullNeckAnalysis", "statement_only_prop", "7", "Poincare.D7.SurgeryFlow.Statements"),
    ("Poincare.D7.SurgeryFlow.missingExtinctionTheorem", "statement_only_prop", "7", "Poincare.D7.SurgeryFlow.Statements"),
    ("Poincare.D7.SurgeryFlow.missingSurgeryFlowTheorem", "statement_only_prop", "7", "Poincare.D7.SurgeryFlow.Statements"),
    ("Poincare.D7.SurgeryFlow.ExtinctionData", "structure", "7", "Poincare.D7.SurgeryFlow.Statements"),
    ("Poincare.Longrun.Surgery.ExtinctionTheorem", "statement_only_structure", "7", "Poincare.Longrun.Surgery.Missing"),
    ("Poincare.Longrun.Surgery.MissingInputs", "statement_only_structure", "7", "Poincare.Longrun.Surgery.Missing"),
    ("Poincare.D7.SurgeryFlow.realLineProcedureChain_simplyConnected", "vacuous_P_implies_P", "7", "Poincare.D7.SurgeryFlow.Basic"),
    # --- §8 evolution / I7 ----------------------------------------------------
    ("Poincare.Longrun.Evolution.FiniteRepresentsContinuousPerelman", "statement_only_prop", "8", "Poincare.Longrun.Evolution.Bridge"),
    ("Poincare.Longrun.Evolution.FiniteMeshConvergence", "statement_only_prop", "8", "Poincare.Longrun.Evolution.Bridge"),
    ("Poincare.Longrun.Evolution.PerelmanEvolutionBoundary", "statement_only_structure", "8", "Poincare.Longrun.Evolution.Bridge"),
    ("Poincare.Longrun.Evolution.PerelmanApproximation", "structure", "8", "Poincare.Longrun.Evolution.Bridge"),
    ("Poincare.Longrun.Evolution.ContinuousPerelmanFMonotonicity", "statement_only_prop", "8", "Poincare.Longrun.Evolution.Bridge"),
    ("Poincare.D7.Limit.HeatMeshConvergence", "model_prop", "8", "Poincare.D7.Limit.Convergence"),
    ("Poincare.D7.Limit.heatMeshConvergence_of_stability", "model_conditional_theorem", "8", "Poincare.D7.Limit.Convergence"),
    ("Poincare.D7.Limit.finiteMeshConvergence_of_stability", "model_conditional_theorem", "8", "Poincare.D7.Limit.Convergence"),
    ("Poincare.D7.Limit.HeatMeshConvergenceTheorem", "statement_only_prop", "8", "Poincare.D7.Limit.Blocked"),
    ("Poincare.D7.Limit.IsRefiningMesh", "hypothesis_predicate", "8", "Poincare.D7.Limit.Convergence"),
    ("Poincare.D7.Limit.HasVanishingError", "hypothesis_predicate", "8", "Poincare.D7.Limit.Convergence"),
    # --- §9 adversarial -------------------------------------------------------
    ("Poincare.Longrun.Topology.stage6Target_of_sphereRecognition", "circular_conclusion_equivalent", "9a", "Poincare.Longrun.Topology.Stage6Bridge"),
    ("Poincare.Longrun.Topology.stage6Target_of_compactThreeManifold", "circular_conclusion_equivalent", "9a", "Poincare.Longrun.Topology.Stage6Bridge"),
    ("Poincare.Longrun.Topology.stage6Target_iff_sphereRecognition", "proved_bridge_defeq", "9a", "Poincare.Longrun.Topology.Stage6Bridge"),
    ("Poincare.Stage6.poincareConjectureTopologicalThree", "statement_only_alias", "9a", "Poincare.Longrun.Topology.Stage6Bridge"),
    # --- §2 registered negative-control cluster -------------------------------
    ("d12NegControlBadAxiom", "registered_negative_control", "2", "Poincare.D12.TriangulationTopology.NegControl.NegControl"),
    ("d12NegControlBadTheorem", "registered_negative_control", "2", "Poincare.D12.TriangulationTopology.NegControl.NegControl"),
    ("Poincare.D12.VolumeIBP.Audit.negativeControl", "registered_negative_control", "2", "Poincare.D12.VolumeIBP.Audit"),
    ("Poincare.D13.CriticalPathReview.NegControl.negControlBadAxiom", "registered_negative_control", "2", "Poincare.D13.CriticalPathReview.NegControl"),
    ("Poincare.D13.CriticalPathReview.NegControl.negControlBadTheorem", "registered_negative_control", "2", "Poincare.D13.CriticalPathReview.NegControl"),
]

# declarations whose *bodies* pin down the semantic class (statement-only, def-alias, ...)
SHAPES = [
    "Poincare.Stage6.poincareConjectureTopologicalThree",
    "Poincare.Longrun.Topology.stage6Target",
    "Poincare.Longrun.Topology.SphereThree",
    "Poincare.Longrun.Topology.EuclideanThree",
    "Poincare.Longrun.Topology.CompactThreeManifold",
    "Poincare.D12.SurgeryRecognition.AntipodalGroup",
    "Poincare.D10.TriangulationLowDim.MoiseTriangulationTheorem",
    "Poincare.D7.SurgeryFlow.missingFullNeckAnalysis",
    "Poincare.D7.SurgeryFlow.missingExtinctionTheorem",
    "Poincare.D7.SurgeryFlow.missingSurgeryFlowTheorem",
    "Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses",
    "Poincare.D7.SurgeryFlow.ExtinctionData",
    "Poincare.Longrun.Surgery.ExtinctionTheorem",
    "Poincare.Longrun.Surgery.MissingInputs",
    "Poincare.Longrun.Surgery.NeckAnalysis",
    "Poincare.Longrun.Evolution.FiniteMeshConvergence",
    "Poincare.Longrun.Evolution.FiniteRepresentsContinuousPerelman",
    "Poincare.Longrun.Evolution.PerelmanEvolutionBoundary",
    "Poincare.Longrun.Evolution.ContinuousPerelmanFMonotonicity",
    "Poincare.D7.Limit.HeatMeshConvergence",
    "Poincare.D7.Limit.HeatMeshConvergenceTheorem",
    "Poincare.D7.Recognition.ExtinctionCertificate",
    "Poincare.D7.Recognition.SphericalPieceRecognition",
    "Poincare.D7.Recognition.CanonicalNeighborhoodInput",
    "Poincare.D7.Recognition.RecognitionHypotheses",
    "Poincare.D12.SurgeryRecognition.ConnectedSumDecompositionV2",
    "Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV2",
    "Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV3",
    "Poincare.D12.SurgeryRecognition.SphericalSpaceFormModel",
]

ALLOWED = ["propext", "Classical.choice", "Quot.sound"]
NEG_CONTROL = [
    "d12NegControlBadAxiom",
    "d12NegControlBadTheorem",
    "Poincare.D12.VolumeIBP.Audit.negativeControl",
    "Poincare.D13.CriticalPathReview.NegControl.negControlBadAxiom",
    "Poincare.D13.CriticalPathReview.NegControl.negControlBadTheorem",
]

def imports(names):
    return sorted({m for _, _, _, m in names})


def emit_types():
    lines = ["/- SEMREV-L5 independent replay: exact types of the declarations cited by the L5 card. -/"]
    for m in imports(CITED):
        lines.append(f"import {m}")
    lines.append("")
    lines.append("set_option autoImplicit false")
    lines.append("set_option pp.universes true")
    lines.append("set_option maxHeartbeats 0")
    for name, cls, sec, _ in CITED:
        lines.append(f"-- card-class: {cls} (card section {sec})")
        lines.append(f"#check @{name}")
    lines.append("")
    return "\n".join(lines)


def emit_shapes():
    lines = ["/- SEMREV-L5 independent replay: printed definitions (semantic-class evidence). -/"]
    for m in imports(CITED):
        lines.append(f"import {m}")
    lines.append("")
    lines.append("set_option autoImplicit false")
    lines.append("set_option maxHeartbeats 0")
    for name in SHAPES:
        lines.append(f"#print {name}")
    lines.append("")
    return "\n".join(lines)


def emit_axioms():
    cited = [c[0] for c in CITED]
    lines = [r'''/- SEMREV-L5 independent FAIL-CLOSED audit of the cited declarations.

This file is authored by the SEMREV reviewer, not copied from the L5 detector.
It fails to compile (non-zero exit) if any cited declaration is missing, unsafe,
or has an axiom cone outside {propext, Classical.choice, Quot.sound}, with the
five registered negative-control declarations reported separately and required to
carry exactly their forbidden axiom.
-/
import Lean.Util.CollectAxioms
import Lean.Elab.Command
''']
    for m in imports(CITED):
        lines.append(f"import {m}")
    lines.append("")
    lines.append("open Lean Elab Command")
    lines.append("")
    lines.append("namespace SemRevAudit")
    lines.append("")
    lines.append("def allowedAxioms : List Name := " + repr(ALLOWED).replace("'", '"').replace("[", "[").replace("]", "]") + ".map String.toName")
    lines.append("")
    lines.append("def cited : List Name := [")
    for n in cited:
        lines.append(f'  `{n},')
    lines.append("]")
    lines.append("")
    lines.append("def registeredNegControls : List Name := [")
    for n in NEG_CONTROL:
        lines.append(f'  `{n},')
    lines.append("]")
    lines.append(r'''
run_cmd do
  let env ← getEnv
  let mut missing : Array Name := #[]
  let mut unsafeD : Array Name := #[]
  let mut partialD : Array Name := #[]
  let mut badAxioms : Array (Name × Name) := #[]
  let mut sorryD : Array Name := #[]
  let mut negSeen : Array Name := #[]
  let mut negClean : Array Name := #[]
  let mut nTheorems := 0
  let mut nDefs := 0
  for n in cited do
    match env.find? n with
    | none => missing := missing.push n
    | some ci =>
      match ci with
      | .thmInfo _ => nTheorems := nTheorems + 1
      | .defnInfo v =>
          nDefs := nDefs + 1
          match v.safety with
          | .«unsafe» => unsafeD := unsafeD.push n
          | .«partial» => partialD := partialD.push n
          | .safe => pure ()
      | _ => pure ()
      let axs ←
        try Lean.collectAxioms n
        catch _ => pure #[`collectAxiomsException]
      IO.println s!"SEMREVCONE\t{n}\t{";".intercalate (axs.toList.map Name.toString)}"
      let kindStr := match ci with
        | .axiomInfo _ => "axiom"
        | .defnInfo v => match v.safety with
          | .«unsafe» => "unsafe_def"
          | .«partial» => "partial_def"
          | .safe => "def"
        | .thmInfo _ => "theorem"
        | .opaqueInfo _ => "opaque"
        | .quotInfo _ => "quot"
        | .inductInfo _ => "induct/structure"
        | .ctorInfo _ => "ctor"
        | .recInfo _ => "rec"
      let isP ← try liftTermElabM (Meta.isProp ci.type) catch _ => pure false
      let declProp ← try liftTermElabM (Meta.forallTelescopeReducing ci.type fun _ b => Meta.isDefEq b (.sort .zero)) catch _ => pure false
      IO.println s!"SEMREVKIND\t{n}\t{kindStr}\tprop={isP}\tdeclaresProp={declProp}"
      let mut hasForbidden := false
      for a in axs do
        if a == `sorryAx then sorryD := sorryD.push n
        if !allowedAxioms.contains a then
          hasForbidden := true
          if registeredNegControls.contains n then
            negSeen := negSeen.push n
          else
            badAxioms := badAxioms.push (n, a)
      if registeredNegControls.contains n && !hasForbidden then
        negClean := negClean.push n
  IO.println s!"SEMREV\tcited\t{cited.length}"
  IO.println s!"SEMREV\ttheorems\t{nTheorems}"
  IO.println s!"SEMREV\tdefs\t{nDefs}"
  IO.println s!"SEMREV\tmissing\t{missing.size}"
  IO.println s!"SEMREV\tunsafe\t{unsafeD.size}"
  IO.println s!"SEMREV\tpartial\t{partialD.size}"
  IO.println s!"SEMREV\tsorryAx\t{sorryD.size}"
  IO.println s!"SEMREV\tunapproved_axiom_cones\t{badAxioms.size}"
  IO.println s!"SEMREV\tregistered_neg_controls_with_forbidden_cone\t{negSeen.toList.eraseDups.length}"
  IO.println s!"SEMREV\tregistered_neg_controls_without_forbidden_cone\t{negClean.size}"
  for n in missing do IO.println s!"SEMREVFAIL\tmissing\t{n}"
  for n in unsafeD do IO.println s!"SEMREVFAIL\tunsafe\t{n}"
  for n in sorryD do IO.println s!"SEMREVFAIL\tsorryAx\t{n}"
  for n in negClean do IO.println s!"SEMREVFAIL\tneg_control_clean\t{n}"
  for (n, a) in badAxioms do IO.println s!"SEMREVFAIL\tunapproved_axiom\t{n}\t{a}"
  if !(missing.isEmpty && unsafeD.isEmpty && sorryD.isEmpty && badAxioms.isEmpty) then
    throwError "SEMREV fail-closed cited-declaration audit FAILED"
  if negSeen.size != registeredNegControls.length then
    throwError "SEMREV negative-control registry incomplete"
  IO.println "SEMREVVERDICT PASS"
''')
    lines.append("")
    lines.append("end SemRevAudit")
    lines.append("")
    return "\n".join(lines)


def main():
    probes = os.path.join(ROOT, "probes")
    os.makedirs(probes, exist_ok=True)
    with open(os.path.join(probes, "SemRevTypes.lean"), "w") as f:
        f.write(emit_types())
    with open(os.path.join(probes, "SemRevShapes.lean"), "w") as f:
        f.write(emit_shapes())
    with open(os.path.join(probes, "SemRevAxioms.lean"), "w") as f:
        f.write(emit_axioms())
    with open(os.path.join(ROOT, "evidence", "cited-declarations.json"), "w") as f:
        json.dump(
            {
                "cited": [
                    {"name": n, "card_semantic_class": c, "card_section": s, "module": m}
                    for n, c, s, m in CITED
                ],
                "allowed_axioms": ALLOWED,
                "registered_negative_controls": NEG_CONTROL,
                "shapes": SHAPES,
            },
            f,
            indent=1,
        )
    print("wrote probes and cited-declarations.json")


if __name__ == "__main__":
    main()
