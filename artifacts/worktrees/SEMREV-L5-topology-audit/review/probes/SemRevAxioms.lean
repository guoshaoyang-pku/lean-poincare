/- SEMREV-L5 independent FAIL-CLOSED audit of the cited declarations.

This file is authored by the SEMREV reviewer, not copied from the L5 detector.
It fails to compile (non-zero exit) if any cited declaration is missing, unsafe,
or has an axiom cone outside {propext, Classical.choice, Quot.sound}, with the
five registered negative-control declarations reported separately and required to
carry exactly their forbidden axiom.
-/
import Lean.Util.CollectAxioms
import Lean.Elab.Command

import Poincare.D10.TriangulationLowDim.Complex
import Poincare.D10.TriangulationLowDim.Moise
import Poincare.D12.SurgeryRecognition.All
import Poincare.D12.TriangulationTopology.DiskGluing
import Poincare.D12.TriangulationTopology.NegControl.NegControl
import Poincare.D12.TriangulationTopology.TwoHemisphereInstance
import Poincare.D12.VolumeIBP.Audit
import Poincare.D13.CriticalPathReview.NegControl
import Poincare.D7.Limit.Blocked
import Poincare.D7.Limit.Convergence
import Poincare.D7.Recognition.All
import Poincare.D7.SurgeryFlow.Basic
import Poincare.D7.SurgeryFlow.Statements
import Poincare.Longrun.Evolution.Bridge
import Poincare.Longrun.Surgery.Missing
import Poincare.Longrun.Topology.Stage6Bridge
import Poincare.VKPort.HatcherLib.Ch1.VanKampen

open Lean Elab Command

namespace SemRevAudit

def allowedAxioms : List Name := ["propext", "Classical.choice", "Quot.sound"].map String.toName

def cited : List Name := [
  `Poincare.D12.SurgeryRecognition.doubleBallHomeoSphere,
  `Poincare.D12.SurgeryRecognition.sphereConnectSum_homeo_sphere,
  `Poincare.D12.SurgeryRecognition.sphereConnectSum_transported,
  `Poincare.D12.SurgeryRecognition.iteratedSphereSum_homeo_sphere,
  `Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2,
  `Poincare.D12.SurgeryRecognition.finiteFreeOrbit_isQuotientCoveringMap,
  `Poincare.D12.SurgeryRecognition.deckTrivial_of_simplyConnected_quotient,
  `Poincare.D12.SurgeryRecognition.stage6Target_of_v2decomposition,
  `Poincare.D12.SurgeryRecognition.stage6Target_of_v2hypotheses,
  `Poincare.D12.SurgeryRecognition.stage6Target_of_v3hypotheses,
  `Poincare.D12.SurgeryRecognition.AntipodalGroup,
  `Poincare.D7.Recognition.stage6Target_of_certificates,
  `HatcherLib.vanKampenMap,
  `HatcherLib.vanKampenMap_surjective,
  `HatcherLib.vanKampen_ker_eq_normalSubgroup_of_factorizationsConnected,
  `Poincare.D12.TriangulationTopology.alexanderHomeo,
  `Poincare.D12.TriangulationTopology.alexanderHomeo_eq_refl_iff,
  `Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere,
  `Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere_refl_apply,
  `Poincare.D12.TriangulationTopology.sphereOfTwoDisks,
  `Poincare.D12.TriangulationTopology.sphereOfTwoDisks_hemisphere_instance,
  `Poincare.D10.TriangulationLowDim.MoiseTriangulationTheorem,
  `Poincare.D10.TriangulationLowDim.FiniteAbstractSimplicialComplex,
  `Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses,
  `Poincare.D7.SurgeryFlow.missingFullNeckAnalysis,
  `Poincare.D7.SurgeryFlow.missingExtinctionTheorem,
  `Poincare.D7.SurgeryFlow.missingSurgeryFlowTheorem,
  `Poincare.D7.SurgeryFlow.ExtinctionData,
  `Poincare.Longrun.Surgery.ExtinctionTheorem,
  `Poincare.Longrun.Surgery.MissingInputs,
  `Poincare.D7.SurgeryFlow.realLineProcedureChain_simplyConnected,
  `Poincare.Longrun.Evolution.FiniteRepresentsContinuousPerelman,
  `Poincare.Longrun.Evolution.FiniteMeshConvergence,
  `Poincare.Longrun.Evolution.PerelmanEvolutionBoundary,
  `Poincare.Longrun.Evolution.PerelmanApproximation,
  `Poincare.Longrun.Evolution.ContinuousPerelmanFMonotonicity,
  `Poincare.D7.Limit.HeatMeshConvergence,
  `Poincare.D7.Limit.heatMeshConvergence_of_stability,
  `Poincare.D7.Limit.finiteMeshConvergence_of_stability,
  `Poincare.D7.Limit.HeatMeshConvergenceTheorem,
  `Poincare.D7.Limit.IsRefiningMesh,
  `Poincare.D7.Limit.HasVanishingError,
  `Poincare.Longrun.Topology.stage6Target_of_sphereRecognition,
  `Poincare.Longrun.Topology.stage6Target_of_compactThreeManifold,
  `Poincare.Longrun.Topology.stage6Target_iff_sphereRecognition,
  `Poincare.Stage6.poincareConjectureTopologicalThree,
  `d12NegControlBadAxiom,
  `d12NegControlBadTheorem,
  `Poincare.D12.VolumeIBP.Audit.negativeControl,
  `Poincare.D13.CriticalPathReview.NegControl.negControlBadAxiom,
  `Poincare.D13.CriticalPathReview.NegControl.negControlBadTheorem,
]

def registeredNegControls : List Name := [
  `d12NegControlBadAxiom,
  `d12NegControlBadTheorem,
  `Poincare.D12.VolumeIBP.Audit.negativeControl,
  `Poincare.D13.CriticalPathReview.NegControl.negControlBadAxiom,
  `Poincare.D13.CriticalPathReview.NegControl.negControlBadTheorem,
]

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


end SemRevAudit
