/-
SEMREV independent fail-closed census probe for D13-manifold-ibp-volume-form.
Written for longrun task SEMREV-D13-cross-audit-ophis; imports the transported snapshot only.
-/
import Poincare.D12.VolumeIBP
import Poincare.D12.VolumeIBP.Basic
import Poincare.D12.VolumeIBP.Blocked
import Poincare.D12.VolumeIBP.ChangeOfVariables
import Poincare.D12.VolumeIBP.Compat
import Poincare.D12.VolumeIBP.Divergence
import Poincare.D12.VolumeIBP.Example
import Poincare.D12.VolumeIBP.IBP
import Poincare.D12.VolumeIBP.Regularity
import Poincare.D13
import Poincare.D13.BochnerFlat
import Poincare.D13.Bridge
import Poincare.D13.CertificateOn
import Poincare.D13.EuclideanChart
import Poincare.D13.GaussianF
import Poincare.D13.GaussianMoment
import Poincare.D13.HeatBridge
import Poincare.D13.HeatKernelBridge
import Poincare.D13.ManifoldIBP
import Poincare.D13.ManifoldIBP.Blocked
import Poincare.D13.ManifoldIBP.ChartSum
import Poincare.D13.ManifoldIBP.DisjointModel
import Poincare.D13.ManifoldIBP.GlobalIBP
import Poincare.D13.ManifoldIBP.GlobalMeasure
import Poincare.D13.ManifoldIBP.IntegrableTransfer
import Poincare.D13.ManifoldIBP.OverlapIBP
import Poincare.D13.ManifoldIBP.OverlapIBPData
import Poincare.D13.ManifoldIBP.OverlapIBPModel
import Poincare.D13.ManifoldIBP.OverlapModel
import Poincare.D13.ManifoldIBP.OverlapOperatorCheck
import Poincare.D13.ManifoldIBP.POUAssembly
import Poincare.D13.ManifoldIBP.POUAssemblyAE
import Poincare.D13.ManifoldIBP.POUConstruction
import Poincare.D13.ManifoldIBP.POUModel
import Poincare.D13.ManifoldIBP.PartialChartModel
import Poincare.D13.ManifoldIBP.PartialChartModelPOU
import Poincare.D13.ManifoldIBP.SmoothAtlas
import Poincare.D13.ManifoldIBP.SmoothAtlasIBP
import Poincare.D13.ManifoldIBP.SmoothAtlasModel
import Poincare.D13.ManifoldIBP.SmoothAtlasPartial
import Poincare.D13.ManifoldIBP.SmoothAtlasPartialAE
import Poincare.D13.ManifoldIBP.SmoothPartition
import Poincare.D13.ManifoldIBP.Transfer
import Poincare.D13.ManifoldIBP.VolumeFormBridge
import Poincare.D13.Riemannian
import Poincare.D13.Riemannian.AtlasBridge
import Poincare.D13.Riemannian.AtlasPairing
import Poincare.D13.Riemannian.ChartMetricBridge
import Poincare.D13.Riemannian.MetricBridge
import Poincare.D13.Riemannian.MetricBridgeSmooth
import Poincare.D13.Riemannian.PullbackPairing
import Poincare.D13.VolumeForm
import Poincare.D13.VolumeForm.Basic
import Poincare.D13.VolumeForm.Gluing
import Poincare.D13.VolumeForm.Transformation
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace SEMREV_D13_manifold_ibp_volume_form

def approvedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def negativeControlModules : List Name := [
  "Poincare.D12.VolumeIBP.Audit".toName,
  "Poincare.D13.Audit".toName]

def auditedModules : List Name := [
  "Poincare.D12.VolumeIBP".toName,
  "Poincare.D12.VolumeIBP.Basic".toName,
  "Poincare.D12.VolumeIBP.Blocked".toName,
  "Poincare.D12.VolumeIBP.ChangeOfVariables".toName,
  "Poincare.D12.VolumeIBP.Compat".toName,
  "Poincare.D12.VolumeIBP.Divergence".toName,
  "Poincare.D12.VolumeIBP.Example".toName,
  "Poincare.D12.VolumeIBP.IBP".toName,
  "Poincare.D12.VolumeIBP.Regularity".toName,
  "Poincare.D13".toName,
  "Poincare.D13.BochnerFlat".toName,
  "Poincare.D13.Bridge".toName,
  "Poincare.D13.CertificateOn".toName,
  "Poincare.D13.EuclideanChart".toName,
  "Poincare.D13.GaussianF".toName,
  "Poincare.D13.GaussianMoment".toName,
  "Poincare.D13.HeatBridge".toName,
  "Poincare.D13.HeatKernelBridge".toName,
  "Poincare.D13.ManifoldIBP".toName,
  "Poincare.D13.ManifoldIBP.Blocked".toName,
  "Poincare.D13.ManifoldIBP.ChartSum".toName,
  "Poincare.D13.ManifoldIBP.DisjointModel".toName,
  "Poincare.D13.ManifoldIBP.GlobalIBP".toName,
  "Poincare.D13.ManifoldIBP.GlobalMeasure".toName,
  "Poincare.D13.ManifoldIBP.IntegrableTransfer".toName,
  "Poincare.D13.ManifoldIBP.OverlapIBP".toName,
  "Poincare.D13.ManifoldIBP.OverlapIBPData".toName,
  "Poincare.D13.ManifoldIBP.OverlapIBPModel".toName,
  "Poincare.D13.ManifoldIBP.OverlapModel".toName,
  "Poincare.D13.ManifoldIBP.OverlapOperatorCheck".toName,
  "Poincare.D13.ManifoldIBP.POUAssembly".toName,
  "Poincare.D13.ManifoldIBP.POUAssemblyAE".toName,
  "Poincare.D13.ManifoldIBP.POUConstruction".toName,
  "Poincare.D13.ManifoldIBP.POUModel".toName,
  "Poincare.D13.ManifoldIBP.PartialChartModel".toName,
  "Poincare.D13.ManifoldIBP.PartialChartModelPOU".toName,
  "Poincare.D13.ManifoldIBP.SmoothAtlas".toName,
  "Poincare.D13.ManifoldIBP.SmoothAtlasIBP".toName,
  "Poincare.D13.ManifoldIBP.SmoothAtlasModel".toName,
  "Poincare.D13.ManifoldIBP.SmoothAtlasPartial".toName,
  "Poincare.D13.ManifoldIBP.SmoothAtlasPartialAE".toName,
  "Poincare.D13.ManifoldIBP.SmoothPartition".toName,
  "Poincare.D13.ManifoldIBP.Transfer".toName,
  "Poincare.D13.ManifoldIBP.VolumeFormBridge".toName,
  "Poincare.D13.Riemannian".toName,
  "Poincare.D13.Riemannian.AtlasBridge".toName,
  "Poincare.D13.Riemannian.AtlasPairing".toName,
  "Poincare.D13.Riemannian.ChartMetricBridge".toName,
  "Poincare.D13.Riemannian.MetricBridge".toName,
  "Poincare.D13.Riemannian.MetricBridgeSmooth".toName,
  "Poincare.D13.Riemannian.PullbackPairing".toName,
  "Poincare.D13.VolumeForm".toName,
  "Poincare.D13.VolumeForm.Basic".toName,
  "Poincare.D13.VolumeForm.Gluing".toName,
  "Poincare.D13.VolumeForm.Transformation".toName,
  "ProbeScratch".toName]

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo v => match v.safety with
      | .«unsafe» => "unsafe_def"
      | .«partial» => "partial_def"
      | .safe => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

end SEMREV_D13_manifold_ibp_volume_form

open SEMREV_D13_manifold_ibp_volume_form in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let auditedSet : Std.HashSet Name :=
    auditedModules.foldl (fun acc m => acc.insert m) ∅
  let rows := env.constants.fold (fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some midx =>
        let m := mods.getD midx .anonymous
        if auditedSet.contains m && !negativeControlModules.contains m then acc.push (n, ci, m)
        else acc
    | none => acc) #[]
  let mut nAxiom := 0
  let mut nUnsafe := 0
  let mut nSorry := 0
  let mut nNative := 0
  let mut nOther := 0
  let mut nFail := 0
  let mut nPartial := 0
  let mut nThm := 0
  let mut nOpaque := 0
  let mut nProofWanted := 0
  for (n, ci, m) in rows do
    if n.toString.contains "proof_wanted" then nProofWanted := nProofWanted + 1
    match ci with
    | .axiomInfo _ => nAxiom := nAxiom + 1
    | .opaqueInfo _ => nOpaque := nOpaque + 1
    | .defnInfo v =>
        match v.safety with
        | .«unsafe» => nUnsafe := nUnsafe + 1
        | .«partial» => nPartial := nPartial + 1
        | .safe => pure ()
    | .thmInfo _ => nThm := nThm + 1
    | _ => pure ()
    let axs ←
      try Lean.collectAxioms n
      catch _ => nFail := nFail + 1; pure #[]
    for a in axs do
      if a == ``sorryAx then nSorry := nSorry + 1
      else if a == ``ofReduceBool || a.toString.contains "native_decide" then nNative := nNative + 1
      else if !approvedAxioms.contains a then nOther := nOther + 1
    IO.println s!"XDECL\t{n}\t{kindOf ci}\t{m}\t{";".intercalate (axs.toList.map Name.toString)}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tdeclarations\t{rows.size}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\ttheorems\t{nThm}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tpartial_defs\t{nPartial}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\topaque\t{nOpaque}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tproject_axioms\t{nAxiom}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tunsafe\t{nUnsafe}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tsorry_cones\t{nSorry}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tnative_decide_cones\t{nNative}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tunapproved_axiom_cones\t{nOther}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tcollect_failures\t{nFail}"
  IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tproof_wanted\t{nProofWanted}"
  if nAxiom + nUnsafe + nSorry + nNative + nOther + nFail + nProofWanted > 0 then
    IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tVERDICT\tFAIL"
    throwError "SEMREV: forbidden dependency found (D13-manifold-ibp-volume-form)"
  else
    IO.println s!"XAUDIT\tD13-manifold-ibp-volume-form\tVERDICT\tPASS"
