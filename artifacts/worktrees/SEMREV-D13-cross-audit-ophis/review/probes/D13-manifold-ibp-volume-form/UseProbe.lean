/-
SEMREV independent use probe for D13-manifold-ibp-volume-form (written for the SEMREV review).
Checks existence, type-level and value-level occurrence of closure pairs, and reverse direct use.
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

namespace SEMREVUse_D13_manifold_ibp_volume_form

def existsNames : List Name := [
  "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional".toName,
  "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_laplacianIntegralZero".toName,
  "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_integrable_dirichlet".toName,
  "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_dirichletEnergy".toName,
  "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_greenIdentity".toName]

def pairs : List (Name × Name) := [
  ("Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional".toName, "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_laplacianIntegralZero".toName),
  ("Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional".toName, "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_integrable_dirichlet".toName),
  ("Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional".toName, "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_dirichletEnergy".toName),
  ("Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional".toName, "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_greenIdentity".toName)]

def reverseNames : List Name := [
  "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional".toName]

def scanPrefixes : List Name := [
  "Poincare".toName]

end SEMREVUse_D13_manifold_ibp_volume_form

open SEMREVUse_D13_manifold_ibp_volume_form in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  for n in existsNames do
    match env.find? n with
    | none => IO.println s!"USE_EXISTS\t{n}\tMISSING"
    | some ci =>
        let axs ← try Lean.collectAxioms n catch _ => pure #[]
        IO.println s!"USE_EXISTS\t{n}\tOK\t{";".intercalate (axs.toList.map Name.toString)}"
  for (ctor, down) in pairs do
    let ci? := env.find? down
    let inType := match ci? with
      | some ci => ci.type.getUsedConstants.contains ctor
      | none => false
    let inValue := match ci? with
      | some ci => (match ci.value? true with
          | some v => v.getUsedConstants.contains ctor
          | none => false)
      | none => false
    IO.println s!"USE_PAIR\t{ctor}\t{down}\texists={(env.find? down).isSome}\ttype={inType}\tvalue={inValue}"
  for ctor in reverseNames do
    let mut direct : Array Name := #[]
    for (d, _) in env.constants.toList do
      if d == ctor then continue
      let inScan : Bool :=
        match env.getModuleIdxFor? d with
        | some i => scanPrefixes.any (fun r => r.isPrefixOf (mods.getD i .anonymous))
        | none => false
      if !inScan then continue
      match env.find? d with
      | some ci =>
          let inT := ci.type.getUsedConstants.contains ctor
          let inV := match ci.value? true with
            | some v => v.getUsedConstants.contains ctor
            | none => false
          if inT || inV then direct := direct.push d
      | none => pure ()
    IO.println s!"USE_REVERSE\t{ctor}\t{direct.size}"
    for d in direct.qsort (fun a b => a.toString < b.toString) do
      IO.println s!"USE_USER\t{ctor}\t{d}"
  IO.println s!"USE_DONE\tD13-manifold-ibp-volume-form"
