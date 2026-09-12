/-
SEMREV independent use probe for D13-vankampen-recognition (written for the SEMREV review).
Checks existence, type-level and value-level occurrence of closure pairs, and reverse direct use.
-/
import Poincare.D12.SurgeryRecognition.All
import Poincare.D12.SurgeryRecognition.Audit
import Poincare.D12.SurgeryRecognition.BallGluing
import Poincare.D12.SurgeryRecognition.ConnectedSumTopology
import Poincare.D12.SurgeryRecognition.CoveringRecognition
import Poincare.D12.SurgeryRecognition.DeckTrivial
import Poincare.D12.SurgeryRecognition.ExpandedInterfaces
import Poincare.D12.SurgeryRecognition.SphereOfSpheres
import Poincare.D13.VanKampenRecognition.All
import Poincare.D13.VanKampenRecognition.Audit
import Poincare.D13.VanKampenRecognition.FreeProduct
import Poincare.D13.VanKampenRecognition.SR4Closure
import Poincare.D13.VanKampenRecognition.SphereVanKampen
import Poincare.D13.VanKampenRecognition.Stereographic
import Poincare.D7.Canonical.Basic
import Poincare.D7.Canonical.Classification
import Poincare.D7.Canonical.Curvature
import Poincare.D7.Canonical.Models
import Poincare.D7.Canonical.Statements
import Poincare.D7.Compactness.Basic
import Poincare.D7.Curvature.Basic
import Poincare.D7.Curvature.Example
import Poincare.D7.Curvature.Sectional
import Poincare.D7.Curvature.Symmetries
import Poincare.D7.Recognition.All
import Poincare.D7.Recognition.Assembly
import Poincare.D7.Recognition.Audit
import Poincare.D7.Recognition.Basic
import Poincare.D7.Recognition.Homeomorphism
import Poincare.D7.Recognition.Probe
import Poincare.D7.RicciScalar
import Poincare.D7.RicciScalar.Basic
import Poincare.D7.RicciScalar.Bridge
import Poincare.D7.RicciScalar.Example
import Poincare.D7.RicciScalar.Product
import Poincare.D7.RicciScalar.Scalar
import Poincare.D7.RicciScalar.Variation
import Poincare.D7.ShortTime.Basic
import Poincare.D7.ShortTime.Equivalence
import Poincare.D7.ShortTime.Gauge
import Poincare.D7.ShortTime.MatrixDeriv
import Poincare.D7.ShortTime.ODE
import Poincare.D7.ShortTime.Statements
import Poincare.VKPort.HatcherLib.Ch1.AlgebraicConstructions
import Poincare.VKPort.HatcherLib.Ch1.BasicConstructions
import Poincare.VKPort.HatcherLib.Ch1.VanKampen
import Poincare.VKPort.HatcherLib.Ch1.VanKampenAdaptedGrid
import Poincare.VKPort.HatcherLib.Ch1.VanKampenGlobalSweep
import Poincare.VKPort.HatcherLib.Ch1.VanKampenGrid
import Poincare.VKPort.HatcherLib.Ch1.VanKampenSubdivision
import Poincare.VKPort.HatcherLib.Ch1.VanKampenSweep
import Poincare.VKPort.HatcherLib.Ch1.VanKampenWordCalculus
import Poincare.VKPort.HatcherLib.VKProbe
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace SEMREVUse_D13_vankampen_recognition

def existsNames : List Name := [
  "Poincare.D13.VanKampenRecognition.simplyConnectedPieces_of_v2".toName,
  "Poincare.D13.VanKampenRecognition.ConnectedSumDecomposition.mkV2Complete".toName,
  "Poincare.D13.VanKampenRecognition.RemainingRecognitionHypothesesV4.toRemainingV3".toName,
  "Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2".toName,
  "Poincare.D13.VanKampenRecognition.stage6Target_of_v4hypotheses_from_certificates".toName]

def pairs : List (Name × Name) := [
  ("Poincare.D13.VanKampenRecognition.simplyConnectedPieces_of_v2".toName, "Poincare.D13.VanKampenRecognition.ConnectedSumDecomposition.mkV2Complete".toName),
  ("Poincare.D13.VanKampenRecognition.simplyConnectedPieces_of_v2".toName, "Poincare.D13.VanKampenRecognition.RemainingRecognitionHypothesesV4.toRemainingV3".toName),
  ("Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2".toName, "Poincare.D12.SurgeryRecognition.stage6Target_of_v2hypotheses".toName),
  ("Poincare.D13.VanKampenRecognition.ConnectedSumDecomposition.mkV2Complete".toName, "Poincare.D13.VanKampenRecognition.stage6Target_of_v4hypotheses_from_certificates".toName)]

def reverseNames : List Name := [
  "Poincare.D13.VanKampenRecognition.simplyConnectedPieces_of_v2".toName,
  "Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2".toName]

def scanPrefixes : List Name := [
  "Poincare".toName]

end SEMREVUse_D13_vankampen_recognition

open SEMREVUse_D13_vankampen_recognition in
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
  IO.println s!"USE_DONE\tD13-vankampen-recognition"
