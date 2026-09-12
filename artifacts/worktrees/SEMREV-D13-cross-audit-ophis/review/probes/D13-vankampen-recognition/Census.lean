/-
SEMREV independent fail-closed census probe for D13-vankampen-recognition.
Written for longrun task SEMREV-D13-cross-audit-ophis; imports the transported snapshot only.
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

namespace SEMREV_D13_vankampen_recognition

def approvedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def negativeControlModules : List Name := [
  ]

def auditedModules : List Name := [
  "Poincare.D12.SurgeryRecognition.All".toName,
  "Poincare.D12.SurgeryRecognition.Audit".toName,
  "Poincare.D12.SurgeryRecognition.BallGluing".toName,
  "Poincare.D12.SurgeryRecognition.ConnectedSumTopology".toName,
  "Poincare.D12.SurgeryRecognition.CoveringRecognition".toName,
  "Poincare.D12.SurgeryRecognition.DeckTrivial".toName,
  "Poincare.D12.SurgeryRecognition.ExpandedInterfaces".toName,
  "Poincare.D12.SurgeryRecognition.SphereOfSpheres".toName,
  "Poincare.D13.VanKampenRecognition.All".toName,
  "Poincare.D13.VanKampenRecognition.Audit".toName,
  "Poincare.D13.VanKampenRecognition.FreeProduct".toName,
  "Poincare.D13.VanKampenRecognition.SR4Closure".toName,
  "Poincare.D13.VanKampenRecognition.SphereVanKampen".toName,
  "Poincare.D13.VanKampenRecognition.Stereographic".toName,
  "Poincare.D7.Canonical.Basic".toName,
  "Poincare.D7.Canonical.Classification".toName,
  "Poincare.D7.Canonical.Curvature".toName,
  "Poincare.D7.Canonical.Models".toName,
  "Poincare.D7.Canonical.Statements".toName,
  "Poincare.D7.Compactness.Basic".toName,
  "Poincare.D7.Curvature.Basic".toName,
  "Poincare.D7.Curvature.Example".toName,
  "Poincare.D7.Curvature.Sectional".toName,
  "Poincare.D7.Curvature.Symmetries".toName,
  "Poincare.D7.Recognition.All".toName,
  "Poincare.D7.Recognition.Assembly".toName,
  "Poincare.D7.Recognition.Audit".toName,
  "Poincare.D7.Recognition.Basic".toName,
  "Poincare.D7.Recognition.Homeomorphism".toName,
  "Poincare.D7.Recognition.Probe".toName,
  "Poincare.D7.RicciScalar".toName,
  "Poincare.D7.RicciScalar.Basic".toName,
  "Poincare.D7.RicciScalar.Bridge".toName,
  "Poincare.D7.RicciScalar.Example".toName,
  "Poincare.D7.RicciScalar.Product".toName,
  "Poincare.D7.RicciScalar.Scalar".toName,
  "Poincare.D7.RicciScalar.Variation".toName,
  "Poincare.D7.ShortTime.Basic".toName,
  "Poincare.D7.ShortTime.Equivalence".toName,
  "Poincare.D7.ShortTime.Gauge".toName,
  "Poincare.D7.ShortTime.MatrixDeriv".toName,
  "Poincare.D7.ShortTime.ODE".toName,
  "Poincare.D7.ShortTime.Statements".toName,
  "Poincare.VKPort.HatcherLib.Ch1.AlgebraicConstructions".toName,
  "Poincare.VKPort.HatcherLib.Ch1.BasicConstructions".toName,
  "Poincare.VKPort.HatcherLib.Ch1.VanKampen".toName,
  "Poincare.VKPort.HatcherLib.Ch1.VanKampenAdaptedGrid".toName,
  "Poincare.VKPort.HatcherLib.Ch1.VanKampenGlobalSweep".toName,
  "Poincare.VKPort.HatcherLib.Ch1.VanKampenGrid".toName,
  "Poincare.VKPort.HatcherLib.Ch1.VanKampenSubdivision".toName,
  "Poincare.VKPort.HatcherLib.Ch1.VanKampenSweep".toName,
  "Poincare.VKPort.HatcherLib.Ch1.VanKampenWordCalculus".toName,
  "Poincare.VKPort.HatcherLib.VKProbe".toName]

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

end SEMREV_D13_vankampen_recognition

open SEMREV_D13_vankampen_recognition in
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
  IO.println s!"XAUDIT\tD13-vankampen-recognition\tdeclarations\t{rows.size}"
  IO.println s!"XAUDIT\tD13-vankampen-recognition\ttheorems\t{nThm}"
  IO.println s!"XAUDIT\tD13-vankampen-recognition\tpartial_defs\t{nPartial}"
  IO.println s!"XAUDIT\tD13-vankampen-recognition\topaque\t{nOpaque}"
  IO.println s!"XAUDIT\tD13-vankampen-recognition\tproject_axioms\t{nAxiom}"
  IO.println s!"XAUDIT\tD13-vankampen-recognition\tunsafe\t{nUnsafe}"
  IO.println s!"XAUDIT\tD13-vankampen-recognition\tsorry_cones\t{nSorry}"
  IO.println s!"XAUDIT\tD13-vankampen-recognition\tnative_decide_cones\t{nNative}"
  IO.println s!"XAUDIT\tD13-vankampen-recognition\tunapproved_axiom_cones\t{nOther}"
  IO.println s!"XAUDIT\tD13-vankampen-recognition\tcollect_failures\t{nFail}"
  IO.println s!"XAUDIT\tD13-vankampen-recognition\tproof_wanted\t{nProofWanted}"
  if nAxiom + nUnsafe + nSorry + nNative + nOther + nFail + nProofWanted > 0 then
    IO.println s!"XAUDIT\tD13-vankampen-recognition\tVERDICT\tFAIL"
    throwError "SEMREV: forbidden dependency found (D13-vankampen-recognition)"
  else
    IO.println s!"XAUDIT\tD13-vankampen-recognition\tVERDICT\tPASS"
