-- A3 round-13 definitional hyp-equals-conclusion screen (generated)
import Poincare.D12.SurgeryRecognition.All
import Poincare.D12.SurgeryRecognition.Audit
import Poincare.D12.SurgeryRecognition.BallGluing
import Poincare.D12.SurgeryRecognition.ConnectedSumTopology
import Poincare.D12.SurgeryRecognition.CoveringRecognition
import Poincare.D12.SurgeryRecognition.DeckTrivial
import Poincare.D12.SurgeryRecognition.ExpandedInterfaces
import Poincare.D12.SurgeryRecognition.SphereOfSpheres

open Lean Elab Command
open Lean Meta
namespace A3R13D

def claimed : List Name := [``Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2,
  ``Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV2.toRemaining,
  ``Poincare.D12.SurgeryRecognition.SphericalSpaceFormModel.spaceFormFiberEquivGroup,
  ``Poincare.D12.SurgeryRecognition.SphericalSpaceFormModel.spaceFormProjection,
  ``Poincare.D12.SurgeryRecognition.SphericalSpaceFormModel.spaceFormProjection_covering,
  ``Poincare.D12.SurgeryRecognition.SphericalSpaceFormModel.spaceForm_fiber_subsingleton,
  ``Poincare.D12.SurgeryRecognition.SphericalSpaceFormModel.spaceForm_monodromy_transitive,
  ``Poincare.D12.SurgeryRecognition.SphericalSpaceFormModel.spaceForm_monodromy_trivial,
  ``Poincare.D12.SurgeryRecognition.antipodalCoveringMap,
  ``Poincare.D12.SurgeryRecognition.antipodalModel,
  ``Poincare.D12.SurgeryRecognition.antipodalModel_nontrivial,
  ``Poincare.D12.SurgeryRecognition.antipodalQuotientCovering,
  ``Poincare.D12.SurgeryRecognition.antipodal_fiber_card_two,
  ``Poincare.D12.SurgeryRecognition.antipodal_free,
  ``Poincare.D12.SurgeryRecognition.antipodal_two_sheets,
  ``Poincare.D12.SurgeryRecognition.deckTrivial_of_simplyConnected_quotient,
  ``Poincare.D12.SurgeryRecognition.doubleBallHomeoSphere,
  ``Poincare.D12.SurgeryRecognition.endGame_finalTopology,
  ``Poincare.D12.SurgeryRecognition.equatorHomeoS2,
  ``Poincare.D12.SurgeryRecognition.finiteFreeOrbit_isQuotientCoveringMap,
  ``Poincare.D12.SurgeryRecognition.iteratedSphereSum_homeo_sphere,
  ``Poincare.D12.SurgeryRecognition.northHemisphereHomeo,
  ``Poincare.D12.SurgeryRecognition.quotientHomeoOfSubsingleton,
  ``Poincare.D12.SurgeryRecognition.southHemisphereHomeo,
  ``Poincare.D12.SurgeryRecognition.sphereConnectSum_homeo_sphere,
  ``Poincare.D12.SurgeryRecognition.sphereThree_pathConnectedSpace,
  ``Poincare.D12.SurgeryRecognition.sphericalPieceRecognition_of,
  ``Poincare.D12.SurgeryRecognition.sphericalPieceRecognition_of_spaceForm,
  ``Poincare.D12.SurgeryRecognition.stage6Target_of_v2decomposition,
  ``Poincare.D12.SurgeryRecognition.stage6Target_of_v2hypotheses,
  ``Poincare.D12.SurgeryRecognition.stage6Target_of_v3hypotheses]

/-- Only theorems with a Prop-valued hypothesis can commit the
assumption-as-conclusion defect; a plain function whose argument type equals
its result type (e.g. `def f (x : R) : R`) is benign. -/
def run : CommandElabM Unit := do
  liftTermElabM do
    let mut checked := 0
    for n in claimed do
      let ci ← getConstInfo n
      unless ci matches .thmInfo _ do continue
      checked := checked + 1
      Lean.Meta.forallTelescope ci.type (fun args body => do
        if ← isDefEq body (.const ``True []) then
          logInfo m!"A3R13D|TRIVIAL_TRUE|{n}"
        for a in args do
          let ty ← inferType a
          if ← isProp ty then
            if ← isDefEq ty body then
              let u := a.fvarId!.name
              logInfo m!"A3R13D|HYP_DEFEQ|{n}|{u}"
        )
    logInfo m!"A3R13D|CHECKED|{checked}"
  logInfo m!"A3R13D|DONE"

end A3R13D
run_cmd A3R13D.run
