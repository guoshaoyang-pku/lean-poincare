-- A3 round-13 definitional hyp-equals-conclusion screen (generated)
import Poincare.D12.ComparisonGeodesics.AxiomAudit
import Poincare.D12.ComparisonGeodesics.Definitions
import Poincare.D12.ComparisonGeodesics.ModelEuclidean
import Poincare.D12.ComparisonGeodesics.RiccatiComparison
import Poincare.D12.ComparisonGeodesics.SingularRiccati
import Poincare.D12.ComparisonGeodesics.SturmComparison
import Poincare.D12.ComparisonGeodesics.VolumeRatio

open Lean Elab Command
open Lean Meta
namespace A3R13D

def claimed : List Name := [``Poincare.D12.ComparisonGeodesics.areaRatio_antitone_of_logDeriv_le,
  ``Poincare.D12.ComparisonGeodesics.bishopGromovVolumeRatio,
  ``Poincare.D12.ComparisonGeodesics.bishopGromov_volume_le,
  ``Poincare.D12.ComparisonGeodesics.euclidModel_singular_comparison,
  ``Poincare.D12.ComparisonGeodesics.euclideanNormalizedOn_not_continuousOn_zero,
  ``Poincare.D12.ComparisonGeodesics.hasDerivAtR_id,
  ``Poincare.D12.ComparisonGeodesics.logDeriv_hasDerivAt,
  ``Poincare.D12.ComparisonGeodesics.logDeriv_le_of_le,
  ``Poincare.D12.ComparisonGeodesics.radialVolume_pos_of_pos,
  ``Poincare.D12.ComparisonGeodesics.riccati_delta_le_exp,
  ``Poincare.D12.ComparisonGeodesics.riccati_ge_of_singular_normalization,
  ``Poincare.D12.ComparisonGeodesics.riccati_le_of_singular_normalization,
  ``Poincare.D12.ComparisonGeodesics.solution_le_of_same_initial,
  ``Poincare.D12.ComparisonGeodesics.sturm_zero_comparison,
  ``Poincare.D12.ComparisonGeodesics.volumeRatio_antitone,
  ``Poincare.D12.ComparisonGeodesics.wronskian_deriv]

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
