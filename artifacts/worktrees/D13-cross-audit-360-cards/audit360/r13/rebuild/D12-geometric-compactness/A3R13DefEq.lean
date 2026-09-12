-- A3 round-13 definitional hyp-equals-conclusion screen (generated)
import Poincare.D12.GeometricCompactness.AxiomAudit
import Poincare.D12.GeometricCompactness.Basic
import Poincare.D12.GeometricCompactness.Criterion
import Poincare.D12.GeometricCompactness.Frontier
import Poincare.D12.GeometricCompactness.GridFamily

open Lean Elab Command
open Lean Meta
namespace A3R13D

def claimed : List Name := [``Poincare.D12.GeometricCompactness.ancientKappaCompactnessFrontier,
  ``Poincare.D12.GeometricCompactness.bishopGromovVolumeComparison,
  ``Poincare.D12.GeometricCompactness.canonicalNeighborhoodFrontier,
  ``Poincare.D12.GeometricCompactness.canonicalNeighborhoodFrontier_iff,
  ``Poincare.D12.GeometricCompactness.cheegerGromovCompactness,
  ``Poincare.D12.GeometricCompactness.closure_isCompact_of_totallyBounded,
  ``Poincare.D12.GeometricCompactness.cover_transfer_of_ghDist,
  ``Poincare.D12.GeometricCompactness.cover_transfer_of_hausdorffDist_lt,
  ``Poincare.D12.GeometricCompactness.cover_transfer_of_isometry,
  ``Poincare.D12.GeometricCompactness.curvatureBoundImpliesUniformCovers,
  ``Poincare.D12.GeometricCompactness.curvatureBoundImpliesUniformCovers_iff,
  ``Poincare.D12.GeometricCompactness.diam_rep_of_toGHSpace,
  ``Poincare.D12.GeometricCompactness.diam_transfer_of_ghDist,
  ``Poincare.D12.GeometricCompactness.diam_transfer_of_hausdorffDist_lt,
  ``Poincare.D12.GeometricCompactness.ghDist_congr_left,
  ``Poincare.D12.GeometricCompactness.ghDist_congr_right,
  ``Poincare.D12.GeometricCompactness.gh_subseq_of_compact,
  ``Poincare.D12.GeometricCompactness.gh_subseq_of_familyBounds,
  ``Poincare.D12.GeometricCompactness.gh_subseq_of_uniformCovers,
  ``Poincare.D12.GeometricCompactness.gridFamily_closure_isCompact,
  ``Poincare.D12.GeometricCompactness.gridFamily_infinite,
  ``Poincare.D12.GeometricCompactness.gridFamily_subseq,
  ``Poincare.D12.GeometricCompactness.gridFamily_totallyBounded,
  ``Poincare.D12.GeometricCompactness.gridGH_injective,
  ``Poincare.D12.GeometricCompactness.gridPoint_coord,
  ``Poincare.D12.GeometricCompactness.gridSpace_card,
  ``Poincare.D12.GeometricCompactness.gridSpace_diam_le,
  ``Poincare.D12.GeometricCompactness.gridUniformCover,
  ``Poincare.D12.GeometricCompactness.grid_gh_tendsto_square,
  ``Poincare.D12.GeometricCompactness.gromovCriterion,
  ``Poincare.D12.GeometricCompactness.harmonicCoordinatesExistence,
  ``Poincare.D12.GeometricCompactness.hausdorffDist_grid_square_le,
  ``Poincare.D12.GeometricCompactness.isCompact_of_uniformCovers,
  ``Poincare.D12.GeometricCompactness.isCompact_unitSquare,
  ``Poincare.D12.GeometricCompactness.square_grid_dense,
  ``Poincare.D12.GeometricCompactness.toGHSpace_rep_isometryEquiv,
  ``Poincare.D12.GeometricCompactness.totallyBounded_iff_uniformCovers,
  ``Poincare.D12.GeometricCompactness.uniformCovers_of_totallyBounded,
  ``Poincare.D12.GeometricCompactness.zero_mem_gridSet]

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
