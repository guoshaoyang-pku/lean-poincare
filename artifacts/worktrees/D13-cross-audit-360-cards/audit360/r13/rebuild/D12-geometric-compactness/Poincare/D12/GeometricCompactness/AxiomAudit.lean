/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D12-geometric-compactness)
-/
import Poincare.D12.GeometricCompactness.Frontier
import Poincare.D12.GeometricCompactness.GridFamily

/-!
# Poincare.D12.GeometricCompactness.AxiomAudit

Task-local per-declaration axiom audit for D12-geometric-compactness.

The `#print axioms` commands below are the human-readable kernel audit.  The
programmatic fail-closed audit lives in `tools/d12_axiom_audit.py`: it parses
exactly this file's output and fails unless every declaration's axiom set is
a subset of `{propext, Classical.choice, Quot.sound}`, and it runs a planted
negative control (an intentional `axiom`) to prove that forbidden axioms are
actually detected.

Allowed axioms (kernel trust): `propext`, `Classical.choice`, `Quot.sound`.
Nothing else may appear for any new declaration.
-/

open Poincare.D12.GeometricCompactness

/-! ### Basic.lean -/
#print axioms Poincare.D12.GeometricCompactness.cover_transfer_of_hausdorffDist_lt
#print axioms Poincare.D12.GeometricCompactness.cover_transfer_of_ghDist
#print axioms Poincare.D12.GeometricCompactness.cover_transfer_of_isometry
#print axioms Poincare.D12.GeometricCompactness.diam_transfer_of_hausdorffDist_lt
#print axioms Poincare.D12.GeometricCompactness.diam_transfer_of_ghDist
#print axioms Poincare.D12.GeometricCompactness.ghDist_congr_left
#print axioms Poincare.D12.GeometricCompactness.ghDist_congr_right
#print axioms Poincare.D12.GeometricCompactness.toGHSpace_rep_isometryEquiv
#print axioms Poincare.D12.GeometricCompactness.diam_rep_of_toGHSpace

/-! ### Criterion.lean -/
#print axioms Poincare.D12.GeometricCompactness.uniformCovers_of_totallyBounded
#print axioms Poincare.D12.GeometricCompactness.totallyBounded_iff_uniformCovers
#print axioms Poincare.D12.GeometricCompactness.isCompact_of_uniformCovers
#print axioms Poincare.D12.GeometricCompactness.gromovCriterion
#print axioms Poincare.D12.GeometricCompactness.gh_subseq_of_compact
#print axioms Poincare.D12.GeometricCompactness.gh_subseq_of_uniformCovers

/-! ### GridFamily.lean -/
#print axioms Poincare.D12.GeometricCompactness.square_grid_dense
#print axioms Poincare.D12.GeometricCompactness.gridUniformCover
#print axioms Poincare.D12.GeometricCompactness.gridSpace_diam_le
#print axioms Poincare.D12.GeometricCompactness.hausdorffDist_grid_square_le
#print axioms Poincare.D12.GeometricCompactness.grid_gh_tendsto_square
#print axioms Poincare.D12.GeometricCompactness.gridSpace_card
#print axioms Poincare.D12.GeometricCompactness.gridGH_injective
#print axioms Poincare.D12.GeometricCompactness.gridFamily_infinite
#print axioms Poincare.D12.GeometricCompactness.gridFamily_totallyBounded
#print axioms Poincare.D12.GeometricCompactness.gridFamily_closure_isCompact
#print axioms Poincare.D12.GeometricCompactness.gridFamily_subseq
#print axioms Poincare.D12.GeometricCompactness.isCompact_unitSquare
#print axioms Poincare.D12.GeometricCompactness.zero_mem_gridSet
#print axioms Poincare.D12.GeometricCompactness.gridPoint_coord

/-! ### Frontier.lean (proved part only; the statement-only `def`s are Props and are listed
here for completeness — they introduce no axioms by construction, and `#print axioms` on a
`def` with no proof obligations reports the same kernel set) -/
#print axioms Poincare.D12.GeometricCompactness.closure_isCompact_of_totallyBounded
#print axioms Poincare.D12.GeometricCompactness.gh_subseq_of_familyBounds
#print axioms Poincare.D12.GeometricCompactness.harmonicCoordinatesExistence
#print axioms Poincare.D12.GeometricCompactness.bishopGromovVolumeComparison
#print axioms Poincare.D12.GeometricCompactness.curvatureBoundImpliesUniformCovers
#print axioms Poincare.D12.GeometricCompactness.cheegerGromovCompactness
#print axioms Poincare.D12.GeometricCompactness.ancientKappaCompactnessFrontier
#print axioms Poincare.D12.GeometricCompactness.canonicalNeighborhoodFrontier
#print axioms Poincare.D12.GeometricCompactness.canonicalNeighborhoodFrontier_iff
#print axioms Poincare.D12.GeometricCompactness.curvatureBoundImpliesUniformCovers_iff

