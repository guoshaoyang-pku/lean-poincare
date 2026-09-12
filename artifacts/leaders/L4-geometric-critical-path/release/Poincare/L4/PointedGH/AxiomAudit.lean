/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task L4-child-pointed-gh-transport)
-/
import Poincare.L4.PointedGH.Instances

/-!
# Poincare.L4.PointedGH.AxiomAudit

Task-local per-declaration kernel axiom audit for `L4-child-pointed-gh-transport`.

The `#print axioms` commands below are the human-readable kernel audit.  The programmatic
fail-closed audit lives in `tools/l4_pointed_axiom_audit.py`: it parses exactly this file's
output and fails unless every declaration's axiom set is a subset of
`{propext, Classical.choice, Quot.sound}`, it fails if the parse is vacuous, it runs a planted
negative control (an intentional `axiom`) to prove that forbidden axioms are actually detected,
and it scans the task's source files (comment/string-aware) for forbidden constructs and for any
*code-level* mention of D12's statement-only `Prop`s.

Allowed axioms (kernel trust): `propext`, `Classical.choice`, `Quot.sound`.  Nothing else may
appear for any new declaration.
-/

/-! ### Transport.lean (proved metric-level) -/
#print axioms Poincare.L4.PointedGH.exists_dist_of_hausdorffDist_lt
#print axioms Poincare.L4.PointedGH.exists_dist_of_hausdorffDist_lt'
#print axioms Poincare.L4.PointedGH.exists_dist_optimalGHInjl_optimalGHInjr_lt
#print axioms Poincare.L4.PointedGH.exists_dist_optimalGHInjr_optimalGHInjl_lt
#print axioms Poincare.L4.PointedGH.exists_dist_optimalGHInjl_optimalGHInjr_lt_add
#print axioms Poincare.L4.PointedGH.exists_dist_rep_lt_of_dist_lt
#print axioms Poincare.L4.PointedGH.exists_dist_rep_lt_of_dist_lt'
#print axioms Poincare.L4.PointedGH.exists_dist_optimalGHInjl_optimalGHInjr_le

/-! ### Family.lean (explicit data structure + assemblies) -/
#print axioms Poincare.L4.PointedGH.PointedGHCoupling
#print axioms Poincare.L4.PointedGH.PointedGHCoupling.reindex
#print axioms Poincare.L4.PointedGH.PointedGHCoupling.reindex_Z
#print axioms Poincare.L4.PointedGH.PointedGHCoupling.ghDist_tendsto
#print axioms Poincare.L4.PointedGH.PointedGHCoupling.basepoint_tendsto
#print axioms Poincare.L4.PointedGH.PointedGHCoupling.pointed_convergence
#print axioms Poincare.L4.PointedGH.ghDist_rep_toGHSpace
#print axioms Poincare.L4.PointedGH.pointed_coupling_of_tendsto
#print axioms Poincare.L4.PointedGH.pointed_subseq_of_familyBounds
#print axioms Poincare.L4.PointedGH.pointed_subseq_of_familyBounds_of_mem
#print axioms Poincare.L4.PointedGH.pointed_subseq_of_compact

/-! ### Instances.lean (Euclidean and grid instantiation) -/
#print axioms Poincare.L4.PointedGH.hausdorffDist_closedBall_le
#print axioms Poincare.L4.PointedGH.euclidBall
#print axioms Poincare.L4.PointedGH.euclidBallOrigin
#print axioms Poincare.L4.PointedGH.euclidx
#print axioms Poincare.L4.PointedGH.euclidxLim
#print axioms Poincare.L4.PointedGH.euclideanPointedCoupling
#print axioms Poincare.L4.PointedGH.euclideanPointedCoupling_nonempty
#print axioms Poincare.L4.PointedGH.euclidean_ghDist_tendsto
#print axioms Poincare.L4.PointedGH.euclidean_basepoint_tendsto
#print axioms Poincare.L4.PointedGH.gridx
#print axioms Poincare.L4.PointedGH.gridxLim
#print axioms Poincare.L4.PointedGH.gridPointedCoupling
#print axioms Poincare.L4.PointedGH.gridPointedCoupling_nonempty
#print axioms Poincare.L4.PointedGH.grid_ghDist_tendsto
#print axioms Poincare.L4.PointedGH.grid_basepoint_tendsto
#print axioms Poincare.L4.PointedGH.grid_pointed_subseq
#print axioms Poincare.L4.PointedGH.euclidX_basepoint_radius
#print axioms Poincare.L4.PointedGH.gridX_card

/-! ### Consumed D12 declarations (provenance: unchanged copies, hash-checked) -/
#print axioms GromovHausdorff.hausdorffDist_optimal
#print axioms Poincare.D12.GeometricCompactness.cover_transfer_of_hausdorffDist_lt
#print axioms Poincare.D12.GeometricCompactness.cover_transfer_of_ghDist
#print axioms Poincare.D12.GeometricCompactness.gh_subseq_of_compact
#print axioms Poincare.D12.GeometricCompactness.gh_subseq_of_uniformCovers
#print axioms Poincare.D12.GeometricCompactness.gh_subseq_of_familyBounds
#print axioms Poincare.D12.GeometricCompactness.gridFamily_totallyBounded
#print axioms Poincare.D12.GeometricCompactness.hausdorffDist_grid_square_le
