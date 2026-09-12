/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4-C3 — per-declaration kernel axiom audit

Fail-closed dependency audit for every declaration authored by the L4-C3 task
(`Poincare/L4/DoublingToCovers/`), plus the D12 interface declarations it consumes.

The audit runs `Lean.collectAxioms` on each target and fails if any transitive axiom is
outside `{propext, Classical.choice, Quot.sound}` (this also catches `sorryAx`,
`native_decide`'s `ofReduceBool`, `Lean.trustCompiler` and any project `axiom`).

Run from the release directory:

    lake env lean Audit/L4C3AxiomAudit.lean

Expected last line: `L4C3AxiomAudit: PASS`.
-/
import Poincare.L4.DoublingToCovers.Bridge
import Poincare.L4.DoublingToCovers.Counterexample
import Poincare.L4.DoublingToCovers.Consumption
import Poincare.L4.DoublingToCovers.EuclideanWitness
import Poincare.L4.DoublingToCovers.Sharpness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

namespace L4C3AxiomAudit

/-! ## Raw `#print axioms` output for the headline results

The programmatic fail-closed audit below covers every declaration; these commands record the
kernel's own `#print axioms` output in `evidence/l4c3-axiom-audit.log`. -/

#print axioms Poincare.L4.DoublingToCovers.card_le_of_pairwise_dist_ge
#print axioms Poincare.L4.DoublingToCovers.coveringNumber_closedBall_le_of_doubling
#print axioms Poincare.L4.DoublingToCovers.card_le_of_ratio
#print axioms Poincare.L4.DoublingToCovers.Disc.instIsUnifLocDoublingMeasure
#print axioms Poincare.L4.DoublingToCovers.Disc.coveringNumber_univ
#print axioms Poincare.L4.DoublingToCovers.diam_discreteFamily
#print axioms Poincare.L4.DoublingToCovers.not_uniformCovers_discreteFamily_at
#print axioms Poincare.L4.DoublingToCovers.not_totallyBounded_discreteFamily
#print axioms Poincare.L4.DoublingToCovers.uniformCovers_of_ratio_data
#print axioms Poincare.L4.DoublingToCovers.isCompact_of_ratio_data
#print axioms Poincare.L4.DoublingToCovers.gh_subseq_of_ratio_data
#print axioms Poincare.L4.DoublingToCovers.coveringNumber_unitBall_real_le
#print axioms Poincare.L4.DoublingToCovers.Disc.card_le_of_uniform_ratio
#print axioms Poincare.L4.DoublingToCovers.Disc.count_ratio_data_sharp
#print axioms Poincare.L4.DoublingToCovers.not_uniformRatioData_discreteFamily_at
#print axioms Poincare.L4.DoublingToCovers.not_uniformRatioData_discreteFamily
#print axioms Poincare.L4.DoublingToCovers.uniformCovers_of_ratio_data_hypothesis_fails
#print axioms Poincare.L4.DoublingToCovers.exists_doubling_coveringNumber_gt
#print axioms Poincare.D12.GeometricCompactness.gromovCriterion
#print axioms Poincare.D12.GeometricCompactness.totallyBounded_iff_uniformCovers


/-- The only axioms accepted in a dependency cone. -/
def approvedAxioms : List Name :=
  ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]

/-- Authored `Poincare/L4/DoublingToCovers/Bridge.lean` declarations. -/
def bridgeDecls : List Name :=
  [``Poincare.L4.DoublingToCovers.encard_le_of_forall_finset_card_le,
   ``Poincare.L4.DoublingToCovers.card_le_of_pairwise_dist_ge,
   ``Poincare.L4.DoublingToCovers.packingNumber_closedBall_le_of_doubling,
   ``Poincare.L4.DoublingToCovers.exists_packingNumber_closedBall_le_of_doubling,
   ``Poincare.L4.DoublingToCovers.coveringNumber_closedBall_le_of_doubling,
   ``Poincare.L4.DoublingToCovers.exists_coveringNumber_closedBall_le_of_doubling,
   ``Poincare.L4.DoublingToCovers.exists_cover_of_packingNumber_le,
   ``Poincare.L4.DoublingToCovers.exists_cover_ball_of_doubling,
   ``Poincare.L4.DoublingToCovers.exists_radius_cover_ball_of_doubling,
   ``Poincare.L4.DoublingToCovers.card_le_of_ratio,
   ``Poincare.L4.DoublingToCovers.packingNumber_closedBall_le_of_ratio,
   ``Poincare.L4.DoublingToCovers.coveringNumber_closedBall_le_of_ratio,
   ``Poincare.L4.DoublingToCovers.exists_cover_ball_of_ratio]

/-- Authored `Poincare/L4/DoublingToCovers/Counterexample.lean` declarations. -/
def counterexampleDecls : List Name :=
  [``Poincare.L4.DoublingToCovers.Disc,
   ``Poincare.L4.DoublingToCovers.Disc.instMetricSpace,
   ``Poincare.L4.DoublingToCovers.Disc.instIsUnifLocDoublingMeasure,
   ``Poincare.L4.DoublingToCovers.Disc.dist_def,
   ``Poincare.L4.DoublingToCovers.Disc.dist_eq_zero,
   ``Poincare.L4.DoublingToCovers.Disc.dist_eq_one,
   ``Poincare.L4.DoublingToCovers.Disc.dist_le_one,
   ``Poincare.L4.DoublingToCovers.Disc.closedBall_eq_singleton,
   ``Poincare.L4.DoublingToCovers.Disc.closedBall_eq_univ,
   ``Poincare.L4.DoublingToCovers.Disc.coveringNumber_univ,
   ``Poincare.L4.DoublingToCovers.map_isometryEquiv_closedBall,
   ``Poincare.L4.DoublingToCovers.isUnifLocDoublingMeasure_map_isometryEquiv,
   ``Poincare.L4.DoublingToCovers.exists_doubling_measure_discreteFamily,
   ``Poincare.L4.DoublingToCovers.discreteFamily,
   ``Poincare.L4.DoublingToCovers.mem_discreteFamily,
   ``Poincare.L4.DoublingToCovers.diam_discreteFamily,
   ``Poincare.L4.DoublingToCovers.isometry_doubling_discreteFamily,
   ``Poincare.L4.DoublingToCovers.not_uniformCovers_discreteFamily_at,
   ``Poincare.L4.DoublingToCovers.not_uniformCovers_discreteFamily,
   ``Poincare.L4.DoublingToCovers.not_totallyBounded_discreteFamily]

/-- Authored `Poincare/L4/DoublingToCovers/Consumption.lean` declarations. -/
def consumptionDecls : List Name :=
  [``Poincare.L4.DoublingToCovers.instMeasurableSpaceRep,
   ``Poincare.L4.DoublingToCovers.instBorelSpaceRep,
   ``Poincare.L4.DoublingToCovers.exists_cover_univ_of_ratio,
   ``Poincare.L4.DoublingToCovers.uniformCovers_of_ratio_data,
   ``Poincare.L4.DoublingToCovers.isCompact_of_ratio_data,
   ``Poincare.L4.DoublingToCovers.gh_subseq_of_ratio_data,
   ``Poincare.L4.DoublingToCovers.uniform_local_doubling_not_uniformCovers,
   ``Poincare.L4.DoublingToCovers.discreteFamily_not_totallyBounded]

/-- Authored `Poincare/L4/DoublingToCovers/EuclideanWitness.lean` declarations. -/
def euclideanDecls : List Name :=
  [``Poincare.L4.DoublingToCovers.volume_ratio_data,
   ``Poincare.L4.DoublingToCovers.coveringNumber_unitBall_real_le,
   ``Poincare.L4.DoublingToCovers.exists_cover_unitBall_real]

/-- Authored `Poincare/L4/DoublingToCovers/Sharpness.lean` declarations. -/
def sharpnessDecls : List Name :=
  [``Poincare.L4.DoublingToCovers.Disc.measure_univ_eq_sum_singleton,
   ``Poincare.L4.DoublingToCovers.Disc.card_le_of_uniform_ratio,
   ``Poincare.L4.DoublingToCovers.Disc.count_univ,
   ``Poincare.L4.DoublingToCovers.Disc.count_ratio_data_sharp,
   ``Poincare.L4.DoublingToCovers.not_uniformRatioData_discreteFamily_at,
   ``Poincare.L4.DoublingToCovers.not_uniformRatioData_discreteFamily,
   ``Poincare.L4.DoublingToCovers.uniformCovers_of_ratio_data_hypothesis_fails,
   ``Poincare.L4.DoublingToCovers.exists_doubling_coveringNumber_gt]

/-- Consumed D12 interface declarations (imported source claims, re-audited here). -/
def d12Decls : List Name :=
  [``Poincare.D12.GeometricCompactness.cover_transfer_of_ghDist,
   ``Poincare.D12.GeometricCompactness.diam_transfer_of_ghDist,
   ``Poincare.D12.GeometricCompactness.uniformCovers_of_totallyBounded,
   ``Poincare.D12.GeometricCompactness.totallyBounded_iff_uniformCovers,
   ``Poincare.D12.GeometricCompactness.isCompact_of_uniformCovers,
   ``Poincare.D12.GeometricCompactness.gromovCriterion,
   ``Poincare.D12.GeometricCompactness.gh_subseq_of_compact,
   ``Poincare.D12.GeometricCompactness.gh_subseq_of_uniformCovers]

def allTargets : List Name :=
  bridgeDecls ++ counterexampleDecls ++ consumptionDecls ++ euclideanDecls ++ sharpnessDecls ++
    d12Decls

run_cmd do
  let env ← getEnv
  let mut failures : Array String := #[]
  let mut audited : Nat := 0
  for n in allTargets do
    unless env.contains n do
      failures := failures.push s!"missing declaration: {n}"
      continue
    let axs ← Lean.collectAxioms n
    audited := audited + 1
    let bad := axs.filter (fun a => !approvedAxioms.contains a)
    if !bad.isEmpty then
      failures := failures.push
        s!"{n}: UNAPPROVED axioms {bad.toList.map Name.toString}"
    else
      logInfo m!"{n}: axioms {axs.toList.map Name.toString}"
  logInfo m!"L4C3AxiomAudit: declarations audited: {audited}"
  if failures.isEmpty then
    logInfo "L4C3AxiomAudit: PASS — every cone is contained in propext, Classical.choice, Quot.sound"
  else
    for f in failures do
      logError m!"{f}"
    throwError "L4C3AxiomAudit: FAIL — forbidden dependency in an L4-C3 cone"

end L4C3AxiomAudit
