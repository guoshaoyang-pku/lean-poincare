/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4-child-gh-family-covers — per-declaration kernel axiom audit

Fail-closed dependency audit for every declaration authored by this task
(`Poincare/L4/Compactness/FamilyCovers.lean` and
`Poincare/L4/Compactness/FamilyCoversWitness.lean`), plus the consumed upstream
declarations (the round-3 pair-level theorem and the D12 compactness criterion).

The audit runs `Lean.collectAxioms` on each target and fails if any transitive
axiom is outside `{propext, Classical.choice, Quot.sound}` — this catches
`sorryAx`, `native_decide`'s generated axiom, `Lean.trustCompiler` and any
project `axiom`.  It also fails if a target declaration is missing or if the
module import fails.

Run from the release directory:

    lake env lean Audit/L4FamilyCoversAxiomAudit.lean

Expected last line: `L4FamilyCoversAxiomAudit: PASS`.
-/
import Poincare.L4.Compactness.FamilyCovers
import Poincare.L4.Compactness.FamilyCoversWitness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

namespace L4FamilyCoversAxiomAudit

/-! ## Raw `#print axioms` output for the headline results -/

#print axioms Poincare.L4.Compactness.exists_finset_ball_cover_card_le_of_coveringNumber_le
#print axioms Poincare.L4.Compactness.exists_set_ball_cover_card_le_of_coveringNumber_le
#print axioms Poincare.L4.Compactness.coveringNumber_univ_le_of_uniformDoubling
#print axioms Poincare.L4.Compactness.uniformCovers_of_uniformDoubling
#print axioms Poincare.L4.Compactness.uniformCovers_of_uniformDoubling_familyScale
#print axioms Poincare.L4.Compactness.coveringNumber_univ_le_of_ghDist_lt_of_familyDoubling
#print axioms Poincare.L4.Compactness.totallyBounded_of_uniformDoubling
#print axioms Poincare.L4.Compactness.isCompact_of_uniformDoubling
#print axioms Poincare.L4.Compactness.finiteDiscFamily_hypotheses
#print axioms Poincare.L4.Compactness.finiteDiscFamily_coveringNumber_quarter
#print axioms Poincare.L4.Compactness.not_uniformCovers_allDiscFamily
#print axioms Poincare.L4.Compactness.not_uniformDoubling_allDiscFamily

/-- The only axioms accepted in a dependency cone. -/
def approvedAxioms : List Name :=
  ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]

/-- Authored `Poincare/L4/Compactness/FamilyCovers.lean` declarations. -/
def familyCoversDecls : List Name :=
  [``Poincare.L4.Compactness.exists_finset_ball_cover_card_le_of_coveringNumber_le,
   ``Poincare.L4.Compactness.exists_set_ball_cover_card_le_of_coveringNumber_le,
   ``Poincare.L4.Compactness.exists_div_pow_two_le,
   ``Poincare.L4.Compactness.coveringNumber_univ_le_of_uniformDoubling,
   ``Poincare.L4.Compactness.uniformCovers_of_uniformDoubling,
   ``Poincare.L4.Compactness.uniformCovers_of_uniformDoubling_familyScale,
   ``Poincare.L4.Compactness.coveringNumber_univ_le_of_ghDist_lt_of_familyDoubling,
   ``Poincare.L4.Compactness.totallyBounded_of_uniformDoubling,
   ``Poincare.L4.Compactness.isCompact_of_uniformDoubling]

/-- Authored `Poincare/L4/Compactness/FamilyCoversWitness.lean` declarations. -/
def witnessDecls : List Name :=
  [``Poincare.L4.Compactness.Disc,
   ``Poincare.L4.Compactness.Disc.instMetricSpace,
   ``Poincare.L4.Compactness.Disc.dist_def,
   ``Poincare.L4.Compactness.Disc.dist_eq_zero,
   ``Poincare.L4.Compactness.Disc.dist_eq_one,
   ``Poincare.L4.Compactness.Disc.dist_le_one,
   ``Poincare.L4.Compactness.Disc.closedBall_eq_univ,
   ``Poincare.L4.Compactness.Disc.ball_one_eq_singleton,
   ``Poincare.L4.Compactness.Disc.ball_half_eq_singleton,
   ``Poincare.L4.Compactness.Disc.encard_le_of_univ_subset_ball_half_cover,
   ``Poincare.L4.Compactness.discGH,
   ``Poincare.L4.Compactness.finiteDiscFamily,
   ``Poincare.L4.Compactness.allDiscFamily,
   ``Poincare.L4.Compactness.mem_finiteDiscFamily,
   ``Poincare.L4.Compactness.mem_allDiscFamily,
   ``Poincare.L4.Compactness.finiteDiscFamily_subset_allDiscFamily,
   ``Poincare.L4.Compactness.discGH_injective,
   ``Poincare.L4.Compactness.finiteDiscFamily_finite,
   ``Poincare.L4.Compactness.finiteDiscFamily_nonempty,
   ``Poincare.L4.Compactness.discGH_rep_isometryEquiv,
   ``Poincare.L4.Compactness.encard_univ_rep_discGH,
   ``Poincare.L4.Compactness.cardinal_mk_univ_rep_discGH,
   ``Poincare.L4.Compactness.cardinal_mk_univ_disc,
   ``Poincare.L4.Compactness.coveringNumber_closedBall_discGH_le,
   ``Poincare.L4.Compactness.discGH_scale,
   ``Poincare.L4.Compactness.finiteDiscFamily_doubling,
   ``Poincare.L4.Compactness.finiteDiscFamily_scale,
   ``Poincare.L4.Compactness.finiteDiscFamily_hypotheses,
   ``Poincare.L4.Compactness.finiteDiscFamily_coveringNumber_quarter,
   ``Poincare.L4.Compactness.finiteDiscFamily_uniformCovers_half_explicit,
   ``Poincare.L4.Compactness.finiteDiscFamily_cover_half_card_ge,
   ``Poincare.L4.Compactness.finiteDiscFamily_uniformCovers_half,
   ``Poincare.L4.Compactness.totallyBounded_finiteDiscFamily,
   ``Poincare.L4.Compactness.isCompact_finiteDiscFamily,
   ``Poincare.L4.Compactness.exists_ball_cover_card_le_of_isometryEquiv,
   ``Poincare.L4.Compactness.allDiscFamily_scale,
   ``Poincare.L4.Compactness.not_uniformCovers_allDiscFamily,
   ``Poincare.L4.Compactness.not_uniformDoubling_allDiscFamily]

/-- Consumed upstream declarations (re-audited here). -/
def consumedDecls : List Name :=
  [``Poincare.L4.Compactness.coveringNumber_le_of_ghDist_lt,
   ``Poincare.L4.Compactness.coveringNumber_univ_le_of_ghDist_lt_of_doubling,
   ``Poincare.L4.Compactness.coveringNumber_le_of_doubling,
   ``Poincare.L4.Compactness.coveringNumber_le_of_doubling_of_le,
   ``Poincare.L4.Compactness.exists_finset_isCover_card_le,
   ``Poincare.D12.GeometricCompactness.uniformCovers_of_totallyBounded,
   ``Poincare.D12.GeometricCompactness.totallyBounded_iff_uniformCovers,
   ``Poincare.D12.GeometricCompactness.isCompact_of_uniformCovers]

def allTargets : List Name :=
  familyCoversDecls ++ witnessDecls ++ consumedDecls

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
  logInfo m!"L4FamilyCoversAxiomAudit: declarations audited: {audited}"
  if failures.isEmpty then
    logInfo "L4FamilyCoversAxiomAudit: PASS — every cone is contained in propext, \
      Classical.choice, Quot.sound"
  else
    for f in failures do
      logError m!"{f}"
    throwError "L4FamilyCoversAxiomAudit: FAIL — forbidden dependency in an \
      L4-child-gh-family-covers cone"

end L4FamilyCoversAxiomAudit
