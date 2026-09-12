/- Independent reviewer axiom audit (scratch) -/
import Poincare.L4.Compactness.FamilyCovers
import Poincare.L4.Compactness.FamilyCoversWitness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

namespace ReviewerAudit

def familyCoversDecls : List Name := [
  ``Poincare.L4.Compactness.exists_finset_ball_cover_card_le_of_coveringNumber_le,
  ``Poincare.L4.Compactness.exists_set_ball_cover_card_le_of_coveringNumber_le,
  ``Poincare.L4.Compactness.exists_div_pow_two_le,
  ``Poincare.L4.Compactness.coveringNumber_univ_le_of_uniformDoubling,
  ``Poincare.L4.Compactness.uniformCovers_of_uniformDoubling,
  ``Poincare.L4.Compactness.uniformCovers_of_uniformDoubling_familyScale,
  ``Poincare.L4.Compactness.coveringNumber_univ_le_of_ghDist_lt_of_familyDoubling,
  ``Poincare.L4.Compactness.totallyBounded_of_uniformDoubling,
  ``Poincare.L4.Compactness.isCompact_of_uniformDoubling
]

def witnessDecls : List Name := [
  ``Poincare.L4.Compactness.Disc,
  ``Poincare.L4.Compactness.Disc.instTopologicalSpace,
  ``Poincare.L4.Compactness.Disc.instDiscreteTopology,
  ``Poincare.L4.Compactness.Disc.instDecidableEq,
  ``Poincare.L4.Compactness.Disc.instFintype,
  ``Poincare.L4.Compactness.Disc.instNonempty,
  ``Poincare.L4.Compactness.Disc.d,
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
  ``Poincare.L4.Compactness.not_uniformDoubling_allDiscFamily
]

def approved : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]

run_cmd do
  let env ← getEnv
  let mut failures : Array String := #[]
  let mut audited : Nat := 0
  for n in familyCoversDecls ++ witnessDecls do
    unless env.contains n do
      failures := failures.push ("MISSING " ++ toString n)
      continue
    let axs ← Lean.collectAxioms n
    audited := audited + 1
    let bad := axs.filter (fun a => !approved.contains a)
    if !bad.isEmpty then
      failures := failures.push ("BAD " ++ toString n ++ " : " ++ toString (bad.toList.map Name.toString))
    logInfo (toString n ++ " CONE = " ++ toString (axs.toList.map Name.toString))
  logInfo ("REVIEWER-AUDIT declarations audited: " ++ toString audited)
  if failures.isEmpty then
    logInfo "REVIEWER-AUDIT: PASS"
  else
    for f in failures do logError f
    throwError "REVIEWER-AUDIT: FAIL"

/- raw #print axioms on every declaration -/
#print axioms Poincare.L4.Compactness.exists_finset_ball_cover_card_le_of_coveringNumber_le
#print axioms Poincare.L4.Compactness.exists_set_ball_cover_card_le_of_coveringNumber_le
#print axioms Poincare.L4.Compactness.exists_div_pow_two_le
#print axioms Poincare.L4.Compactness.coveringNumber_univ_le_of_uniformDoubling
#print axioms Poincare.L4.Compactness.uniformCovers_of_uniformDoubling
#print axioms Poincare.L4.Compactness.uniformCovers_of_uniformDoubling_familyScale
#print axioms Poincare.L4.Compactness.coveringNumber_univ_le_of_ghDist_lt_of_familyDoubling
#print axioms Poincare.L4.Compactness.totallyBounded_of_uniformDoubling
#print axioms Poincare.L4.Compactness.isCompact_of_uniformDoubling
#print axioms Poincare.L4.Compactness.Disc
#print axioms Poincare.L4.Compactness.Disc.instTopologicalSpace
#print axioms Poincare.L4.Compactness.Disc.instDiscreteTopology
#print axioms Poincare.L4.Compactness.Disc.instDecidableEq
#print axioms Poincare.L4.Compactness.Disc.instFintype
#print axioms Poincare.L4.Compactness.Disc.instNonempty
#print axioms Poincare.L4.Compactness.Disc.d
#print axioms Poincare.L4.Compactness.Disc.instMetricSpace
#print axioms Poincare.L4.Compactness.Disc.dist_def
#print axioms Poincare.L4.Compactness.Disc.dist_eq_zero
#print axioms Poincare.L4.Compactness.Disc.dist_eq_one
#print axioms Poincare.L4.Compactness.Disc.dist_le_one
#print axioms Poincare.L4.Compactness.Disc.closedBall_eq_univ
#print axioms Poincare.L4.Compactness.Disc.ball_one_eq_singleton
#print axioms Poincare.L4.Compactness.Disc.ball_half_eq_singleton
#print axioms Poincare.L4.Compactness.Disc.encard_le_of_univ_subset_ball_half_cover
#print axioms Poincare.L4.Compactness.discGH
#print axioms Poincare.L4.Compactness.finiteDiscFamily
#print axioms Poincare.L4.Compactness.allDiscFamily
#print axioms Poincare.L4.Compactness.mem_finiteDiscFamily
#print axioms Poincare.L4.Compactness.mem_allDiscFamily
#print axioms Poincare.L4.Compactness.finiteDiscFamily_subset_allDiscFamily
#print axioms Poincare.L4.Compactness.discGH_injective
#print axioms Poincare.L4.Compactness.finiteDiscFamily_finite
#print axioms Poincare.L4.Compactness.finiteDiscFamily_nonempty
#print axioms Poincare.L4.Compactness.discGH_rep_isometryEquiv
#print axioms Poincare.L4.Compactness.encard_univ_rep_discGH
#print axioms Poincare.L4.Compactness.cardinal_mk_univ_rep_discGH
#print axioms Poincare.L4.Compactness.cardinal_mk_univ_disc
#print axioms Poincare.L4.Compactness.coveringNumber_closedBall_discGH_le
#print axioms Poincare.L4.Compactness.discGH_scale
#print axioms Poincare.L4.Compactness.finiteDiscFamily_doubling
#print axioms Poincare.L4.Compactness.finiteDiscFamily_scale
#print axioms Poincare.L4.Compactness.finiteDiscFamily_hypotheses
#print axioms Poincare.L4.Compactness.finiteDiscFamily_coveringNumber_quarter
#print axioms Poincare.L4.Compactness.finiteDiscFamily_uniformCovers_half_explicit
#print axioms Poincare.L4.Compactness.finiteDiscFamily_cover_half_card_ge
#print axioms Poincare.L4.Compactness.finiteDiscFamily_uniformCovers_half
#print axioms Poincare.L4.Compactness.totallyBounded_finiteDiscFamily
#print axioms Poincare.L4.Compactness.isCompact_finiteDiscFamily
#print axioms Poincare.L4.Compactness.exists_ball_cover_card_le_of_isometryEquiv
#print axioms Poincare.L4.Compactness.allDiscFamily_scale
#print axioms Poincare.L4.Compactness.not_uniformCovers_allDiscFamily
#print axioms Poincare.L4.Compactness.not_uniformDoubling_allDiscFamily
