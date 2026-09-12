import Poincare.L4.Compactness.MeasureGrowthChainWitness
import Lean.Util.FoldConsts

open Lean

/- Kernel axiom audit for `MeasureGrowthChainWitness`. -/
#print axioms Poincare.L4.Compactness.dZero
#print axioms Poincare.L4.Compactness.dOne
#print axioms Poincare.L4.Compactness.dZero_ne_dOne
#print axioms Poincare.L4.Compactness.twoPointEquiv
#print axioms Poincare.L4.Compactness.twoPointZero
#print axioms Poincare.L4.Compactness.twoPointOne
#print axioms Poincare.L4.Compactness.twoPointEquiv_twoPointZero
#print axioms Poincare.L4.Compactness.twoPointEquiv_twoPointOne
#print axioms Poincare.L4.Compactness.twoPointZero_ne_one
#print axioms Poincare.L4.Compactness.dist_twoPointZero_twoPointOne
#print axioms Poincare.L4.Compactness.twoPoint_eq_zero_or_one
#print axioms Poincare.L4.Compactness.twoPointMeasure
#print axioms Poincare.L4.Compactness.twoPointMeasure_apply
#print axioms Poincare.L4.Compactness.twoPointMeasure_closedBall
#print axioms Poincare.L4.Compactness.twoPointMeasureOf
#print axioms Poincare.L4.Compactness.two_mul_half
#print axioms Poincare.L4.Compactness.half_le_two_mul_half
#print axioms Poincare.L4.Compactness.one_le_two_mul_half
#print axioms Poincare.L4.Compactness.one_le_two_mul_one
#print axioms Poincare.L4.Compactness.coe_half
#print axioms Poincare.L4.Compactness.half_le_two_mul_half_nn
#print axioms Poincare.L4.Compactness.one_le_two_mul_half_nn
#print axioms Poincare.L4.Compactness.half_le_two_mul_half_nn'
#print axioms Poincare.L4.Compactness.twoPointMeasureOf_apply_member
#print axioms Poincare.L4.Compactness.twoPointGrowth
#print axioms Poincare.L4.Compactness.twoPointGrowth_nondegenerate
#print axioms Poincare.L4.Compactness.twoPointGrowth_doublingConstant
#print axioms Poincare.L4.Compactness.totallyBounded_twoPoint
#print axioms Poincare.L4.Compactness.isCompact_twoPoint
#print axioms Poincare.L4.Compactness.exists_pointed_subseq_twoPoint

/-- Transitive constant-dependency closure of a declaration (types + values). -/
partial def reachAux (env : Environment) (work : List Name) (acc : NameSet) : NameSet :=
  match work with
  | [] => acc
  | n :: rest =>
    if acc.contains n then reachAux env rest acc
    else
      let acc := acc.insert n
      match env.find? n with
      | none => reachAux env rest acc
      | some ci => reachAux env (ci.getUsedConstantsAsSet.toList ++ rest) acc

run_cmd do
  let env ← getEnv
  let roots : List Name := [
    `Poincare.L4.Compactness.dZero,
    `Poincare.L4.Compactness.twoPointEquiv,
    `Poincare.L4.Compactness.twoPoint_eq_zero_or_one,
    `Poincare.L4.Compactness.twoPointMeasure,
    `Poincare.L4.Compactness.twoPointMeasure_apply,
    `Poincare.L4.Compactness.twoPointMeasure_closedBall,
    `Poincare.L4.Compactness.twoPointMeasureOf,
    `Poincare.L4.Compactness.twoPointMeasureOf_apply_member,
    `Poincare.L4.Compactness.twoPointGrowth,
    `Poincare.L4.Compactness.twoPointGrowth_nondegenerate,
    `Poincare.L4.Compactness.twoPointGrowth_doublingConstant,
    `Poincare.L4.Compactness.totallyBounded_twoPoint,
    `Poincare.L4.Compactness.isCompact_twoPoint,
    `Poincare.L4.Compactness.exists_pointed_subseq_twoPoint
  ]
  let forbidden : List Name := [
    `Poincare.D12.GeometricCompactness.curvatureBoundImpliesUniformCovers,
    `Poincare.D12.GeometricCompactness.cheegerGromovCompactness,
    `Poincare.D12.GeometricCompactness.bishopGromovVolumeComparison,
    `Poincare.D12.GeometricCompactness.harmonicCoordinatesExistence,
    `Poincare.D12.GeometricCompactness.gromovCriterion
  ]
  let mut totalHits : Nat := 0
  let mut frontierConsts : NameSet := {}
  let mut union : NameSet := {}
  for r in roots do
    let s := reachAux env [r] {}
    for f in forbidden do
      if s.contains f then
        totalHits := totalHits + 1
        IO.println s!"HIT: {r} transitively uses {f}"
    for c in s.toList do
      union := union.insert c
      if (`Poincare.D12.GeometricCompactness.Frontier).isPrefixOf c then
        frontierConsts := frontierConsts.insert c
  IO.println s!"witness FORBIDDEN HITS: {totalHits}"
  IO.println s!"witness Frontier-declared constants reachable: {frontierConsts.size}"
  for c in frontierConsts.toList do
    IO.println s!"  frontier-const: {c}"
  IO.println s!"witness sorryAx reachable: {union.contains `sorryAx}"
