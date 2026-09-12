import Poincare.L4.Compactness.MeasureGrowthChain
import Lean.Util.FoldConsts

open Lean

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

def reach (env : Environment) (root : Name) : NameSet := reachAux env [root] {}

run_cmd do
  let env ← getEnv
  let roots : List Name := [
    `Poincare.L4.Compactness.instMeasurableSpaceGHSpaceRep,
    `Poincare.L4.Compactness.instBorelSpaceGHSpaceRep,
    `Poincare.L4.Compactness.UniformMeasureGrowth,
    `Poincare.L4.Compactness.UniformMeasureGrowth.coveringNumber_le,
    `Poincare.L4.Compactness.UniformMeasureGrowth.doublingConstant,
    `Poincare.L4.Compactness.UniformMeasureGrowth.coveringNumber_le_doublingConstant,
    `Poincare.L4.Compactness.totallyBounded_of_uniformMeasureGrowth,
    `Poincare.L4.Compactness.isCompact_of_uniformMeasureGrowth,
    `Poincare.L4.Compactness.exists_pointed_subseq_of_uniformMeasureGrowth,
    `Poincare.L4.Compactness.subsingletonGHSpaceRepPUnit,
    `Poincare.L4.Compactness.dirac_closedBall_of_subsingleton,
    `Poincare.L4.Compactness.punitGrowth,
    `Poincare.L4.Compactness.punitGrowth_measure_varies,
    `Poincare.L4.Compactness.totallyBounded_punit,
    `Poincare.L4.Compactness.isCompact_punit,
    `Poincare.L4.Compactness.exists_pointed_subseq_punit
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
  for r in roots do
    let s := reach env r
    for f in forbidden do
      if s.contains f then
        totalHits := totalHits + 1
        IO.println s!"HIT: {r} transitively uses {f}"
    for c in s.toList do
      if (`Poincare.D12.GeometricCompactness.Frontier).isPrefixOf c then
        frontierConsts := frontierConsts.insert c
    IO.println s!"closure size of {r}: {s.size}"
  IO.println s!"FORBIDDEN HITS: {totalHits}"
  IO.println s!"Frontier-declared constants reachable from roots: {frontierConsts.size}"
  for c in frontierConsts.toList do
    IO.println s!"  frontier-const: {c}"
  -- also: is sorryAx anywhere in the union closure?
  let mut union : NameSet := {}
  for r in roots do
    for c in (reach env r).toList do union := union.insert c
  IO.println s!"sorryAx reachable: {union.contains `sorryAx}"
  IO.println s!"union closure size: {union.size}"
