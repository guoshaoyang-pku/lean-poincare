/-
  scratch/review_circle_audit.lean  —  adversarial review of
    release/Poincare/L4/Compactness/MeasureGrowthChainCircle.lean        (unit circle)
    release/Poincare/L4/Compactness/MeasureGrowthChainCircleFamily.lean  (all T ∈ [1,2])
  (NOT part of release/; compiled with an absolute path from the release dir)

  Contents:
  * `#print axioms` for the public top-level declarations of both modules;
  * a per-declaration axiom dump for EVERY declaration of both modules (obtained by
    enumerating the modules' constants through the environment API, which also covers
    the mangled `_private.*` names and `_proof_*` auxiliaries);
  * a transitive constant-dependency-closure scan of the public declarations of both
    modules, checking that no statement-only D12 frontier Prop occurs anywhere in the
    closure and that no `sorry` constant occurs;
  * an environment-level union of the axiom sets of both modules.
-/
import Poincare.L4.Compactness.MeasureGrowthChainCircleFamily
import Lean

open Lean

namespace ReviewCircleAudit

/-- Transitive closure of constants reachable from `roots` through types and values. -/
partial def closure (env : Environment) (fuel : Nat) (work : List Name)
    (seen : Std.HashSet Name) : Std.HashSet Name :=
  match fuel with
  | 0 => seen
  | fuel + 1 =>
    match work with
    | [] => seen
    | n :: rest =>
      if seen.contains n then closure env fuel rest seen
      else
        let seen := seen.insert n
        let more : List Name :=
          match env.find? n with
          | none => []
          | some ci =>
            ci.type.getUsedConstants.toList ++
              (match ci.value? with
               | some v => v.getUsedConstants.toList
               | none => [])
        closure env fuel (more ++ rest) seen

/-- All constants whose defining module is the one containing `root`. -/
def moduleDecls (env : Environment) (root : Name) : List Name :=
  match env.getModuleIdxFor? root with
  | none => []
  | some idx =>
    env.constants.toList.filterMap (fun (n, _) =>
      if env.getModuleIdxFor? n == some idx then some n else none)

end ReviewCircleAudit

open ReviewCircleAudit

-- =====================================================================
-- 1. Axiom audit: public declarations of the unit-circle module
-- =====================================================================

section Axioms

#print axioms Poincare.L4.Compactness.instFactLtRealOfNat_poincare
#print axioms Poincare.L4.Compactness.circleEquiv
#print axioms Poincare.L4.Compactness.circleZero
#print axioms Poincare.L4.Compactness.circleMeasure
#print axioms Poincare.L4.Compactness.circleMeasure_closedBall
#print axioms Poincare.L4.Compactness.circleMeasure_univ
#print axioms Poincare.L4.Compactness.circleMeasureOf
#print axioms Poincare.L4.Compactness.circleMeasureOf_apply_member
#print axioms Poincare.L4.Compactness.circle_norm_le_one
#print axioms Poincare.L4.Compactness.circle_dist_le_one
#print axioms Poincare.L4.Compactness.circle_m_pos
#print axioms Poincare.L4.Compactness.circle_toNNReal_eq_of_pos
#print axioms Poincare.L4.Compactness.circleGrowth
#print axioms Poincare.L4.Compactness.circleGrowth_measure_varies
#print axioms Poincare.L4.Compactness.totallyBounded_circle
#print axioms Poincare.L4.Compactness.isCompact_circle
#print axioms Poincare.L4.Compactness.exists_pointed_subseq_circle

-- =====================================================================
-- 1b. Axiom audit: public declarations of the T-family module
-- =====================================================================

#print axioms Poincare.L4.Compactness.circleEquivT
#print axioms Poincare.L4.Compactness.circleMeasureT
#print axioms Poincare.L4.Compactness.circleMeasureT_closedBall
#print axioms Poincare.L4.Compactness.circleMeasureT_univ
#print axioms Poincare.L4.Compactness.circleMeasureTOf
#print axioms Poincare.L4.Compactness.circleMeasureTOf_apply_member
#print axioms Poincare.L4.Compactness.circleT_norm_le
#print axioms Poincare.L4.Compactness.circleT_dist_le
#print axioms Poincare.L4.Compactness.circleGrowthT
#print axioms Poincare.L4.Compactness.circleGrowthT_constants
#print axioms Poincare.L4.Compactness.circleGrowthT_measure_varies
#print axioms Poincare.L4.Compactness.totallyBounded_circleT
#print axioms Poincare.L4.Compactness.isCompact_circleT
#print axioms Poincare.L4.Compactness.exists_pointed_subseq_circleT

end Axioms

-- =====================================================================
-- 1c. Per-declaration axioms for every constant of both modules
-- =====================================================================

run_cmd do
  let env ← getEnv
  for root in [`Poincare.L4.Compactness.circleEquiv,
               `Poincare.L4.Compactness.circleEquivT] do
    let modNames := moduleDecls env root
    IO.println s!"PER-DECL AXIOMS for module of {root} ({modNames.length} decls):"
    for n in modNames do
      let a ← Lean.collectAxioms n
      IO.println s!"  {n} :: {a.toList}"

-- =====================================================================
-- 2. Dependency-closure scan for statement-only D12 frontier Props
-- =====================================================================

run_cmd do
  let env ← getEnv
  let roots : List Name :=
    [ -- unit circle module
      `Poincare.L4.Compactness.circleEquiv
    , `Poincare.L4.Compactness.circleMeasure
    , `Poincare.L4.Compactness.circleMeasure_closedBall
    , `Poincare.L4.Compactness.circleMeasure_univ
    , `Poincare.L4.Compactness.circleMeasureOf
    , `Poincare.L4.Compactness.circle_norm_le_one
    , `Poincare.L4.Compactness.circle_dist_le_one
    , `Poincare.L4.Compactness.circleGrowth
    , `Poincare.L4.Compactness.circleGrowth_measure_varies
    , `Poincare.L4.Compactness.totallyBounded_circle
    , `Poincare.L4.Compactness.isCompact_circle
    , `Poincare.L4.Compactness.exists_pointed_subseq_circle
      -- T-family module
    , `Poincare.L4.Compactness.circleEquivT
    , `Poincare.L4.Compactness.circleMeasureT
    , `Poincare.L4.Compactness.circleMeasureT_closedBall
    , `Poincare.L4.Compactness.circleMeasureT_univ
    , `Poincare.L4.Compactness.circleMeasureTOf
    , `Poincare.L4.Compactness.circleT_norm_le
    , `Poincare.L4.Compactness.circleT_dist_le
    , `Poincare.L4.Compactness.circleGrowthT
    , `Poincare.L4.Compactness.circleGrowthT_constants
    , `Poincare.L4.Compactness.circleGrowthT_measure_varies
    , `Poincare.L4.Compactness.totallyBounded_circleT
    , `Poincare.L4.Compactness.isCompact_circleT
    , `Poincare.L4.Compactness.exists_pointed_subseq_circleT ]
  let cl := closure env 5000000 roots {}
  IO.println s!"CLOSURE SIZE (constants reachable from the 26 public declarations): {cl.size}"
  let frontier : List String :=
    [ "curvatureBoundImpliesUniformCovers", "cheegerGromovCompactness"
    , "bishopGromovVolumeComparison", "harmonicCoordinatesExistence"
    , "gromovCriterion", "ancientKappaCompactnessFrontier"
    , "canonicalNeighborhoodFrontier" ]
  let hits := cl.toList.filter (fun n => frontier.any (fun f => n.toString.contains f))
  IO.println s!"FRONTIER-PROP HITS: {hits}"
  IO.println s!"SORRY HITS: {cl.toList.filter (fun n => n.toString.contains "sorry")}"

-- =====================================================================
-- 3. Union of axioms over every declaration of both modules
-- =====================================================================

run_cmd do
  let env ← getEnv
  let mut axs : Std.HashSet Name := {}
  let mut total := 0
  for root in [`Poincare.L4.Compactness.circleEquiv,
               `Poincare.L4.Compactness.circleEquivT] do
    for n in moduleDecls env root do
      total := total + 1
      let a ← Lean.collectAxioms n
      for x in a do axs := axs.insert x
  IO.println s!"UNION OF AXIOMS OVER ALL {total} MODULE DECLS: {axs.toList}"
