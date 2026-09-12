import Audit.CounterexampleAudit
import Audit.CurvatureODEAudit
import Audit.EvolutionAudit
import Audit.GeometryAudit
import Audit.PromotedEvolutionAudit
import D6AuditReport
import Ledger.DefinitionSmoke
import Ledger.PerelmanDefinitions
import Poincare.Basic
import Poincare.D12.TriangulationTopology.AntipodalQuotient
import Poincare.D12.TriangulationTopology.AxiomAudit
import Poincare.D12.TriangulationTopology.CoveringLemma
import Poincare.D12.TriangulationTopology.DiskGluing
import Poincare.D12.TriangulationTopology.Downstream
import Poincare.D12.TriangulationTopology.HemisphereDisk
import Poincare.D12.TriangulationTopology.MoiseBranch
import Poincare.D12.TriangulationTopology.NegControl.NegControl
import Poincare.D12.TriangulationTopology.SimplexBoundary
import Poincare.D12.TriangulationTopology.SimplexCone
import Poincare.D12.TriangulationTopology.SphereGluing
import Poincare.D12.TriangulationTopology.SphereMissedPoint
import Poincare.D12.TriangulationTopology.SphereOfTwoDisks
import Poincare.D12.TriangulationTopology.SpherePolygonal
import Poincare.D12.TriangulationTopology.SphereRecognition
import Poincare.D12.TriangulationTopology.SphereSimplyConnected
import Poincare.D12.TriangulationTopology.SphereSimplyConnectedMain
import Poincare.D12.TriangulationTopology.TwoHemisphereInstance
import Poincare.Longrun.CurvatureODE
import Poincare.Longrun.CurvatureODE.Bridge
import Poincare.Longrun.CurvatureODE.Evolution
import Poincare.Longrun.CurvatureODE.Invariant
import Poincare.Longrun.CurvatureODE.Monotonicity
import Poincare.Longrun.CurvatureODE.ScalarODE
import Poincare.Longrun.CurvatureODE.State
import Poincare.Longrun.Entropy
import Poincare.Longrun.Entropy.AxiomAudit
import Poincare.Longrun.Entropy.Bridge
import Poincare.Longrun.Entropy.Certificate
import Poincare.Longrun.Entropy.DiscreteHeat
import Poincare.Longrun.Entropy.FiniteGeometry
import Poincare.Longrun.Entropy.Functional
import Poincare.Longrun.Evolution
import Poincare.Longrun.Evolution.Bridge
import Poincare.Longrun.Evolution.Continuous
import Poincare.Longrun.Evolution.Counterexample
import Poincare.Longrun.Evolution.Discrete
import Poincare.Longrun.Evolution.Functional
import Poincare.Longrun.Evolution.Gibbs
import Poincare.Longrun.Geometry
import Poincare.Longrun.Geometry.ConnectionAdapter
import Poincare.Longrun.Geometry.Contraction
import Poincare.Longrun.Geometry.LeviCivitaBlocked
import Poincare.Longrun.Geometry.MetricData
import Poincare.Longrun.PDE.AxiomAudit
import Poincare.Longrun.PDE.ContinuousInterface
import Poincare.Longrun.PDE.DiscreteMaximumPrinciple
import Poincare.Longrun.PDE.Energy
import Poincare.Longrun.PDE.HeatGrid
import Poincare.Longrun.Surgery
import Poincare.Longrun.Surgery.Axioms
import Poincare.Longrun.Surgery.Basic
import Poincare.Longrun.Surgery.Chain
import Poincare.Longrun.Surgery.Missing
import Poincare.Longrun.Surgery.Toy
import Poincare.Longrun.Topology.AxiomAudit
import Poincare.Longrun.Topology.Basic
import Poincare.Longrun.Topology.CompactThreeManifold
import Poincare.Longrun.Topology.MissingTheorems
import Poincare.Longrun.Topology.Noncollapsing
import Poincare.Longrun.Topology.NormalizedVolume
import Poincare.Longrun.Topology.Stage6Bridge
import Poincare.Stage1.CurvatureAlgebra
import Poincare.Stage1.RiemannAdapter
import Poincare.Stage6.SphereSimplyConnected
import Poincare.Stage6.TopologyBridge
import Probe.GeometryApi
import Probe.PdeApi
import ReleaseAudit
import ReleaseCheck

-- D13-cross-audit-360-cards round 12 (invocation 9), adversarial lane A3: PROBE-ROOT variant.
--
-- INDEPENDENT transitive axiom-cone checker, v2 (performance-hardened).
-- Deliberate differences from the `#print axioms` machinery
-- (`Lean.CollectAxioms`, used by rounds 1-10), unchanged from round 11:
--
--   1. no call to `CollectAxioms.collect` / `Expr.getUsedConstants`: the `Expr`
--      constructors are walked by hand;
--   2. no use of the `extFind?` axiom-cache extension that `CollectAxioms` uses
--      for imported declarations.  Every cone here is recomputed from the raw
--      constant type/value in `env.constants`, so a stale or wrong cached axiom
--      set in an imported `.olean` could not hide an axiom from this check.
--
-- v2 changes vs round 11 (pure performance; the traversal semantics are
-- identical and round-12 results are compared cone-by-cone with round 11 on the
-- cards that completed there):
--   * `ConeState` threads the memo tables across one-root-at-a-time calls, so
--     progress can be logged from `run_cmd` without putting logging in the
--     traversal;
--   * per-name axiom-ness cache (avoids an environment lookup per graph edge);
--   * progress lines `A3R12PPROGRESS|<roots_done>|<roots_total>|<memo>` so a
--     long union closure can be extrapolated rather than only hit a timeout.
--
-- AUDIT INSTRUMENT ONLY.  The `a3r12Test*` declarations below are a
-- positive/negative self-test of the traversal; they are never imported by any
-- producer module, never enter a `lake build` target, and are excluded by name
-- from the fail-closed scan.  The positive control is an `axiom` on purpose:
-- the checker must detect it or no cone result below is trustworthy.

open Lean Elab Command

namespace A3R12

/-- Constants occurring in an expression, by manual structural recursion. -/
partial def constsOf (e : Expr) (acc : Std.HashSet Name) : Std.HashSet Name :=
  match e with
  | .app f a         => constsOf a (constsOf f acc)
  | .lam _ t b _     => constsOf b (constsOf t acc)
  | .forallE _ t b _ => constsOf b (constsOf t acc)
  | .letE _ t v b _  => constsOf b (constsOf v (constsOf t acc))
  | .mdata _ b       => constsOf b acc
  | .proj _ _ b      => constsOf b acc
  | .const n _       => acc.insert n
  | .fvar _          => acc
  | .bvar _          => acc
  | .mvar _          => acc
  | .sort _          => acc
  | .lit _           => acc

/-- Direct constant references of one declaration.  `valuesOnly = false` takes
the type, the value (theorems and opaque definitions included) and constructor
names of inductives; `valuesOnly = true` takes only the value. -/
def directRefs (env : Environment) (n : Name) (valuesOnly : Bool) : Array Name := Id.run do
  let mut s : Std.HashSet Name := {}
  match env.find? n with
  | none => pure ()
  | some ci =>
    if !valuesOnly then s := constsOf ci.type s
    match ci.value? (allowOpaque := true) with
    | some v => s := constsOf v s
    | none => pure ()
    if !valuesOnly then
      match ci with
      | .inductInfo v => for c in v.ctors do s := s.insert c
      | _ => pure ()
  return s.toArray

/-- Memo tables for the transitive closure.  `visiting` is local to one step and
must be empty between steps. -/
structure ConeState where
  memo : Std.HashMap Name (Array Name) := {}
  refMemo : Std.HashMap Name (Array Name) := {}
  axMemo : Std.HashMap Name Bool := {}

/-- One memoised post-order DFS step from root `r`, extending `st`. -/
def coneStep (env : Environment) (st : ConeState) (r : Name) : ConeState := Id.run do
  let mut memo := st.memo
  let mut refMemo := st.refMemo
  let mut axMemo := st.axMemo
  let mut visiting : Std.HashSet Name := {}
  if memo.contains r then return { memo := memo, refMemo := refMemo, axMemo := axMemo }
  let mut stack : Array (Name × Bool) := #[(r, false)]
  while !stack.isEmpty do
    let (n, finish) := stack.back!
    stack := stack.pop
    if finish then
      if memo.contains n then continue
      let refs ← match refMemo.get? n with
        | some rs => pure rs
        | none =>
          let rs := directRefs env n false
          refMemo := refMemo.insert n rs
          pure rs
      let mut s : Std.HashSet Name := {}
      for c in refs do
        let ax ← match axMemo.get? c with
          | some b => pure b
          | none =>
            let b := (env.find? c).any (fun i => i.isAxiom)
            axMemo := axMemo.insert c b
            pure b
        if ax then s := s.insert c
        for a in memo.getD c #[] do s := s.insert a
      memo := memo.insert n (s.toArray.qsort (fun a b => a.toString < b.toString))
      visiting := visiting.erase n
    else
      if memo.contains n || visiting.contains n then continue
      visiting := visiting.insert n
      stack := stack.push (n, true)
      let refs ← match refMemo.get? n with
        | some rs => pure rs
        | none =>
          let rs := directRefs env n false
          refMemo := refMemo.insert n rs
          pure rs
      for c in refs do
        if !memo.contains c && !visiting.contains c then stack := stack.push (c, false)
  return { memo := memo, refMemo := refMemo, axMemo := axMemo }

/-- Does `root` transitively reach `target` (early-exit BFS with a shared
`directRefs` memo across calls)? -/
def reaches (env : Environment) (memo : Std.HashMap Name (Array Name))
    (root target : Name) (valuesOnly : Bool) : Bool × Std.HashMap Name (Array Name) := Id.run do
  let mut memo := memo
  if root == target then return (true, memo)
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[root]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let refs ← match memo.get? n with
      | some rs => pure rs
      | none =>
        let rs := directRefs env n valuesOnly
        memo := memo.insert n rs
        pure rs
    for c in refs do
      if c == target then return (true, memo)
      if !seen.contains c then stack := stack.push c
  return (false, memo)

/-- Transitive reachable-constant *count* of `root` (streaming; no set kept). -/
def reachCount (env : Environment) (memo : Std.HashMap Name (Array Name))
    (root : Name) (valuesOnly : Bool) : Nat × Std.HashMap Name (Array Name) := Id.run do
  let mut memo := memo
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[root]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let refs ← match memo.get? n with
      | some rs => pure rs
      | none =>
        let rs := directRefs env n valuesOnly
        memo := memo.insert n rs
        pure rs
    for c in refs do
      if !seen.contains c then stack := stack.push c
  return (seen.size, memo)

/-- Indexed suffix resolution: exact match first, then the shortest name under
`root` ending in `.suffix`, then the shortest name anywhere ending in
`.suffix`.  (Round 11 scanned `env.constants` up to three times per call, which
dominated the late-card runs.) -/
structure NameIndex where
  exact : Std.HashMap String Name := {}
  byLast : Std.HashMap String (Array Name) := {}

def NameIndex.build (env : Environment) : NameIndex := Id.run do
  let mut exact : Std.HashMap String Name := {}
  let mut byLast : Std.HashMap String (Array Name) := {}
  for (n, _) in env.constants.toList do
    let s := n.toString
    exact := exact.insert s n
    let last := match s.splitOn "." with
      | [] => s
      | parts => parts.getLast!
    byLast := byLast.insert last ((byLast.getD last #[]).push n)
  return { exact := exact, byLast := byLast }

def NameIndex.resolve (ix : NameIndex) (root : Name) (s : String) : Option Name := Id.run do
  match ix.exact.get? s with
  | some n => return some n
  | none => pure ()
  let last := match s.splitOn "." with
    | [] => s
    | parts => parts.getLast!
  let cands := ix.byLast.getD last #[]
  let mut hit : Option Name := none
  for n in cands do
    if root.isPrefixOf n && n.toString.endsWith ("." ++ s) then
      match hit with
      | none => hit := some n
      | some h =>
        if n.toString.length < h.toString.length ||
           (n.toString.length == h.toString.length && n.toString < h.toString) then
          hit := some n
  if hit.isSome then return hit
  for n in cands do
    if n.toString.endsWith ("." ++ s) then
      match hit with
      | none => hit := some n
      | some h =>
        if n.toString.length < h.toString.length ||
           (n.toString.length == h.toString.length && n.toString < h.toString) then
          hit := some n
  return hit

end A3R12

-- AUDIT INSTRUMENT self-test declarations (excluded from the fail-closed scan).
def a3r12Roots : List String := [
  "Poincare.D12.TriangulationTopology.coneQuotHomeoDisk",
  "Poincare.D12.TriangulationTopology.suspQuotHomeoSphere",
  "Poincare.D12.TriangulationTopology.doubleDiskQuotHomeoSphere",
  "Poincare.D12.TriangulationTopology.coneQuotHomeoTopCatDisk",
  "Poincare.D12.TriangulationTopology.suspQuotHomeoTopCatSphere",
  "Poincare.D12.TriangulationTopology.doubleDiskQuotHomeoTopCatSphere",
  "Poincare.D12.TriangulationTopology.sphereThreeGluedDisks",
  "Poincare.D12.TriangulationTopology.sphereThreeSuspension",
  "Poincare.D12.TriangulationTopology.coneOverSphere2HomeoDisk3",
  "Poincare.D12.TriangulationTopology.sphereNonempty",
  "Poincare.D12.TriangulationTopology.diskNonempty",
  "Poincare.D12.TriangulationTopology.sphereCompactSpace",
  "Poincare.D12.TriangulationTopology.diskCompactSpace",
  "Poincare.D12.TriangulationTopology.iccCompactSpace",
  "Poincare.D12.TriangulationTopology.coneQuotNonempty",
  "Poincare.D12.TriangulationTopology.suspQuotNonempty",
  "Poincare.D12.TriangulationTopology.doubleDiskQuotNonempty",
  "Poincare.D12.TriangulationTopology.norm_sq_esnoc",
  "Poincare.D12.TriangulationTopology.norm_eq_one_iff_norm_sq_eq_one",
  "Poincare.D12.TriangulationTopology.norm_esnoc_smul_sqrt_sub_sq_eq_one",
  "Poincare.D12.TriangulationTopology.esnoc_injective2",
  "Poincare.D12.TriangulationTopology.sqrt_one_sub_sq_eq_norm_of_norm_sq_add_sq_eq_one",
  "Poincare.D12.TriangulationTopology.eq_neg_self_of_sqrt_eq_neg_sqrt",
  "Poincare.D12.TriangulationTopology.coneMapQuot_surjective",
  "Poincare.D12.TriangulationTopology.coneMapQuot_injective",
  "Poincare.D12.TriangulationTopology.suspMapQuot_surjective",
  "Poincare.D12.TriangulationTopology.suspMapQuot_injective",
  "Poincare.D12.TriangulationTopology.doubleDiskMapQuot_surjective",
  "Poincare.D12.TriangulationTopology.doubleDiskMapQuot_injective",
  "Poincare.D12.TriangulationTopology.sphereThree_eq_sphere3",
  "Poincare.D12.TriangulationTopology.disk3_boundary_eq_sphere2",
  "Poincare.D12.TriangulationTopology.disk_boundary_eq_sphere",
  "Poincare.D12.TriangulationTopology.coveringOfSimplyConnectedIsHomeo",
  "Poincare.D12.TriangulationTopology.coveringOfSimplyConnectedIsHomeo_bijective",
  "Poincare.D12.TriangulationTopology.coveringOfSimplyConnectedIsHomeo_of_nonempty",
  "Poincare.D12.TriangulationTopology.coveringMap_surjective_of_pathConnected",
  "Poincare.D12.TriangulationTopology.coveringMap_injective_of_simplyConnected",
  "Poincare.D12.TriangulationTopology.trivialization_id",
  "Poincare.D12.TriangulationTopology.isCoveringMap_id",
  "Poincare.D12.TriangulationTopology.diskContractible",
  "Poincare.D12.TriangulationTopology.diskSimplyConnected",
  "Poincare.D12.TriangulationTopology.diskCoverPipeline",
  "Poincare.D12.TriangulationTopology.locallyCompactSpace_of_compact_t2",
  "Poincare.D12.TriangulationTopology.zmod2_eq_zero_or_one",
  "Poincare.D12.TriangulationTopology.zmod2Mul_eq_ofAdd_one_or_one",
  "Poincare.D12.TriangulationTopology.antipodal_mul_self",
  "Poincare.D12.TriangulationTopology.sphere_eq_neg_self_impossible",
  "Poincare.D12.TriangulationTopology.antipodalSmul",
  "Poincare.D12.TriangulationTopology.one_ne_ofAdd_one",
  "Poincare.D12.TriangulationTopology.antipodalSmul_one",
  "Poincare.D12.TriangulationTopology.antipodalSmul_ofAdd_one",
  "Poincare.D12.TriangulationTopology.antipodalMulAction",
  "Poincare.D12.TriangulationTopology.antipodal_smul_one_eq",
  "Poincare.D12.TriangulationTopology.antipodal_smul_ofAdd_one_eq",
  "Poincare.D12.TriangulationTopology.continuous_antipodal_ofAdd_one",
  "Poincare.D12.TriangulationTopology.antipodalContinuousConstSMul",
  "Poincare.D12.TriangulationTopology.antipodalIsCancelSMul",
  "Poincare.D12.TriangulationTopology.RealProjective",
  "Poincare.D12.TriangulationTopology.antipodalQuotientCovering",
  "Poincare.D12.TriangulationTopology.rpCompactSpace",
  "Poincare.D12.TriangulationTopology.rpT2Space",
  "Poincare.D12.TriangulationTopology.rpNonempty",
  "Poincare.D12.TriangulationTopology.spherePathConnectedSpace_of_pos",
  "Poincare.D12.TriangulationTopology.rpPathConnectedSpace_of_pos",
  "Poincare.D12.TriangulationTopology.sphericalSpaceFormRecognition",
  "Poincare.D12.TriangulationTopology.simplexBoundaryHomeoSphere",
  "Poincare.D12.TriangulationTopology.simplexBoundaryFnHomeoSphere",
  "Poincare.D12.TriangulationTopology.simplexBoundaryHomeoBoundaryFn",
  "Poincare.D12.TriangulationTopology.simplexBoundaryToSphere",
  "Poincare.D12.TriangulationTopology.sphereToSimplexBoundaryFn",
  "Poincare.D12.TriangulationTopology.simplexMin_neg_of_unit",
  "Poincare.D12.TriangulationTopology.continuous_simplexMin",
  "Poincare.D12.TriangulationTopology.simplexMin_eq_zero_of_mem_boundary",
  "Poincare.D12.TriangulationTopology.simplexMin_attains",
  "Poincare.D12.TriangulationTopology.simplexBoundaryCompactSpace",
  "Poincare.D12.TriangulationTopology.simplexBoundaryT2Space",
  "Poincare.D12.TriangulationTopology.simplexBoundaryNonempty",
  "Poincare.D12.TriangulationTopology.lowerHemisphereHomeoDisk",
  "Poincare.D12.TriangulationTopology.lowerHemisphereToDisk",
  "Poincare.D12.TriangulationTopology.diskToLowerHemisphere",
  "Poincare.D12.TriangulationTopology.sqrt_one_sub_trunc_norm_sq_eq_neg_last",
  "Poincare.D12.TriangulationTopology.lowerHemisphereCompactSpace",
  "Poincare.D12.TriangulationTopology.lowerHemisphereT2Space",
  "Poincare.D12.TriangulationTopology.lowerHemisphereNonempty",
  "Poincare.D12.TriangulationTopology.simplexSet",
  "Poincare.D12.TriangulationTopology.simplexFnNonempty",
  "Poincare.D12.TriangulationTopology.simplexFnT2Space",
  "Poincare.D12.TriangulationTopology.simplexConeMap",
  "Poincare.D12.TriangulationTopology.simplexConeMap_mem",
  "Poincare.D12.TriangulationTopology.continuous_sphereToSimplexBoundary_apply",
  "Poincare.D12.TriangulationTopology.continuous_sphereToSimplexBoundary",
  "Poincare.D12.TriangulationTopology.continuous_simplexConeMap",
  "Poincare.D12.TriangulationTopology.simplexConeMap_respects",
  "Poincare.D12.TriangulationTopology.simplexConeMapQuot",
  "Poincare.D12.TriangulationTopology.continuous_simplexConeMapQuot",
  "Poincare.D12.TriangulationTopology.truncToCenter_simplexConeMap",
  "Poincare.D12.TriangulationTopology.simplex_point_eq_center_add_norm_mul_dir",
  "Poincare.D12.TriangulationTopology.simplexConeMapQuot_injective",
  "Poincare.D12.TriangulationTopology.simplexConeMapQuot_surjective",
  "Poincare.D12.TriangulationTopology.sphereConeHomeoSimplex",
  "Poincare.D12.TriangulationTopology.simplexHomeoConeQuot",
  "Poincare.D12.TriangulationTopology.simplexBoundaryConeRel",
  "Poincare.D12.TriangulationTopology.simplexBoundaryConeMap",
  "Poincare.D12.TriangulationTopology.simplexBoundaryConeMap_mem",
  "Poincare.D12.TriangulationTopology.continuous_simplexBoundaryConeMap",
  "Poincare.D12.TriangulationTopology.simplexBoundaryConeMap_respects",
  "Poincare.D12.TriangulationTopology.simplexBoundaryConeMapQuot",
  "Poincare.D12.TriangulationTopology.continuous_simplexBoundaryConeMapQuot",
  "Poincare.D12.TriangulationTopology.simplexMin_le_center",
  "Poincare.D12.TriangulationTopology.simplexMin_lt_center_of_ne_center",
  "Poincare.D12.TriangulationTopology.simplexRadialTime",
  "Poincare.D12.TriangulationTopology.simplexBoundaryPoint",
  "Poincare.D12.TriangulationTopology.simplexRadialTime_nonneg",
  "Poincare.D12.TriangulationTopology.simplexRadialTime_le_one",
  "Poincare.D12.TriangulationTopology.simplexRadialTime_pos_of_ne_center",
  "Poincare.D12.TriangulationTopology.simplexBoundaryPoint_mem_of_ne_center",
  "Poincare.D12.TriangulationTopology.simplexRadialTime_eq_of_radial_repr",
  "Poincare.D12.TriangulationTopology.simplexBoundaryPoint_eq_of_radial_repr",
  "Poincare.D12.TriangulationTopology.simplexBoundaryConeMapQuot_injective",
  "Poincare.D12.TriangulationTopology.simplexVertexZero",
  "Poincare.D12.TriangulationTopology.simplexVertexZero_mem_boundary",
  "Poincare.D12.TriangulationTopology.simplexBoundaryConeMapQuot_surjective",
  "Poincare.D12.TriangulationTopology.simplexBoundaryConeHomeoSimplex",
  "Poincare.D12.TriangulationTopology.simplexHomeoBoundaryCone",
  "Poincare.D12.TriangulationTopology.simplexHomeoStdSimplexFn",
  "Poincare.D12.TriangulationTopology.simplexHomeoDisk",
  "Poincare.D12.TriangulationTopology.simplexHomeoBoundaryConeStd",
  "Poincare.D12.TriangulationTopology.simplexFnCompactSpace",
  "Poincare.D12.TriangulationTopology.simplexBoundaryFnCompactSpace",
  "Poincare.D12.TriangulationTopology.simplexBoundaryConeCompactSpace",
  "Poincare.D12.TriangulationTopology.simplexBoundaryConeT2Space",
  "Poincare.D12.TriangulationTopology.simplexBoundaryConeNonempty",
  "Poincare.D12.TriangulationTopology.quotMapHomeo",
  "Poincare.D12.TriangulationTopology.simplexBoundaryConeRel_iff_coneRel",
  "Poincare.D12.TriangulationTopology.simplexBoundaryConeHomeoSphereCone",
  "Poincare.D12.TriangulationTopology.PuncturedDisk",
  "Poincare.D12.TriangulationTopology.sphereBase",
  "Poincare.D12.TriangulationTopology.diskDirection",
  "Poincare.D12.TriangulationTopology.diskDirection_of_ne",
  "Poincare.D12.TriangulationTopology.radialExtend",
  "Poincare.D12.TriangulationTopology.radialExtend_apply",
  "Poincare.D12.TriangulationTopology.norm_radialExtend",
  "Poincare.D12.TriangulationTopology.radialExtend_zero",
  "Poincare.D12.TriangulationTopology.diskDirection_radialExtend",
  "Poincare.D12.TriangulationTopology.continuous_diskDirection_punctured",
  "Poincare.D12.TriangulationTopology.continuousOn_diskDirection",
  "Poincare.D12.TriangulationTopology.continuous_radialExtend",
  "Poincare.D12.TriangulationTopology.sphereToDisk",
  "Poincare.D12.TriangulationTopology.sphereToDisk_coe",
  "Poincare.D12.TriangulationTopology.diskDirection_sphereToDisk",
  "Poincare.D12.TriangulationTopology.radialExtend_sphereToDisk",
  "Poincare.D12.TriangulationTopology.radialExtend_id",
  "Poincare.D12.TriangulationTopology.radialExtend_comp",
  "Poincare.D12.TriangulationTopology.alexanderHomeo",
  "Poincare.D12.TriangulationTopology.alexanderHomeo_refl",
  "Poincare.D12.TriangulationTopology.alexanderHomeo_zero",
  "Poincare.D12.TriangulationTopology.alexanderHomeo_sphereToDisk",
  "Poincare.D12.TriangulationTopology.alexanderHomeo_eq_refl_iff",
  "Poincare.D12.TriangulationTopology.diskGlueRel",
  "Poincare.D12.TriangulationTopology.DiskGlueQuot",
  "Poincare.D12.TriangulationTopology.quotMapHomeo_mk",
  "Poincare.D12.TriangulationTopology.diskGlueSumHomeo",
  "Poincare.D12.TriangulationTopology.diskGlueSumHomeo_inl",
  "Poincare.D12.TriangulationTopology.diskGlueSumHomeo_inr",
  "Poincare.D12.TriangulationTopology.alexanderHomeo_symm_sphereToDisk",
  "Poincare.D12.TriangulationTopology.diskGlueRel_transport",
  "Poincare.D12.TriangulationTopology.diskGlueRel_id_iff_doubleDiskRel",
  "Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere",
  "Poincare.D12.TriangulationTopology.diskGlueQuotCompactSpace",
  "Poincare.D12.TriangulationTopology.diskGlueQuotT2Space",
  "Poincare.D12.TriangulationTopology.diskGlueQuotNonempty",
  "Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere_refl_apply",
  "Poincare.D12.TriangulationTopology.sphereOfTwoDisks",
  "Poincare.D12.TriangulationTopology.UpperHemisphere",
  "Poincare.D12.TriangulationTopology.sphere_trunc_norm_sq_add_last_sq_eq_one",
  "Poincare.D12.TriangulationTopology.sqrt_one_sub_trunc_norm_sq_eq_last",
  "Poincare.D12.TriangulationTopology.upperHemisphereToDisk",
  "Poincare.D12.TriangulationTopology.diskToUpperHemisphere",
  "Poincare.D12.TriangulationTopology.continuous_upperHemisphereToDisk",
  "Poincare.D12.TriangulationTopology.continuous_diskToUpperHemisphere",
  "Poincare.D12.TriangulationTopology.upperHemisphereToDisk_diskToUpperHemisphere",
  "Poincare.D12.TriangulationTopology.diskToUpperHemisphere_upperHemisphereToDisk",
  "Poincare.D12.TriangulationTopology.upperHemisphereHomeoDisk",
  "Poincare.D12.TriangulationTopology.upperHemisphereCompactSpace",
  "Poincare.D12.TriangulationTopology.upperHemisphereT2Space",
  "Poincare.D12.TriangulationTopology.upperHemisphereNonempty",
  "Poincare.D12.TriangulationTopology.lowerHemisphere_boundary_eq_inter",
  "Poincare.D12.TriangulationTopology.lowerHemisphere_isClosed",
  "Poincare.D12.TriangulationTopology.upperHemisphere_isClosed",
  "Poincare.D12.TriangulationTopology.hemisphere_cover",
  "Poincare.D12.TriangulationTopology.hemisphere_charts_agree",
  "Poincare.D12.TriangulationTopology.sphereOfTwoDisks_hemisphere_instance",
]

axiom a3r12TestAxiom : True
theorem a3r12TestUsesAxiom : True := a3r12TestAxiom
theorem a3r12TestNoAxiom : (1 : Nat) + 1 = 2 := rfl

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let root : Name := `Poincare.D12
  -- documented producer negative control: an axiom in no proof cone (excluded
  -- here only so the instrument does not self-flag; separately scanned)
  let excluded : List Name := [`Poincare.D12.VolumeIBP.Audit.negativeControl]
  -- 1. self-test on the instrument declarations
  let st0 := A3R12.coneStep env {} `a3r12TestUsesAxiom
  let st1 := A3R12.coneStep env st0 `a3r12TestNoAxiom
  let axPos := st1.memo.getD `a3r12TestUsesAxiom #[]
  let axNeg := st1.memo.getD `a3r12TestNoAxiom #[]
  unless axPos.contains `a3r12TestAxiom do
    throwError "A3R12P SELFTEST FAIL: traversal missed the instrument axiom"
  unless axNeg.isEmpty do
    throwError "A3R12P SELFTEST FAIL: traversal invented axioms {axNeg.toList}"
  logInfo m!"A3R12P SELFTEST PASS (positive control detected, negative control clean)"
  -- 2. the card's probed declarations (probe-root variant), one memoised pass
  let ix := A3R12.NameIndex.build env
  let mut roots : Array Name := #[]
  for s in a3r12Roots do
    match ix.resolve root s with
    | some n => if !excluded.contains n then roots := roots.push n
    | none => throwError "A3R12P ROOT-RESOLVE-FAIL {s}"
  roots := roots.qsort (fun a b => a.toString < b.toString)
  let mut st : A3R12.ConeState := {}
  for i in [:roots.size] do
    st := A3R12.coneStep env st roots[i]!
    if (i + 1) % 20 == 0 || i + 1 == roots.size then
      logInfo m!"A3R12PPROGRESS|{i + 1}|{roots.size}|{st.memo.size}"
  let cones := st.memo
  let mut bad : Array (Name × List Name) := #[]
  for n in roots do
    let axs := cones.getD n #[]
    let unapproved := axs.toList.filter (fun a => !allowed.contains a)
    if !unapproved.isEmpty then bad := bad.push (n, unapproved)
    logInfo m!"A3R12PCONE|{n}|{String.intercalate "," (axs.toList.map Name.toString)}|0"
  logInfo m!"A3R12P TOTAL {roots.size} declarations, memo size {cones.size}"
  for (n, u) in bad do
    logError m!"A3R12P BAD {n} -> {u.map Name.toString}"
  if !bad.isEmpty then
    throwError "A3R12P FAIL: {bad.size} declarations with unapproved transitive axioms"
  logInfo m!"A3R12P PASS"
