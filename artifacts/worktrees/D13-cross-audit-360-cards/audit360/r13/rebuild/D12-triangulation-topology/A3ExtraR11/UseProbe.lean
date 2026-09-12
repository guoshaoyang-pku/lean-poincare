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

-- D13-cross-audit-360-cards round 11, adversarial lane A3: quick use probe.
--
-- Same hand-written traversal as IndepConesTemplate.lean (independent of
-- CollectAxioms), but this file only answers dependency questions, so it is
-- cheap to iterate.  Two instruments:
--
--   A3R11QUERY  -- is the target transitively reachable from the consumer, in
--                  (type+value) and (value-only, i.e. proof-term) modes?
--   A3R11USER   -- complete enumeration of the D12-root declarations that reach
--                  the target.  Correct because a constant outside the D12 root
--                  cannot reference a D12 constant, so every path stays inside
--                  the root; the fixpoint below is therefore exhaustive.
--
-- AUDIT INSTRUMENT ONLY; no producer module imports this file.

open Lean Elab Command

namespace A3R11Q

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

def reachableFrom (env : Environment) (root : Name) (valuesOnly : Bool) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[root]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    for c in directRefs env n valuesOnly do
      if !seen.contains c then stack := stack.push c
  return seen

def resolveSuffix (env : Environment) (root : Name) (s : String) : Option Name := Id.run do
  let mut hit : Option Name := none
  for (n, _) in env.constants.toList do
    if n.toString == s then return some n
  for (n, _) in env.constants.toList do
    if root.isPrefixOf n && n.toString.endsWith ("." ++ s) then
      match hit with
      | none => hit := some n
      | some h => if n.toString.length < h.toString.length then hit := some n
  if hit.isSome then return hit
  for (n, _) in env.constants.toList do
    if n.toString.endsWith ("." ++ s) then
      match hit with
      | none => hit := some n
      | some h => if n.toString.length < h.toString.length then hit := some n
  return hit

/-- Complete user sets (within `members`) for a batch of targets, by building the
reverse adjacency once per mode and running a BFS per target.

Correct because a constant outside the D12 root cannot reference a D12 constant,
so every path to a D12 target stays inside the root. -/
def usersOfAll (env : Environment) (members : Array Name) (targets : Array Name)
    (valuesOnly : Bool) : Std.HashMap Name (Array Name) := Id.run do
  let mut refs : Std.HashMap Name (Array Name) := {}
  for n in members do refs := refs.insert n (directRefs env n valuesOnly)
  let mut rev : Std.HashMap Name (Array Name) := {}
  for n in members do
    for c in refs.getD n #[] do
      rev := rev.insert c ((rev.getD c #[]).push n)
  let mut out : Std.HashMap Name (Array Name) := {}
  for t in targets do
    let mut seen : Std.HashSet Name := {}
    seen := seen.insert t
    let mut work : Array Name := #[t]
    while !work.isEmpty do
      let x := work.back!
      work := work.pop
      for p in rev.getD x #[] do
        if !seen.contains p then
          seen := seen.insert p
          work := work.push p
    out := out.insert t ((seen.erase t).toArray.qsort (fun a b => a.toString < b.toString))
  return out

end A3R11Q

axiom a3r11QTestAxiom : True
theorem a3r11QTestUsesAxiom : True := a3r11QTestAxiom

def a3r11Queries : List (String × String × String) := [
  ("sphereOfTwoDisks_hemisphere_instance", "sphereOfTwoDisks", "C8-n13a non-vacuity instance applies the closed-cover theorem"),
  ("sphereOfTwoDisks", "diskGlueQuotHomeoSphere", "C8-n13 theorem composes the gluing lemma"),
  ("diskGlueQuotHomeoSphere", "alexanderHomeo", "C8-n12 gluing lemma uses the Alexander trick"),
  ("diskGlueQuotHomeoSphere_refl_apply", "doubleDiskQuotHomeoSphere", "C8-n12 compatibility with the earlier double-disk theorem"),
  ("sphericalSpaceFormRecognition", "coveringOfSimplyConnectedIsHomeo", "C8-node5 downstream recognition consumes the covering lemma"),
  ("simplexHomeoDisk", "coneQuotHomeoDisk", "C8-node9b composition: coneQuotHomeoDisk component"),
  ("simplexHomeoDisk", "simplexHomeoConeQuot", "C8-node9b composition: simplexHomeoConeQuot component"),
  ("simplexHomeoDisk", "simplexHomeoStdSimplexFn", "C8-node9b composition: simplexHomeoStdSimplexFn component"),
  ("simplexHomeoBoundaryCone", "simplexHomeoBoundaryConeStd", "C8-node9b literal radial boundary-cone form"),
  ("alexanderHomeo", "alexanderHomeo_sphereToDisk", "C8-node14 Alexander trick boundary restriction"),
  ("alexanderHomeo", "alexanderHomeo_eq_refl_iff", "C8-node14 Alexander trick nondegeneracy"),
  ("", "sphereOfTwoDisks", "C8 resolve closed-cover theorem"),
  ("", "alexanderHomeo", "C8 resolve Alexander trick"),
  ("", "coveringOfSimplyConnectedIsHomeo", "C8 resolve covering lemma"),
]
def a3r11Users : List String := [
  "coveringOfSimplyConnectedIsHomeo",
  "antipodalQuotientCovering",
  "simplexBoundaryHomeoSphere",
  "lowerHemisphereHomeoDisk",
  "simplexHomeoDisk",
  "diskGlueQuotHomeoSphere",
  "alexanderHomeo",
  "sphereOfTwoDisks",
  "sphereOfTwoDisks_hemisphere_instance",
  "suspQuotHomeoSphere",
  "coneQuotHomeoDisk",
  "doubleDiskQuotHomeoSphere",
  "simplexHomeoBoundaryCone",
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let root : Name := `Poincare.D12
  -- self-test: reachability must see the instrument axiom
  unless (A3R11Q.directRefs env `a3r11QTestUsesAxiom false).contains `a3r11QTestAxiom do
    throwError "A3R11Q SELFTEST FAIL"
  logInfo m!"A3R11Q SELFTEST PASS"
  let mut members : Array Name := #[]
  for (n, _ci) in env.constants.toList do
    if root.isPrefixOf n then members := members.push n
  logInfo m!"A3R11Q MEMBERS {members.size}"
  for (consS, targS, tag) in a3r11Queries do
    match A3R11Q.resolveSuffix env root consS, A3R11Q.resolveSuffix env root targS with
    | some c, some t =>
      let rc := (A3R11Q.reachableFrom env c false).contains t
      let rv := (A3R11Q.reachableFrom env c true).contains t
      logInfo m!"A3R11QUERY|{tag}|{consS}|{targS}|{c}|{t}|typevalue={rc}|valueonly={rv}"
    | _, _ => logError m!"A3R11QUERY-RESOLVE-FAIL|{tag}|{consS}|{targS}"
  let userTargets ← a3r11Users.mapM (fun s =>
    match A3R11Q.resolveSuffix env root s with
    | some t => pure t
    | none => throwError "A3R11USER-RESOLVE-FAIL|{s}")
  let usersTV := A3R11Q.usersOfAll env members userTargets.toArray false
  let usersVO := A3R11Q.usersOfAll env members userTargets.toArray true
  for (s, t) in a3r11Users.zip userTargets do
    let tv := usersTV.getD t #[]
    let vo := usersVO.getD t #[]
    logInfo m!"A3R11USER|{s}|{t}|typevalue={String.intercalate "," (tv.toList.map Name.toString)}|valueonly={String.intercalate "," (vo.toList.map Name.toString)}"
  logInfo m!"A3R11Q DONE"
