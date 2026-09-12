import Audit.CounterexampleAudit
import Audit.CurvatureODEAudit
import Audit.D12.D12Audit
import Audit.EvolutionAudit
import Audit.GeometryAudit
import Audit.PromotedEvolutionAudit
import D6AuditReport
import Ledger.DefinitionSmoke
import Ledger.PerelmanDefinitions
import Poincare.Basic
import Poincare.D12
import Poincare.D12.ConnectionCurvature
import Poincare.D12.ConnectionCurvature.ChartLeviCivita
import Poincare.D12.ConnectionCurvature.ChartLeviCivitaForm
import Poincare.D12.ConnectionCurvature.ChartLeviCivitaSmooth
import Poincare.D12.ConnectionCurvature.ChartModel1D
import Poincare.D12.ConnectionCurvature.ConformalChartModel
import Poincare.D12.ConnectionCurvature.MilnorLeviCivita
import Poincare.D12.ConnectionCurvature.RicciSymmetry
import Poincare.D12.ConnectionCurvature.SoThreeModel
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

-- D13-cross-audit-360-cards round 12 (invocation 9), adversarial lane A3:
-- downstream-use probe v2 (performance-hardened; same hand-written traversal as
-- IndepConesTemplate.lean, so it is independent of `CollectAxioms`/`extFind?`).
--
-- Instruments:
--   A3R12QUERY  -- is the target transitively reachable from the consumer, in
--                  (type+value) and (value-only, i.e. proof-term) modes?  Tags
--                  prefixed `NEG:` assert *absence* and fail if reachable.
--   A3R12USER   -- complete enumeration of the D12-root declarations that reach
--                  the target.  Correct because a constant outside the D12 root
--                  cannot reference a D12 constant, so every path stays inside
--                  the root; the reverse BFS over the root is exhaustive.
--
-- v2 vs round 11: indexed name resolution (round 11 scanned `env.constants` up
-- to three times per call), early-exit reachability, and a `directRefs` memo
-- shared across queries.  This is what makes the topology-heavy cards feasible.
--
-- AUDIT INSTRUMENT ONLY; no producer module imports this file.

open Lean Elab Command

namespace A3R12Q

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

/-- Early-exit reachability with a shared `directRefs` memo. -/
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

/-- Complete user sets (within `members`) for a batch of targets: build the
reverse adjacency once per mode and BFS per target. -/
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

end A3R12Q

axiom a3r12QTestAxiom : True
theorem a3r12QTestUsesAxiom : True := a3r12QTestAxiom
theorem a3r12QTestNoAxiom : (1 : Nat) + 1 = 2 := rfl

def a3r12Queries : List (String × String × String) := [
  ("leviCivitaExists", "LeviCivitaExistenceStatement", "CC-I1-e1 closure proves the formerly blocked Prop (type-level)"),
  ("leviCivitaExists", "milnorConnection", "CC-I1-e2 witness is the Milnor connection (proof term)"),
  ("leviCivitaExists", "milnorConnection_isLeviCivita", "CC-I1-e3 closure proof component"),
  ("so3MeanLeviCivita", "meanLeviCivitaData", "CC-I1-x1 model witness is built from meanLeviCivitaData"),
  ("so3_ricci_e00", "so3MeanLeviCivita", "CC-I1-c so3_ricci_e00 consumes the model Levi-Civita datum"),
  ("so3_ricci_symm", "so3MeanLeviCivita", "CC-I1-c2 model Ricci symmetry consumes the model datum"),
  ("so3_ricci_symm", "ricci_symm", "CC-I1-b model Ricci symmetry consumes the abstract ricci_symm"),
  ("so3_milnor_eq_mean", "milnorConnection_eq_mean_iff", "CC-I1-f model uses the iff (nondegenerate)"),
  ("so3MeanLeviCivita", "leviCivitaExists", "NEG:CC-I1-a producer model is NOT built from the closure"),
  ("ricci_symm", "leviCivitaExists", "NEG:CC-I1-d abstract ricci_symm does NOT mention the closure"),
  ("so3_ricci_e00", "ricci_symm", "NEG:CC-I1-g so3_ricci_e00 uses the model lemma, not the abstract ricci_symm"),
  ("ricci_contraction_eq_sum_basis", "ricci_symm", "NEG:CC-I1-h contraction lemma does not use the abstract ricci_symm"),
  ("", "LeviCivitaExistenceStatement", "CC-I1-e4 blocked statement former resolves"),
  ("", "leviCivitaExists", "CC-I1-e5 closure declaration resolves"),
  ("", "so3_ricci_symm", "CC-I1-e6 model Ricci symmetry declaration resolves"),
]
def a3r12Users : List String := [
  "leviCivitaExists",
  "milnorConnection_eq_mean_iff",
  "meanLeviCivitaData",
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let root : Name := `Poincare.D12
  let ix := A3R12Q.NameIndex.build env
  -- self-test: reachability must see the instrument axiom, and must not invent
  -- a path where there is none
  let (posHit, _) := A3R12Q.reaches env {} `a3r12QTestUsesAxiom `a3r12QTestAxiom false
  let (negHit, _) := A3R12Q.reaches env {} `a3r12QTestNoAxiom `a3r12QTestAxiom false
  unless posHit do
    throwError "A3R12Q SELFTEST FAIL: reachability missed the instrument axiom"
  if negHit then
    throwError "A3R12Q SELFTEST FAIL: reachability invented a dependency"
  logInfo m!"A3R12Q SELFTEST PASS"
  let mut members : Array Name := #[]
  for (n, _ci) in env.constants.toList do
    if root.isPrefixOf n then members := members.push n
  logInfo m!"A3R12Q MEMBERS {members.size}"
  let mut memoTV : Std.HashMap Name (Array Name) := {}
  let mut memoVO : Std.HashMap Name (Array Name) := {}
  let mut qmiss : Nat := 0
  for (consS, targS, tag) in a3r12Queries do
    if consS == "" then
      match ix.resolve root targS with
      | some t => logInfo m!"A3R12RESOLVE|{tag}|{targS}|{t}"
      | none => qmiss := qmiss + 1; logError m!"A3R12RESOLVE-FAIL|{tag}|{targS}"
      continue
    match ix.resolve root consS, ix.resolve root targS with
    | some c, some t =>
      let (rc, m1) := A3R12Q.reaches env memoTV c t false
      memoTV := m1
      let (rv, m2) := A3R12Q.reaches env memoVO c t true
      memoVO := m2
      let neg := tag.startsWith "NEG:"
      let ok := if neg then !rc else rc
      let expect := if neg then "false" else "true"
      logInfo m!"A3R12QUERY|{tag}|{consS}|{targS}|{c}|{t}|typevalue={rc}|valueonly={rv}|expected={expect}|ok={ok}"
      if !ok then
        qmiss := qmiss + 1
        logError m!"A3R12QUERY-MISS|{tag}|{consS}|{targS}|{c}|{t}"
    | _, _ => qmiss := qmiss + 1; logError m!"A3R12QUERY-RESOLVE-FAIL|{tag}|{consS}|{targS}"
  logInfo m!"A3R12Q QUERIES {a3r12Queries.length} total, {qmiss} missing"
  let mut userTargets : Array Name := #[]
  for s in a3r12Users do
    match ix.resolve root s with
    | some t => userTargets := userTargets.push t
    | none => throwError "A3R12USER-RESOLVE-FAIL|{s}"
  let usersTV := A3R12Q.usersOfAll env members userTargets false
  let usersVO := A3R12Q.usersOfAll env members userTargets true
  for i in [:a3r12Users.length] do
    let s := a3r12Users[i]!
    let t := userTargets[i]!
    let tv := usersTV.getD t #[]
    let vo := usersVO.getD t #[]
    logInfo m!"A3R12USER|{s}|{t}|typevalue={String.intercalate "," (tv.toList.map Name.toString)}|valueonly={String.intercalate "," (vo.toList.map Name.toString)}"
  if qmiss != 0 then
    throwError "A3R12Q FAIL: {qmiss} dependent-use queries unresolved or not wired"
  logInfo m!"A3R12Q DONE"
