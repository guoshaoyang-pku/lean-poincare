import Audit.CounterexampleAudit
import Audit.CurvatureODEAudit
import Audit.EvolutionAudit
import Audit.GeometryAudit
import Audit.PromotedEvolutionAudit
import D6AuditReport
import Ledger.DefinitionSmoke
import Ledger.PerelmanDefinitions
import Poincare.Basic
import Poincare.D12.GeometricCompactness.AxiomAudit
import Poincare.D12.GeometricCompactness.Basic
import Poincare.D12.GeometricCompactness.Criterion
import Poincare.D12.GeometricCompactness.Frontier
import Poincare.D12.GeometricCompactness.GridFamily
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

-- D13-cross-audit-360-cards round 11 (invocation 8), adversarial lane A3.
--
-- INDEPENDENT transitive axiom-cone checker and downstream-use checker.
-- Written from scratch for this invocation.  Two deliberate differences from
-- the `#print axioms` machinery (`Lean.CollectAxioms`, used by rounds 1-10):
--
--   1. no call to `CollectAxioms.collect` / `Expr.getUsedConstants`: the `Expr`
--      constructors are walked by hand;
--   2. no use of the `extFind?` axiom-cache extension that `CollectAxioms` uses
--      for imported declarations.  Every cone here is recomputed from the raw
--      constant type/value in `env.constants`, so a stale or wrong cached axiom
--      set in an imported `.olean` could not hide an axiom from this check.
--
-- The graph walk is a single memoised post-order DFS over the union of all
-- roots, so every reachable constant is expanded at most once.
--
-- It additionally answers, mechanically, the `exact_blockers_closed` claim
-- question "is the claimed downstream use actually wired?" by computing the
-- reachable-constant set of each claimed consumer in two modes:
--   type+value -- the consumer mentions the target in its statement or proof;
--   valueonly  -- the consumer's *proof term* references the target.
--
-- AUDIT INSTRUMENT ONLY.  The `a3r11Test*` declarations below are a
-- positive/negative self-test of the traversal; they are never imported by any
-- producer module, never enter a `lake build` target, and are excluded by name
-- from the fail-closed scan.  The positive control is an `axiom` on purpose:
-- the checker must detect it or no cone result below is trustworthy.

open Lean Elab Command

namespace A3R11

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

/-- Memoised transitive axiom sets for a batch of roots.  Returns the memo table
(so callers can inspect intermediate constants as well). -/
def allCones (env : Environment) (roots : Array Name) : Std.HashMap Name (Array Name) := Id.run do
  let mut memo : Std.HashMap Name (Array Name) := {}
  let mut refMemo : Std.HashMap Name (Array Name) := {}
  let mut visiting : Std.HashSet Name := {}
  for r in roots do
    if memo.contains r then continue
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
          if (env.find? c).any (fun i => i.isAxiom) then s := s.insert c
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
  return memo

/-- Transitive reachable-constant set of `root` (including `root` itself). -/
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

/-- Resolve a dotted suffix to a fully-qualified name: exact match first, then
the shortest name under `root` ending in `.suffix`, then the shortest name in
the whole environment. -/
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

end A3R11

-- AUDIT INSTRUMENT self-test declarations (excluded from the fail-closed scan).
axiom a3r11TestAxiom : True
theorem a3r11TestUsesAxiom : True := a3r11TestAxiom
theorem a3r11TestNoAxiom : (1 : Nat) + 1 = 2 := rfl

-- Downstream-use queries for this package, filled in by the generator:
-- (consumer dotted suffix, target dotted suffix, tag).  Consumer `""` = resolve
-- the target only.
def a3r11Queries : List (String × String × String) := [
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let root : Name := `Poincare.D12
  -- documented producer negative control: an axiom in no proof cone (excluded
  -- here only so the instrument does not self-flag; separately scanned)
  let excluded : List Name := [`Poincare.D12.VolumeIBP.Audit.negativeControl]
  -- 1. self-test on the instrument declarations
  let st := A3R11.allCones env #[`a3r11TestUsesAxiom, `a3r11TestNoAxiom]
  let axPos := st.getD `a3r11TestUsesAxiom #[]
  let axNeg := st.getD `a3r11TestNoAxiom #[]
  unless axPos.contains `a3r11TestAxiom do
    throwError "A3R11 SELFTEST FAIL: traversal missed the instrument axiom"
  unless axNeg.isEmpty do
    throwError "A3R11 SELFTEST FAIL: traversal invented axioms {axNeg.toList}"
  logInfo m!"A3R11 SELFTEST PASS (positive control detected, negative control clean)"
  -- 2. every constant under the D12 root, one memoised pass
  let mut roots : Array Name := #[]
  for (n, _ci) in env.constants.toList do
    if root.isPrefixOf n && !excluded.contains n then roots := roots.push n
  let cones := A3R11.allCones env roots
  let mut bad : Array (Name × List Name) := #[]
  for n in roots do
    let axs := cones.getD n #[]
    let unapproved := axs.toList.filter (fun a => !allowed.contains a)
    if !unapproved.isEmpty then bad := bad.push (n, unapproved)
    logInfo m!"A3R11CONE|{n}|{String.intercalate "," (axs.toList.map Name.toString)}|0"
  logInfo m!"A3R11 TOTAL {roots.size} declarations, memo size {cones.size}"
  -- 3. downstream-use queries
  let mut qmiss : Nat := 0
  for (consS, targS, tag) in a3r11Queries do
    let tf := A3R11.resolveSuffix env root targS
    if consS == "" then
      match tf with
      | some t => logInfo m!"A3R11RESOLVE|{tag}|{targS}|{t}"
      | none => qmiss := qmiss + 1; logError m!"A3R11RESOLVE-FAIL|{tag}|{targS}"
    else
      match A3R11.resolveSuffix env root consS, tf with
      | some c, some t =>
        let rc := (A3R11.reachableFrom env c false).contains t
        let rv := (A3R11.reachableFrom env c true).contains t
        -- a tag prefixed `NEG:` asserts the *absence* of the dependency, so a
        -- reachable target is the failure there
        let neg := tag.startsWith "NEG:"
        let ok := if neg then !rc else rc
        let expect := if neg then "false" else "true"
        logInfo m!"A3R11QUERY|{tag}|{consS}|{targS}|{c}|{t}|typevalue={rc}|valueonly={rv}|expected={expect}|ok={ok}"
        if !ok then
          qmiss := qmiss + 1
          logError m!"A3R11QUERY-MISS|{tag}|{consS}|{targS}|{c}|{t}"
      | _, _ => qmiss := qmiss + 1; logError m!"A3R11QUERY-RESOLVE-FAIL|{tag}|{consS}|{targS}"
  logInfo m!"A3R11 QUERIES {a3r11Queries.length} total, {qmiss} missing"
  for (n, u) in bad do
    logError m!"A3R11 BAD {n} -> {u.map Name.toString}"
  if !bad.isEmpty then
    throwError "A3R11 FAIL: {bad.size} declarations with unapproved transitive axioms"
  if qmiss != 0 then
    throwError "A3R11 FAIL: {qmiss} downstream-use queries unresolved or not wired"
  logInfo m!"A3R11 PASS"
