import Audit.CounterexampleAudit
import Audit.CurvatureODEAudit
import Audit.EvolutionAudit
import Audit.GeometryAudit
import Audit.PromotedEvolutionAudit
import D6AuditReport
import Ledger.DefinitionSmoke
import Ledger.PerelmanDefinitions
import Poincare.Basic
import Poincare.D12.TensorMaximumBochner.Audit
import Poincare.D12.TensorMaximumBochner.BochnerIdentity
import Poincare.D12.TensorMaximumBochner.PositivityPreservation
import Poincare.D12.TensorMaximumBochner.So3Model
import Poincare.D12.TensorMaximumBochner.So3Polynomial
import Poincare.D12.TensorMaximumBochner.So3RicciFlow
import Poincare.D12.TensorMaximumBochner.TangentCone
import Poincare.D12.TensorMaximumBochner.TensorCalculus
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
  ("kernelTangent_of_feasibleDirection", "FeasibleDirection", "C9-C1a necessity theorem consumes the feasibility condition"),
  ("kernelTangent_of_feasibleDirection", "KernelTangent", "C9-C1b necessity theorem concludes the correct condition"),
  ("kernelTangent_not_feasible", "KernelTangent", "C9-C1c sharpness witness satisfies the condition"),
  ("kernelTangent_not_feasible", "FeasibleDirection", "C9-C1d sharpness witness violates feasibility"),
  ("hamiltonField_kernelTangent", "hamiltonField", "C9-C2a Hamilton field theorem uses the field definition"),
  ("hamiltonField_kernelTangent", "adjugate_posSemidef", "C9-C2b Hamilton field theorem uses adjugate PSD"),
  ("hamiltonField_kernelTangent", "dotProduct_mulVec_sq", "C9-C2c Hamilton field theorem uses the A^2 kernel identity"),
  ("hamiltonField_not_strengthened", "hamiltonField", "C9-C1e gap theorem uses the field definition"),
  ("counterexample_kernelTangent", "counterexampleA", "C9 witness uses counterexampleA"),
  ("counterexample_not_feasible", "counterexampleA", "C9 witness uses counterexampleA"),
  ("", "hamiltonField", "C9 resolve field def"),
  ("", "KernelTangent", "C9 resolve correct condition"),
]
def a3r11Users : List String := [
  "KernelTangent",
  "hamiltonField",
  "kernelTangent_of_feasibleDirection",
  "hamiltonField_kernelTangent",
  "staysPosSemidef_of_tangent",
  "staysPosSemidef_of_field",
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
    if consS == "" then
      -- resolve-only entry: the claim names a declaration that must exist
      match A3R11Q.resolveSuffix env root targS with
      | some t => logInfo m!"A3R11RESOLVE|{tag}|{targS}|{t}"
      | none => logError m!"A3R11RESOLVE-FAIL|{tag}|{targS}"
      continue
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
