import Audit.CounterexampleAudit
import Audit.CurvatureODEAudit
import Audit.EvolutionAudit
import Audit.GeometryAudit
import Audit.PromotedEvolutionAudit
import D6AuditReport
import Ledger.DefinitionSmoke
import Ledger.PerelmanDefinitions
import Poincare.Basic
import Poincare.D12.SurgeryRecognition.All
import Poincare.D12.SurgeryRecognition.Audit
import Poincare.D12.SurgeryRecognition.BallGluing
import Poincare.D12.SurgeryRecognition.ConnectedSumTopology
import Poincare.D12.SurgeryRecognition.CoveringRecognition
import Poincare.D12.SurgeryRecognition.DeckTrivial
import Poincare.D12.SurgeryRecognition.ExpandedInterfaces
import Poincare.D12.SurgeryRecognition.SphereOfSpheres
import Poincare.D7.Canonical.Basic
import Poincare.D7.Canonical.Classification
import Poincare.D7.Canonical.Curvature
import Poincare.D7.Canonical.Models
import Poincare.D7.Canonical.Statements
import Poincare.D7.Compactness.Basic
import Poincare.D7.Curvature.Basic
import Poincare.D7.Curvature.Example
import Poincare.D7.Curvature.Sectional
import Poincare.D7.Curvature.Symmetries
import Poincare.D7.Recognition.All
import Poincare.D7.Recognition.Assembly
import Poincare.D7.Recognition.Audit
import Poincare.D7.Recognition.Basic
import Poincare.D7.Recognition.Homeomorphism
import Poincare.D7.Recognition.Probe
import Poincare.D7.RicciScalar
import Poincare.D7.RicciScalar.Basic
import Poincare.D7.RicciScalar.Bridge
import Poincare.D7.RicciScalar.Example
import Poincare.D7.RicciScalar.Product
import Poincare.D7.RicciScalar.Scalar
import Poincare.D7.RicciScalar.Variation
import Poincare.D7.ShortTime.Basic
import Poincare.D7.ShortTime.Equivalence
import Poincare.D7.ShortTime.Gauge
import Poincare.D7.ShortTime.MatrixDeriv
import Poincare.D7.ShortTime.ODE
import Poincare.D7.ShortTime.Statements
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
import Poincare.VKPort.HatcherLib.Ch1.AlgebraicConstructions
import Poincare.VKPort.HatcherLib.Ch1.BasicConstructions
import Poincare.VKPort.HatcherLib.Ch1.VanKampen
import Poincare.VKPort.HatcherLib.Ch1.VanKampenAdaptedGrid
import Poincare.VKPort.HatcherLib.Ch1.VanKampenGlobalSweep
import Poincare.VKPort.HatcherLib.Ch1.VanKampenGrid
import Poincare.VKPort.HatcherLib.Ch1.VanKampenSubdivision
import Poincare.VKPort.HatcherLib.Ch1.VanKampenSweep
import Poincare.VKPort.HatcherLib.Ch1.VanKampenWordCalculus
import Poincare.VKPort.HatcherLib.VKProbe
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
  "Poincare.D12.SurgeryRecognition.doubleBallHomeoSphere",
  "Poincare.D12.SurgeryRecognition.northHemisphereHomeo",
  "Poincare.D12.SurgeryRecognition.southHemisphereHomeo",
  "Poincare.D12.SurgeryRecognition.equatorHomeoS2",
  "Poincare.D12.SurgeryRecognition.sphereConnectSum_homeo_sphere",
  "Poincare.D12.SurgeryRecognition.iteratedSphereSum_homeo_sphere",
  "Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2",
  "Poincare.D12.SurgeryRecognition.endGame_finalTopology",
  "Poincare.D12.SurgeryRecognition.stage6Target_of_v2decomposition",
  "Poincare.D12.SurgeryRecognition.stage6Target_of_v2hypotheses",
  "Poincare.D12.SurgeryRecognition.finiteFreeOrbit_isQuotientCoveringMap",
  "Poincare.D12.SurgeryRecognition.antipodal_free",
  "Poincare.D12.SurgeryRecognition.antipodalQuotientCovering",
  "Poincare.D12.SurgeryRecognition.antipodalCoveringMap",
  "Poincare.D12.SurgeryRecognition.antipodal_fiber_card_two",
  "Poincare.D12.SurgeryRecognition.antipodal_two_sheets",
  "Poincare.D12.SurgeryRecognition.antipodalModel",
  "Poincare.D12.SurgeryRecognition.antipodalModel_nontrivial",
  "Poincare.D12.SurgeryRecognition.quotientHomeoOfSubsingleton",
  "Poincare.D12.SurgeryRecognition.sphericalPieceRecognition_of",
  "Poincare.D12.SurgeryRecognition.sphereThree_pathConnectedSpace",
  "Poincare.D12.SurgeryRecognition.SphericalSpaceFormModel.spaceFormProjection",
  "Poincare.D12.SurgeryRecognition.SphericalSpaceFormModel.spaceFormProjection_covering",
  "Poincare.D12.SurgeryRecognition.SphericalSpaceFormModel.spaceFormFiberEquivGroup",
  "Poincare.D12.SurgeryRecognition.SphericalSpaceFormModel.spaceForm_monodromy_trivial",
  "Poincare.D12.SurgeryRecognition.SphericalSpaceFormModel.spaceForm_monodromy_transitive",
  "Poincare.D12.SurgeryRecognition.SphericalSpaceFormModel.spaceForm_fiber_subsingleton",
  "Poincare.D12.SurgeryRecognition.deckTrivial_of_simplyConnected_quotient",
  "Poincare.D12.SurgeryRecognition.sphericalPieceRecognition_of_spaceForm",
  "Poincare.D12.SurgeryRecognition.stage6Target_of_v3hypotheses",
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
