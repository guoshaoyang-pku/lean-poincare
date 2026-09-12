-- A3 round-13 statement-level screen (generated)
import Ledger.PerelmanDefinitions
import Poincare.D10.HeatKernelEuclidean.Basic
import Poincare.D10.HeatKernelEuclidean.HeatEquation
import Poincare.D10.HeatKernelEuclidean.Mass
import Poincare.D10.HeatKernelEuclidean.Semigroup
import Poincare.D12.SemanticLedger.Defect
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
import Poincare.D7.HeatKernel.Basic
import Poincare.D7.HeatKernel.Blocked
import Poincare.D7.HeatKernel.Content
import Poincare.D7.HeatKernel.Example
import Poincare.D7.HeatKernel.Grid
import Poincare.D7.HeatKernel.Instance
import Poincare.D7.Recognition.Assembly
import Poincare.D7.Recognition.Basic
import Poincare.D7.Recognition.Homeomorphism
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
import Poincare.Longrun.Geometry.ConnectionAdapter
import Poincare.Longrun.Geometry.Contraction
import Poincare.Longrun.Geometry.LeviCivitaBlocked
import Poincare.Longrun.Geometry.MetricData
import Poincare.Longrun.Surgery.Basic
import Poincare.Longrun.Surgery.Chain
import Poincare.Longrun.Surgery.Missing
import Poincare.Longrun.Surgery.Toy
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

open Lean Elab Command
namespace A3R13T

/-- peel binders, return (hypothesis types in order, body) -/
partial def peel (e : Expr) (acc : Array Expr) : Array Expr × Expr :=
  match e with
  | .forallE _ d b _ => peel b (acc.push d)
  | _ => (acc, e)

def isTrue (e : Expr) : Bool := e.isConstOf ``True
def isFalse (e : Expr) : Bool := e.isConstOf ``False

/-- conclusion `a = a` or `a ↔ a` up to STRUCTURAL equality.
NOTE: `Expr`'s `BEq` instance is hash-based in this toolchain (`a == b` can be
true for structurally different expressions); `Expr.equal` is the structural
comparison and is what this screen must use. -/
def reflexiveConclusion (e : Expr) : Bool :=
  if e.isAppOfArity ``Eq 3 then
    let a := e.getArg! 1
    let b := e.getArg! 2
    a.equal b
  else if e.isAppOfArity ``Iff 2 then
    (e.getArg! 0).equal (e.getArg! 1)
  else false

/-- proof term is a single constant, possibly applied only to fvars bound by
the theorem's own telescope (a renaming/restatement) -/
def aliasOf (e : Expr) : Option Name :=
  let rec head (e : Expr) : Option Name :=
    match e with
    | .const n _ => some n
    | .app f _ => head f
    | .mdata _ b => head b
    | _ => none
  let rec onlyBound (e : Expr) : Bool :=
    match e with
    | .const _ _ => true
    | .app f a => onlyBound f && onlyBound a
    | .mdata _ b => onlyBound b
    | .fvar _ => true
    | _ => false
  if onlyBound e then head e else none

def screen (roots : List Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if roots.any (fun r => r.isPrefixOf n) then
      count := count + 1
      let (hyps, body) := peel ci.type #[]
      if isTrue body then
        logInfo m!"A3R13T|TRIVIAL|{n}|True"
      else if reflexiveConclusion body then
        logInfo m!"A3R13T|TRIVIAL|{n}|reflexive"
      for h in hyps do
        if isFalse h then
          logInfo m!"A3R13T|FALSE_HYP|{n}"
        if h.equal body then
          logInfo m!"A3R13T|HYP_EQ|{n}|syntactic"
      match ci.value? (allowOpaque := true) with
      | some v =>
        if let some m := aliasOf v then
          if m != n then
            logInfo m!"A3R13T|ALIAS|{n}|{m}"
      | none => pure ()
  logInfo m!"A3R13T|COUNT|{count}"

end A3R13T
run_cmd A3R13T.screen [`Poincare.D7, `Poincare.D10, `Poincare.D12]
