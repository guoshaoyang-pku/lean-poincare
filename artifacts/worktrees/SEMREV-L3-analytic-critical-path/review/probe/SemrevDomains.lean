/-
SEMREV-L3 independent review — round 3, Stage F: machine-checked semantic class, Euclidean
scope and derivative-domain audit.

This probe adds three checks over the round-2 census:

  * **semantic class per declaration** (`SEMREV-CLASS`): for every constant whose name mentions
    `HeatTimeDeriv`, its declaration kind and whether it is a proposition-family `def`
    (`def … : Prop`, i.e. after peeling the ∀-telescope the body is the sort `Prop`) or data.
    Proposition-family defs are exactly the statement-only candidates; their inhabitants are
    counted by the companion `SemrevInhabitants.lean` search.
  * **statement-level Euclidean scope** (`SEMREV-SCOPE`): all `Poincare.*` constants occurring in
    each L3 declaration's type are collected; any outside the heat-kernel whitelist, and any
    occurrence of a geometric keyword (Ricci/curvature/manifold/surgery/…), is reported as a
    scope violation and aborts the probe. This checks the "Euclidean model only" claim against
    the *compiled types*, not against prose.
  * **derivative-domain audit** (`SEMREV-DOMAIN`): for every declaration whose type mentions
    `HasDerivAt`, the binder telescope is printed and tested for a positivity hypothesis
    (`0 <`, `Ioo`, `Ioi`, `𝓝[>`); any derivative statement without one is reported and fails the
    probe, so a domain restriction cannot silently disappear.

The file also contains kernel-checked `example`s for the domain facts themselves: the truncated
heat convolution is literally `0` at nonpositive times (D12 `heatConv_of_nonpos`), the L3
integrable formula is definitionally the written-out D12 integrand, and the D12 obligation is
definitionally equal to its from-source restatement.
-/

import Poincare.L3.HeatTimeDeriv.All
import Lean

open Lean Meta Elab Command

namespace SemrevDomains

/-- Constants whose occurrence in an L3 type would contradict the Euclidean-model scope claim. -/
def forbiddenKeywords : List String :=
  ["Ricci", "Riemann", "Curvature", "Manifold", "Surgery", "Monotonic", "Perelman",
   "Extinction", "MetricData", "DeTurck"]

/-- Poincare namespaces the L3 statements are allowed to mention. -/
def allowedPrefixes : List String :=
  ["Poincare.L3.HeatTimeDeriv.",
   "Poincare.D12.ParabolicLocal.",
   "Poincare.D12.HeatSemigroup.",
   "Poincare.D10.HeatKernelEuclidean.",
   "Poincare.D11.HeatKernelBridge."]

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "AXIOM"
  | .defnInfo v => if v.safety == .unsafe then "UNSAFE-DEF" else "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

/-- Does `t` occur in `e`? -/
partial def mentions (t : Name) : Expr → Bool
  | .const n _ => n == t
  | .app f a => mentions t f || mentions t a
  | .lam _ d b _ => mentions t d || mentions t b
  | .forallE _ d b _ => mentions t d || mentions t b
  | .letE _ d v b _ => mentions t d || mentions t v || mentions t b
  | .mdata _ b => mentions t b
  | .proj _ _ b => mentions t b
  | _ => false

/-- Collect the `Poincare.*` constants occurring in `e`. -/
partial def collectPoincare (acc : Std.HashSet Name) : Expr → Std.HashSet Name
  | .const n _ => if n.toString.startsWith "Poincare." then acc.insert n else acc
  | .app f a => collectPoincare (collectPoincare acc f) a
  | .lam _ d b _ => collectPoincare (collectPoincare acc d) b
  | .forallE _ d b _ => collectPoincare (collectPoincare acc d) b
  | .letE _ d v b _ => collectPoincare (collectPoincare (collectPoincare acc d) v) b
  | .mdata _ b => collectPoincare acc b
  | .proj _ _ b => collectPoincare acc b
  | _ => acc

/-- Peel the ∀-telescope syntactically. -/
partial def peeledBody : Expr → Expr
  | .forallE _ _ b _ => peeledBody b
  | e => e

/-- A `def` whose telescope ends in the sort `Prop` (a statement-only candidate). -/
def isPropFamily (ci : ConstantInfo) : Bool :=
  match peeledBody ci.type with
  | .sort .zero => true
  | _ => false

/-- All binder types of a telescope, pretty-printed (bvars appear as `_x`; enough to detect the
`0 <`, `Ioo`, `Ioi`, `𝓝[>` domain patterns). -/
partial def binderTypes (e : Expr) (acc : Array String) : MetaM (Array String) := do
  match e with
  | .forallE _ d b _ =>
    let s := (← ppExpr d).pretty
    withLocalDeclD `_x d fun x => binderTypes (b.instantiate1 x) (acc.push s)
  | _ => pure acc

run_cmd liftTermElabM do
  let env ← getEnv
  let mut classCount := 0
  let mut propDefs : Array Name := #[]
  let mut domainCount := 0
  let mut domainFail : Array Name := #[]
  let mut scopeOutside : Array (Name × Name) := #[]
  let mut keywordHits : Array (Name × Name) := #[]
  let mut poincareMentioned : Std.HashSet Name := {}
  for (n, ci) in env.constants.toList do
    if (n.toString.splitOn "HeatTimeDeriv").length > 1 then
      classCount := classCount + 1
      let cls := if isPropFamily ci then "prop-family" else "data"
      logInfo s!"SEMREV-CLASS|{n}|{kindOf ci}|{cls}"
      if isPropFamily ci then propDefs := propDefs.push n
      -- scope scan on the type
      let ps := collectPoincare {} ci.type
      for p in ps.toList do
        poincareMentioned := poincareMentioned.insert p
        if !allowedPrefixes.any (fun pre => p.toString.startsWith pre) then
          scopeOutside := scopeOutside.push (n, p)
        if forbiddenKeywords.any (fun k => (p.toString.splitOn k).length > 1) then
          keywordHits := keywordHits.push (n, p)
      -- domain scan
      if mentions ``HasDerivAt ci.type then
        domainCount := domainCount + 1
        let bs ← binderTypes ci.type #[]
        let s := String.intercalate " ; " bs.toList
        let hasPos := s.contains "0 <" || s.contains "Ioo" || s.contains "Ioi" || s.contains "𝓝[>"
        logInfo s!"SEMREV-DOMAIN|{n}|positivity|{if hasPos then "yes" else "NO"}|{s}"
        if !hasPos then domainFail := domainFail.push n
  logInfo s!"SEMREV-CLASS-SUMMARY|constants|{classCount}|prop-family|{propDefs.size}"
  for p in propDefs do
    logInfo s!"SEMREV-PROPDEF|{p}"
  logInfo s!"SEMREV-SCOPE-SUMMARY|poincare-constants-mentioned|{poincareMentioned.size}|outside-whitelist|{scopeOutside.size}|keyword-hits|{keywordHits.size}"
  for p in poincareMentioned.toList do
    logInfo s!"SEMREV-SCOPE-POINCARE|{p}"
  for (n, p) in scopeOutside do
    logError s!"SEMREV-SCOPE-OUTSIDE|{n}|{p}"
  for (n, p) in keywordHits do
    logError s!"SEMREV-SCOPE-KEYWORD|{n}|{p}"
  logInfo s!"SEMREV-DOMAIN-SUMMARY|derivative-declarations|{domainCount}|without-positivity|{domainFail.size}"
  if !scopeOutside.isEmpty then
    throwError "SEMREV-L3 scope audit: FAIL — {scopeOutside.size} out-of-whitelist Poincare constant(s)"
  if !keywordHits.isEmpty then
    throwError "SEMREV-L3 scope audit: FAIL — {keywordHits.size} geometric keyword hit(s)"
  if !domainFail.isEmpty then
    throwError "SEMREV-L3 domain audit: FAIL — {domainFail.size} derivative declaration(s) without a positivity hypothesis"
  logInfo "SEMREV-L3 class/scope/domain audit: PASS"

end SemrevDomains

/-! ## Kernel-checked domain and formula facts (examples, not part of the artifact) -/

namespace SemrevDomainsExamples

open MeasureTheory Real
open scoped Topology InnerProductSpace Laplacian RealInnerProductSpace
open Poincare.L3.HeatTimeDeriv
open Poincare.D12.ParabolicLocal
open Poincare.D10.HeatKernelEuclidean

/-- The truncated heat convolution is literally zero at `t = 0`: the `0 < t` hypotheses of every
L3 derivative statement are load-bearing, not decoration. -/
example (n : ℕ) (f : BUCn n) :
    heatConv n 0 f = 0 :=
  heatConv_of_nonpos n 0 le_rfl f

/-- …and at every negative time. -/
example (n : ℕ) {t : ℝ} (ht : t < 0) (f : BUCn n) :
    heatConv n t f = 0 :=
  heatConv_of_nonpos n t ht.le f

/-- `timeCoeff` is definitionally the D12 kernel time coefficient. -/
example (n : ℕ) (t : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    timeCoeff n t z = ‖z‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t) := rfl

/-- `timeDerivIntegral` is definitionally the written-out D12 integrand. -/
example (n : ℕ) (t : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    timeDerivIntegral n t f x =
      ∫ y : EuclideanSpace ℝ (Fin n),
        gaussianKernel n t (x - y) * timeCoeff n t (x - y) * f y := rfl

/-- The D12 obligation is **definitionally equal** to its from-source restatement (equality of
the two `Prop`s, not merely an application test). -/
example (n : ℕ) :
    mildToClassicalBridge n =
      (∀ {t : ℝ} (ht : 0 < t) (f : BUCn n),
        HasDerivAt (fun s : ℝ => fun x : EuclideanSpace ℝ (Fin n) => (heatConv n s f.val) x)
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ∫ y : EuclideanSpace ℝ (Fin n),
              Poincare.D10.HeatKernelEuclidean.gaussianKernel n t (x - y) *
                (‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) * f.val y) t) := by
  unfold mildToClassicalBridge
  rfl

end SemrevDomainsExamples
