/-
SEMREV-L3 independent review — round 2, Stage D: whole-environment inhabitant search.

The round-1 review established that `SpatialLaplacianBridge` has no inhabitant by enumerating
only the constants whose *name* mentions `HeatTimeDeriv`. This probe strengthens that:

  1. it computes the **transitive closure of definitions** whose value mentions any of the
     signature constants of the targets (`heatConv`, `gaussianKernel`, `timeDerivIntegral`,
     `timeCoeff`, `HasDerivAt`, …), so a statement phrased through an alias/abbreviation is not
     missed;
  2. it collects **every constant in the environment whose type mentions that closure**;
  3. for each such candidate it tests definitional equality (transparency `.all`, so named and
     fully unfolded statements are both caught) at **every depth of leading ∀-binders**.

Targets:
  * `SpatialLaplacianBridge`         — expected: 0 inhabitants (statement-only residual);
  * `UniformMildToClassicalBridge`   — expected: >= 1 (`uniformMildToClassicalBridge_holds`);
  * `D12.ParabolicLocal.mildToClassicalBridge` — the discharged obligation, expected >= 1;
  * `KernelClassicalHeatSolution`    — positive control: a *Type* target known to have an
    inhabitant (`heatConv_classicalHeatSolution`), so a search that finds it is non-vacuous.

Rows are `SEMREV-INHAB|<target>|<constant>|<kind>`; summary lines follow. The file aborts
(exit 1) if any expected-inhabited target has no inhabitant, so an instrumentation failure cannot
masquerade as "0 inhabitants".
-/

import Poincare.L3.HeatTimeDeriv.All
import Lean

open Lean Meta Elab Command

namespace SemrevInhabitants

/-- `(target, expectInhabited)` — the props/types searched for in the whole environment. -/
def targets : List (Name × Bool) :=
  [ (``Poincare.L3.HeatTimeDeriv.SpatialLaplacianBridge, false),
    (``Poincare.L3.HeatTimeDeriv.UniformMildToClassicalBridge, true),
    (``Poincare.D12.ParabolicLocal.mildToClassicalBridge, true),
    (``Poincare.L3.HeatTimeDeriv.KernelClassicalHeatSolution, true) ]

/-- Signature constants: any statement about one of the targets must mention one of these
(possibly through a chain of definitions, closed below). -/
def baseIngredients : List Name :=
  [ ``Poincare.L3.HeatTimeDeriv.SpatialLaplacianBridge,
    ``Poincare.L3.HeatTimeDeriv.UniformMildToClassicalBridge,
    ``Poincare.L3.HeatTimeDeriv.KernelClassicalHeatSolution,
    ``Poincare.D12.ParabolicLocal.mildToClassicalBridge,
    ``Poincare.D12.ParabolicLocal.heatConv,
    ``Poincare.D12.HeatSemigroup.heatOperator,
    ``Poincare.L3.HeatTimeDeriv.timeDerivIntegral,
    ``Poincare.L3.HeatTimeDeriv.timeCoeff,
    ``Poincare.L3.HeatTimeDeriv.timeDerivKernel,
    ``Poincare.D10.HeatKernelEuclidean.gaussianKernel,
    ``HasDerivAt ]

/-- Syntactic occurrence of a constant from `s` anywhere in `e`. -/
partial def mentions (s : Std.HashSet Name) : Expr → Bool
  | .const n _ => s.contains n
  | .app f a => mentions s f || mentions s a
  | .lam _ t b _ => mentions s t || mentions s b
  | .forallE _ t b _ => mentions s t || mentions s b
  | .letE _ t v b _ => mentions s t || mentions s v || mentions s b
  | .mdata _ b => mentions s b
  | .proj _ _ b => mentions s b
  | _ => false

/-- Short kind tag. -/
def kindOf : ConstantInfo → String
  | .axiomInfo _ => "AXIOM"
  | .defnInfo v => if v.safety == .unsafe then "UNSAFE-DEF" else "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

/-- Test `e` against every target, then recurse under each leading ∀-binder (so that both a
statement written with the target name and a statement written out in full are caught).
Returns `(hits, skipped)`. -/
partial def scanType (e : Expr) (cname : Name) (acc : Array (Name × Name)) (skipped : Nat) :
    MetaM (Array (Name × Name) × Nat) := do
  let mut acc := acc
  let mut skipped := skipped
  for (tgt, _) in targets do
    let nvar ← mkFreshExprMVar (mkConst ``Nat)
    let tgtApp := mkApp (mkConst tgt) nvar
    let res ← try
        some <$> withTransparency .all (isDefEq e tgtApp)
      catch _ => pure none
    match res with
    | some true => acc := acc.push (tgt, cname)
    | some false => pure ()
    | none => skipped := skipped + 1
  match e with
  | .forallE _ d b _ =>
      withLocalDeclD `_x d fun x => scanType (b.instantiate1 x) cname acc skipped
  | _ => pure (acc, skipped)

/-- The whole search, in `TermElabM`. -/
def search : TermElabM Unit := do
  let env ← getEnv
  let consts := env.constants.toList
  logInfo s!"SEMREV-INHAB|ENV|constants|{consts.length}"
  -- 1. transitive closure of definitions mentioning the ingredients
  let mut ing : Std.HashSet Name := {}
  for n in baseIngredients do
    ing := ing.insert n
  let mut rounds := 0
  let mut changed := true
  while changed && rounds < 12 do
    changed := false
    rounds := rounds + 1
    for (n, ci) in consts do
      if ing.contains n then continue
      match ci with
      | .defnInfo v => if mentions ing v.value then ing := ing.insert n; changed := true
      | _ => pure ()
  logInfo s!"SEMREV-INHAB|CLOSURE|size|{ing.size}|rounds|{rounds}|converged|{!changed}"
  -- 2. candidates whose type mentions the closure
  let mut candidates : Array (Name × ConstantInfo) := #[]
  for (cname, ci) in consts do
    if mentions ing ci.type then candidates := candidates.push (cname, ci)
  logInfo s!"SEMREV-INHAB|CANDIDATES|{candidates.size}"
  -- 3. defeq scan at every binder depth
  let mut hits : Array (Name × Name × String) := #[]
  let mut skippedTotal := 0
  for (cname, ci) in candidates do
    let (found, sk) ← scanType ci.type cname #[] 0
    skippedTotal := skippedTotal + sk
    for (tgt, cn) in found do
      hits := hits.push (tgt, cn, kindOf ci)
  logInfo s!"SEMREV-INHAB|SKIPPED|{skippedTotal}"
  let mut counts : Std.HashMap Name Nat := {}
  for (tgt, _) in targets do
    counts := counts.insert tgt 0
  for (tgt, cn, k) in hits do
    counts := counts.insert tgt (counts.getD tgt 0 + 1)
    logInfo s!"SEMREV-INHAB|{tgt}|{cn}|{k}"
  let mut ok := true
  for (tgt, expect) in targets do
    let c := counts.getD tgt 0
    logInfo s!"SEMREV-INHAB|SUMMARY|{tgt}|{c}"
    if expect && c == 0 then
      logError s!"SEMREV-INHAB: expected-inhabited target {tgt} found no inhabitant — instrumentation failure"
      ok := false
  if !ok then
    throwError "SEMREV-L3 inhabitant search: FAIL (instrumentation)"
  else
    logInfo "SEMREV-L3 inhabitant search: PASS (all positive controls found)"

end SemrevInhabitants

set_option maxHeartbeats 0 in
run_cmd liftTermElabM SemrevInhabitants.search
