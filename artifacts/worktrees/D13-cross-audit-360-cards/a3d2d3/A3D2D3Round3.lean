-- A3 round-3 kernel-level dependency screen for the L-D2-CURVATURE-IDENTITIES
-- overstrong-hypothesis claim (prior audit: "orthonormality unused" in
-- `MetricData.scalarCurvature_eq_sum_basis`).
--
-- Method: inspect the *proof term* of the compiled declaration, take the
-- transitive closure of the constants it uses, and check whether any of the
-- structure projections `form`, `symm`, `pos_def`, `orthonormal` occur in that
-- closure.  A constant that does not occur in the transitive proof cone is
-- definitely unused.  Positive controls (`form_basis_apply`) must reach
-- `orthonormal`; the negative controls (the contraction formula and the
-- raising-map expansion) must not reach any metric field.  Fail-closed.
import Poincare.Longrun.Geometry.MetricData
import Poincare.Stage1.CurvatureAlgebra

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let formFields : List Name :=
    [``Poincare.Longrun.Geometry.MetricData.form,
     ``Poincare.Longrun.Geometry.MetricData.symm,
     ``Poincare.Longrun.Geometry.MetricData.pos_def,
     ``Poincare.Longrun.Geometry.MetricData.orthonormal]
  let valueOf (n : Name) : Option Expr :=
    match env.find? n with
    | some (.thmInfo v) => some v.value
    | some (.defnInfo v) => some v.value
    | some (.opaqueInfo v) => some v.value
    | _ => none
  let transCone (root : Name) : Std.HashSet Name := Id.run do
    let mut visited : Std.HashSet Name := {}
    let mut stack : List Name := [root]
    while let some n := stack.head? do
      stack := stack.tail
      if visited.contains n then continue
      visited := visited.insert n
      if let some v := valueOf n then
        for c in v.getUsedConstants do
          if !visited.contains c then stack := c :: stack
    return visited
  -- (declaration, must the metric fields occur in the transitive proof cone?)
  let targets : List (Name × Bool) :=
    [(``Poincare.Longrun.Geometry.MetricData.scalarCurvature_eq_sum_basis, false),
     (``Poincare.Longrun.Geometry.MetricData.raiseIndex_eq_sum_smulRight, false),
     (``Poincare.Longrun.Geometry.MetricData.form_basis_apply, true),
     (``Poincare.Longrun.Geometry.MetricData.form_raiseIndex, true)]
  let mut bad : Nat := 0
  for (t, mustUse) in targets do
    match env.find? t with
    | none => logError m!"A3DEPS: missing {t}"; bad := bad + 1
    | some _ =>
      let cone := transCone t
      let hits := formFields.filter (fun f => cone.contains f)
      logInfo m!"A3DEPS: {t} transitive cone size {cone.size}; metric fields = {hits.map Name.toString}"
      if mustUse && hits.isEmpty then
        logError m!"A3DEPS-BAD: {t} expected to reach a metric field but reaches none"
        bad := bad + 1
      if !mustUse && !hits.isEmpty then
        logError m!"A3DEPS-BAD: {t} expected basis-only but reaches {hits.map Name.toString}"
        bad := bad + 1
  if bad == 0 then
    logInfo m!"A3DEPS: PASS (contraction formula basis-only in the transitive proof cone; positivity control reaches orthonormality)"
  else
    throwError "A3DEPS: FAIL ({bad} deviations)"
