# D1-mathlib-geometry-map — result card

> **Delivery note (sandbox).** The required shared path
> `/data3/guoshaoyang/workdir/lean_poincare/longrun/results/D1-mathlib-geometry-map.md`
> is outside the `workspace-write` sandbox (session workspace =
> `longrun/worktrees/D1_geometry_map`). Writing there was denied, and the escalation
> request failed closed because no approval answerer is available. This card (and the
> JSON beside it) is therefore mirrored at
> `<worktree>/longrun/results/D1-mathlib-geometry-map.md`. **Integrator action:** copy the
> two mirrored files to the shared `longrun/results/` directory, or grant the worker write
> access to it.

- **Task id:** `D1-mathlib-geometry-map`
- **Stage / lane:** D1 / scout+builder (`requires_lean: true`)
- **Model:** `deepseek-v4.1-flash-expires-on-0910`
- **Session:** `session-0657e2ff-2927-4960-ba5a-bf05709a7dae`
- **Started:** `2026-09-08T19:51:27+08:00` (worker heartbeat)
- **Finished:** `2026-09-08T19:58:00+08:00`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D1_geometry_map`
- **Shared files touched:** none under `Poincare/`; the shared `longrun/results/` write was
  denied by the sandbox (see delivery note).

## 1. What was built

A compilable Lean API probe at `Probe/GeometryApi.lean` (258 lines, sha256
`6102f8556e858a890245573c79ea0251e957f5513a3206a6a7cf70b31954493a`) that:

1. imports only modules that exist in the pinned mathlib (6 modules, all verified by
   compilation);
2. runs **54** successful `#check`s covering manifolds, tangent bundles, smooth maps,
   covariant derivatives, torsion, metric compatibility, Levi-Civita connections,
   Riemannian structures, fiberwise inner products, and finite-dimensional traces;
3. contains **9** kernel-checked toy lemmas/definitions that actually use the discovered
   APIs (see §4);
4. contains no placeholder proof, no extra logical assumption, no compiler-trusting
   declaration, no statement-only stub
   (`grep -nE "sorry|axiom|unsafe|native_decide|proof_wanted" Probe/GeometryApi.lean` → no
   matches, exit code 1);
5. encodes the **missing** Riemann curvature tensor as an explicit compilable interface
   `Probe.CurvatureTensor` plus a trace-based Ricci contraction, with checked toy theorems;
6. compiles with `lake env lean Probe/GeometryApi.lean`, exit code 0, with zero errors and
   zero warnings.

### Worktree bootstrap

The assigned worktree was empty, so it was bootstrapped as an isolated Lake workspace that
resolves the already-built pinned mathlib without touching `poincare-lab/`:

- copied `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` from `poincare-lab/`;
- symlinked `.lake/packages -> /data3/guoshaoyang/workdir/lean_poincare/poincare-lab/.lake/packages`
  (read-only use of the prebuilt mathlib oleans; no shared file modified).

Pinned dependency:

- mathlib4 `7974e751bece493b6ff508039423ca9fa2452fa8`
- toolchain `leanprover/lean4:v4.34.0-rc2`

## 2. Exact command and exit code

```text
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D1_geometry_map
export PATH=/data3/guoshaoyang/workdir/lean_poincare/elan/bin:$PATH
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
lake env lean Probe/GeometryApi.lean
exit code: 0
```

Compiler stdout/stderr was captured verbatim in `Probe/GeometryApi.check.log`
(237 lines, 0 errors, 0 warnings). The 54 `#check` signatures are in that log; the last
three lines are the intentional `#check_failure` probes:

```text
Unknown identifier `RiemannCurvatureTensor`
Unknown identifier `RiemannianCurvature`
Unknown identifier `RicciTensor`
```

## 3. Imports (all exist in the pinned mathlib)

```lean
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.LinearAlgebra.Trace
```

`LeviCivita` transitively provides `CovariantDerivative/Basic.lean`,
`CovariantDerivative/Metric.lean`, `CovariantDerivative/Torsion.lean`,
`VectorBundle/Tangent.lean`, `VectorBundle/ContMDiffSection.lean`; `Riemannian.Basic`
provides `IsRiemannianManifold`, `riemannianEDist` and `riemannianMetricVectorSpace`;
`LinearAlgebra.Trace` provides `LinearMap.trace` and `LinearMap.trace_id`.

## 4. Checked toy lemmas (all `#print axioms` clean)

| Declaration | Statement | APIs exercised |
| --- | --- | --- |
| `Probe.trace_id_toy` | `trace R V id = finrank R V` | `LinearMap.trace`, `LinearMap.trace_id`, `Module.finrank` |
| `Probe.inner_self_nonneg_toy` | `0 ≤ inner ℝ v v` | `inner`, `real_inner_self_nonneg` |
| `Probe.torsion_antisymm_toy` | `cov.torsion x X₀ Y₀ = - cov.torsion x Y₀ X₀` | `CovariantDerivative.torsion`, `.torsion_antisymm` |
| `Probe.leviCivita_isLeviCivita_toy` | `(leviCivitaConnection I M).IsLeviCivitaConnection` | `CovariantDerivative.leviCivitaConnection`, `.isLeviCivitaConnection_leviCivitaConnection` |
| `Probe.leviCivita_uniqueness_toy` | any Levi-Civita `cov` agrees with `leviCivitaConnection` on differentiable vector fields | `IsLeviCivitaConnection.uniqueness` (Koszul formula) |
| `Probe.CurvatureTensor.self_eq_zero` | `R(X,X)Z = 0` | missing-curvature interface, antisymmetry |
| `Probe.CurvatureTensor.bianchi_toy` | `R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0` | missing-curvature interface, first Bianchi field |
| `Probe.CurvatureTensor.ricci_add_toy` | `Ric(Y+Y',Z) = Ric(Y,Z) + Ric(Y',Z)` | `endo`, `ricci`, `LinearMap.trace` additivity |
| `Probe.CurvatureTensor.ricci_zero_toy` | zero curvature has zero Ricci contraction | `CurvatureTensor.zero`, `ricci`, `LinearMap.trace` |

`#print axioms` output (run by appending the audit commands to a copy of the probe and
compiling it; the probe file itself is kept free of the audited token):

```text
'Probe.trace_id_toy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.inner_self_nonneg_toy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.torsion_antisymm_toy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.leviCivita_isLeviCivita_toy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.leviCivita_uniqueness_toy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.CurvatureTensor.self_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.CurvatureTensor.bianchi_toy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.CurvatureTensor.ricci_add_toy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.CurvatureTensor.ricci_zero_toy' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only Lean's three standard axioms appear; there is no `sorryAx` and no project axiom.

## 5. API map (54 checked declarations)

**Manifolds, tangent bundles, smooth maps** —
`ModelWithCorners`, `ChartedSpace`, `IsManifold`, `TangentSpace`, `TangentBundle`,
`Bundle.TotalSpace`, `Bundle.Trivial`, `tangentBundleCore`, `ContMDiff`, `ContMDiffAt`,
`MDifferentiable`, `MDifferentiableAt`, `HasMFDerivAt`, `mfderiv`, `tangentMap`,
`ContMDiffMap`, `ContMDiffSection`, `Diffeomorph`, `VectorField.mlieBracket`.

**Connections / covariant derivatives** —
`IsCovariantDerivativeOn`, `ContMDiffCovariantDerivativeOn`, `CovariantDerivative`,
`CovariantDerivative.ContMDiffCovariantDerivative`, `CovariantDerivative.addOneForm`,
`CovariantDerivative.affineCombination`, `CovariantDerivative.difference`,
`CovariantDerivative.torsion`, `.torsion_apply`, `.torsion_self`, `.torsion_antisymm`,
`CovariantDerivative.derivMetricTensor`, `CovariantDerivative.IsMetricCompatible`,
`.mvfderiv_inner_eq`, `CovariantDerivative.IsLeviCivitaConnection`,
`.apply_eq`, `.uniqueness`, `CovariantDerivative.leviCivitaConnection`,
`CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection`.

**Riemannian structure / inner products** —
`Bundle.RiemannianBundle`, `Bundle.RiemannianMetric`, `IsContMDiffRiemannianBundle`,
`ContMDiffRiemannianMetric`, `IsRiemannianManifold`, `riemannianEDist`, `inner`,
`innerSL`, `real_inner_self_nonneg`, `riemannianMetricVectorSpace`.

**Finite-dimensional traces** —
`LinearMap.trace`, `LinearMap.trace_id`, `LinearMap.trace_comp_comm`,
`LinearMap.trace_eq_matrix_trace`, `Matrix.trace`, `Module.finrank`.

## 6. Missing API encoded as an interface

`grep -ri curvature Mathlib` on the pinned tree finds only one passing comment
(`MeasureTheory/Measure/Doubling.lean`); there is **no** Riemann curvature tensor, no Ricci
tensor and no scalar curvature. `#check_failure` records this for
`RiemannCurvatureTensor`, `RiemannianCurvature`, `RicciTensor`.

`Probe.CurvatureTensor I M` is the explicit compilable interface:

```lean
structure CurvatureTensor {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] where
  toFun : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x
  antisymm : ∀ x X Y Z, toFun x X Y Z = - toFun x Y X Z
  bianchi  : ∀ x X Y Z, toFun x X Y Z + toFun x Y Z X + toFun x Z X Y = 0
```

Around it the probe defines `CurvatureTensor.zero`, `CurvatureTensor.endo`
(`X ↦ R(X,Y)Z`), `CurvatureTensor.ricci` (`Ric(Y,Z) = tr(X ↦ R(X,Y)Z)` via
`LinearMap.trace`), and the checked toys 6–9 listed above.

## 7. Blockers and suggested follow-ups

| Blocker | Evidence | Suggested follow-up |
| --- | --- | --- |
| No Riemann curvature tensor | `#check_failure RiemannCurvatureTensor`; `grep -ri curvature` → one comment only | `D2-geometry-foundation`: define curvature from `CovariantDerivative` (or accept `CurvatureTensor` as hypothesis) |
| No Ricci/scalar curvature | `#check_failure RicciTensor` | `D2-geometry-foundation` / `D3-kappa-ledger` |
| No geodesics, exponential map, or parallel transport | `grep -rli "geodesic\|expMap" Mathlib/Geometry` → no hits; `Metric.lean` lists parallel transport as TODO | new `D2-geometry-foundation` subtask |
| Levi-Civita connection is not known to be `C^k` (smoothness unproved upstream) | `LeviCivita.lean` header: "Future PRs will prove smoothness" | track upstream; state smoothness as hypothesis in D2 |
| Covariant derivative only known to depend on the germ, not the 1-jet, of a section | TODO in `CovariantDerivative/Basic.lean` (planned `Ehresmann.lean`) | D2 interface with explicit hypothesis if needed |
| No Ehresmann connection / second fundamental form / curvature of submanifolds | planned upstream files absent | not on the critical path for Ricci flow; note only |

No mathematical blocking condition prevented this task from completing: the probe compiles
with exit code 0 and the missing curvature API is encoded as a compilable interface with
checked toy theorems, as required. The only unresolved delivery issue is the sandbox denial
of the shared `longrun/results/` path.

## 8. Files changed

Worktree `D1_geometry_map` (not a git repository; hash-addressed):

- `Probe/GeometryApi.lean` (new, 258 lines)
- `Probe/GeometryApi.check.log` (new, captured compiler output)
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` (new, copied from `poincare-lab/`)
- `.lake/packages` (new symlink to the shared prebuilt mathlib packages)
- `longrun/results/D1-mathlib-geometry-map.md` (this mirrored card)
- `longrun/results/D1-mathlib-geometry-map.json` (mirrored machine-readable result)

Intended shared destination (write denied by sandbox):

- `/data3/guoshaoyang/workdir/lean_poincare/longrun/results/D1-mathlib-geometry-map.md`
- `/data3/guoshaoyang/workdir/lean_poincare/longrun/results/D1-mathlib-geometry-map.json`
