# D7-geodesic-exponential — geodesic / exponential-map layer

- **Task**: `D7-geodesic-exponential`
- **Worktree**: `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-geodesic-exponential`
- **Status**: `DONE`
- **Repair**: attempt 1 — the compile gate had no lake project at the worktree root; fixed by adding
  the root gate scaffold only (see §7). All 72 `.lean` files now exit 0 under the gate command.
- **Lean**: `leanprover/lean4:v4.34.0-rc2` (commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`)
- **mathlib**: rev `7974e751bece493b6ff508039423ca9fa2452fa8` (`release/lake-manifest.json`)
- **Authored**: 8 files, 851 lines, all under `release/Poincare/D7/Geodesic/`
- **Machine-readable card**: `longrun/results/D7-geodesic-exponential.json`

## 0. Scaffold

- Prescribed: `cp -al ../D6_weekly_release/. .`
- **Outcome: failed.** Hard links across the two worktrees are rejected by the workspace sandbox
  with `Invalid cross-device link` (EXDEV), even though both trees live on `/data3`
  (`stat -c %d` = `66313` for both). Minimal repro:
  `ln ../D6_weekly_release/README.md ./_t3` → `EXDEV`; hard links *inside* the worktree succeed.
- **Fallback used**: `cp -a ../D6_weekly_release/. .` (byte-identical recursive copy).
- **Baseline integrity** (verified): `diff -rq --exclude=.lake --exclude=D7` against
  `../D6_weekly_release` reports **no differences inside `release/`**; `input/`, `tools/`,
  `manifest/`, `negcontrol/`, `logs/` and `README.md` are byte-identical. No copied source file was
  modified; only `.lake` build outputs were refreshed and new `D7` files were added. The only
  extra root-level entries after the attempt-1 repair are the three gate-scaffold files of §7
  (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`) and this card; they do not touch any
  copied baseline content.

## 1. Mathlib probe (exact paths)

Probe artifacts: grep over `release/.lake/packages/mathlib` plus the kernel-checked file
`release/Poincare/D7/Geodesic/MathlibProbe.lean` (uses `#check_failure` for absent names and
`#check` for present ones; compiles with exit 0).

### 1.1 Riemannian geodesics — absent

There is **no** geodesic curve, geodesic equation, geodesic flow/spray, or Christoffel symbol for a
covariant derivative in the pinned mathlib. `grep -rin geodesic Mathlib/` matches only four files,
all unrelated to Riemannian geodesics:

| path | declaration / context | what it actually is |
|---|---|---|
| `Mathlib/Geometry/Group/WordMetric.lean:68` | `Group.Generators.IsGeodesic` | word geodesic in a group (length-minimal word) |
| `Mathlib/GroupTheory/FreeGroup/NielsenSchreier.lean:315` | `geodesicSubtree` | spanning tree of a free groupoid |
| `Mathlib/Analysis/Complex/UpperHalfPlane/FixedPoints.lean` | docstring | mentions a geodesic line in the half-plane |
| `Mathlib/Combinatorics/Quiver/Arborescence.lean` | docstring | unrelated mention |

Kernel-checked absence (`#check_failure` succeeds because the name is unknown): `Geodesic`,
`IsGeodesic` (root namespace), `GeodesicCurve`, `GeodesicEquation`, `geodesicFlow`, `GeodesicSpray`.

### 1.2 Exponential map — absent

No `expMap`, `Riemannian.exp` or `ExponentialMap` for a Riemannian metric (`#check_failure`
passes). Nearest namesakes, none of which is the Riemannian exponential:

- `Circle.exp` (`Mathlib/Analysis/Complex/Circle.lean`),
- `exp_map_apply` for nilpotent derivations (`Mathlib/Algebra/Lie/Derivation/Basic.lean:419`),
- `expMap` on the number-field `realSpace`
  (`Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean`).

### 1.3 Second-order ODE existence — absent

`Mathlib/Analysis/ODE/` (`Basic.lean`, `ExistUnique.lean`, `PicardLindelof.lean`, `Gronwall.lean`,
`Transform.lean`, `DiscreteGronwall.lean`) is **first order only**:

| declaration | path:line |
|---|---|
| `IsIntegralCurve` / `IsIntegralCurveOn` / `IsIntegralCurveAt` | `Mathlib/Analysis/ODE/Basic.lean:44-54` |
| `IsPicardLindelof` | `Mathlib/Analysis/ODE/PicardLindelof.lean:79` |
| `exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt` (local existence) | `Mathlib/Analysis/ODE/ExistUnique.lean:144` |
| `ODE_solution_unique` (uniqueness) | `Mathlib/Analysis/ODE/ExistUnique.lean:326` |

Manifold-level first-order theory (`Mathlib/Geometry/Manifold/IntegralCurve/`):

| declaration | path:line |
|---|---|
| `IsMIntegralCurve` | `Basic.lean:77` |
| `exists_isMIntegralCurveAt_of_contMDiffAt` (local in time, needs `[CompleteSpace E]`) | `ExistUnique.lean:65` |
| `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff` (uniqueness) | `ExistUnique.lean:189` |
| `IsMIntegralCurve.comp_mul_ne_zero` (time rescaling) | `Transform.lean:126` |

No occurrence of "second order" exists anywhere in those directories. Consequently the geodesic
equation — second order on `M`, or first order on `TM` for the geodesic spray — has **no**
existence or uniqueness theorem in mathlib.

### 1.4 What does exist and is consumed

| declaration | path:line |
|---|---|
| `CovariantDerivative` | `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean:366` |
| `IsCovariantDerivativeOn` | `.../CovariantDerivative/Basic.lean:92` |
| `ContMDiffCovariantDerivative` | `.../CovariantDerivative/Basic.lean:412` |
| `CovariantDerivative.IsMetricCompatible` | `.../CovariantDerivative/Metric.lean:155` |
| `CovariantDerivative.torsion` | `.../CovariantDerivative/Torsion.lean:120` |
| `CovariantDerivative.IsLeviCivitaConnection` | `.../CovariantDerivative/LeviCivita.lean:201` |
| `CovariantDerivative.leviCivitaConnection` | `.../CovariantDerivative/LeviCivita.lean:359` |
| `CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection` | `.../CovariantDerivative/LeviCivita.lean:408` |
| `Bundle.RiemannianBundle` | `Mathlib/Topology/VectorBundle/Riemannian.lean:420` |
| `IsRiemannianManifold` | `Mathlib/Geometry/Manifold/Riemannian/Basic.lean:81` |
| `Manifold.pathELength` | `Mathlib/Geometry/Manifold/Riemannian/PathELength.lean:66` |
| `Manifold.riemannianEDist` | `Mathlib/Geometry/Manifold/Riemannian/PathELength.lean:208` |
| `IsLocalDiffeomorphAt` | `Mathlib/Geometry/Manifold/LocalDiffeomorph.lean:158` |
| `HasStrictFDerivAt.localInverse` (Banach inverse function theorem) | `Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean:149` |
| `ContDiffAt.to_local_inverse` | `Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean:66` |

## 2. The `GeodesicData` interface

Because mathlib has no geodesic equation at all, the interface is needed even more strongly than
the task anticipated. In the model space `E` (a normed `ℝ`-vector space) the geodesic equation is
the explicit second-order ODE

```
γ''(t) = Γ (γ t) (γ' t) (γ' t),      Γ : E →L[ℝ] E →L[ℝ] E →L[ℝ] E
```

with the sign convention that the classical Christoffel symbol is `-Γ`. File:
`release/Poincare/D7/Geodesic/Basic.lean`.

`GeodesicData E` fields (all hypotheses visible):

| field | type | role |
|---|---|---|
| `Γ` | `E →L[ℝ] E →L[ℝ] E →L[ℝ] E` | connection / Christoffel symbol |
| `p` | `E` | initial point |
| `v` | `E` | initial velocity |
| `curve` | `ℝ → E` | solution curve |
| `curve_zero` | `curve 0 = p` | initial condition |
| `deriv_curve_zero` | `deriv curve 0 = v` | initial velocity condition |
| `isGeodesic` | `IsGeodesic Γ curve` | the geodesic equation (two explicit `HasDerivAt` requirements) |

Supporting definitions: `FlatMetric` (symmetric positive-definite continuous bilinear form) and
`IsMetricCompatible g Γ` := `∀ x v w u, g.metric (Γ x v w) u + g.metric w (Γ x v u) = 0`
(the flat-metric form of `∇g = 0` for the covariant derivative `∇_X W = D_X W - Γ(X,W)`).

## 3. Kernel-checked toy theorems

### 3.1 Uniqueness in the flat/affine model — `FlatUniqueness.lean`

| theorem | statement |
|---|---|
| `deriv_affine` | `deriv (fun t => p + t • v) = fun _ => v` |
| `isAffineGeodesic_affine` | `t ↦ p + t • v` is an affine geodesic (existence) |
| `deriv_eq_const_of_isAffineGeodesic` | `IsAffineGeodesic γ → deriv γ t = deriv γ 0` |
| `eq_affine_of_isAffineGeodesic` | `IsAffineGeodesic γ → γ t = γ 0 + t • deriv γ 0` |
| `eq_of_isAffineGeodesic_init` | **uniqueness**: equal initial point and velocity ⇒ `γ₁ = γ₂` everywhere |
| `flatGeodesicData` | the `GeodesicData` with `Γ = 0`, `curve t = p + t • v` |
| `flatGeodesicData_unique` | any `GeodesicData` with `Γ = 0`, `p`, `v` has this curve |

The proof reduces `γ'' = 0` to constant first derivative via
`is_const_of_deriv_eq_zero` (`Mathlib/Analysis/Calculus/MeanValue.lean:751`).

### 3.2 Constant speed under metric compatibility — `MetricSpeed.lean`

| theorem | statement |
|---|---|
| `GeodesicData.speed_hasDerivAt_zero` | `IsMetricCompatible g Γ` ⇒ the squared speed `t ↦ g(γ' t, γ' t)` has derivative `0` at every `t` |
| `GeodesicData.speed_const` | `g(γ' t, γ' t) = g(v, v)` for all `t` (constant speed) |
| `innerFlatMetric` | the canonical inner-product metric as a `FlatMetric` |
| `flatGeodesicData_speed_const` | concrete: `⟪γ' t, γ' t⟫_ℝ = ⟪v, v⟫_ℝ` |

The two product-rule terms from `HasDerivAt.clm_apply` cancel exactly by
`IsMetricCompatible g Γ` at `(γ t, γ' t, γ' t, γ' t)`.

### 3.3 Affine reparametrisation — `Reparam.lean`

| theorem | statement |
|---|---|
| `hasDerivAt_affine` | `HasDerivAt (fun s => a * s + b) a t` |
| `isGeodesic_comp_affine` | `IsGeodesic Γ γ → IsGeodesic Γ (fun t => γ (a * t + b))` |
| `GeodesicData.reparam` | reparametrised `GeodesicData`: new `p = γ b`, new `v = a • γ' b` |
| `GeodesicData.reparam_isGeodesic` | the reparametrised curve solves the same geodesic equation |
| `GeodesicData.reparam_curve/_Gamma/_p/_v` | projection lemmas (`@[simp]`) |

The chain rule (`HasDerivAt.scomp`) gives `(γ ∘ σ)'' t = a² • γ''(σ t)`, and bilinearity of `Γ`
gives `Γ(γ(σ t))(a • γ'(σ t))(a • γ'(σ t)) = a² • Γ(γ(σ t))(γ'(σ t))(γ'(σ t))`.

### 3.4 Sanity checks — `Smoke.lean`

Inhabitedness (`Nonempty (GeodesicData E)`), projection computations, affine reparametrisation and
the concrete constant-speed statement are all instantiated by compiled `example`s.

## 4. State-only interfaces and their exact missing dependencies

File: `release/Poincare/D7/Geodesic/ManifoldInterfaces.lean`. The single missing primitive is the
**covariant acceleration of a curve** `∇_{γ'}γ'` (pullback connection / geodesic spray); it is
recorded as explicit interface data

```
GeodesicContext { cov : CovariantDerivative I E (TangentSpace I),
                  accel : (γ : ℝ → M) → (t : ℝ) → TangentSpace I (γ t),
                  accel_is_covariant_acceleration : Prop }
```

and `IsManifoldGeodesic S γ := ∀ t, S.accel γ t = 0`. The three interfaces are `def`s of type
`Prop` — statements, never asserted:

| interface | statement (abbreviated) | exact missing dependency |
|---|---|---|
| `GeodesicExistenceOnCompleteManifolds` | for all `p, v` there are `γ, V` with `γ 0 = p`, `V p = v`, `IsMIntegralCurve γ V`, `IsManifoldGeodesic S γ` | covariant acceleration along curves + global existence for the second-order geodesic ODE from completeness. Mathlib has only *local* first-order existence (`exists_isMIntegralCurveAt_of_contMDiffAt`). |
| `HopfRinow` | for all `p, q` there are `γ, V` with `γ 0 = p`, `γ 1 = q`, `IsMIntegralCurve γ V`, `IsManifoldGeodesic S γ`, `pathELength I γ 0 1 = riemannianEDist I p q` | everything above, plus the exponential map and the minimizing-geodesic / length-comparison theorem. Mathlib has `pathELength` and `riemannianEDist` but no geodesic minimizer theory. |
| `ExpMapLocalDiffeomorphism` | for each `p` there is `e : T_pM → M` with `e 0 = p`, `IsLocalDiffeomorphAt (𝓘(ℝ, T_pM)) I ∞ e 0`, and `e v` is the time-one endpoint of a geodesic with initial velocity `v` | the exponential map (geodesic equation on manifolds), `d exp_p(0) = id`, and a manifold-level inverse function theorem. Mathlib has `IsLocalDiffeomorphAt` and the Banach-space inverse function theorem, but no theorem producing a local diffeomorphism for `exp_p`. |

## 5. Verification evidence

- **Per-file `lake env lean`** (all exit 0):

  | file | exit | time |
  |---|---|---|
  | `Poincare/D7/Geodesic/Basic.lean` | 0 | 3.5 s |
  | `Poincare/D7/Geodesic/FlatUniqueness.lean` | 0 | 2.4 s |
  | `Poincare/D7/Geodesic/MetricSpeed.lean` | 0 | 2.3 s |
  | `Poincare/D7/Geodesic/Reparam.lean` | 0 | 2.5 s |
  | `Poincare/D7/Geodesic/ManifoldInterfaces.lean` | 0 | 2.4 s |
  | `Poincare/D7/Geodesic/MathlibProbe.lean` | 0 | 2.3 s |
  | `Poincare/D7/Geodesic/AxiomAudit.lean` | 0 | 2.2 s |
  | `Poincare/D7/Geodesic/Smoke.lean` | 0 | 2.1 s |

- **Full compile gate** (attempt-1 repair re-run, exact `dispatch_loop.compile_gate` algorithm:
  `os.walk` the worktree, skip `.lake`/`.git`/`.dshpkg`, `lake env lean <abs path>` with
  `cwd = worktree root`): **72 `.lean` files checked, 72 exit 0, 0 failures**. The 8 authored files
  are among them (see §7). A minimal-environment re-check (`env -i` with only `HOME`, `ELAN_HOME`,
  `PATH`) on `release/Poincare/D7/Geodesic/Smoke.lean` also exits 0.
- **`lake build Poincare`**: exit 0 (8936 jobs), whole library including the D6 baseline plus this
  layer.
- **`#print axioms`** (`AxiomAudit.lean`, driver exit 0): **38 declarations checked**, one distinct
  axiom cone — `[propext, Classical.choice, Quot.sound]` (Lean's three standard axioms). No
  `sorryAx`, no project axiom, no `native_decide` axiom, no `proof_wanted`. The per-declaration
  list is in the JSON card.
- **Forbidden-token scan** (`input/d5-tools/scan_forbidden.py`, comment/string aware) over the 8
  authored files: **0** hard matches (`sorry`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`,
  `sorryAx`, `admit`), **0** soft matches (`implemented_by`, `extern`). (The copied negative control
  `negcontrol/NegativeControl.lean` intentionally contains `sorry`/`native_decide` and is not an
  authored file; it is not part of the release library.)
- **Baseline integrity**: copied D6 sources unchanged (see §0).

## 6. Files added

```
release/Poincare/D7/Geodesic/AxiomAudit.lean           (71 lines)
release/Poincare/D7/Geodesic/Basic.lean                (135 lines)
release/Poincare/D7/Geodesic/FlatUniqueness.lean       (141 lines)
release/Poincare/D7/Geodesic/ManifoldInterfaces.lean   (121 lines)
release/Poincare/D7/Geodesic/MathlibProbe.lean         (93 lines)
release/Poincare/D7/Geodesic/MetricSpeed.lean          (107 lines)
release/Poincare/D7/Geodesic/Reparam.lean              (117 lines)
release/Poincare/D7/Geodesic/Smoke.lean                (66 lines)
longrun/results/D7-geodesic-exponential.md             (this card)
longrun/results/D7-geodesic-exponential.json           (machine-readable card)
```

No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs in any authored file.

## 7. Compile-gate repair (attempt 1)

### 7.1 Symptom and root cause

The attempt-1 `gate.json` was removed by the dispatcher when it queued this repair
(`dispatch_loop.write_repair_prompt` deletes it), so the per-file table was not recoverable.
Re-running the gate command (`lake env lean <abs path>` with `cwd` = the worktree **root**)
reproduces the failure for every `.lean` file, with:

```
error: no default toolchain configured. run `elan default stable` to install & configure the latest Lean 4 stable release.
```

Root cause: the D5/D6 scaffold put the lake project in `release/`, so the worktree root had no
`lean-toolchain`, no `lakefile.toml`, no `lake-manifest.json` and no `.lake`. The gate, however,
runs from the worktree root. With no toolchain file in the root or any ancestor, `elan` has no
default toolchain and fails before Lean is even started. This is a gate-environment defect, not a
Lean error in the authored files: the 8 authored files already compiled with exit 0 from `release/`
(§5, first table).

### 7.2 Fix (gate scaffold only — no mathematical content changed)

The worktree root now carries the same root-level lake project layout as the previously verified
D1–D4 worktrees:

| root entry | content |
|---|---|
| `lakefile.toml` | byte-identical copy of `release/lakefile.toml` (`PoincareRelease`, mathlib require, all lean_libs) |
| `lake-manifest.json` | byte-identical copy of `release/lake-manifest.json` (mathlib rev `7974e751`) |
| `lean-toolchain` | byte-identical copy of `release/lean-toolchain` |
| `.lake` | symlink to `release/.lake` (shared package store + already-built release outputs) |

No copied D6 source file and no authored D7 file was modified. `diff -rq --exclude=.lake
--exclude=D7` against `../D6_weekly_release` now reports only these three new root files and this
card; everything inside `release/` remains byte-identical to D6.

### 7.3 Re-run of the exact gate

| scope | files | exit 0 | failures |
|---|---|---|---|
| whole worktree (gate algorithm, cwd = root) | 72 | 72 | 0 |
| authored D7 files | 8 | 8 | 0 |

Authored-file timings in the re-run: `Basic` 3.6 s, `FlatUniqueness` 2.5 s, `MetricSpeed` 2.5 s,
`Reparam` 2.5 s, `ManifoldInterfaces` 2.5 s, `MathlibProbe` 2.3 s, `AxiomAudit` 2.3 s, `Smoke`
2.3 s. The full per-file exit table is in the JSON card (`verification.full_compile_gate`).

TASK_DONE — longrun/results/D7-geodesic-exponential.md
