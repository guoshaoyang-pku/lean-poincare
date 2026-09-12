# D2-geometry-foundation — result card

> **Delivery note (sandbox).** The canonical shared path
> `/data3/guoshaoyang/workdir/lean_poincare/longrun/results/D2-geometry-foundation.md`
> is outside the `workspace-write` sandbox (session workspace =
> `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D2_geometry_foundation`).
> A direct write attempt was denied (`touch` → `Permission denied`), and the escalation
> request failed closed (no approval answerer). This card and its JSON twin are therefore
> mirrored at `<worktree>/longrun/results/`. **Integrator action:** copy the two mirrored
> files to the shared `longrun/results/` directory, or grant the worker write access to it.
>
> Path note: the task prompt names the worktree `…/worktrees/D2_geometry`; the current
> runtime snapshot assigns `…/worktrees/D2_geometry_foundation` (the `D2_geometry` name does
> not exist on disk). All work was done in `D2_geometry_foundation`.

- **Task id:** `D2-geometry-foundation`
- **Stage / lane:** D2 / builder (`requires_lean: true`)
- **Model:** `deepseek-v4.1-flash-expires-on-0910`
- **Session:** `session-0124a812-acf6-4d1b-9312-692b28d82321`
- **Started:** `2026-09-08T23:36:00+08:00`
- **Finished:** `2026-09-08T23:55:00+08:00`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D2_geometry_foundation`
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (commit `6a10ac8c22be`)
- **mathlib:** revision `7974e751bece493b6ff508039423ca9fa2452fa8`
- **Existing Stage1 files:** never overwritten. The worktree contains *private copies*
  (byte-identical) of `Poincare/Stage1/CurvatureAlgebra.lean` and
  `Poincare/Stage1/RiemannAdapter.lean`; both hashes match the shared originals:
  - `CurvatureAlgebra.lean` sha256 `d2295c744bdabacf48fe2734b0e989b8d09bda651c7b61aa05b0729ded11b988`
  - `RiemannAdapter.lean` sha256 `a19c67087666e5fcca9d226972b4eaa5baf94822a11cd49f6a7385088aefd20b`

## 1. D1 result card consumed

The accepted card `D1-mathlib-geometry-map` (and its probe `Probe/GeometryApi.lean`) was
read in full. Its findings drive the design:

1. mathlib has `CovariantDerivative`, `CovariantDerivative.torsion`,
   `IsLeviCivitaConnection`, `leviCivitaConnection`, and Levi-Civita existence/uniqueness;
2. mathlib has **no** curvature tensor, no Ricci tensor, no scalar curvature
   (`#check_failure RiemannCurvatureTensor`, `#check_failure RicciTensor`);
3. Levi-Civita connection smoothness is unproved upstream.

Consequently this task builds the curvature adapter **algebraically** (with the missing
manifold curvature stated as an explicit `BLOCKED` `Prop`), rather than pretending to derive
curvature from a `CovariantDerivative`.

## 2. What was built

A compilable Stage 1/geometry cluster under `Poincare/Longrun/Geometry/`:

| File | Lines | sha256 |
| --- | --- | --- |
| `Poincare/Longrun/Geometry.lean` (umbrella) | 19 | `136065c47e12130a9368cee1bb2f21a43949df701410930c245d03eaecf344fa` |
| `Poincare/Longrun/Geometry/MetricData.lean` | 193 | `adb51294b15f16ff34e322f453f81eda3fdfdb5c1d810ef98ab18a5aa9dcd61c` |
| `Poincare/Longrun/Geometry/ConnectionAdapter.lean` | 348 | `db06e597d552b1cba852f5022e7a1e1a51d8e36e36487e14852261bf6f78aefd` |
| `Poincare/Longrun/Geometry/Contraction.lean` | 133 | `e1bdca9cf795f045e92b9e567d52cb30fd6b96c7942f8a3cb2389e9e2817b5d7` |
| `Poincare/Longrun/Geometry/LeviCivitaBlocked.lean` | 244 | `47f8a7f8598f10c6f2de41a24d2cd2457557e6d8b80f4529edbf3830391685fd` |
| `Audit/GeometryAudit.lean` (axiom audit driver) | 56 | `d1be6855570add633b87723e8b46472d8a79a7a2c20c0e17ff56d337ca21fa46` |

### 2.1 Metric/inner-product data structure with explicit finite-dimensional assumptions
(`MetricData.lean`)

- `MetricData V ι` — a real inner product as data: bilinear `form`, `symm`, `pos_def`,
  **plus** a chosen orthonormal `basis : Module.Basis ι ℝ V` with `[Fintype ι]`; the
  finite-dimensional hypothesis is explicit twice (`[FiniteDimensional ℝ V]` parameter and
  the basis field).
- Checked consequences: `form_self_nonneg`, `eq_zero_of_form_self_eq_zero`, `nondegenerate`,
  `finrank_eq_card` (`finrank ℝ V = Fintype.card ι`).
- `raiseIndex : (V →ₗ V →ₗ ℝ) →ₗ V →ₗ V` built from the orthonormal basis, with the
  checked adjoint property `form_raiseIndex : ⟨raiseIndex B X, Y⟩ = B Y X` and its symmetric
  form `form_raiseIndex_of_symm`.
- `toScalarContractionData : ScalarContractionData ℝ V` (Stage1 type, imported unmodified)
  and the contraction formula
  `scalarCurvature_eq_sum_basis : scalarCurvature K d = ∑ i, ricci K eᵢ eᵢ`.

### 2.2 Abstract connection/curvature adapter compatible with `Poincare.Stage1.CurvatureAlgebra`
(`ConnectionAdapter.lean`)

- `LieBracketData R V` — bilinear bracket with `skew` and `jacobi`; checked derived lemmas
  `jacobi_reverse`, `jacobi_corollary`, `bracket_bracket_comm`.
- `AbstractConnection R V` — `nabla : V →ₗ V →ₗ V`, an abstract `lie` bracket, and the
  torsion-free condition `nabla X Y - nabla Y X = [X,Y]`.
- `AbstractConnection.curvature : V →ₗ V →ₗ V →ₗ V`, the nested-linear-map curvature
  `R(X,Y)Z = ∇_X∇_Y Z - ∇_Y∇_X Z - ∇_{[X,Y]} Z`.
- `AbstractConnection.toCurvatureOperator : CurvatureOperator R V` — the adapter into the
  existing Stage1 interface. Its two obligations are **checked**:
  - `curvature_skew` — first-pair antisymmetry (from bracket skew);
  - `curvature_bianchi` — first Bianchi identity (from torsion-freeness + Jacobi, via the
    intermediate `curvature_cyclic_decomp`).
- Concrete instances: `AbstractConnection.zero` with `zero_toCurvatureOperator`, and over `ℝ`
  the nontrivial `meanConnection b` (`∇_X Y = ½[X,Y]`), with checked curvature
  `mean_curvature_apply : R(X,Y)Z = -¼[[X,Y],Z]`, contracted endomorphism
  `mean_endoRicci : endoRicci K X Y = -¼ (ad_Y ∘ ad_X)`, and the symmetric contraction
  `mean_ricci_comm : ricci K X Y = ricci K Y X` (uses `LinearMap.trace_comp_comm'`).

### 2.3 Checked contraction lemmas (`Contraction.lean`)

- `CurvatureOperator.endoRicci_add`, `endoRicci_smul`
- `CurvatureOperator.ricci_add : ricci (K + L) = ricci K + ricci L`
- `CurvatureOperator.ricci_smul : ricci (a • K) = a • ricci K`
- `CurvatureOperator.scalarCurvature_add`, `scalarCurvature_smul`
- `curvatureForm` — the metric-lowered (0,4) tensor `⟨R(X,Y)Z, W⟩`, with checked
  `curvatureForm_first_pair_skew` and `curvatureForm_first_bianchi`.

### 2.4 Explicit `BLOCKED` interfaces (`LeviCivitaBlocked.lean`)

- `IsTorsionFree`, `IsMetricCompatible`, `IsLeviCivita` (fixed-bracket formulation).
- **Proved (not blocked):** `leviCivita_nabla_unique` — abstract Koszul-style uniqueness:
  two connections torsion-free for the same bracket and metric-compatible for the same
  metric coincide.
- **Proved:** `meanConnection_isMetricCompatible_iff` — the mean connection is
  metric-compatible iff the bracket is metric-skew.
- **`BLOCKED` (explicit `Prop`, no proof):** `LeviCivitaExistenceStatement m b` — existence
  of a torsion-free, metric-compatible abstract connection. Documented as false without extra
  hypotheses (invariant metric). The checked equivalence
  `leviCivitaExistence_iff_nonempty : LeviCivitaExistenceStatement m b ↔ Nonempty (LeviCivitaData m b)`
  shows the `BLOCKED` interface is exactly the hypothesis form, with no smuggled proof.
- **`BLOCKED` (explicit `Prop`, no proof):** `CovariantDerivativeCurvatureStatement` — the
  missing manifold-level `CovariantDerivative.curvature` contract from the D1 card, stated
  over `Poincare.RiemannAdapter.PointwiseCurvature`.
- `LeviCivitaData` (hypothesis structure) and its `toCurvatureOperator`, feeding the Stage1
  adapter.

## 3. Worktree bootstrap (reproducible)

The assigned worktree was empty, so it was bootstrapped as an isolated Lake workspace that
reuses the already-built pinned mathlib without touching `poincare-lab/`:

```text
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D2_geometry_foundation
cp /data3/guoshaoyang/workdir/lean_poincare/poincare-lab/lakefile.toml .
cp /data3/guoshaoyang/workdir/lean_poincare/poincare-lab/lake-manifest.json .
cp /data3/guoshaoyang/workdir/lean_poincare/poincare-lab/lean-toolchain .
mkdir -p .lake
ln -s /data3/guoshaoyang/workdir/lean_poincare/poincare-lab/.lake/packages .lake/packages
mkdir -p Poincare
cp /data3/guoshaoyang/workdir/lean_poincare/poincare-lab/Poincare/Basic.lean Poincare/
mkdir -p Poincare/Stage1
cp /data3/guoshaoyang/workdir/lean_poincare/poincare-lab/Poincare/Stage1/CurvatureAlgebra.lean Poincare/Stage1/
cp /data3/guoshaoyang/workdir/lean_poincare/poincare-lab/Poincare/Stage1/RiemannAdapter.lean Poincare/Stage1/
```

## 4. Exact commands and exit codes

All commands run with:

```text
export PATH=/data3/guoshaoyang/workdir/lean_poincare/elan/bin:$PATH
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
```

### 4.1 Bootstrap build of the consumed Stage1 dependency

```text
lake build Poincare.Stage1.CurvatureAlgebra
exit code: 0

lake build Poincare.Stage1.RiemannAdapter
exit code: 0
```

### 4.2 Clean rebuild of the authored cluster from source

The `.lake/build/lib/lean/Poincare/Longrun` tree was deleted first, so this is a from-source
build:

```text
rm -rf .lake/build/lib/lean/Poincare/Longrun
lake build Poincare.Longrun.Geometry
exit code: 0
# ✔ [3217/3221] Built Poincare.Longrun.Geometry.MetricData (3.4s)
# ✔ [3218/3221] Built Poincare.Longrun.Geometry.ConnectionAdapter (4.4s)
# ✔ [3219/3221] Built Poincare.Longrun.Geometry.Contraction (2.1s)
# ✔ [3220/3221] Built Poincare.Longrun.Geometry.LeviCivitaBlocked (2.7s)
# ✔ [3221/3221] Built Poincare.Longrun.Geometry (1.8s)
# Build completed successfully (3221 jobs).
```

Full-library build:

```text
lake build Poincare
exit code: 0
# Build completed successfully (3223 jobs).
```

### 4.3 `lake env lean` on every authored file

```text
lake env lean Poincare/Longrun/Geometry/MetricData.lean
exit code: 0        # zero output (no errors, no warnings)

lake env lean Poincare/Longrun/Geometry/ConnectionAdapter.lean
exit code: 0        # zero output

lake env lean Poincare/Longrun/Geometry/Contraction.lean
exit code: 0        # zero output

lake env lean Poincare/Longrun/Geometry/LeviCivitaBlocked.lean
exit code: 0        # zero output

lake env lean Poincare/Longrun/Geometry.lean
exit code: 0        # zero output

lake env lean Audit/GeometryAudit.lean
exit code: 0        # 39 #print axioms lines; captured in Audit/GeometryAudit.out
```

Per-file compiler output was captured verbatim in `Audit/logs/*.log` (all empty).

### 4.4 `#print axioms`

```text
lake env lean Audit/GeometryAudit.lean > Audit/GeometryAudit.out 2>&1
exit code: 0
grep -c "sorryAx" Audit/GeometryAudit.out   →  0
```

39 principal declarations were audited. Exactly two axiom sets occur:

```text
[propext, Classical.choice, Quot.sound]
[propext, Quot.sound]
```

Representative output:

```text
'Poincare.Longrun.Geometry.MetricData.scalarCurvature_eq_sum_basis' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Geometry.AbstractConnection.curvature_skew' depends on axioms: [propext, Quot.sound]
'Poincare.Longrun.Geometry.AbstractConnection.curvature_bianchi' depends on axioms: [propext, Quot.sound]
'Poincare.Longrun.Geometry.AbstractConnection.toCurvatureOperator' depends on axioms: [propext, Quot.sound]
'Poincare.Longrun.Geometry.mean_ricci_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CurvatureAlgebra.CurvatureOperator.ricci_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Geometry.curvatureForm_first_bianchi' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Geometry.leviCivita_nabla_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Geometry.LeviCivitaExistenceStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Geometry.CovariantDerivativeCurvatureStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` and no project axiom appear. The full 39-line output is in
`Audit/GeometryAudit.out`.

## 5. Hygiene checks

```text
# actual declarations only (comments excluded by the ^[[:space:]]* anchor)
grep -nE "^[[:space:]]*(sorry|axiom|unsafe|native_decide|proof_wanted)\b" <authored files>
→ no matches

# Stage1 integrity vs shared originals
sha256sum Poincare/Stage1/CurvatureAlgebra.lean  == shared original   → IDENTICAL
sha256sum Poincare/Stage1/RiemannAdapter.lean    == shared original   → IDENTICAL
```

The authored files contain no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted`. The only textual occurrences are in the honesty docstrings that state the
absence of those constructs.

## 6. Mathematical statement and assumptions (summary)

- All objects are abstract `ℝ`-modules; the metric is an explicit symmetric positive-definite
  bilinear form with a chosen finite orthonormal basis.
- The adapter proves that an abstract torsion-free connection with a skew bracket satisfying
  Jacobi produces a Stage1 `CurvatureOperator`, i.e. `R(X,Y)Z = -R(Y,X)Z` and the first
  Bianchi identity. The classical first Bianchi identity is derived purely algebraically from
  torsion-freeness and Jacobi; no metric compatibility is needed for it.
- Contractions: `ricci` and `scalarCurvature` are additive and scalar-linear; the
  metric-induced scalar curvature is the basis sum `∑ i, ricci K eᵢ eᵢ`; the metric-lowered
  (0,4) tensor inherits first-pair antisymmetry and the first Bianchi identity.
- For the mean connection `½[X,Y]`, the curvature is `-¼[[X,Y],Z]` and the Ricci contraction
  is symmetric (the trace of `ad_Y ∘ ad_X` is cyclically invariant).
- Abstract Levi-Civita uniqueness is proved; existence is explicitly `BLOCKED`.

## 7. Blockers and suggested follow-ups

| Blocker | Evidence | Suggested follow-up |
| --- | --- | --- |
| Abstract Levi-Civita **existence** is not a theorem in this algebraic setting (needs metric invariance) | `LeviCivitaExistenceStatement` is an unproved `Prop`; `meanConnection_isMetricCompatible_iff` shows the extra invariant-metric condition | keep as hypothesis (`LeviCivitaData`); instantiate for a bi-invariant metric in a later task |
| No `CovariantDerivative.curvature` in mathlib | D1 card `#check_failure RiemannCurvatureTensor`; `CovariantDerivativeCurvatureStatement` is an unproved `Prop` | track upstream; fill via `RiemannAdapter.RiemannianCurvatureData.ofCurvature` when available |
| No Ricci/scalar curvature in mathlib | D1 card `#check_failure RicciTensor` | D3-kappa-ledger consumes the abstract contractions |
| Levi-Civita connection smoothness unproved upstream | D1 card; not used here | track upstream |
| No geodesics/exponential map/parallel transport in mathlib | D1 card | new subtask if the evolution cluster needs them |

No mathematical blocking condition prevented this task from completing: every authored file
compiles with exit code 0, the cluster builds from a clean `.lake/build` state, and the
missing Levi-Civita existence/curvature theorems are explicit, documented `BLOCKED`
interfaces rather than fabricated proofs. The only unresolved delivery issue is the sandbox
denial of the shared `longrun/results/` path (see the delivery note at the top).

## 8. Files changed (all under the worktree; no shared source modified)

Authored:

- `Poincare/Longrun/Geometry.lean`
- `Poincare/Longrun/Geometry/MetricData.lean`
- `Poincare/Longrun/Geometry/ConnectionAdapter.lean`
- `Poincare/Longrun/Geometry/Contraction.lean`
- `Poincare/Longrun/Geometry/LeviCivitaBlocked.lean`
- `Audit/GeometryAudit.lean`, `Audit/GeometryAudit.out`, `Audit/logs/*.log`

Bootstrap (copied/symlinked, byte-identical or read-only):

- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`
- `.lake/packages` → shared prebuilt mathlib packages
- `Poincare/Basic.lean`, `Poincare/Stage1/CurvatureAlgebra.lean`,
  `Poincare/Stage1/RiemannAdapter.lean`

Mirrored result card (intended shared destination, write denied):

- `longrun/results/D2-geometry-foundation.md`
- `longrun/results/D2-geometry-foundation.json`
