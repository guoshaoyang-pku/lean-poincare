# D9-tensor-algebra-manifolds — result card

- **Task id:** `D9-tensor-algebra-manifolds`
- **Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-tensor-algebra-manifolds`
- **Generated:** `2026-09-10T01:16:23.188703+00:00`; compile-gate repair (harness attempt 1) `2026-09-10T01:57:17+00:00`
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` — `Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release)`
- **Mathlib pin:** `7974e751bece493b6ff508039423ca9fa2452fa8` (D6 weekly release scaffold, unchanged)
- **Verdict:** **TASK_DONE — tensor-bundle interface + state-only Props + kernel-checked fibre model; no proof holes, no postulated constants; compile gate repaired and re-verified (68/68 files exit 0)**

> Honest scope: this task delivers a *standalone, reusable* tensor-algebra layer for the
> release's manifold interface. `TensorBundleData` is an abstract interface (its operations and
> laws are fields, hence obligations on a caller's instance). The three headline laws required by
> the task are **kernel-checked** at the fibre level in a finite-dimensional real inner product
> space (`Toy.lean`). Nothing here claims a manifold-level tensor library, and no
> `TensorBundleData` instance is constructed.

## 1. Authored files (added only under `release/Poincare/D9/TensorAlgebra/`)

| file | lines | `lake env lean` exit | seconds | sha256[:16] |
|---|---|---|---|---|
| Poincare/D9/TensorAlgebra/Interface.lean | 213 | 0 | 3.19 | fd1e8fd6ac136f7f |
| Poincare/D9/TensorAlgebra/Props.lean | 151 | 0 | 2.81 | bd646313f4ac526a |
| Poincare/D9/TensorAlgebra/Toy.lean | 175 | 0 | 2.91 | acae4b1690b3e021 |
| Poincare/D9/TensorAlgebra/AxiomAudit.lean | 53 | 0 | 2.35 | 2a75ff0fa6eb7e06 |

Every file compiles with `cd release && lake env lean <file>` (all exits `0`); the whole package
also builds with `lake build` (exit `0`, 8950 jobs).

## 2. Tensor-bundle interface — `Interface.lean`

`Poincare.D9.TensorAlgebra.TensorBundleData I M` is defined over the release's manifold layer
(`Poincare.Stage1.RiemannAdapter`: `ChartedSpace`, `IsManifold`, `TangentSpace`,
`RiemannianBundle`). Convention: bidegree `(r, s)` = `r` contravariant (upper) and `s` covariant
(lower) indices; the pointwise fibre model is

```lean
TensorFiber I M r s x = MultilinearMap ℝ (fun _ : Fin r => (TangentSpace I x →L[ℝ] ℝ))
                                        ((Fin s → TangentSpace I x) →ₗ[ℝ] ℝ)
```

**Operation fields:** `TensorField`, `eval`, `tensorProduct`, `contract`, `metricTrace`, `flat`, `sharp`, `metric`, `one`, `dualPairing`, `dim`, `Smooth`, `pullback`.

**Law fields (22, all `Prop`-valued, none proved here and none postulated):**
`tensorProduct_add_left`, `tensorProduct_add_right`, `tensorProduct_smul_left`, `tensorProduct_smul_right`, `contract_add`, `contract_smul`, `metricTrace_add`, `metricTrace_smul`, `flat_add`, `flat_smul`, `sharp_add`, `sharp_smul`, `dualPairing_add_left`, `dualPairing_add_right`, `dualPairing_smul_left`, `dualPairing_smul_right`, `flat_sharp`, `sharp_flat`, `contract_tensorProduct`, `metricTrace_metric`, `pullback_id`, `pullback_comp`.

The headline laws among them are `flat_sharp` / `sharp_flat` (the musical isomorphisms are
inverse to each other), `contract_tensorProduct` (`contract (α ⊗ ♯β) = dualPairing α β`) and
`metricTrace_metric` (`metricTrace metric = dim • one`, i.e. `tr_g g = n`).

## 3. State-only Props — `Props.lean`

Every declaration is a `def ... : Prop` (or a `structure` whose laws are `Prop`-valued):
the statements are elaborated and kernel-checked, while their proofs remain obligations of the
interface. No proof body is attempted in this file.

| declaration | status |
|---|---|
| `contract_smooth` | state-only `Prop` |
| `metricTrace_smooth` | state-only `Prop` |
| `flat_smooth` | state-only `Prop` |
| `sharp_smooth` | state-only `Prop` |
| `tensorProduct_smooth` | state-only `Prop` |
| `metric_smooth` | state-only `Prop` |
| `pullback_smooth` | state-only `Prop` |
| `contract_pullback_comm` | state-only `Prop` |
| `IsMetricPreserving` | state-only `Prop` |
| `metricTrace_pullback_comm` | state-only `Prop` |
| `flat_pullback_comm` | state-only `Prop` |
| `sharp_pullback_comm` | state-only `Prop` |
| `trace_divergence_identity` | state-only `Prop` |
| `TraceDivergenceInterface` (structure) | state-only interface |

Coverage of the three required items:

1. **Smoothness of contractions of smooth tensor fields** — `contract_smooth`,
   `metricTrace_smooth`, `flat_smooth`, `sharp_smooth`, `tensorProduct_smooth`,
   `metric_smooth`, `pullback_smooth`.
2. **Commutation of contraction with pullback by local diffeomorphisms** —
   `contract_pullback_comm : ∀ φ, IsLocalDiffeomorph I I ∞ φ →
   contract (φ*T) = φ*(contract T)`. The metric-dependent operations carry the honest extra
   hypothesis `IsMetricPreserving D φ` (`φ* g = g`): `metricTrace_pullback_comm`,
   `flat_pullback_comm`, `sharp_pullback_comm`.
3. **Trace–divergence identity interface** — the structure `TraceDivergenceInterface D` bundles
   `div`, its linearity laws `div_add` / `div_smul`, and
   `trace_divergence : div (tr_g T) = tr_g (div T)` for `(1,2)`-tensors; the standalone
   `trace_divergence_identity` extracts the identity as a `Prop`.

## 4. Kernel-checked toy theorems — `Toy.lean`

Setting: `V` a finite-dimensional real inner product space
(`[NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]`). `♭` is `innerSL ℝ`,
`♯` is its Fréchet–Riesz inverse (`InnerProductSpace.toDual`), `metric` is `⟪·,·⟫`, and
contraction of a `(1,1)`-tensor is mathlib's `LinearMap.trace`.

| required law | Lean declaration | statement |
|---|---|---|
| `tr_g g = n` (orthonormal frame) | `metricTrace_metric_eq_finrank` | `∑ i, metric (b i) (b i) = finrank ℝ V` |
| `tr_g g = n` (mixed form) | `trace_sharp_comp_flat` | `LinearMap.trace ℝ V (♯ ∘ ♭) = finrank ℝ V` |
| `tr_g g = n` (`♯♯g` against `g`) | `metricTrace_inverseMetric_eq_finrank` | `∑ i, inverseMetric (♭ (b i)) (♭ (b i)) = finrank ℝ V` |
| musical isomorphisms inverse | `sharp_flat`, `flat_sharp` | `♯ (♭ v) = v`, `♭ (♯ φ) = φ` |
| `tr (α ⊗ β) = ⟨α, β⟩` | `contract_tensorProduct` | `LinearMap.trace ℝ V (α ⊗ ♯β) = dualPairing α β` |
| `tr (α ⊗ β) = ⟨α, β⟩` (Riesz form) | `contract_tensorProduct_eq_inner` | `= ⟪♯α, ♯β⟫` |

All proofs are complete terms; no proof holes.

## 5. Kernel / axiom evidence

- `#print axioms` audit file: `Poincare/D9/TensorAlgebra/AxiomAudit.lean`; `lake env lean` exit `0`.
- Declarations audited: **31**.
- Axiom cones observed: **propext, Classical.choice, Quot.sound — 31 declarations**.
- Non-standard cones: **none**.
- Forbidden dependencies: `sorryAx` 0, project axioms 0, `unsafe` 0, `native_decide` 0,
  `proof_wanted` 0.

Forbidden-token scan (raw text of each authored file):

| file | sorry | admit | unsafe | native_decide | proof_wanted | `#print axioms` cmds | `axiom` tokens (total) | `axiom` declarations |
|---|---|---|---|---|---|---|---|---|
| Poincare/D9/TensorAlgebra/Interface.lean | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Poincare/D9/TensorAlgebra/Props.lean | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Poincare/D9/TensorAlgebra/Toy.lean | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Poincare/D9/TensorAlgebra/AxiomAudit.lean | 0 | 0 | 0 | 0 | 0 | 31 | 32 | 0 |

The only occurrences of the token `axiom` in the authored sources are the
31 `#print axioms` audit commands required by the task, one prose mention of that
command in the `AxiomAudit.lean` docstring, and the module name `AxiomAudit` itself. There is
**no `axiom` declaration**. The first `#print axioms` output lines are:

```text
'Poincare.D9.TensorAlgebra.TensorBundleData' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D9.TensorAlgebra.contract_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D9.TensorAlgebra.metricTrace_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D9.TensorAlgebra.flat_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D9.TensorAlgebra.sharp_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D9.TensorAlgebra.tensorProduct_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 6. Honest boundaries

- TensorBundleData is an abstract interface: every operation and every law is a field, hence an obligation on a caller's instance; no manifold-level instance is constructed here.
- The toy model is fibre-level (one finite-dimensional inner product space); it checks the three headline laws but does not instantiate TensorBundleData and does not construct tensor fields on a manifold.
- Props.lean is state-only: the smoothness, pullback-commutation and trace-divergence statements are kernel-checked Props whose proofs remain obligations.
- Contraction is stated to commute with pullback along local diffeomorphisms; metric-dependent operations (metricTrace, flat, sharp) are stated under the additional metric-preservation hypothesis IsMetricPreserving.
- The interface's pullback is an abstract field along self-maps; `pullback_smooth` concerns that abstract operation and is an obligation, not a construction.

## 7. Reproduction

```bash
export ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-tensor-algebra-manifolds/release
lake build Poincare.D9.TensorAlgebra.AxiomAudit      # builds Interface, Props, Toy, AxiomAudit
lake env lean Poincare/D9/TensorAlgebra/Interface.lean
lake env lean Poincare/D9/TensorAlgebra/Props.lean
lake env lean Poincare/D9/TensorAlgebra/Toy.lean
lake env lean Poincare/D9/TensorAlgebra/AxiomAudit.lean   # prints the axiom cones
```

This is the *release-package* reproduction. The harness compile gate instead runs
`lake env lean <abs file>` with `cwd` = *worktree root* for every `.lean` file in the
worktree; that path is exercised by the root-level shim and by

```bash
cd /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-tensor-algebra-manifolds
python3 logs/gate_repair_replay.py      # exact copy of dispatch_loop.py::compile_gate
```

## 8. Compile-gate repair (harness attempt 1)

**What the harness reported.** `longrun/bin/dispatch_loop.py::compile_gate` walks the whole
worktree for `.lean` files and runs `lake env lean <abs file>` with `cwd` = *worktree root*
for each of them. The dispatcher deletes `state/D9-tensor-algebra-manifolds/gate.json`
immediately after queuing the repair (`dispatch_loop.py` lines 150–152), so the prompt's
`gate.json` was not readable. `longrun/logs/dispatch.log` records the failure and this
repair's launch:

```text
2026-09-10T09:46:09+0800 REPAIR D9-tensor-algebra-manifolds attempt 1 queued
2026-09-10T09:50:41+0800 LAUNCH D9-tensor-algebra-manifolds (REPAIR_D9-tensor-algebra-manifolds.md)
```

**Diagnosis (reproduced exactly).** Two environment defects, neither a Lean error:

1. The worktree root is not a Lake package (the package is `release/`). With `cwd` = root,
   elan finds no `lean-toolchain` in the root or its ancestors and has no default toolchain
   configured, so every invocation failed before elaborating anything:
   `error: no default toolchain configured`, exit 1 — for all 68 `.lean` files.
2. Even with the toolchain resolvable, the compiled artifacts of the four authored D9 modules
   were absent from `release/.lake/build/lib/lean/Poincare/D9/TensorAlgebra/`. The gate visits
   files alphabetically and `lake env lean <file>` elaborates a file without emitting its
   olean, so `Props.lean` / `AxiomAudit.lean` failed with
   `object file '…/Interface.olean' of module Poincare.D9.TensorAlgebra.Interface does not exist`.

Both were reproduced locally with `logs/gate_repair_replay.py`, a line-for-line copy of the
gate algorithm (same `os.walk` pruning of `.lake`/`.git`/`.dshpkg`, same `cwd` = worktree
root, same `ELAN_HOME`/`PATH`, same 1800 s per-file timeout).

**Repair (no authored math changed).** No `.lean` file was edited — all four authored files
are byte-identical to §1 (sha256 below). Only worktree-root scaffolding was added, mirroring
the repair already accepted for sibling worktrees, plus a rebuild of the release artifacts:

| path | kind | purpose |
|---|---|---|
| `lean-toolchain` | copy of `release/lean-toolchain` | elan resolves `leanprover/lean4:v4.34.0-rc2` from the worktree root |
| `lake-manifest.json` | copy of `release/lake-manifest.json` | pins mathlib rev `7974e751…` |
| `lakefile.toml` | 418-byte shim package `D9WorktreeRoot` | root Lake package requiring mathlib, with a `Poincare` library |
| `.lake -> release/.lake` | relative symlink | exposes the release build artifacts/packages from the root |
| `Poincare -> release/Poincare` | relative symlink | matches the shim's `Poincare` library globs |

```bash
cd release && lake build Poincare      # exit 0, 8932 jobs
# regenerates release/.lake/build/lib/lean/Poincare/D9/TensorAlgebra/
#   {Interface,Props,Toy,AxiomAudit}.{olean,ilean,trace}
```

**Re-verification.**

| check | command | result | evidence |
|---|---|---|---|
| harness-gate replay | exact `compile_gate` over the worktree (68 `.lean` files) | **68/68 exit 0** (255.8 s) | `logs/gate_repair_replay.py`, `logs/gate_repair_replay.json`, `logs/gate_repair_replay.out` |
| per-file checks | `cd release && lake env lean Poincare/D9/TensorAlgebra/<f>.lean` | Interface 0 (2.83 s), Props 0 (3.54 s), Toy 0 (2.64 s), AxiomAudit 0 (2.87 s) | `logs/gate_repair_perfile.txt`, `logs/gate_repair_perfile_*.log` |
| axiom audit | `lake env lean Poincare/D9/TensorAlgebra/AxiomAudit.lean` | 31 declarations, all cones `{propext, Classical.choice, Quot.sound}`, 0 non-standard | `logs/gate_repair_perfile_AxiomAudit.log` |
| forbidden scan | raw text of the 4 authored files | `sorry` 0, `admit` 0, `unsafe` 0, `native_decide` 0, `proof_wanted` 0, `axiom` declarations 0 | §5 table |

Re-verified sha256 of the authored files (unchanged from §1):

```text
fd1e8fd6ac136f7f9c31dab9d18ffc0800dbdb9726e89cee41f2bfa14e824057  Interface.lean
bd646313f4ac526a42d1e836dffed52052d83e791f377d391f9638cc4c6282f3  Props.lean
acae4b1690b3e02161ec25a328143417d08c08e36b1cfdf02950140d86c73457  Toy.lean
2a75ff0fa6eb7e064fa09fbb56b2f2dd3258343d311c496bf4c22da9b912bcd5  AxiomAudit.lean
```

TASK_DONE — card: longrun/results/D9-tensor-algebra-manifolds.md
