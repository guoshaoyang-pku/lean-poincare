# D9-tensor-algebra-manifolds — result card

- **Task id:** `D9-tensor-algebra-manifolds`
- **Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-tensor-algebra-manifolds`
- **Generated:** `2026-09-10T01:49:52+00:00` (repair pass 1; original card `2026-09-10T01:16:23+00:00`)
- **Re-verified:** `2026-09-10T01:58:23+00:00` by the attempt-2 repair session (independent full-tree gate replica, 68/68 green — see §0.1)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` — `Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release)`
- **Mathlib pin:** `7974e751bece493b6ff508039423ca9fa2452fa8` (D6 weekly release scaffold, unchanged)
- **Verdict:** **TASK_DONE — tensor-bundle interface + state-only Props + kernel-checked fibre model; no proof holes, no postulated constants; full compile gate (68/68 files) green**

> Honest scope: this task delivers a *standalone, reusable* tensor-algebra layer for the
> release's manifold interface. `TensorBundleData` is an abstract interface (its operations and
> laws are fields, hence obligations on a caller's instance). The three headline laws required by
> the task are **kernel-checked** at the fibre level in a finite-dimensional real inner product
> space (`Toy.lean`). Nothing here claims a manifold-level tensor library, and no
> `TensorBundleData` instance is constructed.

## 0. Repair pass 1 — compile-gate failure and fix

**Root cause (diagnosed, reproduced).** The longrun compile gate (`dispatch360.py: compile_gate`)
invokes, for every `.lean` file in the worktree,

```text
subprocess.run(["lake", "env", "lean", <abs file>], cwd = <worktree root>, env = ENV)
```

i.e. **from the worktree root**, not from `release/`. At gate time the worktree root contained no
`lean-toolchain` / Lake workspace (the release package and its prebuilt `.lake` live in
`release/`). Running the gate command from the root therefore failed for *every* file with

```text
error: no default toolchain configured. run `elan default stable` to install & configure the latest Lean 4 stable release.
```

exit code `1`, which is exactly the observed "compile gate failed (attempt 1)".
`gate.json` itself is deleted by the dispatcher right after the repair prompt is written, so the
failure was reproduced directly from the gate implementation instead of read from that file.

**Fix (infrastructure only; no mathematical content touched).** A worktree-root Lake workspace
mirroring the release package was added, so the gate's `lake env lean` resolves the pinned
toolchain, the pinned mathlib and the prebuilt oleans:

| root file | role | sha256[:16] |
|---|---|---|
| `lean-toolchain` | pins `leanprover/lean4:v4.34.0-rc2` (identical to `release/lean-toolchain`) | 8190e75a20174106 |
| `lake-manifest.json` | pins mathlib `7974e751…` (identical to `release/lake-manifest.json`) | cbc45ee0bd591606 |
| `lakefile.toml` | root workspace wrapper: package `PoincareWorktree`, lib `Poincare` with `srcDir = "release"`, `globs = ["Poincare.+"]`, `require mathlib` | 2a3d6f3b8d0f4102 |
| `.lake → release/.lake` | symlink putting every prebuilt release/mathlib olean on `LEAN_PATH` (no rebuild, no copy) | — |

**Verification.** The dispatcher's gate was replicated exactly (same walk, same exclusion of
`.lake`/`.git`/`.dshpkg`, same `cwd` = worktree root, same `ELAN_HOME`/`PATH`): **68/68 `.lean`
files exit `0`**, 0 failures, 279.6 s total wall time
(`logs/gate_sim.json`, `logs/gate_sim.stdout`, per-file stderr in `logs/gate_sim/`).
The four authored sources are byte-identical to the original card (same sha256, see §1); the
mathematics of §§2–6 is unchanged.

### 0.1 Independent re-verification (attempt-2 repair session)

A second repair session (dispatcher attempt 2, launched while the attempt-1 worker loop was still
alive) re-diagnosed the failure independently and re-ran the gate end-to-end once the root
workspace above was in place. **Neither repair session modified any source file.**

* **Second, independent full-tree gate replica** (same walk and exclusions, `cwd` = worktree root,
  same `ELAN_HOME`/`PATH`): **68/68 `.lean` files exit `0`**, 0 failures, 278.3 s; raw per-file
  results in `longrun/logs/gate_replica.json`, driver `longrun/logs/gate_replica.py`. This agrees
  with the attempt-1 replica of §0 (`logs/gate_sim.json`, 68/68, `GATE_OK`).
* **Fresh axiom audit** via the gate command (`lake env lean
  release/Poincare/D9/TensorAlgebra/AxiomAudit.lean`, exit `0`): 31 declarations, all 31 cones
  exactly `[propext, Classical.choice, Quot.sound]`, and 0 occurrences of
  `sorryAx`/`unsafe`/`native_decide`/`proof_wanted`; archived at
  `longrun/logs/d9_axiomaudit.txt`.
* **Unaffected mathematics**: the four authored sources still hash to the values in §1
  (`fd1e8fd6…`, `bd646313…`, `acae4b16…`, `2a75ff0f…`), i.e. byte-identical to the original card.
* **Reproduction of the pre-fix failure** (attempt-2 session): in a working directory with no Lake
  workspace, `lake env lean` on `Props.lean` exits `1` with
  `error: unknown module prefix 'Poincare'` and an empty search path — the same class of
  environment failure as §0, removed by the root workspace.

## 1. Authored files (added only under `release/Poincare/D9/TensorAlgebra/`)

| file | lines | gate `lake env lean` exit | seconds | sha256[:16] |
|---|---|---|---|---|
| Poincare/D9/TensorAlgebra/Interface.lean | 213 | 0 | 3.2 | fd1e8fd6ac136f7f |
| Poincare/D9/TensorAlgebra/Props.lean | 151 | 0 | 2.9 | bd646313f4ac526a |
| Poincare/D9/TensorAlgebra/Toy.lean | 175 | 0 | 3.1 | acae4b1690b3e021 |
| Poincare/D9/TensorAlgebra/AxiomAudit.lean | 53 | 0 | 2.6 | 2a75ff0fa6eb7e06 |

Every file compiles with the gate command `cd <worktree root> && lake env lean <file>` (all exits
`0`); the whole tree also passes the gate replica (68/68, see §0).

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

- `#print axioms` audit file: `Poincare/D9/TensorAlgebra/AxiomAudit.lean`; gate exit `0`.
- Declarations audited: **31**.
- Axiom cones observed: **propext, Classical.choice, Quot.sound — 31 declarations**.
- Non-standard cones: **none**. (`grep` for `sorryAx` / `native_decide` / `proof_wanted` in the
  audit output: 0 matches.)
- Forbidden dependencies: `sorryAx` 0, project axioms 0, `unsafe` 0, `native_decide` 0,
  `proof_wanted` 0.
- Fresh audit run during the repair pass: exit `0`, 2.5 s, output archived at
  `logs/axiom_audit_rerepair.txt` (35 lines, 31 `depends on axioms` lines).

Forbidden-token scan (comment/string-aware `input/d5-tools/scan_forbidden.py`, re-run during the
repair pass on the four authored files; raw result in `logs/forbidden_d9.json`):

| file | sorry | admit | unsafe | native_decide | proof_wanted | `#print axioms` cmds | `axiom` tokens (total) | `axiom` declarations |
|---|---|---|---|---|---|---|---|---|
| Poincare/D9/TensorAlgebra/Interface.lean | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Poincare/D9/TensorAlgebra/Props.lean | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Poincare/D9/TensorAlgebra/Toy.lean | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Poincare/D9/TensorAlgebra/AxiomAudit.lean | 0 | 0 | 0 | 0 | 0 | 31 | 32 | 0 |

Scanner verdict for the authored sources: `hard_match_count = 0`, `soft_match_count = 0`
(the keyword-aware scan strips comments/strings, so `#print axioms` is not an `axiom`
declaration and `AxiomAudit` is only a module name). The first `#print axioms` output lines are:

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
- The repair pass added only the worktree-root Lake workspace files needed by the compile gate (`lean-toolchain`, `lake-manifest.json`, `lakefile.toml`, `.lake → release/.lake`); no `release/` source and no mathematical statement was changed.

## 7. Reproduction

```bash
export ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-tensor-algebra-manifolds

# gate-identical per-file compile (cwd = worktree root):
lake env lean release/Poincare/D9/TensorAlgebra/Interface.lean
lake env lean release/Poincare/D9/TensorAlgebra/Props.lean
lake env lean release/Poincare/D9/TensorAlgebra/Toy.lean
lake env lean release/Poincare/D9/TensorAlgebra/AxiomAudit.lean   # prints the axiom cones

# optional: the canonical release build from the release package itself
cd release && lake build Poincare.D9.TensorAlgebra.AxiomAudit
```

TASK_DONE — card: longrun/results/D9-tensor-algebra-manifolds.md
