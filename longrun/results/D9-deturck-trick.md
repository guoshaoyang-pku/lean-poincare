# D9-deturck-trick — result card

- **Task id:** `D9-deturck-trick`
- **Stage / lane:** D9 / Ricci-flow geometry–analysis interface
- **Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-deturck-trick`
- **Generated:** `2026-09-09T15:40:41Z`
- **Repair attempt 1:** `2026-09-09T16:01:44Z` — compile-gate environment fixed at the worktree root (see §6.1). The four authored modules were unchanged at that point (sha256 unchanged; §1).
- **Repair attempt 2:** `2026-09-09T17:27:00Z` — the gate environment had **no** `Poincare/D9/DeTurck/*.olean` (the `release/.lake` tree had been restored to the pre-task D6 base), and the gate command does not build imports, so the two import-dependent files failed to elaborate. The authored import graph was made artifact-independent: the unused `ConnectionLayer` import was removed from `SymbolModel.lean`, and the import-only aggregate driver `All.lean` was deleted. The gate now exits 0 for **all 67** `.lean` files **with `release/.lake/build/lib/lean/Poincare/D9` removed** (see §6.2). Mathematical content is unchanged: 60 kernel-checked declarations, same axiom cones.
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2`; mathlib `7974e751bece493b6ff508039423ca9fa2452fa8` (git head, clean)
- **Verdict:** **DETURCK INTERFACE LAYER DELIVERED — PRINCIPAL-SYMBOL IDENTITY KERNEL-CHECKED; SHORT-TIME EXISTENCE / EQUIVALENCE / UNIQUENESS STATEMENT-ONLY**

> This card does **not** claim existence or uniqueness of Ricci flow, nor the existence of the
> harmonic-map heat flow. Those analytic theorems are recorded as statement-only Props over an
> explicit interface (`FlowInterface`). The kernel-checked content is (i) the finite-dimensional
> principal-symbol cancellation of the linearized Ricci–DeTurck operator — the ellipticity
> computation of DeTurck's trick — and (ii) the component algebra of the DeTurck field and the
> Ricci–DeTurck operator interface. No `sorry`, `axiom`, `unsafe`, `native_decide` or
> `proof_wanted` occurs anywhere in the authored files.

## 1. Deliverables

All authored files live under `release/Poincare/D9/DeTurck/`. Each of the three modules is
self-contained (see §6.2): none imports another authored module.

| file | lines | sha256 (first 16) | contents |
|---|---|---|---|
| `ConnectionLayer.lean` | 266 | `fb0eac8c5f2e49fe` | `ConnectionLayer` (metric `g`, background `g̃`, inverses, Christoffel symbols `Γ`, `Γ̃`), `deTurckField W^k = g^{ij}(Γ^k_{ij} - Γ̃^k_{ij})`, `tensionField τ = -W`, `RicciDeTurckComponents` with `operator = Ric - (1/2)L_W g` and `flowRHS = -2(Ric - (1/2)L_W g)`, non-vacuity layers |
| `SymbolModel.lean` | 307 | `88934b5eac2f3bda` | finite-dimensional symbol model on `MetricData`: `metricSharp`, `covectorNormSq`, `bilinTrace`, `ricciSymbol`, `deTurckFieldSymbol`, `lieSymbol`, `laplacianSymbol`; the principal-symbol identity and its flow form; symmetry preservation; ellipticity |
| `StatementOnly.lean` | 229 | `37ee2e5d8d5fe184` | `FlowInterface`; statement-only `ShortTimeExistence`, `Uniqueness`, `PullbackEquivalenceForward`, `PullbackEquivalenceBackward`, `PullbackEquivalence`, `RicciFlowUniqueness`; kernel-checked conditional corollary `ricciFlowUniqueness_of_deturck`; degenerate toy non-vacuity checks |

## 2. Item 1 — the DeTurck vector field and the Ricci–DeTurck operator interface

`ConnectionLayer ι` is a finite index layer carrying the components of a metric `g`, a
background metric `g̃` (both with inverses and the inverse-metric laws), and the Christoffel
symbols `Γ`, `Γ̃` of the two metrics, with symmetry fields for every family. The defining
equations of the Christoffel symbols in terms of derivatives of the metrics are deliberately
**not** fields: they need the smooth-manifold layer and belong to the statement-only part.

- `ConnectionLayer.deTurckField C k = ∑ i, ∑ j, C.ginv i j * (C.Gamma k i j - C.GammaBar k i j)`
  — the exact formula `W^k = g^{ij}(Γ^k_{ij} - Γ̃^k_{ij})`.
- `ConnectionLayer.connectionDiff` — the connection-difference tensor `A^k_{ij} = Γ^k_{ij} - Γ̃^k_{ij}`,
  with `connectionDiff_symm` (torsion-free index symmetry).
- `ConnectionLayer.tensionField` — the tension field `τ^k = g^{ij}(Γ̃^k_{ij} - Γ^k_{ij})` of the
  identity map `(M,g) → (M,g̃)`, with the kernel-checked sign relation
  `tensionField_eq_neg_deTurckField : τ = -W`.
- `ConnectionLayer.deTurckField_eq_zero_of_Gamma_eq` — `W = 0` when the two connections agree.
- `RicciDeTurckComponents` — the operator interface: Ricci components `ric` and Lie-derivative
  components `lieW` (both interface fields; no curvature or Lie-derivative construction).
- `RicciDeTurckComponents.operator D i j = D.ric i j - (1/2) * D.lieW i j`
  — the Ricci–DeTurck operator `Ric - (1/2) L_W g`.
- `RicciDeTurckComponents.flowRHS_eq` — the kernel-checked flow identity
  `-2 (Ric - (1/2)L_W g) = -2 Ric + L_W g`, i.e. the standard form `∂_t g = -2Ric + L_W g`.
- Non-vacuity: `trivialLayer` has `W = 0`; `exampleLayer` has `W^0 = -2` and `τ^0 = 2`,
  proving the interface computes a nonzero field and is not vacuous.

## 3. Item 2 — the kernel-checked principal-symbol identity (the DeTurck cancellation)

The symbol model is built on the accepted `Poincare.Longrun.Geometry.MetricData` interface
(finite-dimensional real inner-product datum with an orthonormal basis), so `|ξ|²`, `ξ♯` and
`tr h` are computed with the metric `g`. With the sign convention that the symbol of the rough
Laplacian `Δ_g = g^{ij}∇_i∇_j` is `-|ξ|²`:

- `ricciSymbol m ξ h` — the classical symbol of the linearized Ricci tensor,
  `(1/2)(|ξ|² h_{ij} - ξ_i ξ^p h_{pj} - ξ_j ξ^p h_{pi} + ξ_i ξ_j tr h)`;
- `deTurckFieldSymbol m ξ h = h(ξ♯, ·) - (1/2)(tr h) ξ` — the symbol of the linearization of
  `W^k = g^{ij}(Γ^k_{ij} - Γ̃^k_{ij})` (from `δΓ^k_{ij} = (1/2)g^{kl}(∇_i h_{jl} + ∇_j h_{il} - ∇_l h_{ij})`);
- `lieSymbol m ξ h = -(ξ ⊗ Ŵ + Ŵ ⊗ ξ)` — the symbol of `L_W g`;
- `laplacianSymbol m ξ h = |ξ|² h` — the positive Laplacian symbol (symbol of `-Δ_g`).

Kernel-checked results:

- **`ricciSymbol_sub_half_lieSymbol_apply`** (pointwise exact identity):
  `ricciSymbol m ξ h X Y - (1/2) * lieSymbol m ξ h X Y = (1/2) * (covectorNormSq m ξ * h X Y)`.
- **`ricciSymbol_sub_half_lieSymbol`** (operator form):
  `σ(Ric - (1/2)L_W g)(ξ) = (1/2) • laplacianSymbol`, i.e.
  `ricciSymbol - (1/2) • lieSymbol = (1/2) • laplacianSymbol`.
- **`ricciSymbol_sub_half_lieSymbol_eq_smul`**:
  `σ(Ric - (1/2)L_W g)(ξ) h = ((1/2) * |ξ|²) • h` — the symbol is a scalar multiple of the
  identity on 2-tensors.
- **`flowSymbol`** (flow form): `(-2) • ricciSymbol + lieSymbol = - laplacianSymbol`, i.e.
  `σ(-2Ric + L_W g) = -|ξ|² • Id = σ(Δ_g)`.
- **`deTurckSymbol_bijective`**: for every nonzero covector `ξ`, the principal symbol
  `h ↦ σ(Ric - (1/2)L_W g)(ξ) h` is a bijection of the space of bilinear forms. This is the
  ellipticity conclusion. `deTurckSymbol_injective` and `deTurckSymbol_eq_zero_iff` record the
  trivial-kernel form.
- **`ricciSymbol_symm`, `lieSymbol_symm`, `laplacianSymbol_symm`**: the symbols preserve
  symmetry, so the identity descends to symmetric 2-tensors.

## 4. Item 3 — statement-only Props

`FlowInterface` carries the metric type, the solution type, evaluation at a time, smoothness,
the Ricci–DeTurck equation predicate, the Ricci flow equation predicate, pullback by a family
of diffeomorphisms, and the harmonic-map heat flow predicate. All analytic content is in these
interface fields. The statement-only Props are:

- `FlowInterface.ShortTimeExistence` — from every smooth initial metric there is `T > 0` and a
  smooth Ricci–DeTurck solution on `(0,T)` with `g(0) = g0`.
- `FlowInterface.Uniqueness` — two smooth Ricci–DeTurck solutions on `(0,T)` with the same
  initial metric are equal.
- `FlowInterface.PullbackEquivalenceForward` — every Ricci–DeTurck solution pulls back along
  the harmonic-map heat flow to a Ricci flow.
- `FlowInterface.PullbackEquivalenceBackward` — every Ricci flow is the pullback of a
  Ricci–DeTurck flow with the same initial metric along the harmonic-map heat flow.
- `FlowInterface.PullbackEquivalence` — the conjunction of the two halves.
- `FlowInterface.RicciFlowUniqueness` — **the corollary statement**: two smooth Ricci flows on
  `(0,T)` with the same initial metric are equal.

Kernel-checked derivation (analytic inputs are explicit hypotheses, not axioms):
`FlowInterface.ricciFlowUniqueness_of_deturck` proves `RicciFlowUniqueness` from DeTurck-flow
uniqueness, harmonic-map-heat-flow uniqueness and the backward pullback equivalence.

Non-vacuity: the degenerate one-point `FlowInterface.toy` inhabits the interface and
`toy_shortTimeExistence`, `toy_uniqueness`, `toy_pullbackEquivalenceForward`,
`toy_pullbackEquivalenceBackward`, `toy_pullbackEquivalence`, `toy_ricciFlowUniqueness` and
`toy_ricciFlowUniqueness_of_deturck` check that every statement-only Prop is satisfiable. This
is a consistency check of the interface, not a proof of the analysis.

## 5. Kernel audit (`#print axioms`)

Every declaration of the three authored modules is printed with `#print axioms` at the end of
its file (recorded in `logs/D9_deturck_lean_*.log`).

- declarations printed: **60** (ConnectionLayer 21, SymbolModel 22, StatementOnly 17)
- axiom cones observed: **60 × `{propext, Classical.choice, Quot.sound}`**, 0 others
- project axioms: **0**; `sorryAx`: **0**; `unsafe`: **0**; `native_decide`: **0**;
  `proof_wanted`: **0**; `admit`: **0**
- forbidden-token scan (`input/d5-tools/scan_forbidden.py release/Poincare/D9/DeTurck`):
  **3 files scanned, 0 hard matches, 0 soft matches** (`logs/D9_deturck_forbidden_scan.json`)

## 6. Compile gate

| command | exit |
|---|---|
| `lake env lean Poincare/D9/DeTurck/ConnectionLayer.lean` | 0 |
| `lake env lean Poincare/D9/DeTurck/SymbolModel.lean` | 0 |
| `lake env lean Poincare/D9/DeTurck/StatementOnly.lean` | 0 |
| `lake build Poincare.D9.DeTurck.ConnectionLayer Poincare.D9.DeTurck.SymbolModel Poincare.D9.DeTurck.StatementOnly` | 0 (3073 jobs) |
| `python3 input/d5-tools/scan_forbidden.py Poincare/D9/DeTurck` | 0 |

Logs: `logs/D9_deturck_lean_*.log`, `logs/D9_deturck_lake_build.log`,
`logs/D9_deturck_forbidden_scan.json`.

### 6.1 Worktree-root gate environment (repair attempt 1)

The harness compile gate (`dispatch_loop.py :: compile_gate`) does **not** compile from
`release/`: it walks every `.lean` file under the worktree (excluding `.lake`, `.git`,
`.dshpkg`) and runs

```bash
cd <worktree root> && lake env lean <absolute path to the file>
```

with the **worktree root** as the working directory. The accepted D6 scaffold keeps the Lake
package in `release/`, so the worktree root had neither a `lean-toolchain` nor a Lake package
and every `.lean` file failed immediately with

```
error: no default toolchain configured. run `elan default stable` to install & configure the latest Lean 4 stable release.
```

(exit 1). That is an environment failure at the worktree root, not an elaboration or proof
failure in the authored modules. Attempt 1 of the gate failed for this reason.

Repair — three root-level gate-support files, containing **no Lean sources and no mathematical
content**, and no accepted D6 source modified:

| root file | role |
|---|---|
| `lean-toolchain` | copy of `release/lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`) so `elan` resolves the pinned toolchain from the worktree root |
| `lakefile.toml` | package `D9GateRoot` with a path dependency on the `release` package; no `lean_lib`, no sources |
| `lake-manifest.json` | copy of the release package manifest with `packagesDir = release/.lake/packages` and the `PoincareRelease` path-dependency entry; pins mathlib `7974e751…` exactly as the release does |

No `.lake` symlink is required, so the fix survives the relay
(`rsync --exclude='.lake/'`) and the central gate re-run.

### 6.2 Artifact-independent import graph (repair attempt 2)

The gate command `lake env lean <file>` does **not** build imports. In the gate environment the
oleans of the authored modules were absent (`release/.lake/build/lib/lean/Poincare/D9` had been
restored to the pre-task D6 base), so the two files that imported a sibling authored module
failed with

```
error: object file '.../release/.lake/build/lib/lean/Poincare/D9/DeTurck/ConnectionLayer.olean'
of module Poincare.D9.DeTurck.ConnectionLayer does not exist
```

(`All.lean` and `SymbolModel.lean`, exit 1; the other 66 `.lean` files exited 0). This is an
import-resolution failure of the authored import graph, not an elaboration failure of any
declaration.

Repair (authored files only; no mathematical content changed):

- `SymbolModel.lean`: removed `import Poincare.D9.DeTurck.ConnectionLayer`. The module
  references no declaration of that module — the import edge was unused, and removal is
  verified by successful elaboration with the D9 oleans deleted.
- `All.lean` (19-line aggregate import driver): removed. A file whose only content is imports
  of sibling modules cannot elaborate when their oleans are absent, and it carried no
  mathematical content. The three content modules are now each self-contained.
- `ConnectionLayer.lean`, `StatementOnly.lean`: unchanged (already self-contained;
  `import Mathlib.Tactic` only).

Verification with the D9 build directory deleted before the walk
(`rm -rf release/.lake/build/lib/lean/Poincare/D9`), i.e. in the same pristine state in which
the gate failed:

| command | files | exit 0 | exit ≠ 0 |
|---|---|---|---|
| `cd <worktree root> && lake env lean <f>` (all `.lean` files) | 67 | 67 | 0 |

Per-file exit codes and wall times: `logs/D9_deturck_gate_replica_root.log` (67/67 exit 0,
max 6.0 s per file). The 60 kernel-checked declarations and their axiom cones are unchanged
(§5), and all commands of §6 still exit 0.

The harness `compile_gate` itself then re-ran on this worktree and promoted the task at
`2026-09-10T01:24:17+0800` with `ok: true` over the same 67 `.lean` files, every exit code 0
(`../state/D9-deturck-trick/gate.json`).

## 7. What is explicitly NOT claimed

- existence of the Ricci–DeTurck flow (short-time existence is a statement-only Prop);
- uniqueness of the Ricci–DeTurck flow (statement-only Prop);
- existence of the harmonic-map heat flow and its uniqueness (interface predicates; the
  uniqueness is an explicit hypothesis of the conditional corollary);
- the pullback equivalence with Ricci flow (statement-only Props, both directions);
- uniqueness of Ricci flow (statement-only corollary Prop; the conditional derivation is
  kernel-checked but depends on the three analytic hypotheses);
- any smooth-manifold, PDE or parabolic-theory content beyond the component/symbol algebra
  proved above.

## 8. Reproduction

```bash
export ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-deturck-trick/release
for f in ConnectionLayer SymbolModel StatementOnly; do
  lake env lean "Poincare/D9/DeTurck/${f}.lean" || exit 1
done
lake build Poincare.D9.DeTurck.ConnectionLayer Poincare.D9.DeTurck.SymbolModel \
  Poincare.D9.DeTurck.StatementOnly
python3 ../input/d5-tools/scan_forbidden.py Poincare/D9/DeTurck
# harness gate, reproduced exactly (worktree root as cwd), with no D9 oleans present:
cd .. && rm -rf release/.lake/build/lib/lean/Poincare/D9
for f in $(find . -path ./.lake -prune -o -path ./.git -prune -o \
    -path ./.dshpkg -prune -o -name '*.lean' -print | sort); do
  lake env lean "$f" || exit 1
done
```

Environment note: the scaffold command `cp -al ../D6_weekly_release/. .` fails in this
worktree because XFS project quotas reject cross-project hard links (`EXDEV: Invalid
cross-device link`). The scaffold was reproduced with `cp -a` for the small tree and a symlink
for the 7.9 GB `.lake/packages` prebuild, which is the pattern the D6 release itself documents
("`.lake/packages` symlinks the shared pinned mathlib prebuild"). No accepted D6 source was
modified; the only added files are the three modules above, the three root-level gate-support
files of §6.1, the result card, and the logs. Repair attempt 2 deleted the import-only
aggregate driver `All.lean` and the unused `ConnectionLayer` import of `SymbolModel.lean`
(§6.2); no mathematical content was lost.

## 9. Files produced

- `release/Poincare/D9/DeTurck/ConnectionLayer.lean`
- `release/Poincare/D9/DeTurck/SymbolModel.lean`
- `release/Poincare/D9/DeTurck/StatementOnly.lean`
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` (worktree-root gate environment, §6.1; no Lean sources)
- `longrun/results/D9-deturck-trick.md`
- `longrun/results/D9-deturck-trick.json`
- `logs/D9_deturck_lean_*.log`, `logs/D9_deturck_lake_build.log`, `logs/D9_deturck_forbidden_scan.json`
- `logs/D9_deturck_gate_replica_root.log` (all 67 worktree `.lean` files, exit 0, no D9 oleans present)

TASK_DONE — `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-deturck-trick/longrun/results/D9-deturck-trick.md`
