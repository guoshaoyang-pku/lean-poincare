# D9-sobolev-parabolic-estimates — result card

- **Task id:** `D9-sobolev-parabolic-estimates`
- **Stage / lane:** D9 / builder
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-sobolev-parabolic-estimates`
- **Scaffold:** `cp -al ../D6_weekly_release/. .` (the worktree source and destination live on different
  superblocks for `linkat`, so the scaffold was materialised with `cp -a --reflink=auto`, which is
  byte-identical and reflink-shared on XFS)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2`, mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`
  (`master-2026-09-04-26-g7974e751be`)
- **Verdict:** **TASK COMPLETE — STATEMENT-LEVEL ENERGY ESTIMATES + KERNEL-CHECKED SEMI-DISCRETE MODEL**
  (compile gate repaired: worktree-root Lake workspace added; all **69/69** `.lean` files in the
  worktree pass `lake env lean` with exit 0 from the worktree root, which is the directory the
  compile gate uses)

> **Honesty boundary.** The continuous closed-manifold parabolic theory is **statement-only**.
> The pinned mathlib has no Riemannian volume form, no Laplacian on manifolds, no Sobolev spaces and
> no parabolic regularity theory, so the closed-manifold a-priori estimate, the smoothing estimates
> and the Sobolev embeddings are recorded as `def … : Prop` with every hypothesis explicit and are
> **not proved**. What *is* fully kernel-checked is the finite-dimensional (matrix) Laplacian model:
> the exact energy identity, the energy differential inequality and the Grönwall bound. The
> statement-only Props are shown to be non-vacuous by checked witnesses, and the `L²` a-priori
> estimate is *proved* in the matrix model. No `sorry`, `axiom`, `unsafe`, `native_decide` or
> `proof_wanted` occurs anywhere.

## 1. Deliverables

All authored Lean files are under `release/Poincare/D9/ParabolicEstimates/` (5 files, 1317 lines):

| file | lines | role |
|---|---|---|
| `Gronwall.lean` | 91 | real-analysis Grönwall energy bound (checked) |
| `Basic.lean` | 270 | energy-functional interface + weak-solution data (checked) |
| `MatrixModel.lean` | 415 | semi-discrete matrix heat model: identity + Grönwall (checked) |
| `Statements.lean` | 432 | state-only closed-manifold / smoothing / Sobolev Props + witnesses |
| `AxiomAudit.lean` | 109 | consolidated `#print axioms` for all 82 declarations |

## 2. Requirement 1 — energy functional interface and weak-solution data

`Poincare.D9.ParabolicEstimates` defines, over the release's manifold-with-measure layer
(`Measure M`, `ModelWithCorners`, `ChartedSpace`, `IsManifold`, `CompactSpace`, `I.Boundaryless`,
in the style of `Poincare.Longrun.Topology.Noncollapsing` and
`Poincare.Longrun.Entropy.Functional`):

- `energyDensity X μ u = ∫ |u|² dμ` and `forcingEnergy X μ f = ∫ |f|² dμ`;
- `EnergyFunctional X μ`: `u : ℝ → X → ℝ`, `f : ℝ → X → ℝ`, `E : ℝ → ℝ` with the defining identity
  `E t = ∫ |u t|² dμ` and square-integrability of each slice;
- `DirichletForm X`: the abstract pairing `(u,v) ↦ ∫ ⟨∇u,∇v⟩ dμ`, symmetric and nonnegative on the
  diagonal;
- `WeakSolution X μ`: an `EnergyFunctional` plus a test class and the weak equation
  `(d/ds) ∫ u(s) φ dμ = -form (u t) φ + ∫ f(t) φ dμ` for every admissible `φ`;
- `EnergyIdentityStatement S`: the Prop `(d/dt) E = -2 |∇u|² + 2 ⟨u,f⟩`;
- `ClassicalSolution X μ`: weak solution + energy identity;
- `ParabolicL2Bound S C`: the Grönwall bound
  `E(t) ≤ e^{Ct}(E(0) + ∫₀ᵗ ∫ |f|² dμ)` as a Prop.

The **checked reduction** `parabolicL2Bound_of_energyIdentity` proves the abstract bound from the
energy identity, the nonnegativity of the Dirichlet form and the Young bound; the real-analysis
input is the fully proved `gronwall_energy_bound`. `young_integral` proves
`2 ∫ u f dμ ≤ ∫ u² dμ + ∫ f² dμ` from pointwise `2ab ≤ a² + b²`. The zero datum inhabits every
interface (`zeroClassicalSolution`, `zero_parabolicL2Bound`).

## 3. Requirement 2 — kernel-checked semi-discrete heat model

The finite-dimensional model lives in `MatrixModel.lean`.  A **matrix Laplacian** is a symmetric
positive-semidefinite matrix `L` (`IsMatrixLaplacian`), with `matrixEnergy u = u ⬝ᵥ u` and
`dirichletForm L u v = u ⬝ᵥ (L *ᵥ v)`.  A `SemiDiscreteHeatFlow n` is a classical solution of
`∂ₜu = -L u + f` on `Fin n → ℝ` with componentwise continuous `u, f`.

Kernel-checked results (exact statements):

- **Energy identity** (`SemiDiscreteHeatFlow.energy_identity`):
  `HasDerivAt (fun s => matrixEnergy (F.u s)) (-2 * dirichletForm F.L (F.u t) (F.u t) + 2 * (F.u t ⬝ᵥ F.f t)) t`,
  i.e. `(d/dt) E(t) = -2|∇u|² + 2⟨u,f⟩` with `E = u ⬝ᵥ u`, `|∇u|² = u ⬝ᵥ (L *ᵥ u)`,
  `⟨u,f⟩ = u ⬝ᵥ f`.
- **Linear-algebra step** (`hasDerivAt_matrixEnergy`): `(d/dt)(u ⬝ᵥ u) = 2 u ⬝ᵥ u'`, proved with
  `Finset` sum calculus.
- **Cauchy–Schwarz + Young** (`matrixEnergy_young`): `2 u ⬝ᵥ f ≤ E(u) + E(f)`, proved from
  `Finset.sum_mul_sq_le_sq_mul_sq` and `2ab ≤ a² + b²`.
- **Differential inequality** (`energy_deriv_le`): `E'(t) ≤ E(t) + ‖f(t)‖²`, using the
  nonnegativity of the Dirichlet form to drop `-2|∇u|²`.
- **Grönwall bound** (`energy_gronwall`): for `1 ≤ C` and `t ≥ 0`,
  `matrixEnergy (F.u t) ≤ e^{C t} (matrixEnergy (F.u 0) + ∫₀ᵗ matrixEnergy (F.f s) ds)`;
  `matrixEnergy_eq_sum_sq` identifies the right-hand side with the squared `L²` norm.
- **Weak formulation** (`weak_equation`): the discrete integration-by-parts identity moves `L` from
  the solution to the test function using symmetry of `L`.
- **Bridge to the abstract interface**: `matrixEnergyFunctional`, `matrixDirichletForm`,
  `matrixWeakSolution`, `matrixEnergyIdentity` (checked instance of `EnergyIdentityStatement`),
  `matrixClassicalSolution`, and `matrix_parabolicL2Bound` (checked instance of `ParabolicL2Bound`).
- **Graph Laplacian** (`dirichletForm_transpose_mul_self`): for any finite-dimensional gradient
  operator `B`, `dirichletForm (Bᵀ * B) u u = matrixEnergy (B *ᵥ u)`, i.e.
  `|∇u|² = ‖B u‖²`; hence `Bᵀ * B` is a matrix Laplacian
  (`isMatrixLaplacian_transpose_mul_self`).  The zero flow (`zeroHeatFlow`) is a checked inhabitant.

The real-analysis Grönwall lemma `gronwall_energy_bound` is proved by the integrating-factor
argument (`Y(s) = e^{-Cs} E(s)`, FTC on `[0,t]`, monotonicity of the interval integral) and only
uses `0 ≤ C`; the semi-discrete bound uses `1 ≤ C` so that `E ≤ C·E`.

## 4. Requirement 3 — state-only Props

Recorded in `Statements.lean` as `def … : Prop` (no proof, no placeholder):

**Closed-manifold parabolic data and `L²` estimates**

- `ParabolicData M` — volume measure `μ`, field `u`, forcing `f`, energy `E(t) = ∫ |u|² dμ`,
  Dirichlet form, test class, weak equation and energy identity.  *Constructing this datum from a
  Riemannian manifold is exactly the missing analytic content.*
- `ManifoldEnergyIdentity D` — the energy identity as a named Prop (inhabited by the datum).
- `ParabolicL2AprioriEstimate D T C` — for `C ≥ 1`, `T ≥ 0`, `t ∈ [0,T]`:
  `E(t) ≤ e^{Ct}(E(0) + ∫₀ᵗ ∫ |f|² dμ)`.
- `ParabolicEnergyDissipationEstimate D T` — `E(T) + 2 ∫₀ᵀ |∇u|² ≤ E(0) + ∫₀ᵀ ∫ |f|² dμ`.
- `ClosedManifoldParabolicL2AprioriEstimate`,
  `ClosedManifoldParabolicEnergyDissipationEstimate` — the same Props with the exact
  closed-manifold typeclass context (`CompactSpace`, `T2Space`, `I.Boundaryless`).

**Higher-regularity smoothing estimates**

- `ParabolicSmoothingEstimate S u f k C` —
  `‖u(t)‖_{H^k} ≤ C t^{-k/2} ‖u(0)‖_{L²} + C ∫₀ᵗ (t-s)^{-k/2} ‖f(s)‖_{L²} ds` for `t > 0`.
- `ParabolicL2ToHkSmoothing S u k C` — the homogeneous `L² → H^k` bound `C t^{-k/2} ‖u(0)‖_{L²}`.
- `ClosedManifoldParabolicSmoothingEstimate` — closed-manifold form.

**Sobolev embeddings needed to close the Ricci-flow PDE argument**

- `SobolevScale M` — the `H^{s,p}` norm, sup norm and mean as data (mathlib has no Sobolev spaces
  on manifolds).
- `SobolevEmbeddingStatement S s p t q` — the general `H^{s,p} ↪ H^{t,q}` embedding.
- `SobolevEmbeddingH1ToL6 S` — `H¹ ↪ L⁶` (3-manifold; turns `L²` energy bounds for `∇Rm` into `L⁶`
  control).
- `SobolevEmbeddingH2ToContinuous S` — `H² ↪ C⁰` (pointwise curvature bounds from energy bounds).
- `SobolevEmbeddingHkToContinuous S k` — `H^k ↪ C⁰` for `k ≥ 2` (bootstrap).
- `RellichKondrachovStatement S` — `H¹ ↪↪ L²` compactness (limiting arguments).
- `GagliardoNirenbergInterpolationStatement S` — `‖u‖_{H¹} ≤ C ‖u‖_{L²}^{1/2} ‖u‖_{H²}^{1/2}`.
- `PoincareInequalityStatement S` — zero-mean Poincaré inequality (identifies `H¹` with the
  Dirichlet form; supplies the Grönwall constant).
- `ClosedManifoldSobolevEmbeddingH1ToL6`, `ClosedManifoldSobolevEmbeddingH2ToContinuous` — closed
  three-manifold forms.

**Checked non-vacuity witnesses**

- `zeroSobolevScale` satisfies every embedding statement, Rellich–Kondrachov, Poincaré and the
  smoothing estimate (`sobolevEmbedding_zero`, `sobolevEmbeddingH1ToL6_zero`,
  `sobolevEmbeddingH2ToContinuous_zero`, `rellichKondrachov_zero`, `poincare_zero`,
  `parabolicSmoothingEstimate_zero`).
- `unitSobolevScale` on the one-point space is a genuine (non-zero) scale for which `H¹ ↪ L⁶`,
  `H² ↪ C⁰` and Poincaré hold (`sobolevEmbeddingH1ToL6_unit`,
  `sobolevEmbeddingH2ToContinuous_unit`, `poincare_unit`).
- `matrixParabolicData` + `parabolicL2AprioriEstimate_matrix`: the state-only `L²` a-priori
  estimate is a **theorem** in the finite-dimensional model, isolating the missing content to the
  construction of `ParabolicData` from a Riemannian manifold.

## 5. Requirement 4 — no forbidden constructs

- Forbidden-token scan (`input/d5-tools/scan_forbidden.py`, comment/string-aware) over
  `release/Poincare/D9/ParabolicEstimates`: **5 files scanned, 0 hard matches, 0 soft matches**
  (hard: `sorry`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`, `sorryAx`, `admit`;
  soft: `implemented_by`, `extern`).
- `#print axioms` over all **82** authored declarations: the only axiom cone is
  `{propext, Classical.choice, Quot.sound}` (82/82); no `sorryAx`, no project axiom, no
  `native_decide`.

## 6. Gates

### 6.1 Compile-gate environment (repair)

The compile gate walks **every** `.lean` file of the worktree (excluding `.lake`, `.git`,
`.dshpkg`), sorts the absolute paths, and runs

```text
lake env lean <absolute-path-to-file>
```

with the **worktree root** as the working directory.  The accepted D6 release package lives in
`release/`, so the worktree root needs its own Lake workspace; without one, `lake` finds no
`lean-toolchain`/`lakefile.toml`, falls back to an unconfigured elan default and every file exits 1
before any Lean code is read.  That was the attempt-1 failure.

The repair adds only worktree-root infrastructure (no mathematical content, no change to any
authored or promoted `.lean` source), mirroring the accepted D9 sibling worktrees:

| file | role |
| --- | --- |
| `lean-toolchain` | pins `leanprover/lean4:v4.34.0-rc2` (identical to `release/lean-toolchain`) |
| `lakefile.toml` | root workspace requiring mathlib `master`; no Lean libraries, no sources |
| `lake-manifest.json` | copy of `release/lake-manifest.json` (mathlib rev `7974e751…`) |
| `.lake -> release/.lake` | shares the release build artifacts (`build/lib/lean`, `packages`) |

The five authored D9 modules were then built in dependency order
(`lake build Poincare.D9.ParabolicEstimates.Statements` from `release/`), so that the sibling
imports (`Gronwall ← Basic ← MatrixModel ← Statements ← AxiomAudit`) resolve from oleans.

### 6.2 Full-gate result

Exact replication of the gate procedure over the whole worktree, run from the worktree root:

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-sobolev-parabolic-estimates
# for every .lean file (69 files, sorted): lake env lean <file>
```

| gate | command | exit | seconds |
| --- | --- | --- | --- |
| full compile gate | `lake env lean <file>` for all 69 `.lean` files from the worktree root | **0 (69/69)** | 282.1 total, max 6.36 |
| `release/Gronwall.lean` | `lake env lean release/Poincare/D9/ParabolicEstimates/Gronwall.lean` | 0 | 5.67 |
| `release/Basic.lean` | `lake env lean release/Poincare/D9/ParabolicEstimates/Basic.lean` | 0 | 5.24 |
| `release/MatrixModel.lean` | `lake env lean release/Poincare/D9/ParabolicEstimates/MatrixModel.lean` | 0 | 5.71 |
| `release/Statements.lean` | `lake env lean release/Poincare/D9/ParabolicEstimates/Statements.lean` | 0 | 5.88 |
| `release/AxiomAudit.lean` | `lake env lean release/Poincare/D9/ParabolicEstimates/AxiomAudit.lean` | 0 | 5.75 |
| library build | `cd release && lake build` (all default targets) | 0 | 7.05 (8951 jobs) |
| D6 kernel audit | `cd release && lake env lean D6AuditReport.lean` | 0 | — |
| forbidden scan | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D9/ParabolicEstimates` | 0 | 0.0 |

The D6 audit prints `D6AUDIT VERDICT PASS — no sorryAx, no project axiom, no unsafe, no
native_decide, no unapproved axiom, no proof_wanted` over the whole worktree (pre-existing
`partial_decl` entries from the accepted D4/D5 layers are listed but are not `unsafe`, not part of
the authored D9 files, and do not fail the gate).

## 7. What is explicitly NOT claimed

- No proof of the continuous closed-manifold parabolic `L²` a-priori estimate, of the smoothing
  estimates, of the Sobolev embeddings, of Rellich–Kondrachov, of Gagliardo–Nirenberg or of the
  Poincaré inequality: these are statement-only Props.
- No construction of a Riemannian volume measure, a Laplace–Beltrami operator, Sobolev spaces or
  the heat kernel on a manifold: those are the missing mathlib ingredients.
- No Ricci-flow existence, no Perelman monotonicity, no Poincaré conjecture.
- The semi-discrete model is a finite-dimensional linear-algebra/ODE model; it is not a
  discretization error or convergence statement.

## 8. Missing mathlib ingredients (why the Props are statements)

1. Riemannian volume measure and the Laplace–Beltrami operator on a closed manifold
   (needed for `ParabolicData`).
2. Integration by parts / divergence theorem on a Riemannian manifold (needed for the Dirichlet
   form and the weak equation).
3. Sobolev spaces `W^{k,p}(M)` on manifolds and the Sobolev embedding theorems
   (needed for `SobolevScale` instances).
4. Heat-kernel / semigroup theory and parabolic Schauder or `L²` regularity
   (needed for the smoothing estimates).
5. Rellich–Kondrachov compactness and Gagliardo–Nirenberg interpolation on manifolds.

## 9. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-sobolev-parabolic-estimates/release
lake build                                            # builds the D9 modules (and all default targets)
cd ..                                                 # the compile gate runs from the worktree root
lake env lean release/Poincare/D9/ParabolicEstimates/Gronwall.lean
lake env lean release/Poincare/D9/ParabolicEstimates/Basic.lean
lake env lean release/Poincare/D9/ParabolicEstimates/MatrixModel.lean
lake env lean release/Poincare/D9/ParabolicEstimates/Statements.lean
lake env lean release/Poincare/D9/ParabolicEstimates/AxiomAudit.lean
python3 input/d5-tools/scan_forbidden.py release/Poincare/D9/ParabolicEstimates
```

The exact gate procedure (all 69 `.lean` files, sorted, `lake env lean <file>` with `cwd` = the
worktree root) is reproduced by `tools/`-independent shell:

```bash
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-sobolev-parabolic-estimates
find . -name '*.lean' -not -path './.lake/*' -not -path './release/.lake/*' | sort | \
  while read -r f; do lake env lean "$f" >/dev/null 2>&1 || echo "FAIL $f"; done
```

## 10. Files produced

Authored Lean sources (5 files, 1317 lines, sha256 recorded in the JSON card):

- `release/Poincare/D9/ParabolicEstimates/Gronwall.lean`
- `release/Poincare/D9/ParabolicEstimates/Basic.lean`
- `release/Poincare/D9/ParabolicEstimates/MatrixModel.lean`
- `release/Poincare/D9/ParabolicEstimates/Statements.lean`
- `release/Poincare/D9/ParabolicEstimates/AxiomAudit.lean`
- `longrun/results/D9-sobolev-parabolic-estimates.md`
- `longrun/results/D9-sobolev-parabolic-estimates.json`

Gate-environment files added by the repair (infrastructure only, no Lean sources, no mathematical
content):

- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.lake -> release/.lake`

## 11. Repair log (attempt 1 → verified)

| step | observation |
| --- | --- |
| attempt-1 gate | every `.lean` file exited 1: `error: no default toolchain configured` — the worktree root had no Lake workspace, so the gate command could not even start Lean |
| root cause | the compile gate runs `lake env lean <file>` with the **worktree root** as `cwd`; the scaffold only contains the `release/` package |
| repair | added the worktree-root Lake workspace (see §6.1) and built the authored modules so the sibling imports resolve |
| re-check | 69/69 `.lean` files `lake env lean` exit 0; `lake build` (release default targets) exit 0; `D6AuditReport` exit 0 with `D6AUDIT VERDICT PASS`; forbidden scan 0 hard / 0 soft; 82/82 audited declarations have axiom cone `{propext, Classical.choice, Quot.sound}` |
| sources unchanged | no authored `.lean` source was modified by the repair; the five D9 files are byte-identical to the attempt-1 versions (sha256 in the JSON card) |

Result card: `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-sobolev-parabolic-estimates/longrun/results/D9-sobolev-parabolic-estimates.md`

TASK_DONE
