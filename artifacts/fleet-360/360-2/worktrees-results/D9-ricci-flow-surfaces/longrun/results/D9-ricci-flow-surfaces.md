# D9-ricci-flow-surfaces — result card

- **Task id:** `D9-ricci-flow-surfaces`
- **Stage / lane:** D9 / `360-2`
- **Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-ricci-flow-surfaces`
- **Generated:** `2026-09-09T15:44:52Z`; gate-repair update `2026-09-09T15:59:27Z`
- **Verdict:** **TASK_DONE — DIMENSION-2 RICCI-FLOW MILESTONE MODULE KERNEL-CHECKED; HAMILTON AND BERNSTEIN–BANDO–SHI REMAIN STATE-ONLY**

> The module proves the dimension-2 curvature algebra `Ric = (scal/2)·g`, the normalized-flow
> and area-preservation interface, and a kernel-checked explicit solution of the homogeneous
> logistic-type scalar ODE together with its long-time limit. It does **not** prove Hamilton's
> surface convergence theorem or the Bernstein–Bando–Shi smoothing estimates: those are
> recorded as state-only `Prop` interfaces (never as axioms).

## 1. Requirement coverage

| # | requirement | artifact | status |
|---|---|---|---|
| 1 | 2D interface `Ric = (scal/2)·g` | `IsTwoDRicci`, `isTwoDRicci_iff`, `isTwoDRicci_symm`, `trace_adjugate_mul_of_isTwoDRicci`, `trace_inv_mul_of_isTwoDRicci`, `scal_eq_trace_inv_mul_of_isTwoDRicci` | **proved** |
| 1 | normalized flow `∂ₜg = (r - scal)g`, average `r` | `IsNormalizedFlow`, `averageScalar`, `isAreaAverage_averageScalar`, `averageScalar_const_of_integrals` | **proved** |
| 1 | area preservation as a consequence | `hasDerivAt_det_of_normalizedFlow`, `hasDerivAt_areaDensity_of_normalizedFlow`, `areaRate_eq_zero_of_isAreaAverage`, `area_preserved_of_isAreaAverage`, `areaDensity_constant_of_scal_eq_r` | **proved** (Reynolds transport is an explicit hypothesis) |
| 2 | logistic-type scalar ODE for `scal(t)` | `IsScalarODESolution` (`scal' = scal(scal - r)`), `IsLogisticSolution` (`u' = u(r - u)`), `isScalarODESolution_of_laplacian_zero`, `isLogisticSolution_of_laplacian_zero`, `isLogisticSolution_deficit` | **proved** |
| 2 | explicit solution verified by computation | `homogeneousSolution`, `hasDerivAt_homogeneousSolution`, `homogeneousSolution_init`, `logisticSolution`, `hasDerivAt_logisticSolution`, `logisticSolution_init` | **proved** |
| 2 | long-time limit | `subcritical_denom_pos`, `tendsto_homogeneousSolution_zero`, `tendsto_deficit_homogeneousSolution`, `tendsto_logisticSolution` | **proved** |
| 3 | Hamilton's surface theorem | `HamiltonSurfaceTheoremStatement` (+ trivial projections `hamiltonStatement_existsAllTime`, `hamiltonStatement_converges`) | **state-only `Prop`** |
| 3 | Bernstein–Bando–Shi estimates, surfaces | `BernsteinBandoShiSurfaceStatement`, `BernsteinBandoShiUnnormalizedStatement`, `CovariantDerivativeProfile` | **state-only `Prop`** |
| 4 | no `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted` | forbidden-token scan of 5 authored files | **0 hard, 0 soft matches** |

## 2. Files authored

All files are under `release/Poincare/D9/Surfaces/` (the only files added under `release/`).

| file | lines | sha256 |
|---|---|---|
| `Poincare/D9/Surfaces/Basic.lean` | 252 | `61e349fef33367ea9439eb1898e6d3caf83d0042172f3a23d1316ad1c400abf9` |
| `Poincare/D9/Surfaces/HomogeneousODE.lean` | 293 | `f85982e761ded00a3ad8f22544e09c64986e5f872e65572b9d69f83a5cc34017` |
| `Poincare/D9/Surfaces/Statements.lean` | 158 | `714f27a59335d004ef6e11a05ea6cbec3a7ebf2c96e8a28277dfa6531e63d69c` |
| `Poincare/D9/Surfaces/All.lean` | 10 | `3fd972f8e4bc34e6c4d45b24b6996aedb8546d11e8011f64f8892124f77141dd` |
| `Poincare/D9/Surfaces/AxiomAudit.lean` | 67 | `ebbcd1168a56822f05ad959e42f098ff0e4b1d07f26410828e93e5aa3a02c9d1` |
| **total** | **780** | |

**Gate-environment shim (no authored math file changed).** The harness compile gate
(`longrun/bin/dispatch360.py::compile_gate`) invokes `lake env lean <abs file>` with
`cwd` = *worktree root* for every `.lean` file under the worktree. The Lake package lives in
`release/`, so from the root elan had no toolchain file to select and Lake had no package;
the gate therefore failed before elaborating any file (see §8). The repair adds, at the
worktree root only, `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, and the symlinks
`.lake -> release/.lake`, `Poincare -> release/Poincare`. All five authored Lean files above
are byte-identical to the first attempt (sha256 unchanged).

## 3. Mathematical content

### 3.1 Dimension-2 specialization interface (`Basic.lean`)

For a surface, `Ric = (scal/2)·g` is the full content of the curvature algebra: the Ricci
endomorphism has the single eigenvalue `scal/2` with multiplicity two.

- `IsTwoDRicci ric g scal : Prop` is the **interface identity** `ric = (scal/2) • g`. It is a
  `Prop` supplied as a hypothesis at every use site, never an axiom.
- `isTwoDRicci_iff` — entrywise form `Ric i j = (scal/2) g i j`.
- `isTwoDRicci_symm` — the identity preserves symmetry.
- `trace_adjugate_mul_of_isTwoDRicci` — `tr(adj(g)·Ric) = scal·det g`, i.e. the scalar
  curvature is the trace of the Ricci endomorphism (no invertibility needed).
- `trace_inv_mul_of_isTwoDRicci` / `scal_eq_trace_inv_mul_of_isTwoDRicci` — the same with
  `tr(g⁻¹ Ric) = scal` when `det g` is a unit.
- `IsNormalizedFlow g scal r : Prop` — the normalized flow `∂ₜ g = (r - scal) g`, written
  componentwise as `HasDerivAt (fun s => g s i j) ((r t - scal t) * g t i j) t`.
- `averageScalar μ ρ scal = (∫ scal·ρ)/(∫ ρ)`; `isAreaAverage_averageScalar` proves that this
  `r` satisfies the area-average condition `∫ (scal - r) ρ = 0`; and
  `averageScalar_const_of_integrals` proves it is constant in time whenever area and total
  scalar curvature are.
- **Area preservation.** `hasDerivAt_det_of_normalizedFlow` gives
  `d/dt det g = 2 (r - scal) det g`; `hasDerivAt_areaDensity_of_normalizedFlow` gives
  `d/dt √(det g) = (r - scal) √(det g)`; `areaRate_eq_zero_of_isAreaAverage` shows the rate
  `∫ (r - scal) ρ` vanishes when `r` is the area-average; `area_preserved_of_isAreaAverage`
  concludes `A t = A 0` for all `t` (the Reynolds transport formula is an explicit
  hypothesis); `areaDensity_constant_of_scal_eq_r` gives exact constancy in the homogeneous
  case `scal = r` with no transport hypothesis.

### 3.2 Homogeneous toy theorem (`HomogeneousODE.lean`)

The pointwise scalar evolution of the normalized surface flow is
`∂ₜ scal = Δ scal + scal (scal - r)`. The homogeneous reduction kills `Δ scal`:

- `IsScalarODESolution r κ` — `κ' = κ (κ - r)`, derived from
  `∂ₜ scal = Δ scal + scal (scal - r)` by `isScalarODESolution_of_laplacian_zero`.
- `IsLogisticSolution r u` — the classical logistic equation `u' = u (r - u)`;
  `isLogisticSolution_deficit` shows the deficit `u = r - scal` of any scalar-ODE solution
  solves it, and `isLogisticSolution_of_laplacian_zero` derives it from the
  backward-normalized flow `∂ₜ g = (scal - r) g`.
- **Explicit solution, verified by computation:**
  `homogeneousSolution r C t = r / (1 - C e^{rt})`, with
  `hasDerivAt_homogeneousSolution : HasDerivAt (homogeneousSolution r C) (κ κ - κ r) t`
  (chain rule + `field_simp` + `ring`), and `homogeneousSolution_init` fixing `C = 1 - r/κ₀`.
- **Long-time limit:** for `0 < κ₀ < r`, `subcritical_denom_pos` shows the solution exists
  for all `t`, `tendsto_homogeneousSolution_zero` proves `κ(t) → 0` (filter limit), and
  `tendsto_deficit_homogeneousSolution` proves the deficit `r - κ(t) → r` (logistic
  saturation).
- **Logistic solution:** `logisticSolution r K t = r / (1 + K e^{-rt})`,
  `hasDerivAt_logisticSolution` verifies `u' = u (r - u)` by computation,
  `logisticSolution_init` fixes the initial value, and `tendsto_logisticSolution` proves
  `u(t) → r`, the constant-curvature value.

### 3.3 State-only Props (`Statements.lean`)

- `HamiltonSurfaceTheoremStatement μ r` — for every smooth initial datum on `S²`
  (`IsSphereInitialDatum`: positive area, positive-definite metric, Gauss–Bonnet average `r`)
  there is a normalized flow `SurfaceFlow M` (`IsNormalized`, `IsSmooth`, `HasInitialDatum`)
  existing for all nonnegative times (`ExistsAllTime`) and converging to constant curvature
  (`ConvergesToConstantCurvature`).
- `BernsteinBandoShiSurfaceStatement μ` — uniform curvature bound plus scale-invariant
  derivative bounds `t^{k/2}|∂ₜ^k scal| ≤ C_k` and `t^{1+k/2}|∇^k Rm| ≤ C_k` for a smooth
  normalized surface flow (the covariant-derivative norm is the interface
  `CovariantDerivativeProfile`).
- `BernsteinBandoShiUnnormalizedStatement F` — the `t^{1+k/2}|∇^k Rm| ≤ C_k` bound for the
  unnormalized flow `∂ₜ g = -scal g`.
- Only the trivial logical projections of the Hamilton statement are proved, so the interface
  is kernel-checked to be coherent.

## 4. Kernel verification (exact commands, exit codes)

Toolchain: `leanprover/lean4:v4.34.0-rc2` (Lean `4.34.0-rc2`, commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Lake `5.0.0-src+6a10ac8`, mathlib rev
`7974e751bece493b6ff508039423ca9fa2452fa8` (`master-2026-09-04-26-g7974e751be`).

Re-verified `2026-09-09T15:58:34Z`–`2026-09-09T15:59:05Z` after the gate repair:

| step | command | exit | log |
|---|---|---|---|
| full package build | `cd release && lake build` | 0 | `logs/d9_lake_build.log` |
| per-file check | `cd release && lake env lean Poincare/D9/Surfaces/Basic.lean` | 0 (4.62 s) | `logs/d9_perfile_Basic.log` |
| per-file check | `cd release && lake env lean Poincare/D9/Surfaces/HomogeneousODE.lean` | 0 (4.79 s) | `logs/d9_perfile_HomogeneousODE.log` |
| per-file check | `cd release && lake env lean Poincare/D9/Surfaces/Statements.lean` | 0 (4.44 s) | `logs/d9_perfile_Statements.log` |
| per-file check | `cd release && lake env lean Poincare/D9/Surfaces/All.lean` | 0 (4.26 s) | `logs/d9_perfile_All.log` |
| axiom report | `cd release && lake env lean Poincare/D9/Surfaces/AxiomAudit.lean` | 0 (4.36 s) | `logs/d9_axioms.log` |
| forbidden-token scan | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D9/Surfaces` | 0 | `logs/d9_forbidden_scan.json` |
| whole-release scan | `python3 input/d5-tools/scan_forbidden.py release` | 0 | `logs/d9_forbidden_scan_release.json` |
| consolidated re-run | `bash logs/d9_reverify.sh` | 0 | `logs/d9_final_verification.log` |
| **harness-gate replay** | `cd <worktree root> && lake env lean <abs file>` for every `.lean` file | **0 for 69/69 files** | `logs/gate_replay_result.json`, `logs/gate_replay.out` |

The harness-gate replay `logs/gate_replay.py` reproduces `dispatch360.py::compile_gate`
exactly (same `os.walk` pruning of `.lake`/`.git`/`.dshpkg`, same `cwd` = worktree root, same
`lake env lean <abs file>` command, same 1800 s per-file timeout). It found 69 `.lean` files
(68 under `release/` plus the intentional `negcontrol/NegativeControl.lean`), **0 failures**,
246.2 s total. Per-file wall time on the five authored files: 4.3–4.8 s.

### Axiom report

`#print axioms` was recorded for **49 declarations** (`logs/d9_axioms.log`). Every cone is

```
{propext, Classical.choice, Quot.sound}
```

with **0** declarations depending on `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`,
any project axiom, `unsafe`, `native_decide`, or `proof_wanted`. Machine summary:
`logs/d9_axiom_summary.json`.

### Forbidden-token scan

- authored D9 files: 5 scanned, **0 hard matches, 0 soft matches**
  (`sorry`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`, `sorryAx`, `admit`,
  `implemented_by`, `extern`).
- whole `release/` tree: 68 Lean files, **0 hard, 0 soft matches**.

## 5. Honest boundaries

1. **Hamilton's theorem and the Bernstein–Bando–Shi estimates are not proved.** They are
   `def : Prop` interfaces; no declaration claims them as theorems and no axiom encodes them.
2. **The toy ODE is the homogeneous model reduction.** Dropping `Δ scal` leaves
   `scal' = scal(scal - r)`; without diffusion the equation cannot by itself produce the
   Hamilton convergence to constant curvature. The subcritical branch proved here has
   `scal → 0` and deficit `→ r`; the backward-normalized flow has the logistic equation
   `scal' = scal(r - scal)` with the stable value `r` (`tendsto_logisticSolution`).
3. **Area preservation uses the Reynolds transport formula as an explicit hypothesis**
   (`area_preserved_of_isAreaAverage`); the homogeneous case
   (`areaDensity_constant_of_scal_eq_r`) is proved with no transport hypothesis.
4. **The 2D interface is local-coordinate (`2×2` matrix) algebra**, not a manifold-level
   Riemannian geometry development. The `Mat2 = Matrix (Fin 2) (Fin 2) ℝ` model is the
   local-coordinate shadow of the surface; the trace identity
   `tr(g⁻¹ Ric) = scal` is the exact 2D specialization.
5. **Scaffold note.** The prescribed scaffold command `cp -al ../D6_weekly_release/. .`
   fails in this sandbox: `link()` across the two worktrees returns `EXDEV` (hard links
   across the sandbox boundary are refused). The scaffold was reproduced with
   `rsync -a --exclude 'release/.lake/packages' ../D6_weekly_release/ ./` plus a symlink
   `release/.lake/packages → ../D6_weekly_release/release/.lake/packages`. A byte-level
   `diff -r` (excluding `.lake`, `logs`, and the new `Poincare/D9`) shows **no other
   difference** from the D6 scaffold.
6. **Compile-gate environment shim.** The root-level files added by the gate repair
   (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `.lake -> release/.lake`,
   `Poincare -> release/Poincare`) contain no mathematical content. They exist only so the
   harness gate, which runs from the worktree root, can resolve the pinned toolchain, mathlib,
   and the release build. No file under `release/` was modified; the five authored files are
   byte-identical to the first attempt.

## 6. Reproduction

```bash
export ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-ricci-flow-surfaces/release
lake build
lake env lean Poincare/D9/Surfaces/Basic.lean
lake env lean Poincare/D9/Surfaces/HomogeneousODE.lean
lake env lean Poincare/D9/Surfaces/Statements.lean
lake env lean Poincare/D9/Surfaces/All.lean
lake env lean Poincare/D9/Surfaces/AxiomAudit.lean
cd ..
python3 input/d5-tools/scan_forbidden.py release/Poincare/D9/Surfaces

# harness compile-gate reproduction (runs from the worktree root, as dispatch360.py does):
python3 logs/gate_replay.py          # -> logs/gate_replay_result.json, GATE_OK=True
```

## 7. Declaration inventory (49 audited)

`Basic.lean` (17): `IsTwoDRicci`, `isTwoDRicci_iff`, `isTwoDRicci_symm`,
`trace_adjugate_mul_of_isTwoDRicci`, `trace_inv_mul_of_isTwoDRicci`,
`scal_eq_trace_inv_mul_of_isTwoDRicci`, `IsNormalizedFlow`,
`hasDerivAt_det_of_normalizedFlow`, `areaDensity`,
`hasDerivAt_areaDensity_of_normalizedFlow`, `IsAreaAverage`, `averageScalar`,
`isAreaAverage_averageScalar`, `averageScalar_const_of_integrals`,
`areaRate_eq_zero_of_isAreaAverage`, `area_preserved_of_isAreaAverage`,
`areaDensity_constant_of_scal_eq_r`.

`HomogeneousODE.lean` (18): `IsScalarODESolution`, `IsLogisticSolution`,
`isScalarODESolution_of_laplacian_zero`, `isScalarODESolution_const`,
`isLogisticSolution_deficit`, `isLogisticSolution_of_laplacian_zero`,
`homogeneousSolution`, `hasDerivAt_homogeneousSolution`, `homogeneousSolution_zero`,
`homogeneousSolution_init`, `subcritical_denom_pos`, `tendsto_homogeneousSolution_zero`,
`tendsto_deficit_homogeneousSolution`, `logisticSolution`, `hasDerivAt_logisticSolution`,
`logisticSolution_zero`, `logisticSolution_init`, `tendsto_logisticSolution`.

`Statements.lean` (14): `SurfaceFlow`, `SurfaceFlow.IsNormalized`,
`SurfaceFlow.IsUnnormalized`, `SurfaceFlow.IsSmooth`, `SurfaceFlow.HasInitialDatum`,
`SurfaceFlow.ExistsAllTime`, `SurfaceFlow.ConvergesToConstantCurvature`,
`IsSphereInitialDatum`, `HamiltonSurfaceTheoremStatement`,
`hamiltonStatement_existsAllTime`, `hamiltonStatement_converges`,
`CovariantDerivativeProfile`, `BernsteinBandoShiSurfaceStatement`,
`BernsteinBandoShiUnnormalizedStatement`.

## 8. Compile-gate repair (attempt 1)

**Diagnosis.** `longrun/bin/dispatch360.py::compile_gate` walks the whole worktree for
`.lean` files and runs `lake env lean <abs file>` with `cwd` = *worktree root*. The worktree
root is not a Lake package (the package is `release/`), so with that cwd elan reported
`error: no default toolchain configured` and exited 1 before elaborating anything; forcing
the toolchain only moved the failure to `unknown module prefix 'Mathlib'`. Reproduced
directly:

```bash
cd <worktree>            # root, not release/
lake env lean release/Poincare/D9/Surfaces/Basic.lean
# error: no default toolchain configured. run `elan default stable` ...
# exit 1
```

All 69 `.lean` files failed this way, so the attempt-1 gate failure is environmental, not a
Lean error: the five authored files compile with exit 0 from `release/` and are byte-identical
(sha256 unchanged) to attempt 1.

**Repair (worktree root only; no authored file and no file under `release/` modified).**

| path | kind | purpose |
|---|---|---|
| `lean-toolchain` | copy of `release/lean-toolchain` | elan resolves `leanprover/lean4:v4.34.0-rc2` from the root |
| `lake-manifest.json` | copy of `release/lake-manifest.json` | pins mathlib rev `7974e751…` |
| `lakefile.toml` | 418-byte shim package | root Lake package requiring mathlib, with a `Poincare` library |
| `.lake -> release/.lake` | relative symlink | exposes the release build artifacts/packages from the root |
| `Poincare -> release/Poincare` | relative symlink | matches the shim's `Poincare` library globs |

After the repair the exact gate command exits 0 for all 69 `.lean` files
(`logs/gate_replay.py`, `logs/gate_replay_result.json`, `logs/gate_replay.out`), and the
canonical release checks of §4 still pass unchanged (`logs/d9_final_verification.log`).

**Card path:** `longrun/results/D9-ricci-flow-surfaces.md` (machine form:
`longrun/results/D9-ricci-flow-surfaces.json`).

TASK_DONE
