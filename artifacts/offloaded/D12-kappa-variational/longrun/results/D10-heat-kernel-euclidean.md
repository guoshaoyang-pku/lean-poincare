# D10-heat-kernel-euclidean — result card

- **Task id:** `D10-heat-kernel-euclidean`
- **Stage / lane:** D10 / Euclidean heat kernel (explicit, unconditional)
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-heat-kernel-euclidean`
- **Generated:** `2026-09-10T01:18:27Z`; **repair pass:** `2026-09-10T01:31Z` (compile-gate
  fix only — no Lean source and no mathematical content changed; see §5.1)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2`; mathlib `7974e751bece493b6ff508039423ca9fa2452fa8` (git head, work tree clean)
- **Module root:** `release/Poincare/D10/HeatKernelEuclidean/`
- **Verdict:** **UNCONDITIONAL — THE EXPLICIT EUCLIDEAN HEAT KERNEL IS DEFINED, SOLVES THE HEAT EQUATION, HAS TOTAL MASS ONE, AND SATISFIES THE SEMIGROUP CONVOLUTION IDENTITY IN EVERY DIMENSION**

> Every declaration is kernel-checked with no `sorry`, no `axiom`, no `unsafe`,
> no `native_decide`, no `proof_wanted` and **no interface hypothesis**: there is
> no residual `Prop` parameter, no structure field and no named assumption in any
> statement below. The semigroup identity is *proved* (in every dimension `n`,
> not merely stated, and not only in `1D`). All 30 audited declarations depend on
> exactly `[propext, Classical.choice, Quot.sound]`.

---

## 1. Definition (item 1)

`release/Poincare/D10/HeatKernelEuclidean/Basic.lean`

```lean
noncomputable def gaussianKernel (n : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))
```

`EuclideanSpace ℝ (Fin n)` is `PiLp 2 (fun _ : Fin n => ℝ)`, i.e. `ℝⁿ` with the
usual Euclidean inner product; `‖x‖ ^ 2 = ∑ i, x i ^ 2`
(`norm_sq_eq_sum_sq`) and `⟪EuclideanSpace.basisFun (Fin n) ℝ i, x⟫ = x i`
(`inner_basisFun`), both proved here as the bridge to the standard orthonormal
basis of mathlib.

Elementary properties proved alongside the definition: non-negativity
(`gaussianKernel_nonneg`), strict positivity and non-vanishing for `t > 0`
(`gaussianKernel_pos`, `gaussianKernel_ne_zero`), joint measurability in `(t,x)`
(`measurable_gaussianKernel`), continuity in `x` at fixed `t`
(`continuous_gaussianKernel`), and non-vanishing of the prefactor
(`rpow_prefactor_ne_zero`).

## 2. Item 2 — the heat equation `∂ₜK = ΔK` (unconditional)

`release/Poincare/D10/HeatKernelEuclidean/HeatEquation.lean`

Here `Δ` is mathlib's `Laplacian.laplacian` on `EuclideanSpace ℝ (Fin n)`, i.e.
the trace of the second Fréchet derivative against the canonical covariant
tensor — the coordinate second-derivative sum `∑ᵢ ∂ᵢ²`.

| theorem | statement |
| --- | --- |
| `heat_equation` | `∀ n {t}, 0 < t → ∀ x, deriv (fun s => K n s x) t = Δ (K n t) x` |
| `heat_equation_fun` | `∀ n {t}, 0 < t → deriv (fun s => K n s) t = Δ (K n t)` (identity of functions `ℝⁿ → ℝ`) |

Both sides are computed *explicitly and separately*:

1. **Time derivative** (`hasDerivAt_gaussianKernel`, and its Banach-space form
   `hasDerivAt_gaussianKernel_fun` obtained through `hasDerivAt_pi`):
   ```
   HasDerivAt (fun s => K n s x) (K n t x * (‖x‖²/(4t²) - n/(2t))) t ,
   ```
   assembled from `HasDerivAt.rpow_const` applied to `s ↦ 4πs` (chain rule for the
   prefactor, with the algebra `4π·(-n/2)·(4πt)^{-n/2-1} = -(n/(2t))·(4πt)^{-n/2}`
   checked via `Real.rpow_add`/`Real.rpow_neg` and `field_simp`) and from
   `HasDerivAt.exp` applied to `s ↦ -‖x‖²/(4s)` (quotient rule), then multiplied.

2. **Laplacian** (`laplacian_gaussianKernel`): the constant prefactor is pulled
   out of `Δ` (`InnerProductSpace.laplacian_smul`, whose `ContDiffAt ℝ 2`
   side condition is discharged from `contDiff_norm_sq`), and the remaining
   Gaussian is differentiated in the standard orthonormal basis
   (`InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis`) with
   ```
   Δ (fun y => exp (a ‖y‖²)) x = (2 a n + 4 a² ‖x‖²) exp (a ‖x‖²)
   ```
   (`laplacian_exp_norm_sq`, item 2 of `GaussianIntegral.lean`, for an arbitrary
   finite-dimensional real inner product space and an arbitrary orthonormal
   basis). At `a = -1/(4t)` this is `(‖x‖²/(4t²) - n/(2t)) · exp(-‖x‖²/(4t))`.

   The second Fréchet derivative is *not* postulated: `iteratedFDeriv_two_exp_norm_sq`
   proves the diagonal second derivative directly from `HasFDerivAt` data. The
   only technical device is `innerCLM`, an `ℝ`-linear copy of `innerSL ℝ`
   (`innerSL ℝ` is only `starRingEnd ℝ`-linear, which is propositionally but not
   definitionally the same type); it is used so that the CLM-valued derivative of
   `y ↦ (2a) • innerSL ℝ y` has the type expected by `HasFDerivAt.smul`.

3. The two expressions coincide identically: both are
   `K n t x * (‖x‖²/(4t²) - n/(2t))`, so `heat_equation` closes by `rw`.

## 3. Item 3 — total mass `1` and the semigroup convolution identity

### 3.1 Total mass (`Mass.lean`)

| theorem | statement |
| --- | --- |
| `gaussianKernel_integral` | `∀ n {t}, 0 < t → ∫ x, K n t x = 1` |

The multivariate Gaussian integral is first proved for an arbitrary
finite-dimensional real inner product space (`GaussianIntegral.lean`):

```
integral_exp_neg_mul_norm_sq : 0 < a → ∫ v, exp (-a ‖v‖²) = (π/a)^(finrank ℝ V / 2)
```

by transporting mathlib's complex Gaussian integral
`GaussianFourier.integral_cexp_neg_mul_sq_norm_add` (with `c = w = 0`) along
`Complex.ofReal_cpow` and `integral_complex_ofReal`, then converting the
`ℂ`-valued integral of a real-valued function back with
`Complex.ofReal_injective`. (This avoids Fubini entirely.) Its translated form
`integral_exp_neg_mul_norm_sq_sub` (translation invariance of Lebesgue measure,
`integral_sub_right_eq_self`) is what the semigroup computation consumes. The
mass result is then `(4πt)^{-n/2} · (π/(1/(4t)))^{n/2} = (4πt)^{-n/2}(4πt)^{n/2} = 1`
using `Real.rpow_add` and `finrank_euclideanSpace_fin_real`.

### 3.2 The semigroup identity (`Semigroup.lean`)

| theorem | statement |
| --- | --- |
| `SemigroupConvolutionIdentity n` | the named `Prop`: `∀ t s, 0 < t → 0 < s → ∀ x, (K_t * K_s)(x) = K_{t+s}(x)` |
| `semigroupConvolutionIdentity` | `∀ n, SemigroupConvolutionIdentity n` — **proved**, in every dimension |
| `gaussianKernel_convolution` | the same identity unfolded as a plain integral equality |

The proof is the classical explicit computation:

1. **Complete the square** (`conv_exponent_identity`, an identity in an
   arbitrary real inner product space, proved by expanding both sides in the
   inner product and `field_simp; ring`):
   ```
   ‖y‖²/(4t) + ‖x-y‖²/(4s) = ((t+s)/(4ts)) ‖y - (t/(t+s)) x‖² + ‖x‖²/(4(t+s)) .
   ```
2. **Translate** the Gaussian factor: `∫ y, exp (-a ‖y - c‖²) = (π/a)^{n/2}`,
   `a = (t+s)/(4ts)`, `c = (t/(t+s)) x` (`integral_exp_neg_mul_norm_sq_sub`).
3. **Combine the prefactors** (`prefactor_mul`, positive `t, s`):
   ```
   (4πt)^{-n/2} (4πs)^{-n/2} (4πts/(t+s))^{n/2} = (4π(t+s))^{-n/2} ,
   ```
   proved with `Real.mul_rpow` / `Real.div_rpow` / `Real.inv_rpow` /
   `Real.rpow_neg`, reducing to `(b/a)^N = a^{-N} b^N` and
   `(4πts/(t+s))/(16π²ts) = (4π(t+s))⁻¹`.

No named hypothesis, structure field or `Prop` parameter is introduced anywhere;
the `Prop` `SemigroupConvolutionIdentity` is a *definition* that is then
unconditionally proved.

## 4. Item 4 — kernel audit (`#print axioms`)

`release/Poincare/D10/HeatKernelEuclidean/AxiomAudit.lean` prints `#print axioms`
for all **30** declarations and then re-checks the same cones programmatically
with `Lean.collectAxioms`, failing the build on any axiom outside
`{propext, Classical.choice, Quot.sound}`.

- `#print axioms` lines: **30 / 30** report `[propext, Classical.choice, Quot.sound]`
- distinct axiom cones observed: **1**, namely `[propext, Classical.choice, Quot.sound]`
- programmatic re-check: `D10AxiomCheck: PASS — all 30 declarations of the D10 heat-kernel development depend only on [propext, Classical.choice, Quot.sound]`
- `sorryAx` / project axiom / `unsafe` / `native_decide` / `proof_wanted` / `admit`: **0 / 0 / 0 / 0 / 0 / 0**
- negative control (`../negcontrol/NegativeControl.lean`, run from `release/`): exit 0;
  it confirms the audit predicate *does* detect `sorryAx` and the private
  `native_decide` axiom, so the PASS above is not vacuous.

Log: `logs/D10_heat_kernel_axiom_audit.out` (full `#print axioms` transcript).

## 5. Compile gate

### 5.1 Harness compile gate (the gate that actually runs)

The harness gate (`longrun/bin/dispatch_loop.py::compile_gate`) runs

```
lake env lean <absolute path of every .lean file>        # cwd = worktree root
```

over **all 70 `.lean` files** in the worktree (the six D10 modules, the base D6
package, the generated probe and the negative control), skipping only
`.lake`/`.git`/`.dshpkg`.

| item | value |
| --- | --- |
| files checked | **70** |
| files exit 0 | **70** |
| files nonzero | **0** |
| overall | **`ok: true` / `GATE_OK`** |
| log | `logs/D10_worktree_root_gate.log` |
| per-file exit codes | `logs/D10_worktree_root_gate.json` |

Reproduction of exactly that gate:

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-heat-kernel-euclidean
find . -path ./.lake -prune -o -name '*.lean' -print | sort | while read f; do
  lake env lean "$f" || { echo "FAIL $f"; exit 1; }
done
```

**Attempt 1 failed and this was the repair.** The first TASK_DONE was written after
running the per-file gate with `cwd = release/` (below), which is *not* the
harness gate. Two infrastructure defects made the root-cwd gate fail:

1. the worktree root had no `lean-toolchain`, `lakefile.toml` or
   `lake-manifest.json`, so `lake env lean` from the root exited 1 on **every**
   file with `error: no default toolchain configured`;
2. after adding the root package, **50 / 70** files still failed with
   `object file '.../Poincare/Longrun/.../X.olean' does not exist`, because only
   the six D10 modules had been built and the base D6 modules had no oleans.

Fix (no Lean source touched, nothing under `release/Poincare/D10/` modified):

- added worktree-root package files only — `lakefile.toml` (root workspace that
  re-exposes `release/.lake`), `lean-toolchain`, `lake-manifest.json`, and the
  symlink `.lake -> release/.lake`; this is the same pattern the
  `D7-heat-kernel-existence` and `D9-sobolev-parabolic-estimates` worktrees use,
  and it contains no mathematical content;
- ran the full `lake build` from `release/` (exit 0, `8952 jobs`), so every base
  module olean exists for the root-cwd gate
  (`logs/D10_heat_kernel_lake_build.log`; the build's own `D6AUDIT` verdict line
  is `PASS — no sorryAx, no project axiom, no unsafe, no native_decide, no
  unapproved axiom, no proof_wanted`).

`release/Poincare/D10/HeatKernelEuclidean/*.lean` are byte-identical to the
pre-repair card (all six sha256 values in §6 unchanged), so no claim in §1–§4 is
affected by the repair.

### 5.2 Per-file gate for the authored modules (`cwd = release/`)

Logs `logs/D10_heat_kernel_lean_*.{out,err}`:

| file | command | exit | seconds |
| --- | --- | --- | --- |
| `Basic.lean` | `lake env lean Poincare/D10/HeatKernelEuclidean/Basic.lean` | 0 | 2.5 |
| `GaussianIntegral.lean` | `lake env lean Poincare/D10/HeatKernelEuclidean/GaussianIntegral.lean` | 0 | 4.2 |
| `Mass.lean` | `lake env lean Poincare/D10/HeatKernelEuclidean/Mass.lean` | 0 | 2.5 |
| `HeatEquation.lean` | `lake env lean Poincare/D10/HeatKernelEuclidean/HeatEquation.lean` | 0 | 2.9 |
| `Semigroup.lean` | `lake env lean Poincare/D10/HeatKernelEuclidean/Semigroup.lean` | 0 | 3.0 |
| `AxiomAudit.lean` | `lake env lean Poincare/D10/HeatKernelEuclidean/AxiomAudit.lean` | 0 | 2.5 |

No warnings, no `stderr` beyond the sandbox's `landlock-run` notice. The full
package build reproduces the same result:
`lake build` from `release/` completes with exit 0, `Build completed successfully
(8952 jobs)`.

Forbidden-token scan (`input/d5-tools/scan_forbidden.py Poincare/D10/HeatKernelEuclidean`,
comment/string aware): **6 files scanned, 0 hard matches, 0 soft matches**, exit 0
(`logs/D10_heat_kernel_forbidden_scan.json`).

Negative control: `lake env lean ../negcontrol/NegativeControl.lean`, exit 0
(`logs/D10_heat_kernel_negative_control.log`); it reports both the `sorryAx` cone
and the private `native_decide` axiom, so the audit predicate above is not
vacuous.

## 6. Files produced (all new; no D6 release source touched)

| file | lines | sha256 |
| --- | --- | --- |
| `release/Poincare/D10/HeatKernelEuclidean/Basic.lean` | 102 | `6ae3a5a8a3997402a476792ed4f617475852b16831a9d7757fc0563107524a27` |
| `release/Poincare/D10/HeatKernelEuclidean/GaussianIntegral.lean` | 166 | `d8ccb171e581cbd454d68f899dc02dbbcbfbd009072956ca04072412cff1ce31` |
| `release/Poincare/D10/HeatKernelEuclidean/Mass.lean` | 49 | `621028f166d16dade9cf86d36dfd06d3644ebff6156d58049ece2b7b48131357` |
| `release/Poincare/D10/HeatKernelEuclidean/HeatEquation.lean` | 160 | `9a0236461c412b95c45800baed3e970ae620883a7faf487d03be5b982b26d3b3` |
| `release/Poincare/D10/HeatKernelEuclidean/Semigroup.lean` | 144 | `87efdbbc92a7e8a46424edc91cde6c6e6bf84acb483b3ad02a833de39efd8be0` |
| `release/Poincare/D10/HeatKernelEuclidean/AxiomAudit.lean` | 129 | `17a01e4774d64b371bebb95be173d898314a6a1d2f615d53e9e1e156344e0634` |
| **total** | **750** | |

All six files are byte-identical to the pre-repair card (verified by re-hashing
during the repair pass), i.e. the compile-gate repair changed no Lean source.

Repair-pass additions (package configuration only, no mathematical content):
`lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `.lake -> release/.lake`
(worktree root; `lean-toolchain` and `lake-manifest.json` are copies of the
`release/` ones).

Logs written (evidence, not sources): `logs/D10_heat_kernel_lean_{Basic,GaussianIntegral,Mass,HeatEquation,Semigroup,AxiomAudit}.{out,err}`,
`logs/D10_heat_kernel_lake_build.log`, `logs/D10_heat_kernel_axiom_audit.{out,err}`,
`logs/D10_heat_kernel_forbidden_scan.json`, `logs/D10_heat_kernel_negative_control.log`,
`logs/D10_worktree_root_gate.log`, `logs/D10_worktree_root_gate.json`.

Result card: `longrun/results/D10-heat-kernel-euclidean.md` + `.json`.

## 7. Honest scope

- **Proved and unconditional:** the definition of the kernel; its elementary
  properties; the multivariate Gaussian integral in every finite dimension; the
  Laplacian of `exp (a ‖x‖²)` in every finite dimension; `∂ₜK = ΔK` for every
  `n` and every `t > 0`, pointwise and as functions; `∫ K = 1` for every `n` and
  every `t > 0`; the semigroup/convolution identity `K_t * K_s = K_{t+s}` for
  every `n` and all `s, t > 0`.
- **Not claimed:** uniqueness of solutions to the Cauchy problem, the heat kernel
  on manifolds or with potentials, smoothing/regularity estimates,
  `L¹`/`L²` contraction, or any probabilistic interpretation. No claim is made
  about the Poincaré conjecture or Ricci flow here.
- `t > 0` is required throughout; behaviour at `t = 0` (where the formula is
  `0`/undefined in the prefactor for `n ≥ 1`) is not asserted.
- The Laplacian is mathlib's intrinsic `Laplacian.laplacian` (trace of the second
  Fréchet derivative), not a coordinate-sum definition; `laplacian_exp_norm_sq`
  is stated for an arbitrary orthonormal basis, so the identification with the
  coordinate second-derivative sum is available but not separately needed.

## 8. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-heat-kernel-euclidean

# 1. full package build (needed once, so the base modules have oleans)
cd "$WT/release" && lake build

# 2. the harness compile gate, exactly as dispatch_loop.py runs it
#    (cwd = worktree root, every .lean file)
cd "$WT"
find . -path ./.lake -prune -o -name '*.lean' -print | sort | while read f; do
  lake env lean "$f" || { echo "FAIL $f"; exit 1; }
done

# 3. per-file gate for the authored modules + evidence
cd "$WT/release"
for f in Basic GaussianIntegral Mass HeatEquation Semigroup AxiomAudit; do
  lake env lean "Poincare/D10/HeatKernelEuclidean/$f.lean" || exit 1
done
python3 ../input/d5-tools/scan_forbidden.py Poincare/D10/HeatKernelEuclidean
lake env lean ../negcontrol/NegativeControl.lean
```

Scaffold note: `cp -al ../D6_weekly_release/. .` fails in this worktree with
`EXDEV: Invalid cross-device link` (XFS cross-project hard links are refused), so
the scaffold was reproduced with `cp -r` for the small tree, with
`release/.lake/packages` symlinked to the shared pinned mathlib prebuild
(`/data3/guoshaoyang/workdir/lean_poincare/poincare-lab/.lake/packages`), which is
the pattern the D6 release and the D10 sibling task both document. No accepted
D6 source file was modified.

Repair note: the harness gate's cwd is the **worktree root**, so the worktree also
needs its own root lake package. The repair pass added the root `lakefile.toml`
(a workspace re-exposing `release/.lake`), `lean-toolchain`, `lake-manifest.json`
and the `.lake -> release/.lake` symlink — the same device-independent pattern used
by the `D7-heat-kernel-existence` and `D9-sobolev-parabolic-estimates` worktrees.
Nothing under `release/Poincare/D10/HeatKernelEuclidean/` was touched, and no
mathematical statement or proof was changed.

TASK_DONE — `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-heat-kernel-euclidean/longrun/results/D10-heat-kernel-euclidean.md`
