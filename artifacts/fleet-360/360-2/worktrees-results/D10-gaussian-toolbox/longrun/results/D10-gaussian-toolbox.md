# D10-gaussian-toolbox — result card

- **Task id:** `D10-gaussian-toolbox`
- **Lane:** D10 / Gaussian integral toolbox — computational substrate for heat-kernel and PDE work
- **Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-gaussian-toolbox`
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2`; mathlib rev `7974e751bece493b6ff508039423ca9fa2452fa8`
- **Generated:** `2026-09-10T01:25:06Z`
- **Verdict:** **TASK_DONE — the Gaussian toolbox is kernel-checked and unconditional**
  (1D scaling law, exact moments for `n = 0,1,2,3`, convolution of two Gaussians with added
  variances, `n`-dimensional Fubini factorisation and total mass `1`), with every reported
  declaration depending only on `[propext, Classical.choice, Quot.sound]`.

> Nothing in this card is state-only or assumed: every theorem below is proved from mathlib's
> Gaussian integral `integral_gaussian` and mathlib's translation invariance of Lebesgue measure.
> No named hypothesis was needed for the convolution (the narrowest measure-theoretic lemma,
> `MeasureTheory.integral_sub_right_eq_self`, is available in mathlib).

## 1. Authored files

All authored sources live under `release/Poincare/D10/GaussianToolbox/`.

| file | lines | sha256 | role |
|---|---|---|---|
| `Basic.lean` | 249 | `7b514c7a4e62d0f9814c3d7da02455932b0ec8ef5ee529936fd28f1780fb6b34` | scaling law, integrability/decay, moment recursion, four exact moments, normalised density |
| `Convolution.lean` | 121 | `5c442108692471fd5c420f1fda544fcf3d6dd539a3473999875d8d4ca55f8871` | complete-the-square, 1D convolution of Gaussians, variance additivity |
| `Multivariate.lean` | 166 | `b8b148d8afa75c208469b2c2d0d52bf9b867442e2d73b39819cc7ca6bcade87d` | Fubini factorisation on `Fin n → ℝ`, total mass `1`, sum-of-squares and Euclidean-norm forms, standard normalisation |
| `PrintAxioms.lean` | 71 | `a7e2b49a1829d482ed6b0c399787aeefccdb0ffa4af2fbaabbbf6f5ac2cb479c` | 36 per-declaration `#print axioms` commands |

Namespace: `Poincare.GaussianToolbox`.

## 2. Unconditional results

### 2.1 Scaling law (`Basic.lean`)

- `gaussianKernel a x = exp (-(a * x ^ 2))` — the unnormalised kernel.
- `integral_gaussianKernel (a : ℝ) : ∫ x : ℝ, gaussianKernel a x = sqrt (π / a)` — the
  scaling law, unconditionally (at `a = 0` both sides are `0`); the positivity form
  `integral_gaussianKernel_of_pos {a} (ha : 0 < a)` is the statement required by the task.

### 2.2 Exact even moments (`Basic.lean`)

The engine is the integration-by-parts recursion, obtained by integrating the derivative
`hasDerivAt_pow_mul_gaussianKernel` over `ℝ` with mathlib's whole-line FTC-2
(`MeasureTheory.integral_of_hasDerivAt_of_tendsto`), the two endpoint limits being
`tendsto_pow_mul_gaussianKernel_atTop` / `_atBot`:

- `integral_moment_succ {a} (ha : 0 < a) (n) :
  ∫ x, x ^ (2n+2) exp (-(a x²)) = (2n+1) · ∫ x, x ^ (2n) exp (-(a x²)) / (2a)`
- `integrable_pow_mul_gaussianKernel` — every polynomial multiple of a Gaussian is integrable.

Specialising at `a = 1`:

| declaration | statement |
|---|---|
| `integral_moment_zero` | `∫ x, exp (-x²) = √π` |
| `integral_moment_two` | `∫ x, x² exp (-x²) = √π / 2` |
| `integral_moment_four` | `∫ x, x⁴ exp (-x²) = 3√π / 4` |
| `integral_moment_six` | `∫ x, x⁶ exp (-x²) = 15√π / 8` |

Normalisation consequences:

- `integral_gaussianDensity {a} (ha : 0 < a) : ∫ x, gaussianDensity a x = 1`
  where `gaussianDensity a x = √(a/π) · exp (-(a x²))`;
- `integral_gaussianDensity_mul_sq {a} (ha : 0 < a) :
  ∫ x, x² · gaussianDensity a x = gaussianVariance a`, with
  `gaussianVariance a = 1/(2a)` — the second moment is the variance.

### 2.3 Convolution of two Gaussians with added variances (`Convolution.lean`)

- `gaussianKernel_exponent_identity` — completing the square:
  `-(a t²) - b (x-t)² = -((a+b)(t - bx/(a+b))²) - (ab/(a+b)) x²` for `a + b ≠ 0`.
- `gaussianKernel_convolution {a b} (ha : 0 < a) (hb : 0 < b) (x) :
  ∫ t, exp (-(a t²)) · exp (-(b (x-t)²)) = √(π/(a+b)) · exp (-((ab/(a+b)) x²))` —
  the **full computation**: complete the square, factor out the `t`-independent exponential,
  translate (`MeasureTheory.integral_sub_right_eq_self`), and apply the scaling law.
- `sqrt_convolution_param` — `√(a/π)·√(b/π)·√(π/(a+b)) = √((ab/(a+b))/π)`.
- `gaussianDensity_convolution {a b} (ha : 0 < a) (hb : 0 < b) (x) :
  ∫ t, gaussianDensity a t · gaussianDensity b (x - t) = gaussianDensity (ab/(a+b)) x` —
  **the convolution of two normalised Gaussians is a normalised Gaussian**.
- `gaussianVariance_convolutionParam {a b} (ha) (hb) :
  gaussianVariance (ab/(a+b)) = gaussianVariance a + gaussianVariance b` —
  **the variances add**.

No hypothesis is left unproved and no measure-theoretic lemma is assumed: the only measure
theory input is mathlib's `MeasureTheory.integral_sub_right_eq_self`.

### 2.4 The `n`-dimensional Gaussian (`Multivariate.lean`)

- `gaussianVec n x = ∏ i : Fin n, exp (-(x i)²)` and
  `gaussianVecNormalized n x = (√π)⁻ⁿ · gaussianVec n x`.
- `integral_gaussianVec_fubini (n) :
  ∫ x : Fin n → ℝ, gaussianVec n x = ∏ i : Fin n, ∫ t : ℝ, exp (-t²)` —
  **Fubini via mathlib** (`MeasureTheory.integral_fintype_prod_eq_prod`, with
  `MeasureTheory.volume_pi` identifying the product measure).
- `integral_gaussianVec (n) : ∫ x, gaussianVec n x = (√π) ^ n`
  and `integral_gaussianVec_eq_pi_rpow (n) : ∫ x, gaussianVec n x = π ^ (n/2)`.
- `integral_gaussianVecNormalized (n) : ∫ x, gaussianVecNormalized n x = 1` — **total mass 1**.
- `gaussianVec_eq_exp_neg_sum_sq (n) (x) : ∏ i, exp (-(x i)²) = exp (-∑ i, (x i)²)`.
- `gaussianVec_eq_exp_neg_normSq (n) (x : EuclideanSpace ℝ (Fin n)) :
  ∏ i, exp (-(x i)²) = exp (-‖x‖²)` — the Euclidean-norm reading (on the L² type
  `EuclideanSpace ℝ (Fin n)`, since `Fin n → ℝ` carries the sup norm in mathlib).
- `integral_gaussianKernel_half : ∫ t, exp (-(t²/2)) = √(2π)`;
  `integral_standardGaussianVec (n) : ∫ x, ∏ i, exp (-(x i)²/2) = (√(2π)) ^ n`;
  `standardGaussianVec_eq_exp_neg_sum_sq`;
  `integral_standardGaussianDensity (n) :
  ∫ x, (2π)^{-n/2} · ∏ i, exp (-(x i)²/2) = 1` — the standard normalised Gaussian has
  **total mass 1**.

## 3. Verification

### 3.1 Compilation

Every authored file compiles with `lake env lean` from the worktree root (the dispatcher's
compile-gate command form), all exit codes `0`:

| file | command | exit |
|---|---|---|
| `Basic.lean` | `lake env lean release/Poincare/D10/GaussianToolbox/Basic.lean` | 0 |
| `Convolution.lean` | `lake env lean release/Poincare/D10/GaussianToolbox/Convolution.lean` | 0 |
| `Multivariate.lean` | `lake env lean release/Poincare/D10/GaussianToolbox/Multivariate.lean` | 0 |
| `PrintAxioms.lean` | `lake env lean release/Poincare/D10/GaussianToolbox/PrintAxioms.lean` | 0 |

Oleans for the imported modules were also produced (`-o`, exit 0):
`Basic.olean`, `Convolution.olean`, `Multivariate.olean` under
`release/.lake/build/lib/lean/Poincare/D10/GaussianToolbox/`.

### 3.2 `#print axioms`

`PrintAxioms.lean` reports **36 declarations**.  All 36 depend only on

`[propext, Classical.choice, Quot.sound]`

(none on a smaller cone, none on a forbidden postulate).  Counts of forbidden dependencies:
`sorryAx` **0**, project postulates **0**, `unsafe` **0**, `native_decide` **0**,
`proof_wanted` **0**.  The full log is `/tmp/d10logs/axioms1.log` (identical to
`/tmp/d10logs/final_PrintAxioms.log` and to the gate log
`/tmp/d10logs/gate_._release_Poincare_D10_GaussianToolbox_PrintAxioms.lean.log`); the
machine-readable parse is `longrun/results/D10-gaussian-toolbox.json` under
`verification.print_axioms`.

### 3.3 Forbidden-token scan

```
python3 input/d5-tools/scan_forbidden.py release/Poincare/D10/GaussianToolbox
exit 0 — 4 Lean files scanned, hard matches 0, soft matches 0
```

### 3.4 Full-tree gate recheck

A faithful re-run of the dispatcher's compile gate (`find` traversal excluding `.lake`, sorted,
`lake env lean <file>` with `cwd` = the worktree root) compiled **all 68 `.lean` files of the
worktree with exit 0 and 0 failures** — the 64 scaffold files plus the 4 authored files:
`release/Poincare/D10/GaussianToolbox/{Basic,Convolution,Multivariate,PrintAxioms}.lean` all
exit `0`.  Per-file exits are recorded in `longrun/results/D10-gaussian-toolbox.json` under
`verification.gate_recheck`, and the raw log is `/tmp/d10logs/gate_results.txt`.

### 3.5 Scaffold integrity

`diff -r --exclude=.lake` against the D6 weekly release shows **no modified scaffold file**;
the only new path under `release/` is `release/Poincare/D10/`.  The root-level Lake workspace
below is build infrastructure only (no declarations, no mathematical content):

| root path | content |
|---|---|
| `lean-toolchain` | copy of `release/lean-toolchain` |
| `lake-manifest.json` | copy of `release/lake-manifest.json` |
| `lakefile.toml` | minimal root package that `require`s mathlib |
| `.lake/packages` | symlink to `release/.lake/packages` (read-only mathlib cache) |
| `.lake/build/lib/lean` | symlink to `release/.lake/build/lib/lean` (D6 + D10 oleans) |
| `release/.lake/packages` | symlink to the D6 package cache |

## 4. Honest boundary

- No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs in the authored files.
- The only external inputs are mathlib's `integral_gaussian`
  (`∫ x, exp (-b x²) = √(π/b)`), its Gaussian integrability/decay lemmas, the whole-line FTC-2
  `MeasureTheory.integral_of_hasDerivAt_of_tendsto`, Fubini for finite products
  `MeasureTheory.integral_fintype_prod_eq_prod`, and translation invariance
  `MeasureTheory.integral_sub_right_eq_self`.  No narrowing hypothesis was necessary.
- `integral_gaussianKernel` is stated for all real `a`; at `a = 0` both sides are `0` by the
  Bochner-integral convention for a non-integrable function.  The task's `a > 0` form is
  `integral_gaussianKernel_of_pos`.
- The `n`-dimensional statements are made on `Fin n → ℝ`.  That type carries the sup norm in
  mathlib, so `exp (-‖x‖²)` is *not* the Gaussian there; the Euclidean-norm form is stated for
  `EuclideanSpace ℝ (Fin n)` (`gaussianVec_eq_exp_neg_normSq`), and the honest sum-of-squares
  form (`gaussianVec_eq_exp_neg_sum_sq`) is given for `Fin n → ℝ`.
- The compile gate also elaborates the scaffold's `negcontrol/NegativeControl.lean`, which
  intentionally contains `sorry`/`native_decide` (it is the D5/D6 negative control and is not
  part of this task's authored sources); the forbidden-token scan of §3.3 covers only the four
  authored files.
- The 16 MB of D6 `.olean` artifacts under `release/.lake/build/lib/lean` were copied from the
  D6 cache so that the scaffold modules resolve at the worktree root; `release/.lake/packages`
  is a read-only symlink to the D6 package cache.  No scaffold source was edited.

## 5. Reproduction

```bash
cd /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-gaussian-toolbox
mkdir -p release/.lake/build/lib/lean/Poincare/D10/GaussianToolbox
lake env lean -o release/.lake/build/lib/lean/Poincare/D10/GaussianToolbox/Basic.olean \
  release/Poincare/D10/GaussianToolbox/Basic.lean
lake env lean -o release/.lake/build/lib/lean/Poincare/D10/GaussianToolbox/Convolution.olean \
  release/Poincare/D10/GaussianToolbox/Convolution.lean
lake env lean -o release/.lake/build/lib/lean/Poincare/D10/GaussianToolbox/Multivariate.olean \
  release/Poincare/D10/GaussianToolbox/Multivariate.lean
lake env lean release/Poincare/D10/GaussianToolbox/PrintAxioms.lean
python3 input/d5-tools/scan_forbidden.py release/Poincare/D10/GaussianToolbox
```

Full-tree gate re-run (the dispatcher's command form, from the worktree root):

```bash
for f in $(find . -name '*.lean' -not -path './.lake/*' -not -path './release/.lake/*' | sort); do
  lake env lean "$f" || echo "FAIL $f"
done
```

Machine-readable companion: `longrun/results/D10-gaussian-toolbox.json`.

TASK_DONE — card: `longrun/results/D10-gaussian-toolbox.md`
