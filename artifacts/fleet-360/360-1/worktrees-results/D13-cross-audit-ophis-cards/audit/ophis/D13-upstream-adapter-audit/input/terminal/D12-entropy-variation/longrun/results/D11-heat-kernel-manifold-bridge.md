# D11-heat-kernel-manifold-bridge — result card

- **Task id:** `D11-heat-kernel-manifold-bridge`
- **Stage / lane:** D11 / bridge from the explicit D10 Euclidean heat kernel to the D7 heat-kernel interface
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-heat-kernel-manifold-bridge`
- **Generated (UTC):** `2026-09-10T13:33:03Z` (repair attempt 1: root-workspace compile fix; mathematical content unchanged)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2`; mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`
- **Module root:** `release/Poincare/D11/HeatKernelBridge/`
- **Verdict:** **UNCONDITIONAL — THE EXPLICIT D10 EUCLIDEAN HEAT KERNEL INSTANTIATES EVERY D7 HEAT-KERNEL FIELD THAT IS SATISFIABLE IN THE FLAT CASE: GAUSSIAN BOUNDS, SYMMETRY, SEMIGROUP, MASS NORMALISATION AND THE HEAT EQUATION IN EVERY DIMENSION, PLUS THE WEAK (DISTRIBUTIONAL) INITIAL CONDITION; THE LITERAL POINTWISE INITIAL CONDITION IS ISOLATED AS ONE NAMED FIELD AND IS INSTANTIATED IN DIMENSION 0.**

> Every declaration is kernel-checked with no `sorry`, no `axiom`, no `unsafe`, no `native_decide`
> and no `proof_wanted`. All **61** audited declarations depend only on
> `[propext, Classical.choice, Quot.sound]` (programmatic `Lean.collectAxioms` re-check: PASS).
> The seven authored files compile with `lake env lean` (exit 0), and the comment/string-aware
> forbidden-token scan reports 0 hard and 0 soft matches.
>
> **Repair attempt 1 (compile gate):** the dispatcher gate runs `lake env lean <file>` with
> `cwd` = worktree root, where the pre-scaffolded tree had no `lean-toolchain`/`lakefile.toml`/`.lake`,
> so every file failed to resolve a toolchain. The repair added the worktree-root workspace scaffold
> (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.lake -> release/.lake`; build
> configuration only, no Lean content) and built the release package
> (`lake build`, 9173 jobs, exit 0). The full gate — **all 291 `.lean` files** in the worktree, run
> exactly as the dispatcher runs it — now passes **291/291 exit 0** (`logs/repair_gate.json`).

---

## 0. Bottom line

| item | result |
| --- | --- |
| new files (only under `release/Poincare/D11/HeatKernelBridge/`) | **7 Lean files, 1224 lines, 61 audited declarations** |
| compile gate (dispatcher form: `lake env lean <file>`, cwd = worktree root) | **291/291 Lean files exit 0** (7 authored + 283 packaged + `negcontrol/NegativeControl.lean`); evidence `logs/repair_gate.json` |
| `#print axioms` / `Lean.collectAxioms` | **61/61 cone `[propext, Classical.choice, Quot.sound]`**, `D11AxiomCheck: PASS` |
| forbidden tokens (comment/string aware) | **0 hard / 0 soft** in 7 files |
| item 1 — D7 interface fields for the explicit kernel | **all proved unconditionally in every dimension `n`** (`flatHeatKernelCore n`): Gaussian upper/lower bounds, symmetry, semigroup (Chapman–Kolmogorov), normalisation `∫ K = 1`, heat equation `∂ₜK = ΔK` |
| item 1 — full D7 `HeatKernelData` | **inhabited with the explicit D10 kernel in dimension 0** (`flatHeatKernelData_zero`); in positive dimensions the one remaining field is isolated |
| item 2 — initial condition | **weak (distributional) form proved**: `Continuous f → Integrable f volume → ∫ y, K x y t * f y → f x` as `t → 0⁺` (hence for continuous compactly supported test functions) |
| item 3 — axiom audit | **61 declarations, single approved cone**, no forbidden token |
| bridging scaffold modified | **no mathematical source outside `release/Poincare/D11/HeatKernelBridge/`**; repair attempt 1 added the worktree-root workspace scaffold `lakefile.toml` / `lake-manifest.json` / `lean-toolchain` / `.lake -> release/.lake` (build configuration, no Lean content), plus build artefacts under `release/.lake/` and evidence under `logs/` |

**Not claimed:** no heat-kernel existence on a Riemannian manifold, no parametrix, no parabolic
regularity, no Gaussian bounds on manifolds, no distribution theory, no uniqueness of the Cauchy
problem, no `L¹`/`L²` contraction, no probabilistic interpretation, and nothing about the Poincaré
conjecture or Ricci flow.

---

## 1. What was built

| file | lines | role |
| --- | --- | --- |
| `Basic.lean` | 221 | `HeatKernelCore` — the D7 interface `Poincare.D7.HeatKernel.HeatKernelData` with `initialCondition` isolated; `FullInitialCondition` / `WeakInitialCondition`; `HeatKernelData.toCore`, `HeatKernelCore.toHeatKernelData`, `exists_toCore_eq_iff` (tightness) |
| `EuclideanLaplacian.lean` | 109 | mathlib's `Δ` packaged as a genuine linear map `laplacianLinearMap` (via the `C²` submodule and a complement projection), and the translation identity `laplacian_comp_sub` |
| `EuclideanInstance.lean` | 271 | `flatKernel`, `flatHeatKernelCore n`: the explicit D10 kernel as a bridge datum on `EuclideanSpace ℝ (Fin n)`, with all interface fields proved |
| `InitialCondition.lean` | 310 | the weak (distributional) initial condition: elementary `t → 0⁺` limits, uniform Gaussian decay, the Gaussian tail bound, and `flatKernel_tendsto_integral` |
| `ZeroDimension.lean` | 92 | dimension `0`: the weak condition upgrades to the literal D7 field, giving the full datum `flatHeatKernelData_zero` |
| `All.lean` | 34 | umbrella module |
| `AxiomAudit.lean` | 187 | 61 `#print axioms` commands + programmatic `Lean.collectAxioms` re-check |
| **total** | **1224** | |

The D11 namespace is `Poincare.D11.HeatKernelBridge`. Nothing under `release/Poincare/D7/` or
`release/Poincare/D10/` was modified; the bridge only imports and cites them. Integrity check: the
six `release/Poincare/D10/HeatKernelEuclidean/*.lean` sources still hash-match the values recorded
in the D10 result card (`Basic` `6ae3a5a8…`, `GaussianIntegral` `d8ccb171…`, `Mass` `621028f1…`,
`HeatEquation` `9a023646…`, `Semigroup` `87efdbbc…`, `AxiomAudit` `17a01e47…`). No mathematical
source outside `release/Poincare/D11/HeatKernelBridge/` was written. Repair attempt 1 added only
build configuration at the worktree root (no Lean files, no mathematical content):

| root scaffold file | sha256 |
| --- | --- |
| `lakefile.toml` | `b56f13927f2c63a07221b0fde9a31d20d42f99b80e90d4330aa7c06de6c642fa` |
| `lake-manifest.json` | `cbc45ee0bd591606b3bb5ba38c38e41f3d317c59f99cb2dfb0adc7d33b32c3d0` |
| `lean-toolchain` | `8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88` |
| `.lake` | symlink to `release/.lake` |

plus build artefacts under `release/.lake/` and evidence files under `logs/` (`D11_*`,
`repair_gate.json`, `repair_gate/`, `repair_lake_build.log`, `repair_forbidden_scan.json`).

---

## 2. Item 1 — the D7 interface instantiated with the explicit D10 kernel

### 2.1 The interface, with exactly one field isolated

`HeatKernelCore X` (`Basic.lean`) has literally the same fields as
`Poincare.D7.HeatKernel.HeatKernelData X` **except** `initialCondition`:

```
volume dist dim C_up c_up C_lo c_lo kernel laplacian
dist_self dist_nonneg dist_symm c_up_pos c_lo_pos C_up_nonneg C_lo_nonneg
kernel_nonneg gaussianUpperBound gaussianLowerBound symmetry
semigroup normalization heatEquation
```

The bridge is *tight*, in both directions and with no loss of information:

| theorem | content |
| --- | --- |
| `Poincare.D7.HeatKernel.HeatKernelData.toCore` | forget `initialCondition` |
| `HeatKernelCore.toHeatKernelData` | attach an initial condition and obtain a genuine `HeatKernelData` |
| `HeatKernelCore.toHeatKernelData_toCore` / `toCore_toHeatKernelData` | the two round trips are the identity |
| `HeatKernelCore.exists_toCore_eq_iff` | **a D7 `HeatKernelData` with prescribed core `D₀` exists iff `D₀.FullInitialCondition` holds** |
| `HeatKernelData.toCore_fullInitialCondition` | the core of a D7 datum satisfies the full condition |

So the D7 chain loses nothing but the single pointwise `initialCondition`, which is treated in §3.

### 2.2 The explicit instance

`flatHeatKernelCore n : HeatKernelCore (EuclideanSpace ℝ (Fin n))`, for every `n : ℕ`:

| field | value | D10 input used in the proof |
| --- | --- | --- |
| `volume` | Lebesgue measure `volume` | — |
| `dist x y` | `‖x - y‖` | `norm_sub_rev`, `norm_nonneg` |
| `dim` | `(n : ℝ)` | — |
| `C_up`, `c_up` | `(4π) ^ (-n/2)`, `4` | `Real.mul_rpow` |
| `C_lo`, `c_lo` | `(4π) ^ (-n/2)`, `4` | `Real.mul_rpow` |
| `kernel x y t` | `if 0 < t then gaussianKernel n t (x - y) else 0` | `gaussianKernel` |
| `laplacian` | `laplacianLinearMap (EuclideanSpace ℝ (Fin n))` | `InnerProductSpace.laplacian` via `laplacianLinearMap_apply_of_contDiff` |

The remaining fields, and the D10 theorem each cites:

| bridge field | statement | D10 theorem |
| --- | --- | --- |
| `kernel_nonneg` | `0 ≤ flatKernel n x y t` for all `t` | `gaussianKernel_nonneg` (for `t > 0`; `0` otherwise) |
| `gaussianUpperBound` | `K x y t ≤ (4π)^{-n/2} t^{-n/2} exp (-‖x-y‖²/(4t))` | `gaussianKernel_apply` |
| `gaussianLowerBound` | the reverse inequality for `‖x-y‖ ≤ 1` (in fact all `x y`) | `gaussianKernel_apply` |
| `symmetry` | `K x y t = K y x t` | `norm_sub_rev` |
| `semigroup` | `K x y (s+t) = ∫ z, K x z s * K z y t` | **`gaussianKernel_convolution`** + translation invariance of Lebesgue measure (`integral_add_right_eq_self`) |
| `normalization` | `∫ y, K x y t = 1` for `t > 0` | **`gaussianKernel_integral`** + `integral_sub_left_eq_self` |
| `heatEquation` | `HasDerivAt (fun s => K x y s) (Δ_x K · y t) t` for `t > 0` | **`hasDerivAt_gaussianKernel`**, **`laplacian_gaussianKernel`**, `laplacian_comp_sub` |

The three fields named in the task — solution property (`heatEquation`), mass normalisation
(`normalization`) and semigroup identity (`semigroup`) — are restated as
`flatHeatKernelCore_heatEquation`, `flatHeatKernelCore_normalization`,
`flatHeatKernelCore_semigroup`, together with the Gaussian-bound restatements
`flatHeatKernelCore_gaussianUpperBound` / `flatHeatKernelCore_gaussianLowerBound`.

### 2.3 Two interface-defect repairs, documented

Two D7 fields are stated in a form that the literal D10 formula cannot meet; both are handled
explicitly rather than silently:

1. **`kernel_nonneg` is stated for every real `t`.** The real power `(4πt) ^ (-n/2)` is *negative*
   for `t < 0` when `n ≡ 2 (mod 4)` (`Real.rpow` is `Re ((4πt : ℂ) ^ (-n/2))`). The bridge kernel is
   therefore truncated at nonpositive times: `flatKernel n x y t = if 0 < t then K n t (x-y) else 0`.
   It agrees with the D10 kernel on the whole positive time axis
   (`flatKernel_of_pos`, `flatKernel_eq`), which is where all analytic fields are asserted, and it is
   nonnegative for every `t` (`flatKernel_nonneg`).
2. **`initialCondition` quantifies over all continuous test functions** — see §3.

### 2.4 The Laplacian as a genuine linear map

`HeatKernelCore.laplacian` is a *linear map* `(X → ℝ) →ₗ[ℝ] (X → ℝ)`, while mathlib's `Δ` is only
additive on `C²` functions. `EuclideanLaplacian.lean` builds the linear map
`laplacianLinearMap E` by restricting `Δ` to the submodule `contDiffTwoSubmodule E = {f | ContDiff ℝ 2 f}`
(where `ContDiffAt.laplacian_add` and `InnerProductSpace.laplacian_smul` give linearity) and
extending by zero along a complementary subspace (`LinearMap.ofIsCompl`, using choice). On `C²`
functions it *is* mathlib's `Δ`:

```
laplacianLinearMap_apply_of_contDiff : ContDiff ℝ 2 f → laplacianLinearMap E f = Δ f
```

The heat equation consumes this through `laplacianLinearMap_flatKernel` and the translation identity
`laplacian_comp_sub : Δ (fun z => f (z - y)) x = Δ f (x - y)`, proved from mathlib's
orthonormal-basis formula for `Δ` and `iteratedFDeriv_comp_sub`.

### 2.5 The full D7 datum in dimension 0

In dimension `0`, `EuclideanSpace ℝ (Fin 0)` is a single point and
`volume_euclideanSpace_eq_dirac` identifies its Lebesgue measure with the Dirac measure, so *every*
function is integrable (`integrable_euclideanSpace_fin_zero`). The weak initial condition therefore
upgrades to the literal D7 field (`flatHeatKernelCore_fullInitialCondition_zero`) and

```
flatHeatKernelData_zero : Poincare.D7.HeatKernel.HeatKernelData (EuclideanSpace ℝ (Fin 0))
```

is a genuine D7 heat-kernel datum whose kernel is the explicit D10 kernel
(`flatHeatKernelData_zero_kernel`) and whose volume is Lebesgue measure
(`flatHeatKernelData_zero_volume`).

---

## 3. Item 2 — the initial condition in the flat case

### 3.1 Why the literal D7 field is not instantiated in positive dimensions

`initialCondition` asks for

```
∀ (x : X) (f : X → ℝ), Continuous f →
  Tendsto (fun t => ∫ y, kernel x y t * f y) (𝓝[>] 0) (𝓝 (f x))
```

with **no** integrability hypothesis on `f`. In Lean the Bochner integral of a non-integrable
integrand is zero by definition (`MeasureTheory.integral_undef`). A continuous test function growing
faster than every Gaussian — e.g. `f y = exp (‖y‖ ^ 3)` on `ℝⁿ`, `n ≥ 1` — makes
`y ↦ gaussianKernel n t (x - y) * f y` non-integrable for every `t > 0`, so the left-hand side is
identically `0` while `f x ≠ 0`: the literal field is not satisfiable by the flat kernel with
Lebesgue volume. (This obstruction is documented here; the counterexample is *not* formalised in
this development.) The bridge therefore proves the weak (distributional) statement, which is the
correct flat form of the field, and records the literal one as the named predicate
`HeatKernelCore.FullInitialCondition`; §2.1 proves that this is the *only* missing piece for a full
D7 instantiation.

### 3.2 The weak initial condition, proved

```
flatKernel_tendsto_integral :
  ∀ (n) (x) {f}, Continuous f → Integrable f volume →
    Tendsto (fun t => ∫ y, flatKernel n x y t * f y) (𝓝[>] 0) (𝓝 (f x))

flatKernel_tendsto_integral_of_hasCompactSupport :
  ∀ (n) (x) {f}, Continuous f → HasCompactSupport f →
    Tendsto (fun t => ∫ y, flatKernel n x y t * f y) (𝓝[>] 0) (𝓝 (f x))

flatHeatKernelCore_weakInitialCondition : ∀ n, (flatHeatKernelCore n).WeakInitialCondition
```

The compactly supported form is the classical distributional class (continuous compactly supported
test functions are integrable).

### 3.3 How it is proved

The proof is the standard approximation-of-identity argument, formalised through mathlib's peak
function theorem `MeasureTheory.tendsto_integral_peak_smul_of_integrable_of_tendsto`:

1. translate the integral: `∫ y, flatKernel n x y t * f y = ∫ z, gaussianKernel n t z * f (x - z)`
   (`integral_sub_left_eq_self`);
2. check the peak-function hypotheses for `φ t z = gaussianKernel n t z`, `g = f (x - ·)`:
   * nonnegativity (`gaussianKernel_nonneg`);
   * mass one on the finite-measure ball: `tendsto_setIntegral_ball_gaussianKernel`, from
     `tendsto_setIntegral_compl_ball_gaussianKernel` and the D10 total mass
     `gaussianKernel_integral`;
   * uniform decay away from the origin: `tendstoUniformlyOn_gaussianKernel_compl`, from the
     elementary limit `tendsto_prefactor_mul_exp_neg_div` (`t ^ (-n/2) exp (-c/t) → 0` as
     `t → 0⁺`, itself from `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` after `t ↦ t⁻¹`);
   * `g` is continuous at `0` with value `f x` and integrable (`Integrable.comp_sub_left`).

The Gaussian tail bound `setIntegral_compl_ball_gaussianKernel_le` dominates the kernel on the
complement of a ball by `(2) ^ (n/2) * exp (-(R²/8)/t)`, using the D10 multivariate Gaussian
integral `integral_exp_neg_mul_norm_sq` and the elementary prefactor identity
`prefactor_mul_eight`.

### 3.4 The narrowest remaining statement

The only D7 field not instantiated in positive dimensions is the literal pointwise
`initialCondition`, equivalently `(flatHeatKernelCore n).FullInitialCondition`
(§2.1 `flat_exists_heatKernelData_iff`). It is a *named* predicate, not an axiom: nothing in the
development assumes it, and dimension `0` proves it outright. The weak statement proved in §3.2 is
strictly weaker and covers the distributional test-function class.

---

## 4. Item 3 — axiom audit

`release/Poincare/D11/HeatKernelBridge/AxiomAudit.lean` prints `#print axioms` for all **61**
declarations and re-checks the same cones programmatically with `Lean.collectAxioms`, failing the
build on any axiom outside `{propext, Classical.choice, Quot.sound}`.

| item | value |
| --- | --- |
| `#print axioms` lines | **61 / 61** report `[propext, Classical.choice, Quot.sound]` |
| distinct cones observed | **1** (the full standard cone) |
| programmatic re-check | `D11AxiomCheck: PASS — all 61 declarations of the D11 heat-kernel bridge depend only on [propext, Classical.choice, Quot.sound]` |
| `sorryAx` / project axiom / `unsafe` / `native_decide` / `proof_wanted` / `admit` | **0 / 0 / 0 / 0 / 0 / 0** |

`Classical.choice` enters only through the complement projection in `laplacianLinearMap` and the
`Classical.choose_spec` used there.

Raw transcripts: `logs/D11_axiom_audit.out` (original run) and
`logs/repair_gate/release__Poincare__D11__HeatKernelBridge__AxiomAudit.lean.out` (repair re-run,
`D11AxiomCheck: PASS — all 61 declarations`, exit 0).

---

## 5. Compile gate

The dispatcher gate runs `lake env lean <file>` for **every** `.lean` file in the worktree with
`cwd` = worktree root. Attempt 1 failed there: the pre-scaffolded tree had no root-level
`lean-toolchain` / `lakefile.toml` / `.lake`, so no toolchain or `LEAN_PATH` could be resolved and
every file exited non-zero. The repair fixed the environment without touching any mathematical
source:

1. added the worktree-root workspace scaffold — `lakefile.toml` (package `PoincareRelease`, mathlib
   requirement, no Lean sources), `lake-manifest.json`, `lean-toolchain`
   (`leanprover/lean4:v4.34.0-rc2`), and `.lake -> release/.lake` (same layout as the promoted
   `D11-maximum-principle-tensor` worktree);
2. built the release package so that every imported module has an olean:
   `cd release && lake build` → `Build completed successfully (9173 jobs)`, exit 0
   (`logs/repair_lake_build.log`);
3. re-ran the gate exactly as the dispatcher does, over **all 291 `.lean` files** (290 under
   `release/`, including the seven authored files, plus `negcontrol/NegativeControl.lean`):
   **291/291 exit 0** in 79.9 s (`logs/repair_gate.json`, per-file stdout/stderr under
   `logs/repair_gate/`).

The seven authored files, run from the worktree root after the repair:

| file | exit |
| --- | --- |
| `release/Poincare/D11/HeatKernelBridge/Basic.lean` | **0** |
| `release/Poincare/D11/HeatKernelBridge/EuclideanLaplacian.lean` | **0** |
| `release/Poincare/D11/HeatKernelBridge/EuclideanInstance.lean` | **0** |
| `release/Poincare/D11/HeatKernelBridge/InitialCondition.lean` | **0** |
| `release/Poincare/D11/HeatKernelBridge/ZeroDimension.lean` | **0** |
| `release/Poincare/D11/HeatKernelBridge/All.lean` | **0** |
| `release/Poincare/D11/HeatKernelBridge/AxiomAudit.lean` | **0** (prints `D11AxiomCheck: PASS`, 61 declarations) |

The original authored-file check (cwd `release/`, before the repair) also had all seven at exit 0;
its per-file transcripts are in `logs/D11_lean_*.{out,err}` and the exit-code table in
`logs/D11_gate.txt`.

Forbidden-token scan (`input/d5-tools/scan_forbidden.py`, comment/string aware):
**7 files scanned, 0 hard matches, 0 soft matches**, exit 0 — `logs/D11_forbidden_scan.json`
(original) and `logs/repair_forbidden_scan.json` (repair re-run).

The scaffold files contain no Lean content and are pure build configuration; nothing under
`release/Poincare/D11/HeatKernelBridge/` was modified by the repair (the seven authored sources are
byte-identical to the attempt-1 versions).

---

## 6. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-heat-kernel-manifold-bridge

# 1. build the release package (produces the oleans every file imports)
cd "$WT/release"
lake build                                   # 9173 jobs, exit 0

# 2. full compile gate exactly as the dispatcher runs it: every .lean file, cwd = worktree root
cd "$WT"
find . -name '*.lean' -not -path './.lake/*' -not -path './.git/*' -not -path './.dshpkg/*' \
  -print0 | xargs -0 -n1 -P16 lake env lean  # 291/291 exit 0; see logs/repair_gate.json

# 3. axiom audit (61 declarations, single approved cone)
cd "$WT/release" && lake env lean Poincare/D11/HeatKernelBridge/AxiomAudit.lean | grep D11AxiomCheck

# 4. forbidden-token scan
python3 "$WT/input/d5-tools/scan_forbidden.py" "$WT/release/Poincare/D11/HeatKernelBridge"
```

---

## 7. Honest scope and deviations

- **Proved and unconditional:** the seven authored modules; `flatHeatKernelCore n` for every `n` with
  Gaussian upper/lower bounds, symmetry, Chapman–Kolmogorov, `∫ K = 1`, and `∂ₜK = ΔK` at every
  `t > 0`; the weak initial condition for continuous integrable (in particular continuous compactly
  supported) test functions; translation invariance of `Δ`; the completeness equivalence
  `exists_toCore_eq_iff`; a full D7 `HeatKernelData` from the explicit D10 kernel in dimension `0`.
- **Deviation 1 (kernel truncation).** D7's `kernel_nonneg` is stated for all real times; the raw D10
  formula is negative for `t < 0` when `n ≡ 2 (mod 4)`. The bridge kernel is truncated at `t ≤ 0`
  and coincides with the D10 kernel for `t > 0`, where every analytic field lives. No positive-time
  statement is affected.
- **Deviation 2 (initial condition).** The literal D7 field quantifies over all continuous test
  functions and is not satisfiable in positive dimensions with Lebesgue measure; the bridge proves
  the weak (distributional) form for integrable continuous test functions and isolates the literal
  field as `FullInitialCondition`. The non-satisfiability argument (Bochner integral of a
  non-integrable integrand is `0`) is documented but not formalised.
- **Not claimed:** uniqueness of the Cauchy problem, smoothing/regularity, `L¹`/`L²` contraction,
  heat kernels on manifolds, parametrix, distribution theory, or any probabilistic interpretation.
  No claim is made about the Poincaré conjecture or Ricci flow.
- `t > 0` is required throughout for the analytic fields; behaviour at `t = 0` (where the D10 formula
  is singular for `n ≥ 1`) is not asserted.
- The Laplacian is mathlib's intrinsic `Laplacian.laplacian`, packaged as a linear map; the packaged
  map is the genuine Laplacian on all `C²` functions and is only ever applied to `C²` functions.
- **Repair attempt 1 (build environment only).** The dispatcher gate executes `lake env lean` from
  the worktree root; the pre-scaffolded tree had no package there, so attempt 1 failed before
  type-checking any file. The repair added build configuration at the root
  (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.lake -> release/.lake`) and built the
  release package. No mathematical source, statement or proof was changed; the seven authored D11
  files are byte-identical to the attempt-1 versions, and every D11 declaration, axiom cone and
  forbidden-token result is unchanged.

Result card (machine-readable): `longrun/results/D11-heat-kernel-manifold-bridge.json`.

TASK_DONE — `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-heat-kernel-manifold-bridge/longrun/results/D11-heat-kernel-manifold-bridge.md`
