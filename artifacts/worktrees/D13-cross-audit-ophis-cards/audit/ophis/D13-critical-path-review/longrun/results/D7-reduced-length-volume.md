# D7-reduced-length-volume — result card

**Task id:** `D7-reduced-length-volume`
**Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-reduced-length-volume`
**Generated (UTC):** 2026-09-09T17:22:33Z
**Verdict:** `TASK_DONE` — reduced length / reduced volume layer, kept honest. The `L`-length
functional is defined over a **stated metric-flow interface** with the minimiser structure
explicit; the algebraic monotonicity consequences of the reduced-volume certificate fields are
**kernel-checked**; and the reduced length of the finite-dimensional Gaussian shrinking soliton
model is **computed explicitly**, `l(q,τ) = |q|²/(4τ)`, including minimality of the `L`-geodesic
among admissible paths. General minimiser existence and Jacobian comparison are **state-only
`Prop`s** with a ten-entry missing-dependency ledger. No
`sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted` in any authored file.

---

## 0. Bottom line

| item | result |
| --- | --- |
| new files (only under `release/Poincare/D7/Reduced/`) | **7 Lean files, 1391 lines, 84 declarations** |
| content modules | `Basic` (22), `Certificate` (30), `Statements` (15), `Gaussian` (17) |
| compiled with `lake env lean` from the worktree root | **7/7 exit 0** (`longrun/d7rlv-logs/exit_codes.txt`) |
| whole release package `lake build` | **exit 0** (8981 jobs, `longrun/d7rlv-logs/lake_build_exit.txt`) |
| `#print axioms` audit | **78/78 principal declarations**; cones `{propext, Classical.choice, Quot.sound}` (72), `{}` (5), `{propext}` (1); **0 nonstandard** |
| forbidden-token scan (comment/string-aware) | **0 hard hits, 0 soft hits** in 7 files (`longrun/d7rlv-logs/forbidden-scan.json`) |
| copied scaffold files modified | **0** (345 files sha256-checked vs `D7-hamilton-short-time`) |
| item 1 | `MetricFlowInterface`, `LlengthAlong`/`Llength`, `reducedLengthAlong`/`reducedLength`, `LPath`, `IsLMinimizer`, `ReducedLengthData` |
| item 2a | `ReducedVolumeCertificate.antitoneOn`, `volume_le_of_le`, `volume_le_at`, `volume_le_one`, `neg_log_monotoneOn`; finite and Gaussian-weight certificates |
| item 2b | `gaussian_LlengthAlong`, `gaussian_reducedLengthAlong`, `gaussian_length_le`, `gaussian_isLMinimizer`, `gaussianReducedLengthData_reducedLength` |
| item 3 | `LMinimizerExistence`, `JacobianComparison`, `ReducedVolumeMonotonicity`; `reducedVolumeDependencies` (10 entries); 3 named blockers |
| non-vacuity | Gaussian model proves `LMinimizerExistence`; constant-density certificate with weight `1` |

**Not claimed:** no manifold, no path space, no variational existence theorem for the general
interface, no `L`-geodesic differential inequality, no differentiation under the integral, no
`L`-exponential map or Jacobian comparison, no continuum reduced-volume integral, and no
Poincaré or Perelman content beyond the stated reduced-length / reduced-volume layer.

---

## 1. Scaffold, environment, source integrity

The worktree was empty. The prescribed hard-link scaffold was attempted first:

| command | exit | note |
| --- | --- | --- |
| `cp -al ../D7-hamilton-short-time/. .` | **1** | cross-worktree hard links rejected by the filesystem (`Invalid cross-device link`, `EXDEV`); only an empty directory skeleton was created |
| `cp -a ../D7-hamilton-short-time/. .` | **0** | fallback used; 345 files copied (0 hard links) |
| `.lake` / `release/.lake/packages` | — | copied as symlinks, pointing at the shared pinned mathlib prebuild |

**Deliverable-path adaptation.** The queued task spec (`manifest/next-20-tasks.json`) names
`Poincare/Longrun/RicciFlow/ReducedLength.lean` as the deliverable. The worktree instruction for
this run restricts new files to `Poincare/D7/Reduced/`, which was followed; the content is the
same reduced-length / reduced-volume layer, placed in the D7 package tree.

Integrity check (`.lake` and the new log/card directories excluded, symlinks skipped, sha256):

| comparison | files checked | changed | removed |
| --- | --- | --- | --- |
| worktree vs `D7-hamilton-short-time` | 345 | **0** | **0** |

Environment:

| key | value |
| --- | --- |
| Lean | `4.34.0-rc2` (commit `6a10ac8c22be`) |
| Lake | `5.0.0-src+6a10ac8` |
| mathlib | `7974e751bece493b6ff508039423ca9fa2452fa8` |
| `ELAN_HOME` | `/data3/guoshaoyang/workdir/lean_poincare/elan` |

New files (all under `release/Poincare/D7/Reduced/`):

| file | lines | declarations | role |
| --- | --- | --- | --- |
| `Basic.lean` | 264 | 22 | `MetricFlowInterface`, `L`-length, admissible paths, minimiser structure |
| `Certificate.lean` | 352 | 30 | reduced-volume certificates and their monotonicity consequences |
| `Statements.lean` | 188 | 15 | state-only `Prop`s, blockers, missing-dependency ledger |
| `Gaussian.lean` | 360 | 17 | Gaussian shrinking soliton model: explicit `L`-length, reduced length, minimality |
| `Probe.lean` | 107 | 0 | compilable API probe (80 `#check`s) |
| `Audit.lean` | 103 | 0 | 78 `#print axioms` commands |
| `All.lean` | 17 | 0 | umbrella module |

---

## 2. Item 1 — the `L`-length functional over a stated metric-flow interface

**`MetricFlowInterface E`** (`Poincare.D7.Reduced.MetricFlowInterface`) is the stated interface:
`E` is a real inner product space (the tangent-space model), `scalarCurvature : ℝ → E → ℝ` is
`R(τ, x)`, and `metric : ℝ → E → E → ℝ` is the metric `g(τ)`. All fields are explicit:

| field | type | meaning |
| --- | --- | --- |
| `scalarCurvature` | `ℝ → E → ℝ` | scalar curvature in backward time |
| `metric` | `ℝ → E → E → ℝ` | metric tensor |
| `metric_symm` | `∀ τ x y, metric τ x y = metric τ y x` | symmetry |
| `metric_self_nonneg` | `∀ τ x, 0 ≤ metric τ x x` | nonnegativity on the diagonal |
| `metric_add_left` | `∀ τ x y z, metric τ (x+y) z = metric τ x z + metric τ y z` | additivity |
| `metric_smul_left` | `∀ τ c x y, metric τ (c•x) y = c * metric τ x y` | homogeneity |

The **`L`-length** in backward time is defined with an explicit velocity field and with `deriv`:

```
LIntegrandAlong F γ γ' τ = √τ * (R(τ, γ τ) + g(τ)(γ' τ, γ' τ))
LlengthAlong F γ γ' τ₁ τ₂ = ∫_{τ₁}^{τ₂} LIntegrandAlong F γ γ' τ dτ
Llength F γ τ₁ τ₂       = ∫_{τ₁}^{τ₂} √τ * (R(τ, γ τ) + g(τ)(deriv γ τ, deriv γ τ)) dτ
```

with the agreement lemma `Llength_eq_LlengthAlong`, and the reduced lengths

```
reducedLengthAlong F γ γ' τ = (1/(2√τ)) * LlengthAlong F γ γ' 0 τ
reducedLength F γ τ         = (1/(2√τ)) * Llength F γ 0 τ
```

**Minimiser data is an explicit structure, not a hypothesis baked into the definitions.**
`LPath F p q τ` bundles an admissible curve: endpoints `γ 0 = p`, `γ τ = q`, continuity on
`[0, τ]`, differentiability on `(0, τ)` with the stated velocity, interval-integrability of the
energy density `√x g(x)(γ', γ')` and of every metric cross term `g(x)(c, γ')`. `LPath.length`
and `LPath.reducedLength` are its `L`-length and reduced length. `IsLMinimizer P` says
`P.length ≤ Q.length` for every admissible `Q`, and `ReducedLengthData F p q τ` packages a path
with a proof of `IsLMinimizer`. The nonnegativity lemmas
`LlengthAlong_nonneg`, `reducedLengthAlong_nonneg`, `LPath.length_nonneg`,
`LPath.reducedLength_nonneg` and `ReducedLengthData.reducedLength_nonneg` are proved from an
explicit nonnegative-curvature hypothesis.

---

## 3. Item 2a — algebraic monotonicity consequences of the reduced-volume certificate fields

### 3.1 The continuum certificate

`ReducedVolumeCertificate E` carries the volume functional `Ṽ`, its backward-time derivative,
and three analytic fields: `hasDerivAt_volume` (differentiation under the integral), 
`derivative_nonpos` (the reduced-length differential inequality plus nonnegativity of the weight)
and `volume_nonneg`. Its checked consequences are:

| declaration | statement |
| --- | --- |
| `ReducedVolumeCertificate.antitoneOn` | `AntitoneOn Ṽ (Ioi 0)` (mean-value theorem) |
| `ReducedVolumeCertificate.reducedVolume_antitone` | the same for the named `reducedVolume` functional |
| `ReducedVolumeCertificate.volume_le_of_le` | `0 < τ₁ → τ₁ ≤ τ₂ → Ṽ(τ₂) ≤ Ṽ(τ₁)` |
| `ReducedVolumeCertificate.volume_le_at` | comparison against a reference time `τ₀` |
| `ReducedVolumeCertificate.volume_le_one` | `1 ≤ τ → Ṽ(τ) ≤ Ṽ(1)` |
| `ReducedVolumeCertificate.neg_log_monotoneOn` | `Ṽ > 0` ⟹ `τ ↦ -log Ṽ(τ)` nondecreasing |

### 3.2 Finite densities and the Gaussian weights

`FiniteReducedVolumeCertificate ι` is a finite family of densities `ρᵢ` with explicit derivatives
and `ρᵢ' ≤ 0`; `FiniteReducedVolumeCertificate.volume_antitone` proves `∑ᵢ ρᵢ` nonincreasing via
`Finset.sum_le_sum` applied to the mean-value theorem for each density.

`ReducedLengthDensityCertificate ι` is the **Gaussian-weight certificate** with the actual
reduced-volume shape

```
density C τ i = exp(-(n/2) log(4πτ) - lᵢ(τ)),
```

whose field is the Perelman-type lower bound `lᵢ'(τ) ≥ -n/(2τ)`. The kernel-checked chain is:

| declaration | statement |
| --- | --- |
| `hasDerivAt_normalisation` | `d/dτ [-(n/2) log(4πτ)] = -(n/2)/τ` for `τ > 0` |
| `density_hasDerivAt` | `ρᵢ'(τ) = ρᵢ(τ) (-(n/2)/τ - lᵢ'(τ))` |
| `density_derivative_nonpos` | `lᵢ' ≥ -n/(2τ)` ⟹ `ρᵢ'(τ) ≤ 0` |
| `toFiniteCertificate` | the Gaussian weights packaged as a finite certificate |
| `volume_antitone`, `reducedVolume_antitone` | `τ ↦ ∑ᵢ ρᵢ(τ)` is nonincreasing on `Ioi 0` |
| `volume_le_of_le` | `0 < τ₁ → τ₁ ≤ τ₂ → ∑ᵢ ρᵢ(τ₂) ≤ ∑ᵢ ρᵢ(τ₁)` |

This is the exact algebraic mechanism by which the reduced-length differential inequality yields
reduced-volume monotonicity; the Laplacian, gradient and scalar-curvature terms of the continuum
inequality remain in the explicit certificate field.

---

## 4. Item 2b — explicit reduced length of the Gaussian shrinking soliton model

`gaussianFlow n` instantiates the interface on `EuclideanSpace ℝ (Fin n)` with zero scalar
curvature and the Euclidean metric. The `L`-geodesic from the origin to `q` and its velocity are

```
gaussianPath q τ σ     = (√σ / √τ) • q
gaussianVelocity q τ σ = (1 / (2 √τ √σ)) • q
```

The explicit computation is:

| declaration | statement |
| --- | --- |
| `integral_one_div_sqrt` | `∫_0^τ 1/√σ dσ = 2√τ` for `τ ≥ 0` (from `integral_rpow` with exponent `-1/2`) |
| `gaussian_integrand` | `√σ ⟪γ'(σ), γ'(σ)⟫ = ‖q‖² / (4 τ √σ)` for `σ > 0` |
| `gaussian_LlengthAlong` | `L(γ) = ∫_0^τ √σ |γ'(σ)|² dσ = ‖q‖² / (2√τ)` |
| `gaussian_reducedLengthAlong` | `l(q, τ) = L(γ)/(2√τ) = ‖q‖² / (4τ)` |
| `gaussianPath_hasDerivAt` | the geodesic has the stated velocity on `(0, τ)` |
| `intervalIntegrable_one_div_sqrt` | the `σ^{-1/2}` density is interval-integrable |
| `gaussianLPath` | the geodesic is an admissible `LPath` |
| `gaussian_length_le` | **minimality**: every admissible competitor `P` satisfies `‖q‖²/(2√τ) ≤ P.length` |
| `gaussian_isLMinimizer` | the geodesic is an `IsLMinimizer` |
| `gaussianReducedLengthData` | the packaged `ReducedLengthData` |
| `gaussianReducedLengthData_reducedLength` | its reduced length is `‖q‖²/(4τ)` |
| `gaussianLMinimizerExistence` | `LMinimizerExistence (gaussianFlow n) 0` — the state-only `Prop` is **proved** for the model |

The minimality proof is the completing-the-square identity

```
√σ ⟪γ'(σ), γ'(σ)⟫ - 2 ⟪c, γ'(σ)⟫ + ⟪c, c⟫/√σ = √σ ‖γ'(σ) - (1/√σ) c‖² ≥ 0,
c = q / (2√τ),
```

integrated over `[0, τ]`. The cross term integrates to `⟪c, q⟫` by the fundamental theorem of
calculus (`integral_eq_sub_of_hasDerivAt_of_le` on `σ ↦ ⟪c, P.curve σ⟫`), and the last term
integrates with `integral_one_div_sqrt`; the result is `P.length ≥ ‖q‖²/(2√τ)`. The pointwise
identity is available on `(0, τ]`; the `L`-integral only sees the interval, and the a.e.
nonnegativity is handled by `ae_restrict_iff'` together with the null set `{0}`.

---

## 5. Item 3 — state-only `Prop`s and the missing-dependency ledger

| `Prop` | content |
| --- | --- |
| `LMinimizerExistence F p` | `∀ q τ, 0 < τ → ∃ P : LPath F p q τ, IsLMinimizer P` |
| `JacobianComparison J` | `∀ τ x, 0 < τ → J.jacobian τ x ≤ J.comparison τ x` |
| `ReducedVolumeMonotonicity V` | `AntitoneOn V (Ioi 0)` — the program-ledger declaration `missingReducedVolumeMonotonicity` |

`JacobianComparisonInterface E` carries the underlying flow, the `L`-exponential Jacobian, the
comparison Jacobian and explicit nonnegativity/positivity fields; the intended instantiation (the
`L`-exponential map and the Gaussian comparison Jacobian) is not constructed. The certificate
layer proves `reducedVolumeMonotonicity_of_certificate` for a certified volume functional; the
general statement remains state-only because the certificate fields are not discharged.

**Missing dependencies** (`reducedVolumeDependencies : List MissingDependency`, 10 entries,
reusing the `MissingDependency` record of the accepted `D7-hamilton-short-time` layer;
`reducedVolumeDependencies_all_named` checks every entry has a nonempty name and reason):

1. `RLV-1 path space` — compactness/lower-semicontinuity for `L`-length minimisers;
2. `RLV-2 L-geodesic equation` — first variation and the `L`-geodesic ODE;
3. `RLV-3 minimiser regularity` — smoothness on `(0, τ]`, continuity at the base time;
4. `RLV-4 L-exponential map` — construction and differentiability;
5. `RLV-5 second variation and index form` — the `L`-index form and its nonnegativity;
6. `RLV-6 Jacobian comparison` — Perelman's Jacobian bound under a Ricci lower bound;
7. `RLV-7 reduced-length differential inequality` — the full
   `l_τ - Δl + |∇l|² - R + n/(2τ) ≥ 0`;
8. `RLV-8 differentiation under the integral` — dominated convergence for the reduced volume;
9. `RLV-9 manifold metric flow` — manifold metrics, Ricci tensor, covariant calculus (inherited
   blocker `Poincare.D7.Curvature`);
10. `RLV-10 Gaussian normalisation` — the continuum Gaussian integral.

Named blockers (nonempty, kernel-checked): `BlockerLMinimizerExistence`
(`B-D7-RLV-MINIMIZER`), `BlockerJacobianComparison` (`B-D7-RLV-JACOBIAN`) and
`BlockerReducedVolumeMonotonicity` (`B-D7-RLV-MONOTONICITY`).

---

## 6. Item 4 — no forbidden tokens

Comment/string-aware scan of all 7 authored files for `sorry`, `axiom`, `unsafe`,
`native_decide`, `proof_wanted`, `sorryAx`, `admit` (hard) and `implemented_by`, `extern`
(soft): **0 hard hits, 0 soft hits** (`longrun/d7rlv-logs/forbidden-scan.json`). All unproved
content is a `def ... : Prop` / `structure` / `def ... : String`, never an axiom.

The 78-entry `#print axioms` audit (`Reduced/Audit.lean`) reports the cones

| cone | count |
| --- | --- |
| `{propext, Classical.choice, Quot.sound}` | 72 |
| `{}` (blockers, dependency ledger, its length) | 5 |
| `{propext}` | 1 |
| any other | **0** |

No `sorryAx`, no `Lean.ofReduceBool`, no `Lean.trustCompiler`, no project axiom.

---

## 7. Verification transcript

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-reduced-length-volume
bash longrun/d7rlv-logs/run_verification.sh   # per-file compiles + scan + axiom summary + build
```

| command | exit |
| --- | --- |
| `lake env lean release/Poincare/D7/Reduced/Basic.lean` | 0 |
| `lake env lean release/Poincare/D7/Reduced/Certificate.lean` | 0 |
| `lake env lean release/Poincare/D7/Reduced/Statements.lean` | 0 |
| `lake env lean release/Poincare/D7/Reduced/Gaussian.lean` | 0 |
| `lake env lean release/Poincare/D7/Reduced/Probe.lean` | 0 |
| `lake env lean release/Poincare/D7/Reduced/Audit.lean` | 0 |
| `lake env lean release/Poincare/D7/Reduced/All.lean` | 0 |
| `cd release && lake build` | 0 (8981 jobs) |

Headline declarations and their cones (all `{propext, Classical.choice, Quot.sound}` unless
noted):

| declaration | axioms |
| --- | --- |
| `MetricFlowInterface.LlengthAlong` | `{propext, Classical.choice, Quot.sound}` |
| `MetricFlowInterface.reducedLengthAlong` | `{propext, Classical.choice, Quot.sound}` |
| `LPath.length` | `{propext, Classical.choice, Quot.sound}` |
| `IsLMinimizer` | `{propext, Classical.choice, Quot.sound}` |
| `ReducedVolumeCertificate.antitoneOn` | `{propext, Classical.choice, Quot.sound}` |
| `FiniteReducedVolumeCertificate.volume_antitone` | `{propext, Classical.choice, Quot.sound}` |
| `ReducedLengthDensityCertificate.density_derivative_nonpos` | `{propext, Classical.choice, Quot.sound}` |
| `ReducedLengthDensityCertificate.volume_antitone` | `{propext, Classical.choice, Quot.sound}` |
| `integral_one_div_sqrt` | `{propext, Classical.choice, Quot.sound}` |
| `gaussian_integrand` | `{propext, Classical.choice, Quot.sound}` |
| `gaussian_LlengthAlong` | `{propext, Classical.choice, Quot.sound}` |
| `gaussian_reducedLengthAlong` | `{propext, Classical.choice, Quot.sound}` |
| `gaussian_length_le` | `{propext, Classical.choice, Quot.sound}` |
| `gaussian_isLMinimizer` | `{propext, Classical.choice, Quot.sound}` |
| `gaussianReducedLengthData_reducedLength` | `{propext, Classical.choice, Quot.sound}` |
| `gaussianLMinimizerExistence` | `{propext, Classical.choice, Quot.sound}` |
| `LMinimizerExistence` | `{propext, Classical.choice, Quot.sound}` |
| `JacobianComparison` | `{propext, Classical.choice, Quot.sound}` |
| `reducedVolumeDependencies` | `{}` |
| `reducedVolumeDependencies_length` | `{}` |
| `BlockerLMinimizerExistence` | `{}` |

Artifacts:

| artifact | path |
| --- | --- |
| verification script | `longrun/d7rlv-logs/run_verification.sh` |
| per-file exit codes | `longrun/d7rlv-logs/exit_codes.txt` |
| per-file compile logs | `longrun/d7rlv-logs/lean_release_Poincare_D7_Reduced_*.log` |
| `#print axioms` output | `longrun/d7rlv-logs/lean_release_Poincare_D7_Reduced_Audit.lean.log` |
| axiom summary | `longrun/d7rlv-logs/axioms.json` |
| forbidden-token scan | `longrun/d7rlv-logs/forbidden-scan.json` |
| full package build exit | `longrun/d7rlv-logs/lake_build_exit.txt`, `lake_build.log` |

---

## 8. Non-vacuity witnesses

* **Gaussian minimiser.** `gaussianLMinimizerExistence` proves `LMinimizerExistence` for the
  Gaussian model; `gaussian_length_le` is a genuine lower bound over all admissible paths.
* **Explicit reduced length.** `gaussianReducedLengthData_reducedLength` evaluates the packaged
  reduced length to `‖q‖²/(4τ)`; for `n = 0` (or `q = 0`) this is `0`, and for `q ≠ 0` it is
  positive.
* **Constant-zero certificate.** `zeroReducedLengthDensityCertificate ι n hn` with `lᵢ ≡ 0` is a
  `ReducedLengthDensityCertificate` for `n ≥ 0`; its volume is nonincreasing.
* **Critical certificate.** `criticalReducedLengthDensityCertificate ι n` with
  `lᵢ(τ) = -(n/2) log(4πτ)` has `lᵢ' = -n/(2τ)` (the lower bound is attained) and
  `criticalReducedLengthDensityCertificate_density` proves its Gaussian weight is exactly `1`;
  `criticalReducedLengthDensityCertificate_volume` proves its finite volume is the cardinality of
  the index type, hence constant and nonincreasing.

---

## 9. Honest boundary

* The model is **finite-dimensional and pointwise**: `E` plays the role of a tangent space and the
  metric and scalar curvature are abstract data. No manifold, tangent bundle, path space or
  Ricci-flow PDE is constructed.
* **General minimiser existence is state-only.** It is proved only for the finite-dimensional
  Gaussian model. The general case needs the path-space compactness or convexity input
  (`RLV-1`).
* **Jacobian comparison is state-only.** The `L`-exponential map and its Jacobian are not
  constructed; `JacobianComparison` is a `Prop` over an explicit interface (`RLV-4`, `RLV-5`,
  `RLV-6`).
* **Reduced-volume monotonicity is conditional on the certificate fields.** The layer proves the
  order-algebraic consequences of the derivative sign and of the bound `l' ≥ -n/(2τ)`; it does
  not prove the continuum differential inequality, differentiation under the integral, or the
  existence of the minimiser that makes `l` differentiable (`RLV-2`, `RLV-7`, `RLV-8`).
* **The reduced volume is a finite sum**, not the continuum integral
  `∫ (4πτ)^{-n/2} e^{-l} dV`; the Gaussian normalisation integral is listed as `RLV-10`.
* No Ricci-flow existence, no entropy monotonicity, no κ-noncollapsing, no surgery and no
  Poincaré content is claimed.

**Last line:** TASK_DONE — card: `longrun/results/D7-reduced-length-volume.md`
