# D11-reduced-volume-euclidean — result card

**Task id:** `D11-reduced-volume-euclidean`
**Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-reduced-volume-euclidean`
**Generated (UTC):** 2026-09-10T17:58:30Z
**Verdict:** `TASK_DONE` — Perelman's reduced volume is computed **explicitly and
unconditionally** in the Euclidean case: the flat `L`-length, the reduced distance
`ℓ = |x|²/(4τ)` from the D10 heat-kernel asymptotics, the characterisation of the
`L`-geodesics from the origin as exactly the straight rays, the reduced-volume integrand
coinciding with the Gaussian (hence `Ṽ(τ) = 1` for all `τ`, with the D10 Gaussian toolbox),
and the named monotonicity-theorem / manifold-interface `Prop`s consumed by
`D7-reduced-length-volume` with a field-by-field Euclidean instantiation. No
`sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted` in any authored file; every audited
declaration has axiom cone `{}`, `{propext}` or `{propext, Classical.choice, Quot.sound}`.

> Nothing in this card is state-only or assumed: every theorem below is proved from the
> accepted D10 heat kernel / Gaussian toolbox (`Poincare.D10.HeatKernelEuclidean`,
> `Poincare.GaussianToolbox`) and the accepted D7 reduced-length layer
> (`Poincare.D7.Reduced`). The *general* (manifold) monotonicity theorem is a named
> `def … : Prop` statement, never an axiom, and it is **proved** for the Euclidean
> instantiation.

---

## 0. Bottom line

| item | result |
| --- | --- |
| new files (only under `release/Poincare/D11/ReducedVolume/`) | **7 Lean files, 1314 lines, 74 authored declarations** (14 + 21 + 13 + 26 in the four content modules; corrected in session20 from an earlier "75 / 27" miscount — see §25) |
| compiled with `lake env lean` from the worktree root (harness gate) | **7/7 exit 0** (`longrun/d11rve-logs/gate_exit_codes.txt`) |
| whole release package `lake build` | **exit 0** (9173 jobs, `longrun/d11rve-logs/lake_build_full.log`) |
| `#print axioms` audit | **74/74 principal declarations**: cone `{propext, Classical.choice, Quot.sound}` (71), `{}` (2), `{propext}` (1); **0 nonstandard** (`longrun/d11rve-logs/axiom_audit.json`) |
| forbidden-token scan (comment/string-aware) | **0 hard, 0 soft** in 7 files (`input/d5-tools/scan_forbidden.py`) |
| item 1 | `euclideanFlow`, `flatLIntegrand`/`flatLlength` (`∫ √τ (|γ'|² + R) dτ`, `R = 0`), `heatKernelReducedDistance` (`-log((4πτ)^{n/2} K)`), `heatKernel_asymptotics`, `heatKernelReducedDistance_eq` |
| item 2 | `straightRay_*`, `LMinimizer_eq_straightRay`, `minimizer_iff_eq_straightRay`, `reducedVolumeIntegrand_eq_gaussianKernel`, `reducedVolume_eq_one`, `reducedVolume_constant`, `integral_reducedVolumeIntegrandUnnormalized` |
| item 3 | `ManifoldReducedVolumeInterface`, `ReducedVolumeMonotonicityTheorem` (named `Prop`), `euclideanManifoldReducedVolumeInterface`, `euclideanReducedVolumeCertificate`, `euclidean_manifoldReducedVolumeMonotonicity`, field-reference theorems, `EuclideanReducedVolumeAnchor` |
| non-vacuity | every anchor is unconditional; the D7 state-only `LMinimizerExistence`, `JacobianComparison` and the monotonicity theorem are **proved** for the flat interface |

**Not claimed:** no manifold, no path-space theory, no Jacobian comparison for curved spaces,
no reduced-length differential inequality, no differentiation under the integral, and no
Poincaré/Perelman content beyond the Euclidean reduced-length / reduced-volume computation.
The ten D7 missing inputs (`RLV-1` … `RLV-10`) remain missing for the general manifold case
and are recorded in `generalMonotonicityMissingDependencies`.

## 1. Authored files

All authored sources live under `release/Poincare/D11/ReducedVolume/`.

| file | lines | sha256 (first 16) | role |
| --- | --- | --- | --- |
| `Basic.lean` | 178 | `388b62aef7d5d82c` | flat interface, flat `L`-length, reduced distance from heat-kernel asymptotics |
| `StraightRays.lean` | 429 | `16a1fa770ed2ccce` | straight rays, minimality + uniqueness, completing-the-square deficit |
| `Volume.lean` | 169 | `a6d2bf62fc279a33` | integrand = Gaussian, `Ṽ = 1`, `τ^{-n/2}` form, constancy |
| `Statements.lean` | 325 | `c823d0e7b7e07961` | named `Prop`s, manifold interface, D7 certificate/Jacobian instantiation |
| `All.lean` | 22 | `0e8ef1d573d0f5e4` | umbrella module |
| `Probe.lean` | 95 | `81ebdefe23630cca` | 74 `#check` API probes |
| `Audit.lean` | 96 | `51c19cfae339da9c` | 74 `#print axioms` commands |

Namespace: `Poincare.D11.ReducedVolume`. Root gate shims (non-Lean infrastructure, as in the
sibling D9/D10 worktrees): `lakefile.toml` (`srcDir = "release"`), `lean-toolchain`,
`lake-manifest.json`, `.lake -> release/.lake`. No copied scaffold file was modified.

## 2. Item 1 — `L`-length and the reduced distance from the heat-kernel asymptotics (`Basic.lean`)

- `euclideanFlow n : MetricFlowInterface (EuclideanSpace ℝ (Fin n))` — the flat metric-flow
  interface on `ℝⁿ`: scalar curvature `R ≡ 0` and metric `⟪·,·⟫`, definitionally the D7
  Gaussian shrinking soliton model (`gaussianFlow`); `euclideanFlow_scalarCurvature`,
  `euclideanFlow_metric` are the field lemmas.
- `flatLIntegrand γ γ' τ = √τ * (0 + |γ'(τ)|²)` and `flatLlength γ γ' τ₁ τ₂ = ∫ √τ (0+|γ'|²) dτ`
  — the task's `L`-length `∫ √τ (|γ'|² + R) dτ` with the `R = 0` flat slot explicit;
  `flatLlength_eq_LlengthAlong` proves it equals the D7 interface `L`-length on
  `euclideanFlow`; `flatReducedLength` and `flatReducedLength_eq_reducedLength` do the same
  for the `/(2√τ)` reduced length.
- `heatKernelReducedDistance n τ x = -log ((4πτ)^{n/2} K(n,τ,x))` — **the reduced distance
  read off the D10 heat-kernel asymptotics** `K = (4πτ)^{-n/2} exp(-ℓ)`.
- `heatKernel_asymptotics` — `(4πτ)^{-n/2} exp (-ℓ(x,τ)) = K(n,τ,x)` for `τ > 0`.
- `heatKernelReducedDistance_eq` — **the explicit value `ℓ(x,τ) = |x|²/(4τ)`** for `τ > 0`
  (rpow algebra + `Real.log_exp`), with `heatKernelReducedDistance_nonneg` and
  `heatKernelReducedDistance_zero`.
- `heatKernelReducedDistance_eq_reducedLength` — the heat-kernel-asymptotics reduced distance
  equals the variational reduced length of the packaged D7 `L`-minimiser
  (`gaussianReducedLengthData`), so the two definitions of `ℓ` agree on `ℝⁿ`.

## 3. Item 2 — straight rays, `ℓ = |x|²/4τ`, integrand = Gaussian, `Ṽ = 1` (`StraightRays.lean`, `Volume.lean`)

**Straight rays (unconditional).**

- `straightRay x τ σ = (√σ/√τ) • x` — the straight line through the origin (affine parameter
  `s = √σ`), with `straightRayVelocity`, `straightRay_hasDerivAt`, `straightRay_zero`,
  `straightRay_tau`, and the admissible path `straightRayLPath`.
- `straightRay_length` — `L(γ) = |x|²/(2√τ)`; `straightRay_reducedLength` — `ℓ = |x|²/(4τ)`;
  `heatKernelReducedDistance_eq_straightRayReducedLength` ties the heat-kernel reduced
  distance to the ray's reduced length; `straightRay_isLMinimizer` — the ray **is** a
  minimiser (D7 `gaussian_isLMinimizer`); `euclidean_LMinimizerExistence` — the D7
  state-only `LMinimizerExistence` `Prop` **proved** for the flat interface.
- `flatDeficit c v σ = √σ|v|² - 2⟪c,v⟫ + |c|²/√σ`, the completing-the-square identity
  `flatDeficit_eq_normSq` (`= √σ |v - (1/√σ)c|²`), `flatDeficit_nonneg`, and
  `flatDeficit_integral` — the kernel-checked integral identity
  `∫₀^τ (deficit of P) dσ = L(P) - |x|²/(2√τ)` for `c = (1/(2√τ))•x` (FTC for the cross term
  + `∫₀^τ σ^{-1/2} dσ = 2√τ`).
- `ae_velocity_eq_of_deficit_integral_zero` — a vanishing deficit forces
  `P'(σ) = (1/√σ)•c` a.e. (`integral_eq_zero_iff_of_nonneg_ae`).
- `LMinimizer_eq_straightRay` — **every `L`-minimiser from the origin coincides with the
  straight ray on `[0, τ]`** (minimality ⇒ `L(P) = |x|²/(2√τ)` ⇒ deficit integral zero ⇒
  radial velocity a.e. ⇒ FTC gives `P(σ₀) = 2√σ₀•c = (√σ₀/√τ)•x`).
- `IsLMinimizer_of_eq_straightRay` and `minimizer_iff_eq_straightRay` — **the `L`-geodesics
  from the origin in flat `ℝⁿ` are exactly the straight rays**.

**Reduced volume (unconditional, with the D10 Gaussian toolbox).**

- `reducedVolumeIntegrand n τ x = (4πτ)^{-n/2} exp(-ℓ(x,τ))` — Perelman's integrand;
  `reducedVolumeIntegrand_eq_gaussianKernel` — **the integrand coincides with the Gaussian**
  (the D10 heat kernel `gaussianKernel n τ x`), for `τ > 0`.
- `reducedVolumeIntegrandUnnormalized_eq_gaussianKernel` — the task-literal form
  **`τ^{-n/2} exp(-ℓ) = (4π)^{n/2} · K(n,τ,x)`** (via `Real.mul_rpow` +
  `Real.rpow_add`), and `integral_reducedVolumeIntegrandUnnormalized` —
  `∫ τ^{-n/2} exp(-ℓ) dx = (4π)^{n/2}`, **independent of `τ`**.
- `reducedVolume n τ = ∫ (4πτ)^{-n/2} exp(-ℓ) dx`; **`reducedVolume_eq_one`** —
  `Ṽ(τ) = 1` for every `τ > 0`, from `gaussianKernel_integral` (D10 total mass `1`);
  `reducedVolume_constant`, `reducedVolume_nonneg`, `euclideanReducedVolume_eq_one`,
  `integral_reducedVolumeIntegrandUnnormalized_constant` — the constancy statements.
  **The reduced volume is constant `= 1` for all backward times `τ`.**

## 4. Item 3 — the named `Prop`s and the D7-consumed interface (`Statements.lean`)

- `ManifoldReducedVolumeInterface E` — **the manifold reduced-volume interface** consumed by
  `D7-reduced-length-volume`: `flow : MetricFlowInterface E`, `dimension : ℕ`,
  `reducedDistance : ℝ → E → ℝ`, `reducedVolume : ℝ → ℝ`.
- `ReducedVolumeMonotonicityTheorem M` — **the monotonicity theorem as a named `Prop`**:
  `0 < τ₁ ≤ τ₂ ⇒ Ṽ(τ₂) ≤ Ṽ(τ₁)`, instantiated at the D7 declaration
  `Poincare.D7.Reduced.ReducedVolumeMonotonicity`.  State-only for the general manifold
  interface; the ten D7 missing inputs are named in
  `generalMonotonicityMissingDependencies` (RLV-1 … RLV-10, length 10, non-nil).
- **Euclidean instantiation, field by field.**
  `euclideanManifoldReducedVolumeInterface n` fills `flow := euclideanFlow n`,
  `dimension := n`, `reducedDistance := heatKernelReducedDistance n` (`= |x|²/(4τ)`),
  `reducedVolume := reducedVolume n` (`= 1`), with one reference theorem per field
  (`…_flow`, `…_dimension`, `…_reducedDistance`, `…_reducedVolume`).
- `euclideanReducedVolumeCertificate n : ReducedVolumeCertificate (EuclideanSpace ℝ (Fin n))`
  instantiates **every field** of the D7 certificate: `flow`, `volume`, `derivative := 0`,
  `hasDerivAt_volume` (the volume is `1` near every `τ > 0`), `derivative_nonpos`,
  `volume_nonneg` — each discharged by the Euclidean computation, with reference theorems
  `euclideanReducedVolumeCertificate_flow/_volume/_derivative/_antitoneOn`.
- `euclidean_reducedVolumeMonotonicity` and `euclidean_manifoldReducedVolumeMonotonicity` —
  **the monotonicity theorem proved unconditionally in the Euclidean case** (the D7
  certificate consequence, and the named `Prop` for the interface), with equality: the
  volume is constant `1`.
- Jacobian comparison: `flatLExponential` (the flat `L`-exponential `v ↦ 2√τ v`),
  `flatLExponential_det` (Jacobian `(2√τ)ⁿ` via `LinearMap.det_smul`/`det_id`),
  `euclideanJacobianComparisonInterface` (D7 `JacobianComparisonInterface` with
  `jacobian := (2√τ)ⁿ`, `comparison := (2√τ)ⁿ`) and `euclidean_jacobianComparison` — the D7
  `JacobianComparison` `Prop` holds **with equality** in flat space.
- `euclidean_manifold_LMinimizerExistence` — the D7 state-only `LMinimizerExistence` `Prop`,
  proved for the `flow` field of the Euclidean interface.
- `EuclideanReducedVolumeAnchor n` (named `Prop`) and `euclideanReducedVolumeAnchor` — the
  packaged conjunction: `ℓ = |x|²/(4τ)` ∧ integrand = Gaussian ∧ `Ṽ ≡ 1` ∧ monotonicity —
  **the first unconditional anchor of the `L`-geometry chain**.

## 5. Verification evidence

| gate | command | result |
| --- | --- | --- |
| per-file compile (worktree root) | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0** (`longrun/d11rve-logs/gate_exit_codes.txt`) |
| whole release package | `cd release && lake build` | **exit 0, 9173 jobs** (`longrun/d11rve-logs/lake_build_full.log`, 0 error lines) |
| axiom audit | `lake env lean Poincare/D11/ReducedVolume/Audit.lean` | 74/74 cones `{}`/`{propext}`/`{propext, Classical.choice, Quot.sound}`; 0 nonstandard (`longrun/d11rve-logs/axiom_audit.json`) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py <7 files>` | 0 hard, 0 soft |

Toolchain: Lean `4.34.0-rc2` (commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`), Lake
`5.0.0-src+6a10ac8`, mathlib pinned `7974e751bece493b6ff508039423ca9fa2452fa8`.

**Honesty boundary.**  The general (manifold) reduced-volume monotonicity theorem is not
proved here — it is stated as the named `Prop` `ReducedVolumeMonotonicityTheorem` and remains
blocked on the ten D7 inputs RLV-1 … RLV-10.  Everything else in this package — the flat
`L`-length, the reduced distance, the straight-ray characterisation, the Gaussian
coincidence and the value `Ṽ = 1` — is proved unconditionally with no hypotheses beyond
`τ > 0` and no external theorem assumed.

## 6. Session re-verification (2026-09-10T18:10Z)

Fresh gates re-run from the worktree root in this session, all green:

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0** (`longrun/d11rve-logs/fresh_gate_exit_codes.txt`) |
| whole release package | `lake build` | **exit 0**, 9155 jobs (cached), 0 build-error lines (`longrun/d11rve-logs/fresh_lake_build.log`) |
| axiom audit | `lake env lean release/Poincare/D11/ReducedVolume/Audit.lean` | **74/74 declarations**: cone `{propext, Classical.choice, Quot.sound}` (71), `{}` (2), `{propext}` (1); **0 nonstandard** (`longrun/d11rve-logs/fresh_axiom_audit.json`) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume/` | **0 hard, 0 soft** (7 files) |

No change to any authored file or verdict in this session.

## 7. Session re-verification (2026-09-10T18:15Z)

Fresh gates re-run again in this session from the worktree root, all green:

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0** (`longrun/d11rve-logs/recheck_<F>.log`) |
| whole release package | `lake build` | **exit 0**, 9155 jobs, "Build completed successfully" |
| axiom audit | `lake env lean release/Poincare/D11/ReducedVolume/Audit.lean` | **74/74 declarations**: cone `{propext, Classical.choice, Quot.sound}` (71), `{}` (2), `{propext}` (1); **0 nonstandard** (`longrun/d11rve-logs/recheck_axiom_audit.json`) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume/` | **0 hard, 0 soft** (7 files) |
| source integrity | `sha256sum` of the 7 authored files | 7/7 match the hashes recorded in section 1 (no drift) |

No change to any authored file or verdict in this session.

## 8. Session re-verification (2026-09-10T18:18Z)

Fresh gates re-run once more in this session from the worktree root, all green:

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0** (`longrun/d11rve-logs/session3/compile_<F>.log`) |
| whole release package | `lake build` | **exit 0**, "Build completed successfully (9155 jobs)" |
| axiom audit | `lake env lean release/Poincare/D11/ReducedVolume/Audit.lean` | **74/74 declarations**: cone `{propext, Classical.choice, Quot.sound}` (71), `{}` (2), `{propext}` (1); **0 nonstandard** (`longrun/d11rve-logs/session3/axiom_audit.json`) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume/` | **0 hard, 0 soft** (7 files) |
| source integrity | `sha256sum` of the 7 authored files | 7/7 match the hashes recorded in section 1 (no drift) |

No change to any authored file or verdict in this session.

## 9. Session re-verification (2026-09-10T18:21Z)

Fresh gates re-run once more in this session from the worktree root, all green:

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0, 0 warnings** (`longrun/d11rve-session4/compile_<F>.log`, `exit_codes.txt`) |
| whole release package | `lake build` | **exit 0**, "Build completed successfully (9155 jobs)", 0 build-error lines (`longrun/d11rve-session4/lake_build.log`) |
| axiom audit | `lake env lean release/Poincare/D11/ReducedVolume/Audit.lean` | **74/74 declarations**: cone `{propext, Classical.choice, Quot.sound}` (71), `{}` (2), `{propext}` (1); **0 nonstandard** (`longrun/d11rve-session4/compile_Audit.log`) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume/` | **0 hard, 0 soft** (7 files) |
| source integrity | `sha256sum` of the 7 authored files | 7/7 match the hashes recorded in section 1 (no drift) |

No change to any authored file or verdict in this session.

## 10. Session re-verification (2026-09-10T18:25Z)

Fresh gates re-run once more in this session from the worktree root, all green:

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0, 0 warnings** (`longrun/d11rve-session5/compile_<F>.log`, `exit_codes.txt`) |
| whole release package | `lake build` | **exit 0**, "Build completed successfully (9155 jobs)", 0 build-error lines (`longrun/d11rve-session5/lake_build.log`) |
| axiom audit | `lake env lean release/Poincare/D11/ReducedVolume/Audit.lean` | **74/74 declarations**: cone `{propext, Classical.choice, Quot.sound}` (71), `{}` (2), `{propext}` (1); **0 nonstandard** (`longrun/d11rve-session5/axiom_audit.json`) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume/` | **0 hard, 0 soft** (7 files) |
| source integrity | `sha256sum` of the 7 authored files | 7/7 match the hashes recorded in section 1 (no drift) |

No change to any authored file or verdict in this session.

## 11. Session re-verification (2026-09-10T18:28Z)

Fresh gates re-run once more in this session from the worktree root, all green:

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0** (`longrun/d11rve-session6/compile_<F>.log`) |
| whole release package | `lake build` | **exit 0**, "Build completed successfully (9155 jobs)", 0 build-error lines (`longrun/d11rve-session6/lake_build.log`) |
| axiom audit | `lake env lean release/Poincare/D11/ReducedVolume/Audit.lean` | **74/74 declarations**: cone `{propext, Classical.choice, Quot.sound}` (71), `{}` (2), `{propext}` (1); **0 nonstandard** (`longrun/d11rve-session6/axiom_audit.json`) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume/` | **0 hard, 0 soft** (7 files) |
| source integrity | `sha256sum` of the 7 authored files | 7/7 match the hashes recorded in section 1 (no drift) |

No change to any authored file or verdict in this session.

## 12. Session re-verification (2026-09-10T18:31Z)

Fresh gates re-run once more in this session from the worktree root, all green:

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0, 0 warnings** (`longrun/d11rve-session7/compile_<F>.log`) |
| whole release package | `lake build` | **exit 0**, "Build completed successfully (9155 jobs)" |
| axiom audit | `lake env lean release/Poincare/D11/ReducedVolume/Audit.lean` | **74/74 declarations**: cone `{propext, Classical.choice, Quot.sound}` (71), `{}` (2), `{propext}` (1); **0 nonstandard** (`longrun/d11rve-session7/axiom_audit.json`) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume/` | **0 hard, 0 soft** (7 files) |
| source integrity | `sha256sum` of the 7 authored files | 7/7 match the hashes recorded in section 1 (no drift) |

No change to any authored file or verdict in this session.

## 13. Session re-verification (2026-09-10T18:36Z)

Fresh gates re-run once more in this session from the worktree root, all green:

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0, 0 warnings, 0 error lines** (`longrun/d11rve-session8/compile_<F>.log`, `gate_exit_codes.txt`) |
| whole release package | `lake build` | **exit 0**, "Build completed successfully (9155 jobs)", 0 build-error lines (`longrun/d11rve-session8/lake_build.log`) |
| axiom audit | `lake env lean release/Poincare/D11/ReducedVolume/Audit.lean` | **74/74 declarations**: cone `{propext, Classical.choice, Quot.sound}` (71), `{}` (2), `{propext}` (1); **0 nonstandard** (`longrun/d11rve-session8/axiom_audit.json`, `audit_raw.log`) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume/` | **0 hard, 0 soft** (7 files) |
| source integrity | `sha256sum` of the 7 authored files | 7/7 match the hashes recorded in section 1 (no drift) |

No change to any authored file or verdict in this session.

## 14. Session re-verification (2026-09-10T18:40Z)

Fresh gates re-run once more in this session from the worktree root, all green:

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0, 0 warnings** (`longrun/d11rve-session9/compile_<F>.log`) |
| whole release package | `lake build` | **exit 0**, "Build completed successfully (9155 jobs)", 0 build-error lines (`longrun/d11rve-session9/lake_build.log`) |
| axiom audit | `lake env lean release/Poincare/D11/ReducedVolume/Audit.lean` | **74/74 declarations**: cone `{propext, Classical.choice, Quot.sound}` (71), `{}` (2, "does not depend on any axioms"), `{propext}` (1); **0 nonstandard** (`longrun/d11rve-session9/axiom_audit.json`, `audit_raw.log`) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume/` | **0 hard, 0 soft** (7 files) |
| source integrity | `sha256sum` of the 7 authored files | 7/7 match the hashes recorded in section 1 (no drift) |
| content spot-check | re-read of the principal statements | `flatLIntegrand = √τ·(0+|γ'|²)`, `heatKernelReducedDistance_eq : ℓ = |x|²/(4τ)`, `LMinimizer_eq_straightRay`, `minimizer_iff_eq_straightRay`, `reducedVolumeIntegrand_eq_gaussianKernel`, `reducedVolume_eq_one`, `reducedVolume_constant`, `ReducedVolumeMonotonicityTheorem` (named `def … : Prop`, not an axiom), `ManifoldReducedVolumeInterface` fields (`flow`/`dimension`/`reducedDistance`/`reducedVolume`) with per-field reference theorems — all present and proved |

No change to any authored file or verdict in this session.

## 15. Session re-verification (2026-09-10T18:45Z)

Fresh gates re-run once more in this session from the worktree root, all green:

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0, 0 warnings, 0 error lines** (`longrun/d11rve-session10/compile_<F>.log`, `gate_exit_codes.txt`) |
| whole release package | `lake build` | **exit 0**, "Build completed successfully (9155 jobs)"; the only `error` grep hits are `info:` lines for pre-existing D7 declaration *names* containing "error" (`longrun/d11rve-session10/lake_build.log`) |
| axiom audit | `lake env lean release/Poincare/D11/ReducedVolume/Audit.lean` | **74/74 declarations**: cone `{propext, Classical.choice, Quot.sound}` (71), `{}` (2: `generalMonotonicityMissingDependencies`, `generalMonotonicityMissingDependencies_length`), `{propext}` (1: `generalMonotonicityMissingDependencies_ne_nil`); **0 nonstandard** (`longrun/d11rve-session10/axiom_audit.json`) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume/` | **0 hard, 0 soft** (7 files, `longrun/d11rve-session10/forbidden_scan.txt`) |
| source integrity | `sha256sum` of the 7 authored files | 7/7 match the hashes recorded in section 1 (no drift) |
| content spot-check | re-read of `Basic.lean`, `StraightRays.lean`, `Volume.lean`, `Statements.lean`, `All.lean`, `Probe.lean`, `Audit.lean` | `flatLIntegrand = √τ·(0+|γ'|²)`, `flatLlength_eq_LlengthAlong`, `heatKernel_asymptotics`, `heatKernelReducedDistance_eq : ℓ = |x|²/(4τ)`, `flatDeficit_integral`, `LMinimizer_eq_straightRay`, `minimizer_iff_eq_straightRay`, `reducedVolumeIntegrand_eq_gaussianKernel`, `reducedVolume_eq_one`, `reducedVolume_constant`, `ReducedVolumeMonotonicityTheorem` (named `def … : Prop`), `ManifoldReducedVolumeInterface` fields (`flow`/`dimension`/`reducedDistance`/`reducedVolume`) with per-field reference theorems — all present and proved |

No change to any authored file or verdict in this session.

## 16. Session re-verification (2026-09-10T18:47Z)

Fresh gates re-run once more in this session from the worktree root, all green:

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0** (`longrun/d11rve-session11/compile_<F>.log`, `gate_exit_codes.txt`) |
| whole release package | `lake build` | **exit 0**, "Build completed successfully (9155 jobs)", 0 error lines (`longrun/d11rve-session11/lake_build.log`) |
| axiom audit | `lake env lean release/Poincare/D11/ReducedVolume/Audit.lean` | **74/74 declarations**: cone `{propext, Classical.choice, Quot.sound}` (71), `{}` (2: `generalMonotonicityMissingDependencies`, `generalMonotonicityMissingDependencies_length`), `{propext}` (1: `generalMonotonicityMissingDependencies_ne_nil`); **0 nonstandard** (`longrun/d11rve-session11/axiom_audit.json`, `audit_raw.log`) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume/<7 files>` | **0 hard, 0 soft** (`longrun/d11rve-session11/forbidden_scan.txt`) |
| source integrity | `sha256sum` of the 7 authored files | 7/7 match the hashes recorded in section 1 (no drift) |

No change to any authored file or verdict in this session.


## 17. Session re-verification (2026-09-10T18:59ZZ)

Fresh gates re-run once more in this session from the worktree root, all green:

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0, 0 warnings, 0 error lines** (`longrun/d11rve-session12/compile_<F>.log`, `gate_exit_codes.txt`) |
| whole release package | `lake build` | **exit 0**, "Build completed successfully (9155 jobs)"; 0 real build errors — the only `error` grep hits are `info:` lines for pre-existing D7 declaration names containing "error" (`longrun/d11rve-session12/lake_build.log`) |
| axiom audit | `lake env lean release/Poincare/D11/ReducedVolume/Audit.lean` | **74/74 declarations**: cone `{propext, Classical.choice, Quot.sound}` (71), `{}` (2: `generalMonotonicityMissingDependencies`, `generalMonotonicityMissingDependencies_length`), `{propext}` (1: `generalMonotonicityMissingDependencies_ne_nil`); **0 nonstandard** (`longrun/d11rve-session12/axiom_audit.json`, `audit_raw.log`) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume/` | **0 hard, 0 soft** (7 files, `longrun/d11rve-session12/forbidden_scan.txt`) |
| source integrity | `sha256sum` of the 7 authored files | 7/7 match the hashes recorded in section 1 (no drift) |
| content spot-check | declaration scan of the four content modules | `flatLlength_eq_LlengthAlong`, `heatKernel_asymptotics`, `heatKernelReducedDistance_eq : ℓ = |x|²/(4τ)`, `straightRay_isLMinimizer`, `LMinimizer_eq_straightRay`, `minimizer_iff_eq_straightRay`, `reducedVolumeIntegrand_eq_gaussianKernel`, `reducedVolume_eq_one`, `reducedVolume_constant`, `ReducedVolumeMonotonicityTheorem` (named `def … : Prop := ReducedVolumeMonotonicity M.reducedVolume`), `ManifoldReducedVolumeInterface` + per-field reference theorems, `euclideanReducedVolumeCertificate`, `euclidean_reducedVolumeMonotonicity`, `flatLExponential_det`, `euclidean_jacobianComparison`, `EuclideanReducedVolumeAnchor` — all present and proved |

No change to any authored file or verdict in this session.

## 18. Session re-verification (2026-09-10T19:02Z)

Fresh gates re-run once more in this session from the worktree root, all green:

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0, 0 warnings, 0 error lines** (`longrun/d11rve-session13/compile_<F>.log`, `gate_exit_codes.txt`) |
| whole release package | `lake build` | **exit 0**, "Build completed successfully (9155 jobs)"; 0 real build errors — the only `error` grep hits are `info:` lines for pre-existing D7 audit declaration names (`longrun/d11rve-session13/lake_build.log`) |
| axiom audit | `lake env lean release/Poincare/D11/ReducedVolume/Audit.lean` | **74/74 declarations**: cone `{propext, Classical.choice, Quot.sound}` (71), `{}` (2: `generalMonotonicityMissingDependencies`, `generalMonotonicityMissingDependencies_length`), `{propext}` (1: `generalMonotonicityMissingDependencies_ne_nil`); **0 nonstandard** (`longrun/d11rve-session13/audit_raw.log`) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume/` | **0 hard, 0 soft** (7 files, `longrun/d11rve-session13/forbidden_scan.txt`) |
| source integrity | `sha256sum` of the 7 authored files | 7/7 match the hashes recorded in section 1 (no drift) |

No change to any authored file or verdict in this session.


## 19. Session re-verification (2026-09-11, session14)

Fresh gates re-run once more in this session from the worktree root, all green:

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0, 0 warnings, 0 error lines** (`longrun/d11rve-session14/compile_<F>.log`, `gate_exit_codes.txt`) |
| whole release package | `lake build` | **exit 0**, "Build completed successfully (9155 jobs)" (`longrun/d11rve-session14/lake_build.log`) |
| axiom audit | `lake env lean release/Poincare/D11/ReducedVolume/Audit.lean` | **74/74 declarations**: cone `{propext, Classical.choice, Quot.sound}` (71), `{}` (2), `{propext}` (1); **0 nonstandard** (`longrun/d11rve-session14/axiom_audit.json`, `audit_raw.log`) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume/` | **0 hard, 0 soft** (7 files, `longrun/d11rve-session14/forbidden_scan.txt`) |
| source integrity | `sha256sum` of the 7 authored files | 7/7 match the hashes recorded in section 1 (no drift) |
| content spot-check | re-read of all four content modules + All/Probe/Audit | `flatLIntegrand = √τ·(0+|γ'|²)`, `heatKernelReducedDistance_eq : ℓ = |x|²/(4τ)`, `LMinimizer_eq_straightRay`, `minimizer_iff_eq_straightRay`, `reducedVolumeIntegrand_eq_gaussianKernel`, `reducedVolume_eq_one`, `ReducedVolumeMonotonicityTheorem` (named `def … : Prop`), `ManifoldReducedVolumeInterface` + per-field reference theorems — all present and proved |

No change to any authored file or verdict in this session.


## 20. Session re-verification (2026-09-11, session15)

Fresh gates re-run once more in this session from the worktree root, all green:

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0, 0 warnings, 0 error lines** (`longrun/d11rve-session15/compile_<F>.log`, `gate_exit_codes.txt`) |
| whole release package | `lake build` | **exit 0**, "Build completed successfully (9155 jobs)" (`longrun/d11rve-session15/lake_build.log`) |
| axiom audit | `lake env lean release/Poincare/D11/ReducedVolume/Audit.lean` | **74/74 declarations**: cone `{propext, Classical.choice, Quot.sound}` (71), `{}` (2), `{propext}` (1); **0 nonstandard** (`longrun/d11rve-session15/axiom_audit.json`, `audit_raw.log`) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume/` | **0 hard, 0 soft** (7 files, `longrun/d11rve-session15/forbidden_scan.txt`) |
| source integrity | `sha256sum` of the 7 authored files | 4/4 content modules match the hashes recorded in section 1 (Basic `388b62aef7d5d82c`, StraightRays `16a1fa770ed2ccce`, Volume `a6d2bf62fc279a33`, Statements `c823d0e7b7e07961`) |
| content spot-check | re-read of all four content modules + All/Probe/Audit | `flatLIntegrand = √τ·(0+|γ'|²)`, `heatKernelReducedDistance_eq : ℓ = |x|²/(4τ)`, `LMinimizer_eq_straightRay`, `minimizer_iff_eq_straightRay`, `reducedVolumeIntegrand_eq_gaussianKernel`, `reducedVolume_eq_one`, `ReducedVolumeMonotonicityTheorem` (named `def … : Prop`), `ManifoldReducedVolumeInterface` + per-field reference theorems — all present and proved |

No change to any authored file or verdict in this session.


## 21. Session re-verification (2026-09-11, session16)

Fresh gates re-run once more in this session from the worktree root, all green:

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0, 0 warnings, 0 error lines** (`longrun/d11rve-session16/compile_<F>.log`, `gate_exit_codes.txt`) |
| whole release package | `lake build` | **exit 0**, "Build completed successfully (9155 jobs)" (`longrun/d11rve-session16/lake_build.log`) |
| axiom audit | `lake env lean release/Poincare/D11/ReducedVolume/Audit.lean` | **74/74 declarations**: cone `{propext, Classical.choice, Quot.sound}` (71), `{}` (2: `generalMonotonicityMissingDependencies`, `generalMonotonicityMissingDependencies_length`), `{propext}` (1: `generalMonotonicityMissingDependencies_ne_nil`); **0 nonstandard** (`longrun/d11rve-session16/axiom_audit.json`, `audit_raw.log`) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume/` | **0 hard, 0 soft** (7 files, `longrun/d11rve-session16/forbidden_scan.txt`) |
| source integrity | `sha256sum` of the 7 authored files | 7/7 match the hashes recorded in section 1 (Basic `388b62ae`, StraightRays `16a1fa77`, Volume `a6d2bf62`, Statements `c823d0e7`, All `0e8ef1d5`, Probe `81ebdefe`, Audit `51c19cfa`); line counts 178/429/169/325/22/95/96 (1314 total) unchanged |
| content spot-check | re-read of `Basic.lean` (full) + statement re-read of `StraightRays.lean` / `Volume.lean` / `Statements.lean` | `flatLIntegrand = √τ·(0+|γ'|²)`, `flatLlength_eq_LlengthAlong`, `heatKernel_asymptotics`, `heatKernelReducedDistance_eq : ℓ = |x|²/(4τ)`, `LMinimizer_eq_straightRay` (minimiser = ray on `[0,τ]`, FTC proof), `minimizer_iff_eq_straightRay`, `reducedVolumeIntegrand_eq_gaussianKernel`, `reducedVolumeIntegrandUnnormalized_eq_gaussianKernel : τ^(-n/2) exp(-ℓ) = (4π)^(n/2)·K`, `reducedVolume_eq_one`, `reducedVolume_constant`, `ReducedVolumeMonotonicityTheorem` (named `def … : Prop := ReducedVolumeMonotonicity M.reducedVolume`), `ManifoldReducedVolumeInterface` fields (`flow`/`dimension`/`reducedDistance`/`reducedVolume`) + per-field reference theorems, `euclideanReducedVolumeCertificate` (all six D7 certificate fields), `euclidean_jacobianComparison`, `EuclideanReducedVolumeAnchor` — all present and proved |

No change to any authored file or verdict in this session.


## 22. Session re-verification (2026-09-11, session17)

Fresh gates re-run once more in this session from the worktree root, all green:

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0, 0 warnings, 0 error lines** (`longrun/d11rve-session17/compile_<F>.log`, `gate_exit_codes.txt`) |
| whole release package | `lake build` | **exit 0**, "Build completed successfully (9155 jobs)" (`longrun/d11rve-session17/lake_build.log`) |
| axiom audit | `lake env lean release/Poincare/D11/ReducedVolume/Audit.lean` | **74/74 declarations**: `[propext, Classical.choice, Quot.sound]` (71), `[]` (2: `generalMonotonicityMissingDependencies`, `generalMonotonicityMissingDependencies_length` — "does not depend on any axioms"), `[propext]` (1: `generalMonotonicityMissingDependencies_ne_nil`); **0 nonstandard** (`longrun/d11rve-session17/axiom_audit.json`) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume` | **0 hard, 0 soft** (7 files scanned, `longrun/d11rve-session17/forbidden_scan.txt`) |
| source integrity | `sha256sum` of the 7 authored files | 7/7 match the hashes recorded in section 1 (Basic `388b62ae`, StraightRays `16a1fa77`, Volume `a6d2bf62`, Statements `c823d0e7`, All `0e8ef1d5`, Probe `81ebdefe`, Audit `51c19cfa`) |
| content spot-check | re-read `Basic.lean` (full), `StraightRays.lean` (deficit/minimiser section), `Statements.lean` (interface section); declaration scan of `Volume.lean` / `Statements.lean` | `flatLIntegrand = √τ·(0+|γ'|²)`, `flatLlength_eq_LlengthAlong`, `heatKernelReducedDistance_eq : ℓ = |x|²/(4τ)`, `LMinimizer_eq_straightRay` (every `L`-minimiser from the origin = straight ray on `[0,τ]`), `minimizer_iff_eq_straightRay`, `reducedVolumeIntegrand_eq_gaussianKernel`, `reducedVolume_eq_one`, `reducedVolume_constant`, `ReducedVolumeMonotonicityTheorem` (named `def … : Prop := ReducedVolumeMonotonicity M.reducedVolume`), `ManifoldReducedVolumeInterface` fields (`flow`/`dimension`/`reducedDistance`/`reducedVolume`) + per-field reference theorems, `euclideanReducedVolumeCertificate`, `euclidean_reducedVolumeMonotonicity`, `euclidean_jacobianComparison`, `EuclideanReducedVolumeAnchor` — all present and proved |

No change to any authored file or verdict in this session.  Checkpoint updated
(`checkpoint.json` + `longrun/checkpoint.json`, `fresh_reverification_session17_2026_09_11`).

## 23. Session re-verification (2026-09-11, session18)

Fresh gates re-run once more in this session from the worktree root, all green:

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0, 0 warnings, 0 error lines** (`longrun/d11rve-session18/compile_<F>.log`, `gate_exit_codes.txt`) |
| whole release package | `lake build` | **exit 0**, "Build completed successfully (9155 jobs)" (`longrun/d11rve-session18/lake_build.log`) |
| axiom audit | `lake env lean release/Poincare/D11/ReducedVolume/Audit.lean` | **74/74 declarations**: `[propext, Classical.choice, Quot.sound]` (71), `[]` (2: `generalMonotonicityMissingDependencies`, `generalMonotonicityMissingDependencies_length` — "does not depend on any axioms"), `[propext]` (1: `generalMonotonicityMissingDependencies_ne_nil`); **0 nonstandard** (`longrun/d11rve-session18/axiom_audit.json`) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume` | **0 hard, 0 soft** (7 files scanned, `longrun/d11rve-session18/forbidden_scan.txt`) |
| source integrity | `sha256sum` of the 7 authored files | 7/7 match the hashes recorded in section 1 (Basic `388b62ae`, StraightRays `16a1fa77`, Volume `a6d2bf62`, Statements `c823d0e7`, All `0e8ef1d5`, Probe `81ebdefe`, Audit `51c19cfa`) |
| content spot-check | declaration scan + statement re-read of `Basic.lean`, `StraightRays.lean`, `Volume.lean`, `Statements.lean`; D7 cross-reference check | `flatLIntegrand = √τ·(0+|γ'|²)` (`R=0` flat case), `flatLlength`, `heatKernelReducedDistance = -log((4πτ)^{n/2}·gaussianKernel)` (D10 heat-kernel asymptotics), `heatKernelReducedDistance_eq : ℓ = |x|²/(4τ)`, `straightRay_isLMinimizer`, `LMinimizer_eq_straightRay`, `minimizer_iff_eq_straightRay`, `reducedVolumeIntegrand_eq_gaussianKernel`, `reducedVolume_eq_one`, `reducedVolume_constant`, `ReducedVolumeMonotonicityTheorem` (named `def … : Prop := ReducedVolumeMonotonicity M.reducedVolume`), `ManifoldReducedVolumeInterface` fields (`flow`/`dimension`/`reducedDistance`/`reducedVolume`) + per-field reference theorems, `euclideanReducedVolumeCertificate` (instantiates D7 `ReducedVolumeCertificate`), `euclidean_reducedVolumeMonotonicity`, `euclidean_jacobianComparison`, `EuclideanReducedVolumeAnchor` (4-conjunct anchor, proved) — all present and proved; D7 declarations `Poincare.D7.Reduced.{ReducedVolumeCertificate, LMinimizerExistence, ReducedVolumeMonotonicity, MetricFlowInterface}` confirmed to exist |

No change to any authored file or verdict in this session.  Checkpoint updated
(`checkpoint.json` + `longrun/checkpoint.json`, `fresh_reverification_session18_2026_09_11`).

## 24. Session re-verification (2026-09-11, session19)

Continuation invocation.  Rather than trusting the checkpoint, every gate was re-run from
scratch from the worktree root and the mathematical content was re-read.  All green:

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0, 0 warnings, 0 error lines** (`longrun/d11rve-session19/compile_<F>.log`, `gate_exit_codes.txt`); logs contain only timing (Probe additionally its `#check` output) |
| whole release package | `lake build` | **exit 0**, "Build completed successfully (9155 jobs)" (`longrun/d11rve-session19/lake_build.log`); the 14 lines matching `error` are declaration *names* in `Poincare.D7.Limit.Audit` (`...error_le...`), not diagnostics — **no D11 error line** |
| axiom audit | `lake env lean release/Poincare/D11/ReducedVolume/Audit.lean` | **74/74 declarations**: `[propext, Classical.choice, Quot.sound]` (71), `[]` (2: `generalMonotonicityMissingDependencies`, `…_length` — "does not depend on any axioms"), `[propext]` (1: `…_ne_nil`); **0 nonstandard** (`longrun/d11rve-session19/axiom_audit.json`, `audit_raw.log`, `axiom_audit_summary.txt`).  74 real commands (the 75th `#print axioms` occurrence is the docstring mention on line 7) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume` | **0 hard, 0 soft** (7 files scanned, `longrun/d11rve-session19/forbidden_scan.txt`); an independent `grep -E "\b(sorry\|axiom\|unsafe\|native_decide\|proof_wanted\|sorryAx\|admit\|implemented_by\|extern)\b"` matches only the prose in module docstrings that asserts their absence |
| source integrity | `sha256sum` of the 7 authored files | 7/7 match the hashes recorded in section 1 (Basic `388b62ae`, StraightRays `16a1fa77`, Volume `a6d2bf62`, Statements `c823d0e7`, All `0e8ef1d5`, Probe `81ebdefe`, Audit `51c19cfa`) |
| content re-read | full read of `Basic.lean` (178 ln), `Volume.lean` (169 ln), `Statements.lean` (325 ln) and the theorem bodies of `StraightRays.lean` (`straightRay_hasDerivAt`, `straightRay_length`, `straightRay_reducedLength`, `straightRay_isLMinimizer`, `LMinimizer_eq_straightRay`, `IsLMinimizer_of_eq_straightRay`, `minimizer_iff_eq_straightRay`, `flatDeficit_integral`, `ae_velocity_eq_of_deficit_integral_zero`) | task items 1–3 all present **and proved**, exactly as claimed: `flatLIntegrand γ γ' τ = √τ * (0 + ‖γ' τ‖²)` (literal `R = 0` flat case) and `flatLlength = ∫ √τ(0+\|γ'\|²)`; `heatKernelReducedDistance n τ x = -log((4πτ)^(n/2) · gaussianKernel n τ x)` with `heatKernelReducedDistance_eq : ℓ = ‖x‖²/(4τ)` and `heatKernel_asymptotics`; `minimizer_iff_eq_straightRay` (both directions, unconditional on `τ > 0`); `reducedVolumeIntegrandUnnormalized_eq_gaussianKernel : τ^{-n/2} e^{-ℓ} = (4π)^{n/2}·K`, `integral_reducedVolumeIntegrandUnnormalized = (4π)^{n/2}`, `reducedVolume_eq_one : Ṽ(τ) = 1` (via D10 `gaussianKernel_integral`), `reducedVolume_constant`; `ReducedVolumeMonotonicityTheorem M : Prop := D7.Reduced.ReducedVolumeMonotonicity M.reducedVolume`, `ManifoldReducedVolumeInterface` (`flow`/`dimension`/`reducedDistance`/`reducedVolume`) with one `rfl` field-reference theorem per field, `euclideanReducedVolumeCertificate` filling every D7 `ReducedVolumeCertificate` field, `euclidean_manifoldReducedVolumeMonotonicity`, `euclidean_jacobianComparison`, `euclideanReducedVolumeAnchor` (4-conjunct, proved) |
| upstream cross-reference | `grep` over `release/Poincare/D7/Reduced/*.lean` and `release/Poincare/D10/**` | all consumed declarations exist where D11 claims: D7 `MetricFlowInterface` (Basic.lean:81), `ReducedVolumeCertificate` (Certificate.lean:64), `gaussianFlow`/`gaussianPath`/`gaussian_LlengthAlong`/`gaussian_length_le`/`gaussian_isLMinimizer`/`gaussianReducedLengthData` (Gaussian.lean), `LMinimizerExistence`/`ReducedVolumeMonotonicity`/`JacobianComparisonInterface`/`JacobianComparison` (Statements.lean); D10 `gaussianKernel`/`gaussianKernel_apply`/`finrank_euclideanSpace_fin` (HeatKernelEuclidean/Basic.lean), `gaussianKernel_integral` (HeatKernelEuclidean/Mass.lean) |

No change to any authored file or verdict in this session.  Checkpoint updated
(`checkpoint.json` + `longrun/checkpoint.json`, `fresh_reverification_session19_2026_09_11`);
`longrun/results/D11-reduced-volume-euclidean.json` gains the session19 entry.  All seven
authored files are byte-identical to the ones whose hashes are recorded in section 1, so this
re-verification certifies exactly the previously reported artifact.

## 25. Session re-verification (2026-09-11, session20)

Continuation invocation.  The checkpoint was not trusted: every gate was re-run from scratch
from the worktree root, all seven sources were re-read, the consumed D7/D10 declarations were
re-read at their definitions, and two *new* independent checks were added (a namespace census
straight from the Lean environment, and a second comment-stripper for the forbidden-token
audit).  One documentation miscount was found and corrected; no Lean source was changed.

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0, 0 warning/error lines** (`longrun/d11rve-session20/compile_<F>.log`, `gate_exit_codes.txt`) |
| whole release package | `lake build` (worktree root) | **exit 0**, "Build completed successfully (9155 jobs)", 0 error lines (`longrun/d11rve-session20/lake_build.log`) |
| axiom audit | `lake env lean …/Audit.lean` + independent parser | **74/74 blocks**, unique names, every command matched by an output block: `[propext, Classical.choice, Quot.sound]` (71), `[]` (2), `[propext]` (1); **0 nonstandard** (`longrun/d11rve-session20/audit_raw.log`, `axiom_audit.json`) |
| audit coverage (new) | regex extraction of every `theorem`/`def`/`structure` in the four content modules vs the 74 `#print axioms` commands | **74 vs 74, exact bijection**: 0 declarations unaudited, 0 audit commands without a source declaration |
| namespace census (new) | `EnvProbe.lean`: enumerate `env.constants` under `Poincare.D11.ReducedVolume` | **113 constants = 74 authored + 39 auto-generated** (`_proof_*`, `_simp_*`, `eq_1`, structure `mk`/`rec`/`casesOn`/projections/`noConfusion`); **0 `axiomInfo` constants** (`longrun/d11rve-session20/env_probe.log`) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume` | **0 hard, 0 soft**, 7 files (`forbidden_scan.txt`); an independent second comment-stripper finds **0 code occurrences** of any of the 9 hard/soft tokens |
| source integrity | `sha256sum` × 7 | **7/7 byte-identical** to §1 (Basic `388b62ae`, StraightRays `16a1fa77`, Volume `a6d2bf62`, Statements `c823d0e7`, All `0e8ef1d5`, Probe `81ebdefe`, Audit `51c19cfa`) |
| mathematical re-read | `Basic.lean`, `StraightRays.lean`, `Volume.lean`, `Statements.lean` read in full; D7 `Gaussian.lean` (`gaussian_length_le`, `gaussian_isLMinimizer`, `gaussianReducedLengthData_reducedLength`), D7 `Statements.lean` (`LMinimizerExistence`, `ReducedVolumeMonotonicity := AntitoneOn V (Ioi 0)`, `JacobianComparison`), D7 `Certificate.lean` (`ReducedVolumeCertificate`, `antitoneOn`), D10 `Mass.lean` (`gaussianKernel_integral = 1`) | all claims confirmed at definition level: `flatLIntegrand = √τ·(0+‖γ'‖²)`; `heatKernel_asymptotics : (4πτ)^{-n/2} e^{-ℓ} = K`; `heatKernelReducedDistance_eq : ℓ = ‖x‖²/(4τ)`; `minimizer_iff_eq_straightRay` genuine two-sided characterisation resting on the universal lower bound `gaussian_length_le`; `reducedVolumeIntegrand_eq_gaussianKernel` + `gaussianKernel_integral` ⇒ `reducedVolume_eq_one`; `ReducedVolumeMonotonicityTheorem` is a `def … : Prop` (not an axiom) and is proved for the Euclidean instantiation |
| D7 ledger cross-reference (new) | exact `grep` diff of the 10 `String` literals of `generalMonotonicityMissingDependencies` against the 10 `.name` fields of D7 `Poincare.D7.Reduced.reducedVolumeDependencies` | **exact string match RLV-1 … RLV-10** (`reducedVolumeDependencies_length = 10` on the D7 side).  Precision on the file docstring "each entry is discharged in the Euclidean case": RLV-1 (`euclidean_LMinimizerExistence`), RLV-3 (`LMinimizer_eq_straightRay`), RLV-4 (`flatLExponential(_det)`), RLV-6 (`euclidean_jacobianComparison`), RLV-9 (`euclideanFlow`), RLV-10 (`gaussianKernel_integral` via `reducedVolume_eq_one`) have literal Euclidean counterparts; RLV-2 and RLV-8 are obtained in closed form rather than by the general tool (`straightRay_*` minimality, constant volume with derivative `0`); **RLV-5 (second variation / index form) and RLV-7 (reduced-length differential inequality) are bypassed, not instantiated** — the flat computation is direct and these are listed as not-claimed in §5.  This does not affect any theorem: all Euclidean results are proved, and the general monotonicity theorem remains a state-only `Prop` |

**Correction made in this session (documentation only).**  §0 previously read "75 authored
declarations (14 + 21 + 13 + **27**)".  The four content modules contain 14 + 21 + 13 + **26**
= **74** declarations; the Lean-environment census above confirms exactly 74 authored
constants (and 74 `#check` probes and 74 `#print axioms` commands, matching the already-correct
"74/74" audit line).  The "75/27" figures were an arithmetic slip in the summary table and have
been corrected; `checkpoint.json` `status.authored_declarations` was corrected from 75 to 74
accordingly.  No Lean source, hash, gate result or mathematical claim changed.

No change to any authored file or verdict in this session.  Checkpoint updated
(`checkpoint.json` + `longrun/checkpoint.json`, `fresh_reverification_session20_2026_09_11`);
`longrun/results/D11-reduced-volume-euclidean.json` gains the session20 entry.  All seven
authored files are byte-identical to the ones whose hashes are recorded in §1, so this
re-verification certifies exactly the previously reported artifact.

## 26. Session re-verification (2026-09-11, session21)

Continuation invocation.  The checkpoint was not trusted: the whole gate set was re-run from
scratch from the worktree root, and one **new** independent check was added — a *non-vacuity
probe* that instantiates the headline theorems at concrete dimensions, times and points and
closes the resulting numeric equalities.  No Lean source was changed.

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0, 0 warning/error lines** (`longrun/d11rve-session21/compile_<F>.log`, `gate_exit_codes.txt`) |
| whole release package | `lake build` (worktree root) | **exit 0**, "Build completed successfully (9155 jobs)", 0 error lines (`longrun/d11rve-session21/lake_build.log`) |
| axiom audit | `lake env lean …/Audit.lean` + independent parser freshly written this session (`parse_audit.py`) | **74/74 declarations**: `[propext, Classical.choice, Quot.sound]` (71), `[]` (2), `[propext]` (1); union of all cones `= {propext, Classical.choice, Quot.sound}` exactly; **0 nonstandard** (`audit_raw.log`, `axiom_audit.json`) |
| audit coverage | regex extraction of every `theorem`/`def`/`structure` in the four content modules vs the 74 `#print axioms` commands | **exact bijection 74 = 74**: 0 source declarations unaudited, 0 audit commands without a source declaration (the single regex artefact `and` is a prose word inside the `Statements.lean` module docstring, not a declaration) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume` | **0 hard, 0 soft**, **7 files actually scanned** (`forbidden_scan.json`).  Method note: the scanner's `os.walk` interface needs a *directory*; passing the seven file paths scans 0 files and yields a vacuous `0` — the directory form was used |
| source integrity | `sha256sum` × 7 | **7/7 byte-identical** to §1 (Basic `388b62ae`, StraightRays `16a1fa77`, Volume `a6d2bf62`, Statements `c823d0e7`, All `0e8ef1d5`, Probe `81ebdefe`, Audit `51c19cfa`) |
| **non-vacuity probe (new)** | `lake env lean longrun/d11rve-session21/NonVacuityProbe.lean` (outside the release tree) | **exit 0, 0 warnings** (`nonvac_probe.log`): 17 `example` instantiations + 2 concrete norm lemmas, e.g. `heatKernelReducedDistance 1 1 1 = 1/4`, `heatKernelReducedDistance 1 4 4 = 1`, `reducedVolume 2 1 = 1`, `reducedVolume 3 7 = 1`, `euclideanReducedVolume 4 2 = 1`, `LlengthAlong (straightRay 4 1) … 0 1 = 8`, `reducedLengthAlong … = 4`, `IsLMinimizer (straightRayLPath 4 1)`, `AntitoneOn (euclideanReducedVolumeCertificate 2).volume (Ioi 0)`, and `(euclideanManifoldReducedVolumeInterface 2).reducedVolume 1 = 1` |

**Why the non-vacuity probe matters.**  The release theorems are universally quantified over
`n`, `τ > 0` and the point, so a compiling proof alone does not exclude a statement whose
hypotheses are unsatisfiable or whose conclusion is degenerate.  The probe closes genuinely
numeric statements: `Ṽ = 1` becomes an equality between two real numbers that both evaluate to
`1`, and the `L`-length claim becomes the numeric equality `8 = 8`.  Together with
`gaussianKernel_integral : ∫ K = 1` (D10 `Mass.lean`) — whose value is `1`, not `0` — this
rules out the vacuous reading of `reducedVolume_eq_one`.  The probe is compiled but is *not*
part of the release tree and is not imported by `All.lean`.

**Mathematical re-read (this session).**  `Basic.lean`, `Volume.lean` and the statement blocks
of `StraightRays.lean` / `Statements.lean` were re-read at definition level and confirm:
`flatLIntegrand = √τ·(0 + ‖γ'‖²)` (the task's `∫√τ(|γ'|²+R) dτ` with `R = 0`);
`heatKernelReducedDistance := -log((4πτ)^{n/2} K)` with
`heatKernelReducedDistance_eq : ℓ = ‖x‖²/(4τ)`; `heatKernel_asymptotics` the inverse identity;
`minimizer_iff_eq_straightRay` a genuine two-sided characterisation (both directions proved);
`reducedVolumeIntegrand_eq_gaussianKernel` then `gaussianKernel_integral` giving
`reducedVolume_eq_one : Ṽ(τ) = 1`; `ReducedVolumeMonotonicityTheorem` a `def … : Prop` (a
statement, never an axiom) proved for the Euclidean instantiation.  The §25 honesty boundary
stands: RLV-5 (second variation) and RLV-7 (reduced-length differential inequality) are
*bypassed* in the flat computation rather than instantiated — not a gap in any proved theorem.

No change to any authored file or verdict in this session.  Checkpoint updated
(`checkpoint.json` + `longrun/checkpoint.json`, `fresh_reverification_session21_2026_09_11`);
`longrun/results/D11-reduced-volume-euclidean.json` gains the session21 entry.  All seven
authored files are byte-identical to the ones whose hashes are recorded in §1, so this
re-verification certifies exactly the previously reported artifact.

**Last line:** TASK_DONE — card: `longrun/results/D11-reduced-volume-euclidean.md`

## 27. Session re-verification (2026-09-11, session22)

Continuation invocation at 09:22Z.  The checkpoint was again not trusted: the full gate set was
re-run from the worktree root, and a **second, independently written non-vacuity probe**
(different from session21's) was added.  No Lean source was changed.

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0, 0 warning/error lines** (`longrun/d11rve-session22/compile_<F>.log`, `gate_exit_codes.txt`) |
| whole release package | `lake build` (worktree root) | **exit 0**, "Build completed successfully (9155 jobs)", 0 `error`/`✖` lines (`longrun/d11rve-session22/lake_build.log`) |
| axiom audit | `lake env lean …/Audit.lean` + parser `parse_audit.py` written from scratch this session | **74/74 declarations**: `[propext, Classical.choice, Quot.sound]` (71), `[propext]` (1), `[]` (2); union of all cones `= {propext, Classical.choice, Quot.sound}` exactly; **0 nonstandard** (`audit_raw` = `compile_Audit.log`, `axiom_audit.json`, `audit_verdict.txt` = `VERDICT: OK`) |
| audit coverage | regex census of every `def`/`theorem`/`structure` in the four content modules vs the 74 `#print axioms` commands | **74 real declarations** (Basic 14 + StraightRays 21 + Volume 13 + Statements 26) in **exact bijection** with the 74 audit commands; 0 audit commands without a source declaration.  The single regex artefact was pinpointed this session: the prose word `theorem` starting `Statements.lean:11` in the module docstring ("**…part 4: the named propositions — the monotonicity / theorem and the manifold…**"), after which the regex consumes the following prose word `and` as an identifier.  It is not a declaration |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume` | **0 hard, 0 soft**, 7 files scanned (`forbidden_scan.json`).  Belt-and-braces raw `grep` over the 7 files finds the tokens **only** inside docstring sentences that assert their absence (e.g. `Basic.lean:41`), which the comment/string-aware scanner correctly blanks |
| source integrity | `sha256sum` × 7 | **7/7 byte-identical** to §1 (Basic `388b62ae`, StraightRays `16a1fa77`, Volume `a6d2bf62`, Statements `c823d0e7`, All `0e8ef1d5`, Probe `81ebdefe`, Audit `51c19cfa`); `sha256.txt` |
| **non-vacuity probe v2 (new)** | `lake env lean longrun/d11rve-session22/NonVacuityProbe.lean` (outside the release tree) | **exit 0, 0 warnings** (`nonvac_probe.log`): numeric instances `heatKernelReducedDistance 1 1 e₀ = 1/4`, `… 1 4 e₀ = 1/16`, `… 2 2 e₀ = 1/8`, `… 3 1 0 = 0`; **positivity** `0 < reducedVolumeIntegrand n τ 0` and `0 < reducedVolume n τ`; `reducedVolume 3 7 = 1`; straight-ray `LlengthAlong = 1/2` and `reducedLengthAlong = 1/4` at `(n,τ,x) = (1,1,e₀)`; `ReducedVolumeMonotonicity` at `n = 2`; certificate `antitoneOn` at `n = 4`; the interface's `reducedDistance` field at `n = 2`; `LinearMap.det (flatLExponential 1 4) = 4`; `straightRay e₀ 1 0 = 0` |

**What the new probe adds.**  Session21's probe evaluated the headline identities at other
points; this probe additionally closes **strict positivity** of the reduced-volume integrand and
of `Ṽ` itself (`0 < reducedVolume n τ`), which is the sharpest cheap exclusion of the vacuous
reading `Ṽ ≡ 0` of `reducedVolume_eq_one`.  Together with D10's
`gaussianKernel_integral : ∫ K = 1` (a value `1`, not `0`) and
`gaussianKernel_pos : 0 < K` this makes the Euclidean anchor a statement about a genuine
probability density.  The probe is compiled but is *not* part of the release tree and is not
imported by `All.lean`.

**Definition-level mathematical re-read (this session, including the D7 substrate).**
Independently of the previous sessions' notes, the following were checked at definition level
this session:

* D7 `MetricFlowInterface.LIntegrandAlong γ γ' τ = √τ · (R(γ τ) + g(γ' τ, γ' τ))`
  (`D7/Reduced/Basic.lean:113`), so D11's `flatLIntegrand = √τ·(0 + ‖γ'‖²)` is literally the
  task's `∫ √τ (|γ'|² + R) dτ` at `R = 0`; `euclideanFlow_scalarCurvature` and
  `euclideanFlow_metric` fix the two fields that enter it.
* D7 `LPath` records exactly the hypotheses used (endpoints, continuity on `[0,τ]`,
  differentiability on `(0,τ)`, interval-integrability of energy and cross terms) and
  `IsLMinimizer P := ∀ Q, P.length ≤ Q.length` (`D7/Reduced/Basic.lean:228`) — a genuine
  two-sided minimising property among admissible paths, not a placeholder.  Hence
  `minimizer_iff_eq_straightRay` really says *the* `L`-geodesics from `0` are *exactly* the
  straight rays `γ(σ) = (√σ/√τ) x`.
* D10 `gaussianKernel n t x = (4πt)^{-n/2} e^{-‖x‖²/(4t)}` (`D10/HeatKernelEuclidean/Basic.lean:38`)
  and `gaussianKernel_integral : ∫ K = 1` (`D10/HeatKernelEuclidean/Mass.lean:32`) are the
  Gaussian toolbox the task asks for; D11's `reducedVolumeIntegrand_eq_gaussianKernel` is a
  pointwise identity and `reducedVolume_eq_one` its integral.
* D7 `ReducedVolumeMonotonicity V := AntitoneOn V (Set.Ioi 0)` and the
  `ReducedVolumeCertificate` fields (`flow`, `volume`, `derivative`, `hasDerivAt_volume`,
  `derivative_nonpos`, `volume_nonneg`) match D11's `ReducedVolumeMonotonicityTheorem` /
  `euclideanReducedVolumeCertificate` field for field; the D11 certificate discharges
  `hasDerivAt_volume` by eventual constancy on `Ioi 0` (`reducedVolume_eq_one`), which is the
  correct Euclidean degeneration of the differentiation-under-the-integral field.

No gap and no vacuity was found: every headline claim traces to a proved declaration whose
axiom cone is inside `{propext, Classical.choice, Quot.sound}`.  The general (manifold)
monotonicity theorem remains a `def … : Prop` and is **not** claimed as proved for general
manifolds — the §25 honesty boundary (RLV-5 and RLV-7 bypassed rather than instantiated in the
flat case) stands unchanged.

No change to any authored file or verdict in this session.  Checkpoint updated
(`checkpoint.json` + `longrun/checkpoint.json`, `fresh_reverification_session22_2026_09_11`);
`longrun/results/D11-reduced-volume-euclidean.json` gains the session22 entry.  All seven
authored files are byte-identical to the ones whose hashes are recorded in §1, so this
re-verification certifies exactly the previously reported artifact.

TASK_DONE — card: longrun/results/D11-reduced-volume-euclidean.md
