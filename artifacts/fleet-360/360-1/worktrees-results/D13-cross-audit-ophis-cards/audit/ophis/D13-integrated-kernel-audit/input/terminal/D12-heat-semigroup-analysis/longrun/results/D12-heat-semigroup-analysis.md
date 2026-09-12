# D12-heat-semigroup-analysis — result card

- **Task**: D12-heat-semigroup-analysis (HeatSemigroup module)
- **Worktree**: `longrun/worktrees/D12-heat-semigroup-analysis` (isolated; only this worktree was modified)
- **Toolchain**: leanprover/lean4:v4.34.0-rc2; mathlib pinned `7974e751bece493b6ff508039423ca9fa2452fa8` (Apache-2.0; unmodified; consumed from the preloaded snapshot only)
- **Model**: deepseek-v4-pro (as configured; never switched)

## Scope and approach

The objective was a **genuine Euclidean heat-operator estimate on a specified function space**, using
Lebesgue measure and the explicit kernel — positivity and L∞ contraction first, then L1 contraction or
strong continuity, plus one smoothing/differentiation-under-integral lemma, and finally explicit proof
obligations for the compact-manifold step. The heat operator is defined directly against the explicit
D10 Gaussian kernel on `EuclideanSpace ℝ (Fin n)`:

```
heatOperator n t f x = ∫ y, gaussianKernel n t (x - y) * f y   (Lebesgue measure)
```

All results reuse the D10 mass/convolution identity and the D11 `flatKernel` compatibility and weak
initial condition; nothing Euclidean below is labelled a manifold heat-kernel existence theorem, and no
result assumes the target conclusion.

## Proved declarations (kernel-checked, 75 declarations audited)

### 1. Positivity (`Basic.lean`)
- `heatOperator_nonneg n ht hf0 x : 0 ≤ heatOperator n t f x` — for `t > 0`, `f ≥ 0` a.e.
  (the Bochner-integral case split: `integral_nonneg_of_ae` in the integrable case,
  `integral_undef` in the other).

### 2. L∞ contraction (`Basic.lean`, `LinfContraction.lean`)
- `heatOperator_norm_le_of_forall_norm_le n ht hM hf x : ‖P_t f x‖ ≤ M` whenever
  `M ≥ 0` and `∀ y, ‖f y‖ ≤ M` — from `K ≥ 0` and the mass-one identity
  `integral_gaussianKernel_sub : ∫ y, gaussianKernel n t (x - y) = 1` via
  `norm_integral_le_of_norm_le`.
- `heatOperatorBCF_norm_le : ‖heatOperatorBCF n ht f‖ ≤ ‖f‖` on the **Banach space**
  `EuclideanSpace ℝ (Fin n) →ᵇ ℝ` of bounded continuous functions with the sup norm
  (continuity of `P_t f` from the smoothing lemma; the bound from the pointwise estimate with
  `M = ‖f‖`; `BoundedContinuousFunction.norm_le`).

### 3. L¹ contraction (`L1Contraction.lean`)
- `heatOperator_enorm_le_lintegral_enorm`: pointwise `‖P_t f x‖ₑ ≤ ∫⁻ y, ‖K(x-y) f y‖ₑ`
  (mathlib's unconditional `enorm_integral_le_lintegral_enorm`).
- `heatOperator_lintegral_enorm_le : ∫⁻ x, ‖P_t f x‖ₑ ≤ ∫⁻ y, ‖f y‖ₑ` for a.e.-strongly-measurable
  `f` (Tonelli via `lintegral_lintegral_swap`; the inner kernel integral is `1` by
  `lintegral_enorm_gaussianKernel_sub_left`).
- `heatOperator_integrable : Integrable f → Integrable (P_t f)` (kernel-product integrability on
  `volume.prod volume` + `Integrable.integral_prod_left`).
- `heatOperator_integral_norm_le : ∫ x, ‖P_t f x‖ ≤ ∫ y, ‖f y‖` for integrable `f`
  (real L¹ contraction; `ENNReal.toReal_mono` + `integral_eq_lintegral_of_nonneg_ae`).
- `heatOperator_integral_eq_integral : ∫ x, P_t f x = ∫ y, f y` (mass conservation; Fubini).

### 4. Smoothing / differentiation under the integral (`Smoothing.lean`)
- `gaussianKernelFDerivCLM`, `heatKernelMulFDerivCLM`: the explicit Fréchet derivative
  `v ↦ gaussianKernel n t (x - y) · f y · ⟪y - x, v⟫ / (2t)`.
- `hasFDerivAt_gaussianKernel_mul`: the kernel multiple `z ↦ K(z-y) f y` is differentiable.
- `heatKernelMulFDerivCLM_bound_ball` + `one_add_norm_sq_mul_exp_neg_le` + `norm_sub_sq_ge_half`:
  the explicit Gaussian domination `‖F' x y‖ ≤ C(n,t,x₀,M) · exp(-‖y‖²/(16t))` for `x ∈ ball x₀ 1`.
- **`hasFDerivAt_heatOperator`**: for `t > 0`, measurable `f` with `∀ y, ‖f y‖ ≤ M`,
  `HasFDerivAt (P_t f) (∫ y, heatKernelMulFDerivCLM n t f x₀ y) x₀` — proved with
  mathlib's `hasFDerivAt_integral_of_dominated_of_fderiv_le`.
- `differentiable_heatOperator`, `continuous_heatOperator`, `fderiv_heatOperator` (explicit
  derivative formula).

### 5. Strong continuity at `t = 0⁺` (`StrongContinuity.lean`)
- `heatOperator_tendsto_nhdsGT_zero`: for continuous integrable `f` and every `x`,
  `Tendsto (fun t => P_t f x) (𝓝[>] 0) (𝓝 (f x))` — transferred from the D11 weak initial
  condition `flatKernel_tendsto_integral` through `heatOperator_eq_integral_flatKernel`;
  compactly-supported and one-point-convolution forms included.

### 6. Nondegenerate example (`Example.lean`)
- `heatOperator_gaussianKernel : P_t (gaussianKernel n s (· - a)) x = gaussianKernel n (t+s) (x-a)`
  (from the D10 convolution identity) — strictly positive image, total mass `1` before and after,
  the L∞ estimate with the explicit constant `(4πs)^{-n/2}`, and the L¹ estimate with both sides
  equal to `1`: every D12 estimate is non-vacuous on a concrete nonzero function.

### 7. Compact-manifold obligations (`ManifoldObligations.lean`)
Explicit `Prop` statements only (nothing assumed): `CompactManifoldLinfContractionObligation`,
`CompactManifoldL1ContractionObligation`, `CompactManifoldSmoothingObligation`,
`CompactManifoldStrongContinuityObligation`, `CompactManifoldSemigroupObligation`, plus the
kernel-core interface obligation. These are the next-step proof obligations, designed only after
the Euclidean model theorem was checked.

### 8. Operator semigroup law (`Semigroup.lean`) — added this round
- `heatSemigroupKernelProduct_integrable`: the double-kernel product
  `(y,z) ↦ K_s(x-y)·(K_t(y-z)·f z)` is integrable on `volume.prod volume` for integrable `f`
  (kernel factor bounded by the prefactor `(4πs)^{-n/2}`, remainder integrable by part 2).
- **`heatOperator_comp_heatOperator : heatOperator n s (heatOperator n t f) x =
  heatOperator n (s+t) f x`** for `s,t > 0` and integrable `f` — `integral_const_mul`,
  Fubini (`integral_integral_swap`), the change of variables `y ↦ x - y`
  (`integral_kernel_cross_sub_left`) and the D10 convolution identity
  `gaussianKernel_convolution`. Function-level and time-swapped forms
  (`heatOperator_comp_heatOperator_fun`, `_swap`) and the L¹ form
  `heatOperator_comp_heatOperator_integral_norm_eq_zero` included.
- **`heatOperator_comp_heatOperator_of_bounded`**: the same law for a.e.-strongly-measurable `f`
  with a uniform bound `‖f‖ ≤ M` — three applications of Lebesgue dominated convergence
  (`tendsto_integral_of_dominated_convergence`) on the integrable ball truncations
  `f_k = f · 1_{ball 0 k}` (inner bound `M·K_t(y-·)`, outer bound `M·K_s(x-·)`,
  right-hand bound `M·K_{s+t}(x-·)`), using the integrable-case law on each `f_k`.
- **`heatOperatorBCF_comp : heatOperatorBCF n hs (heatOperatorBCF n ht f) =
  heatOperatorBCF n (add_pos hs ht) f`** — the semigroup law on the Banach space
  `EuclideanSpace ℝ (Fin n) →ᵇ ℝ` (plus the swapped form): a genuine downstream use of the
  L∞ contraction and the bounded semigroup law.

### 9. L¹-strong continuity witness on the Gaussian family (`StrongContinuityL1.lean`) — added this round
- `continuousAt_gaussianKernel_time`: the kernel `t ↦ gaussianKernel n t z` is continuous at every
  positive time.
- `gaussianKernel_interval_bound` / `gaussianKernel_interval_bound_le`: the explicit Gaussian
  domination `K_u(z) ≤ (2πs)^{-n/2} exp(-‖z‖²/(6s)) ≤ 6^{n/2} K_{3s}(z)` for `u ∈ (s/2, 3s/2)`.
- **`tendsto_integral_abs_gaussianKernel_sub_of_seq`**: for `s > 0` and any sequence
  `u : ℕ → ℝ` with `Tendsto u atTop (𝓝[>] 0)`,
  `∫ z, |K_{s+u k} z - K_s z| → 0` — Lebesgue dominated convergence with the explicit integrable
  bound `2 · 6^{n/2} · K_{3s}` (the finite prefix of the sequence is cleaned via `max k N`, which
  does not affect the limit).
- **`heatOperator_gaussianKernel_L1_tendsto_seq`**: the heat-operator level statement — for
  `f = gaussianKernel n s (· - a)` and any `u k → 0⁺`,
  `∫ x, |P_{u k} f x - f x| → 0`, via the exact evolution of part 7 and a translation change of
  variables. This is the honest witness version of L¹-strong continuity at `0⁺`; the general
  integrable `f` needs the C_c-density in L¹ recorded below as a dependency request.

## Expanded hypotheses (every theorem carries its obligations explicitly)

- **Positivity**: `0 < t` and `0 ≤ᵐ[volume] f` (no measurability needed — the a.e.-sign suffices
  because the non-integrable Bochner integral vanishes by `integral_undef`).
- **L∞**: `0 < t`, `M ≥ 0`, pointwise bound `∀ y, ‖f y‖ ≤ M` (pointwise form); the BCF form needs
  no extra measurability (continuity + boundedness are built into `→ᵇ`).
- **L¹ (extended)**: `0 < t`, `AEStronglyMeasurable f` (needed only for Tonelli's measurability
  condition); **L¹ (real)**: `Integrable f`.
- **Smoothing**: `0 < t`, `AEStronglyMeasurable f`, `M ≥ 0`, `∀ y, ‖f y‖ ≤ M` (the domination
  constant is explicit: `heatSmoothingBoundConst n t x₀ M = (4πt)^{-n/2} M/(2t) (1+32t e⁻¹) e^{(‖x₀‖+1)²/4t}`).
- **Strong continuity**: `Continuous f`, `Integrable f` (exactly the D11 admissibility class;
  continuous compactly supported functions are included).
- **Semigroup law**: `0 < s`, `0 < t`, `Integrable f` (Fubini form); `0 < s`, `0 < t`,
  `AEStronglyMeasurable f`, `M ≥ 0`, `∀ z, ‖f z‖ ≤ M` (bounded extension); the `→ᵇ` form needs
  only `f : EuclideanSpace ℝ (Fin n) →ᵇ ℝ`.
- **L¹ witness**: `0 < s`, the Gaussian family `f = gaussianKernel n s (· - a)`, and a sequence
  `u k → 0⁺` (the sequence form; the filter form needs the `IsCountablyGenerated (𝓝[>] 0)`
  instance recorded below).

## Semantic classification

| result | class |
| --- | --- |
| positivity, L∞ (pointwise + BCF), L¹ (both forms), mass conservation | **euclidean-model theorems** — general in the specified Euclidean function spaces, conditional only on the expanded regularity above; NOT manifold claims |
| smoothing C¹ (`hasFDerivAt_heatOperator`) | **euclidean-model theorem** (general in `L∞ ∩ measurable`; the domination is explicit) |
| strong continuity at `0⁺` | **conditional transfer** — reduces to the D11 peak-function theorem for continuous integrable test functions; pointwise, not L¹ |
| operator semigroup law `P_s∘P_t = P_{s+t}` (integrable, bounded, `→ᵇ`) | **euclidean-model theorem** (Fubini + D10 convolution identity + DCT on truncations) |
| L¹-strong-continuity witness (Gaussian family) | **euclidean-model witness theorem** — proved directly by DCT with an explicit bound; not the general L¹-strong continuity |
| Gaussian example | **model witness** (non-vacuity check) |
| `CompactManifold*Obligation` | **obligations** (statements only; explicitly not claimed) |

## Blockers

- **Closed this round**: the **operator semigroup law** `P_s(P_t f) = P_{s+t} f` — previously
  recorded as "designed, not yet proved" — is now proved in three forms (integrable `f` by
  Fubini; uniformly bounded measurable `f` by dominated convergence on ball truncations; and on
  the Banach space `→ᵇ` as `heatOperatorBCF_comp`), each with a checked downstream use.
- **Remaining (honest)**:
  1. **General L¹-strong continuity at `t = 0`** (`∫ ‖P_t f - f‖ → 0` for arbitrary integrable
     `f`): requires L¹-density of continuous compactly supported functions on `ℝⁿ`, absent from
     the pinned mathlib. The concrete Gaussian-family witness is proved
     (`heatOperator_gaussianKernel_L1_tendsto_seq`); the general case is NOT claimed.
  2. **Cᵏ smoothing** (`k ≥ 2`): the C¹ step is proved; the iteration is mechanical but unformalised.
  3. **Compact-manifold construction itself**: by design, obligations only.
  4. **Uniform-in-`x` strong continuity** for non-integrable bounded continuous `f`
     (`StrongContinuityBoundedContinuousObligation`): open.
  5. **Filter form of the L¹ witness**: the sequence form is proved; the `𝓝[>] 0` form needs the
     `IsCountablyGenerated (𝓝 (0 : ℝ))` instance (module `Mathlib.Topology.Instances.Real` not
     built in the snapshot), which is purely infrastructural.

## Verification evidence

- **Compile**: `cd release && lake build Poincare.D12.HeatSemigroup.AxiomAudit` — exit 0
  (8899 jobs). Per-file `lake env lean Poincare/D12/HeatSemigroup/<file>.lean` exit 0 for all
  eleven authored files (Basic, L1Contraction, Smoothing, LinfContraction, StrongContinuity,
  ManifoldObligations, Example, Semigroup, StrongContinuityL1, All, AxiomAudit).
- **Axiom audit**: `D12AxiomCheck: PASS — all 75 declarations of the D12 heat-semigroup
  development depend only on [propext, Classical.choice, Quot.sound]` (fail-closed `run_cmd`
  check over `Lean.collectAxioms` in `AxiomAudit.lean`; the module fails to compile if any
  declaration leaves the approved cone; private helper declarations are covered transitively
  through the public cones).
- **Forbidden-term scan**: no `sorry`/`axiom`/`admit`/`unsafe`/`native_decide`/`proof_wanted`
  outside documentation text.
- **Source hashes**: see `D12-heat-semigroup-analysis.json`.

## Next dependency requests

1. For the **compact-manifold construction** (next D13 task): a D11-core datum on a compact
   Riemannian manifold (kernel existence + Gaussian bounds + semigroup field), to be discharged
   against `CompactManifold*Obligation`; the Euclidean side is ready.
2. For **general L¹-strong continuity**: `∀ f : Lp ℝ 1 volume, ∃ φ continuous with compact support,
   snorm (f - φ) 1 ≤ ε` (C_c density in L¹ on `ℝⁿ`) — not present in the pinned mathlib snapshot;
   with it, the DCT template of `StrongContinuityL1.lean` extends the Gaussian-family witness to
   all integrable `f`.
3. For the **filter form** of the L¹ witness: the `IsCountablyGenerated (𝓝 (0 : ℝ))` /
   `FirstCountableTopology ℝ` instance (`Mathlib.Topology.Instances.Real` is not built in the
   pinned snapshot; building it is outside this worktree's mandate).

TASK_DONE
