# D12-spectral-sobolev — result card

Track: turn one spectral/Sobolev prerequisite into a theorem on an explicit torus.
Status: **TASK_DONE** (request for independent acceptance). Elapsed: ~1.5 h (first invocation).

## What was proved

All work lives under `release/Poincare/D12/SpectralSobolev/` (7 files), built from
`release/` with the pinned toolchain `leanprover/lean4:v4.34.0-rc2` and pinned
mathlib `7974e751bece493b6ff508039423ca9fa2452fa8` (unmodified, Apache-2.0).
D11 SpectralTorus has no output in its worktree yet; D12 is self-contained on
mathlib's `Analysis.Fourier.AddCircle` (fourierBasis, Parseval) — recorded as a
dependency request below.

### 1. Heat spectral-series convergence on the explicit 1-torus (dimension 1)

- `heatSeries_hasSum`: for every `T > 0`, `t ≥ 0`, `f ∈ L²(AddCircle T, haar)`,
  the full infinite series `∑' n, exp(-λₙt) cₙ(f) eₙ` with `λₙ = (2πn/T)²`
  converges in L² (no truncation anywhere; convergence is proved from Parseval's
  summable sequence via ℓ²).
- `heatEvolve_norm_le`: L² contraction `‖H_t f‖ ≤ ‖f‖`.
- `heatEvolve_tendsto_self`: strong L² convergence `H_t f → f` as `t → 0⁺`,
  proved with Tannery's theorem on the infinite coefficient series, dominated by
  the Parseval-summable sequence `n ↦ ‖cₙ(f)‖²`.
- `heatEvolve_zero`, `heatEvolve_add`: `H₀ f = f` and the semigroup law
  `H_s (H_t f) = H_{s+t} f` — a genuine one-parameter semigroup of contractions.
- `heatEvolve_fourierLp`, `norm_heatEvolve_fourierLp`, `heatWeight_lt_one_of_pos`:
  the character `fourier n` is an exact eigenfunction; for `t > 0`, `n ≠ 0` the
  weight is strictly below 1, so the dynamics is genuinely nontrivial
  (`heat_evolution_first_mode_nontrivial`).

### 2. Sharp Poincaré–Wirtinger inequality on the circle (dimension 1)

```
theorem poincare_wirtinger (hab : a < b) {f f' : ℝ → ℂ}
    (hderiv : ∀ x, x ∈ [[a, b]] → HasDerivAt f (f' x) x)
    (hper : f b = f a)                       -- descends to ℝ/(b-a)ℤ
    (hmean : fourierCoeffOn hab f 0 = 0)     -- mean zero, torus normalization
    (hintf' : IntervalIntegrable f' volume a b)
    (hL2f : MemLp f 2 (volume.restrict (Ioc a b)))
    (hL2f' : MemLp f' 2 (volume.restrict (Ioc a b))) :
    ∫ x in a..b, ‖f x‖ ^ 2 ≤ ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2
```

Proof is purely spectral and honest about the infinite series: Parseval
(`hasSum_sq_fourierCoeffOn`) for both L² norms, integration by parts
(`fourierCoeffOn_of_hasDerivAt`; the boundary term vanishes by periodicity) giving
`cₙ(f') = (2π i n/(b-a)) cₙ(f)` (`fourierCoeffOn_deriv_periodic`), and the mode
comparison `1 ≤ n²` for `n ≠ 0`.

### 3. Non-vacuity and optimality (concrete witnesses)

- `sine_wave_hypotheses`: the sine wave on the circle of length `2π` satisfies all
  six hypotheses of `poincare_wirtinger`.
- `poincare_wirtinger_sine`: downstream application — `∫₀^{2π} sin² ≤ ∫₀^{2π} cos²`.
- `poincare_wirtinger_sine_saturates`: equality, both sides equal π ≠ 0.
- `poincare_constant_sharp`: any constant C valid for all admissible functions on
  the length-`2π` circle satisfies `1 ≤ C` — the constant `((b-a)/2π)²` is optimal.

## Classification

Semantic class: **model** domain (the explicit 1-torus), with statements **general
within that domain** (arbitrary `a < b` / `T > 0`, arbitrary admissible functions).
No claim is made about general compact manifolds; chart/partition arguments and
general heat kernels remain outside scope.

Blockers closed: **none of the named U-blockers** (`exact_blockers_closed = []` —
legitimate); D12 supplies the explicit-torus spectral layer that the manifold
story will need.

## Evidence

- Compile: `lake build` from `release/` exits 0 (8953 jobs, whole package);
  `lake env lean` exits 0 on each authored file.
- Axioms: 36/36 new declarations depend only on `propext, Classical.choice,
  Quot.sound`; fail-closed programmatic audit (`tools/d12_axiom_audit.sh`) passes
  including a negative control; forbidden-token scan: 0 hard, 0 soft.
- Source hashes and the full JSON card: `longrun/results/D12-spectral-sobolev.json`.

## Next dependency requests

- D11-spectral-torus: please relay its SpectralTorus result card/module list so a
  compatibility statement between its torus setup and these theorems can be proved.
- For any future compact-manifold track: the chart/partition-of-unity transfer of
  this 1-torus spectral layer is the explicit next proof obligation.

TASK_DONE
