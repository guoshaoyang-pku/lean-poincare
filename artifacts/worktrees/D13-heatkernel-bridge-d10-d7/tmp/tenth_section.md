
## 22. Tenth invocation (2026-09-11T18:51+08:00, elapsed ≈ 0.6 h): existence **and uniqueness** for the pinned finite heat kernel, and the conjugate half

### 22.1 Baseline re-verification

Every one of the 22 hashes recorded by the ninth invocation was re-computed with `sha256sum -c`
(`logs/d13_ninth_final_hashes.txt`: all OK, byte-identical), and the full suite was re-run on the
unchanged artifact before any write: `lake build` exit 0 (**9198 jobs**, D6AUDIT PASS,
`D13HeatKernelBridgeAxiomCheck` PASS **357/357**) — `logs/d13_tenth_baseline_build.log`.

### 22.2 The gap: the ninth invocation proved existence, not uniqueness

The ninth invocation constructed, for every *pinned* finite Laplace operator `G`
(`FiniteHeatOperator`: symmetric, constant-annihilating, strictly positive off-diagonal), the
explicit matrix-exponential kernel `finiteHeatKernel G` and proved that it inhabits the repaired
D7 predicate `IsHeatKernelPDE`. Existence alone does not make it **the** heat kernel of `G`. The
tenth invocation closes that gap by the classical energy method, entirely at the finite level, and
extends the same machinery to the conjugate (backward) half of the interface.

### 22.3 The energy method (forward): `FiniteUniqueness.lean`

For a function `u : X → ℝ` on the finite space, `FiniteHeatOperator.energy G u = ∑ x, (u x)^2`.
Along a solution of `∂_t u = Δ u`:

| declaration | content | semantic class |
| --- | --- | --- |
| `energy_nonneg`, `energy_eq_zero_iff` | `0 ≤ energy`, and `energy = 0 ↔ u = 0` | proved theorem |
| `hasDerivAt_energy_of` / `hasDerivAt_energy` | `d/dt energy = 2 ∑ x, u x · ∂_t u x`; in the heat-equation case `= 2 ∑ x, u x · Δ u x` | proved theorem |
| `energy_antitoneOn` | on `[ε, T]`, `0 < ε ≤ T`, the energy of a solution is antitone: the derivative is `2 ∑ u Δu ≤ 0` by `laplacian_quadraticForm_nonpos` | proved theorem |
| `tendsto_energy_zero` | if every component of `u` tends to `0` as `t → 0⁺`, so does the energy | proved theorem |
| `eq_zero_of_hasDerivAt_of_tendsto_zero` | a solution with zero initial limit vanishes identically for `t > 0` | proved theorem |
| `eq_of_hasDerivAt_of_tendsto` | two solutions with the same initial limit coincide for `t > 0` | proved theorem |

The passage from the interface to pointwise data is done by the **singleton test functions**
`singleFun y = 1_{y}`: they are continuous (discrete topology) and integrable for the counting
measure, hence admissible members of both D12 standard classes
(`continuousIntegrableClass_singleFun`, `continuousCompactSupportClass_singleFun`,
`hasCompactSupport_singleFun`, `integrable_singleFun`, `count_isFiniteMeasureOnCompacts`). The
Dirac limit of `IsHeatKernelPDE` against `singleFun z` is exactly the pointwise initial data
`K z y t → if z = y then 1 else 0` (`IsHeatKernelPDE.tendsto_singleFun`), and the canonical kernel
satisfies the same limit (`finiteHeatKernel_tendsto_singleFun`).

### 22.4 Kernel uniqueness and D7-level well-posedness

| declaration | content | semantic class |
| --- | --- | --- |
| `eq_of_pde_of_dirac` | two kernels with the same pinned Laplacian, the genuine PDE and the same pointwise Dirac data agree for `t > 0` | proved theorem |
| `eq_finiteHeatKernel_of_pde_of_dirac` | every such kernel **is** `finiteHeatKernel G` for `t > 0` | proved theorem |
| `eq_finiteHeatKernel_of_isHeatKernelPDE` | every `IsHeatKernelPDE` inhabitant over the finite counting-measure spacetime with the pinned Laplacian equals the canonical kernel | proved theorem |
| `IsHeatKernelPDE.eq_of_same` | any two `IsHeatKernelPDE` inhabitants over the same finite spacetime agree | proved theorem |
| `exists_unique_finiteHeatKernel` | among causal kernels (`K = 0` for `t ≤ 0`) the pinned PDE problem with the pointwise Dirac data has **exactly one** solution | proved theorem |

The D7 consumer `Poincare.D7.HeatKernel.UniquenessStatus` records the result at the D7 level:
`finite_pinned_kernel_unique`, `finite_pinned_interface_unique`,
`finite_pinned_canonical_unique`, `finite_pinned_exists_unique`, and the summary
`finite_pinned_wellposed_summary` (existence ∧ uniqueness ∧ identification of the witness).

### 22.5 The conjugate half: Grönwall-weighted energy and backward uniqueness

The conjugate heat equation is *backward* in time, so the plain energy inequality only bounds later
times by earlier ones. `FiniteConjugateUniqueness.lean` supplies the correct Grönwall-weighted
argument: for `∂_t u = -A u` with `-(C * energy u) ≤ ∑ x, u x · A u x`, the reversed function
`s ↦ u (t₀ - s)` has energy `E' ≤ 2 C E`, so `s ↦ exp (-(2 C) s) * E s` is antitone
(`exp_energy_antitoneOn`), and a solution with zero terminal limit vanishes below `t₀`
(`eq_zero_of_backward_hasDerivAt_of_tendsto`); two solutions with the same terminal limit coincide
(`eq_of_backward_hasDerivAt_of_tendsto`, `eq_of_conjugatePDE_of_tendsto`). Applied to the repaired
conjugate predicate:

* `IsConjugateHeatKernelPDE.tendsto_singleFun` — the terminal Dirac limit against singletons is
  the pointwise terminal data;
* `IsConjugateHeatKernelPDE.eq_of_same` — any two inhabitants over the same finite
  counting-measure spacetime agree below `t₀`;
* `finiteConjugateKernel G t₀ x y t = finiteHeatKernel G x y (t₀ - t)` — the canonical
  time-reversed kernel, with `finiteConjugateKernel_pos`, `finiteConjugateKernel_hasDerivAt`,
  `finiteConjugateKernel_tendsto_singleFun`, `finiteConjugateKernel_anticausal` and the
  inhabitant `finite_isConjugateHeatKernelPDE`;
* `eq_finiteConjugateKernel_of_isConjugateHeatKernelPDE` — identification of every inhabitant with
  the canonical kernel;
* `exists_unique_finiteConjugateKernel` — among anticausal kernels the conjugate problem with the
  pointwise terminal Dirac data has **exactly one** solution.

The D7 consumer `Poincare.D7.ConjugateHeat.UniquenessStatus` records
`finite_conjugate_interface_unique`, `finite_conjugate_canonical_unique`,
`finite_conjugate_exists_unique` and `finite_conjugate_wellposed_summary`.

### 22.6 Declaration inventory (52 new declarations, all audited)

| group | declarations | semantic class |
| --- | --- | --- |
| energy functional | `energy`, `energy_nonneg`, `energy_eq_zero_iff`, `hasDerivAt_energy_of`, `hasDerivAt_energy`, `energy_antitoneOn`, `tendsto_energy_zero`, `eq_zero_of_hasDerivAt_of_tendsto_zero`, `eq_of_hasDerivAt_of_tendsto` | proved theorem (energy method) |
| singleton test functions | `singleFun`, `singleFun_apply_self`, `singleFun_apply_of_ne`, `singleFun_apply`, `continuous_singleFun`, `integrable_singleFun`, `continuousIntegrableClass_singleFun`, `count_isFiniteMeasureOnCompacts`, `hasCompactSupport_singleFun`, `continuousCompactSupportClass_singleFun` | proved theorem |
| Dirac data and kernel uniqueness | `IsHeatKernelPDE.tendsto_singleFun`, `finiteHeatKernel_tendsto_singleFun`, `finiteHeatKernel_causal`, `eq_of_pde_of_dirac`, `eq_finiteHeatKernel_of_pde_of_dirac`, `eq_finiteHeatKernel_of_isHeatKernelPDE`, `IsHeatKernelPDE.eq_of_same`, `exists_unique_finiteHeatKernel` | proved theorem (uniqueness) |
| D7 consumer `Poincare.D7.HeatKernel.UniquenessStatus` | `finite_pinned_kernel_unique`, `finite_pinned_interface_unique`, `finite_pinned_canonical_unique`, `finite_pinned_exists_unique`, `finite_pinned_wellposed_summary` | D7 consumer, proved theorem |
| Grönwall energy / backward uniqueness | `tendsto_const_sub_nhdsGT`, `exp_energy_antitoneOn`, `eq_zero_of_backward_hasDerivAt_of_tendsto`, `eq_of_backward_hasDerivAt_of_tendsto` | proved theorem (Grönwall energy method) |
| conjugate interface | `IsConjugateHeatKernelPDE.tendsto_singleFun`, `eq_of_conjugatePDE_of_tendsto`, `IsConjugateHeatKernelPDE.eq_of_same` | proved theorem |
| finite conjugate model | `finiteConjugateSpacetime`, `finiteConjugateKernel`, `finiteConjugateKernel_pos`, `finiteConjugateKernel_hasDerivAt`, `finiteConjugateKernel_tendsto_singleFun`, `finiteConjugateKernel_anticausal`, `finite_isConjugateHeatKernelPDE`, `eq_finiteConjugateKernel_of_isConjugateHeatKernelPDE`, `exists_unique_finiteConjugateKernel` | model / proved theorem |
| D7 consumer `Poincare.D7.ConjugateHeat.UniquenessStatus` | `finite_conjugate_interface_unique`, `finite_conjugate_canonical_unique`, `finite_conjugate_exists_unique`, `finite_conjugate_wellposed_summary` | D7 consumer, proved theorem |

(27 in `FiniteUniqueness.lean` + 16 in `FiniteConjugateUniqueness.lean` + 5 in the D7 heat-kernel
consumer + 4 in the D7 conjugate consumer = 52; the audit grows from 357 to **409** declarations.)

### 22.7 Honest scope

This is the **finite-dimensional uniqueness and well-posedness theorem**, not the manifold
theorem. What is proved is that once the operator is pinned, the repaired finite interface problem
(existence, uniqueness, and identification with the explicit matrix-exponential kernel) is well
posed on positive times, and the same for the conjugate (backward) problem with the Grönwall
weight. It does **not** prove `D7-HEAT-KERNEL-EXISTENCE` or its conjugate sibling: parametrices,
parabolic regularity, Gaussian bounds, spectral theory and manifold backward uniqueness remain
open, and the finite model is not a substitute for them. `exact_blockers_closed` remains `[]`.

### 22.8 Tenth-invocation final gates

PLACEHOLDER_GATES

### 22.9 Tenth-invocation verdict

PLACEHOLDER_VERDICT
