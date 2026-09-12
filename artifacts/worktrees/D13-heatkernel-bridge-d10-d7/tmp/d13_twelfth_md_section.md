
## 24. Twelfth invocation (2026-09-11T23:45+08:00, elapsed ≈ {{ELAPSED}} h): the Dirichlet gap and the long-time asymptotics of the pinned finite heat kernel

### 24.1 Baseline re-verification

Re-computed the 28 hashes recorded by the eleventh invocation (`sha256sum -c
logs/d13_eleventh_final_hashes.txt`): **28/28 OK, byte-identical**. Full `lake build` on the
untouched artifact: **exit 0, `Build completed successfully (9204 jobs)`, D6AUDIT PASS,
`D13HeatKernelBridgeAxiomCheck PASS 455/455`** (`logs/d13_eleventh_final_*`). The eleventh
invocation's artifact is reproducible; no completed work was restarted.

### 24.2 The gap: well-posedness without a rate

The ninth and tenth invocations made the pinned finite problem *well posed*: the matrix-exponential
kernel exists (`FiniteSpaceHeat.lean`), is unique (`FiniteUniqueness.lean`), and the conjugate
backward problem is likewise well posed (`FiniteConjugateUniqueness.lean`). The tenth invocation's
energy method gives antitonicity of the `ℓ²` energy, but antitonicity carries **no rate** and says
nothing about the limit at infinity. What was missing in the finite model is exactly the pair of
spectral facts on which the manifold heat-kernel long-time theory rests — a Poincaré (spectral-gap)
inequality and convergence of the kernel to the equilibrium measure — and "spectral theory" is one
of the analytic items listed as remaining manifold content of `D7-HEAT-KERNEL-EXISTENCE`
(`checkpoint.json`, `dependency_requests`). The twelfth invocation supplies both, quantitatively,
for the pinned finite model.

### 24.3 The Dirichlet form, the variance identity and the combinatorial gap (proved)

`FiniteErgodicity.lean` first isolates the quadratic form that the pinned operator controls. The
**Dirichlet form** is

`dirichletForm G u = (1/2) * ∑ x ∑ y, L x y * (u x - u y)^2`

(`dirichlet_inner_nonneg`, `dirichletForm_nonneg`); it is the negative of the quadratic form
(`dirichletForm_eq_neg_quadraticForm`, from the ninth invocation's Dirichlet identity) and it
vanishes **exactly on the constants** (`dirichletForm_eq_zero_iff`), because every off-diagonal
entry is strictly positive.

The quantitative ingredient is the elementary **variance identity**

`∑ x ∑ y, (u x - u y)^2 = 2 * card X * ∑ x, (u x)^2 - 2 * (∑ x, u x)^2`

(`sum_sq_sub_eq`), which on mean-zero functions reduces to
`∑ x ∑ y, (u x - u y)^2 = 2 * card X * energy u` (`sum_sq_sub_eq_of_meanZero`). Since the pinned
operator is a *complete* weighted graph, every off-diagonal entry dominates the minimal weight
`minWeight G` (`minWeight_le`, strictly positive by `minWeight_pos`), so for every mean-zero `u`

`card X * w * energy u ≤ dirichletForm G u`   (`dirichletForm_ge_of_weight`),

and with `w = minWeight G` the **combinatorial Dirichlet gap**

`dirichletGap G = card X * minWeight G`

is strictly positive (`dirichletGap_pos`) and satisfies the **Poincaré inequality**

`dirichletGap G * energy u ≤ dirichletForm G u`   (`poincare_inequality`).

This is a computable, strictly positive spectral-gap lower bound: no compactness, no spectral
theorem and no choice principle beyond the ambient classical logic are used.

### 24.4 Mean conservation, Gronwall decay and convergence to equilibrium (proved)

The pinned Laplacian annihilates the constants (`laplacian_one`); summed, `∑ x, Δ u x = 0`
(`sum_laplacian_eq_zero`), so the mean of a solution of `∂_t u = Δ u` has zero derivative
(`hasDerivAt_mean`). For a solution whose mean vanishes at every positive time, the
Gronwall-weighted energy `t ↦ exp (2 * Λ * t) * energy (u t)` has derivative
`exp (2 * Λ * t) * (2 * Λ * energy - 2 * dirichletForm) ≤ 0` by the Poincaré inequality, hence

`energy (u T) ≤ energy (u ε) * exp (-(2 * Λ) * (T - ε))`   (`energy_decay_of_meanZero`).

Applied to the canonical kernel, the deviation `x ↦ finiteHeatKernel G x y t - equilibrium x` from
the equilibrium (uniform) function `equilibrium x = (card X)⁻¹` is mean-zero for `t > 0`
(`finiteHeatKernel_column_sum`, `finiteHeatKernel_shift_meanZero`), solves the same equation
(`laplacian_sub_const`, `finiteHeatKernel_shift_hasDerivAt`), and has the Dirac energy
`1 - (card X)⁻¹` as `t → 0⁺` (`finiteHeatKernel_tendsto_entry`,
`energy_dirac_sub_equilibrium`, `finiteHeatKernel_shift_tendsto_energy`). Letting the lower endpoint
of the Gronwall inequality tend to `0⁺` therefore gives, for every `T > 0`,

`energy (K · y T - equilibrium) ≤ (1 - (card X)⁻¹) * exp (-(2 * Λ) * T)`
(`finiteHeatKernel_energy_decay`), the gap specialization
(`finiteHeatKernel_energy_decay_gap`), convergence of the energy to `0` at infinity
(`finiteHeatKernel_tendsto_equilibrium_energy`) and the pointwise bound

`|K x y t - (card X)⁻¹| ≤ sqrt (1 - (card X)⁻¹) * exp (-(Λ * t))`
(`finiteHeatKernel_pointwise_decay`).

### 24.5 Sharpness on the complete graph (proved)

For the complete-graph pinned operator the combinatorial bound is **attained**, so it is not a
vacuous estimate. The minimal off-diagonal weight is `1` (`completeGraphOperator_apply_of_ne`,
`completeGraphOperator_minWeight`), the gap is exactly `card X`
(`completeGraphOperator_dirichletGap`), and on every mean-zero function the Dirichlet form *equals*
`card X * energy` (`completeGraphOperator_dirichletForm_eq`), i.e. the Poincaré inequality is an
equality (`completeGraphOperator_poincare_attained`). The kernel itself has the closed form

`K x y t = (card X)⁻¹ + exp (-(card X) * t) * (δ x y - (card X)⁻¹)`

(`completeGraphKernelForm`, `completeGraphOperator_laplacian_kernelForm`,
`completeGraphKernelForm_hasDerivAt`, `completeGraphKernelForm_tendsto`,
`completeGraphOperator_finiteHeatKernel` — the last by the tenth invocation's uniqueness theorem),
and its squared deviation from equilibrium is *exactly* the decay bound
(`completeGraphOperator_energy_decay_sharp`, `completeGraphOperator_energy_decay_attained`). The
combinatorial gap is therefore the true spectral gap of the complete-graph Laplacian, and the
exponential rate of the abstract theorem is optimal.

### 24.6 D7-level consumption

`Poincare.D7.HeatKernel.ErgodicityStatus` records the statements at the D7 level, where
`finiteHeatKernel` is the kernel of the genuine legacy datum `finiteHeatKernelData`:
`finite_pinned_dirichlet_gap_pos`, `finite_pinned_poincare`,
`finite_pinned_kernel_energy_decay`, `finite_pinned_kernel_tendsto_equilibrium`,
`finite_pinned_kernel_pointwise_convergence`, `finite_pinned_equilibrium_invariant` (the uniform
function is an invariant state of the pinned semigroup), `finite_pinned_ergodicity_summary`, and the
complete-graph sharpness pair `finite_pinned_complete_graph_gap`,
`finite_pinned_complete_graph_sharp`. No legacy D7/D10/D11/D12 file is edited.

### 24.7 Declaration inventory (56 new declarations, all audited)

`FiniteErgodicity.lean` contributes 47 declarations: `meanZero`, `meanZero_sub_const`,
`dirichlet_inner_nonneg`, `dirichletForm`, `dirichletForm_nonneg`,
`dirichletForm_eq_neg_quadraticForm`, `sum_sq_sub_eq`, `sum_sq_sub_eq_of_meanZero`,
`dirichletForm_ge_of_weight`, `minWeight`, `minWeight_le`, `minWeight_pos`, `dirichletGap`,
`dirichletGap_pos`, `poincare_inequality`, `dirichletForm_eq_zero_iff`,
`completeGraphOperator_apply_of_ne`, `completeGraphOperator_apply_self`,
`completeGraphOperator_minWeight`, `completeGraphOperator_dirichletGap`,
`completeGraphOperator_dirichletForm_eq`, `completeGraphOperator_poincare_attained`,
`sum_laplacian_eq_zero`, `hasDerivAt_mean`, `energy_decay_of_meanZero`, `equilibrium`,
`one_sub_inv_card_nonneg`, `finiteHeatKernel_column_sum`, `finiteHeatKernel_shift_meanZero`,
`laplacian_sub_const`, `finiteHeatKernel_shift_hasDerivAt`, `finiteHeatKernel_tendsto_entry`,
`energy_dirac_sub_equilibrium`, `finiteHeatKernel_shift_tendsto_energy`,
`finiteHeatKernel_shift_energy_decay`, `finiteHeatKernel_energy_decay`,
`finiteHeatKernel_energy_decay_gap`, `finiteHeatKernel_tendsto_equilibrium_energy`,
`finiteHeatKernel_pointwise_decay`, `completeGraphKernelForm`, `sum_mul_one_apply`,
`completeGraphOperator_laplacian_kernelForm`, `completeGraphKernelForm_hasDerivAt`,
`completeGraphKernelForm_tendsto`, `completeGraphOperator_finiteHeatKernel`,
`completeGraphOperator_energy_decay_sharp`, `completeGraphOperator_energy_decay_attained`.
`Poincare.D7.HeatKernel.ErgodicityStatus` contributes 9 declarations (the D7 consumers listed in
§24.6). `All.lean` and `AxiomAudit.lean` are extended (docstring; 56 new `#print axioms`
transcripts, all 56 names added to `bridgeAuditedDeclarations`), so the audit count grows from
455 to **511**.

### 24.8 Honest scope

This is a theorem about the **pinned finite model**, in the same sense as the ninth and tenth
invocations: over a finite type with a symmetric, constant-annihilating operator with strictly
positive off-diagonal entries. It supplies the finite-dimensional counterpart of the spectral-gap
and long-time-asymptotic content of the manifold heat-kernel theory, but it is **not** a proof of
`D7-HEAT-KERNEL-EXISTENCE` (or of its conjugate sibling): the Laplace–Beltrami operator, the
manifold Poincaré inequality, elliptic/parabolic regularity, the parametrix and Gaussian bounds on
a Riemannian manifold remain open, and no named blocker is closed
(`exact_blockers_closed = []`). The hypotheses introduced by this invocation are explicit and
non-vacuous: the space must have two distinct points for a strictly positive gap, the rate `Λ` must
be positive for the limit at infinity, and `meanZero` is required exactly where the Poincaré
inequality is applied (it holds automatically for the kernel deviation by the checked column-sum
identity). All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted`; the axiom audit re-checks all 511 declarations against
`[propext, Classical.choice, Quot.sound]`.

### 24.9 Twelfth-invocation final gates

{{GATES}}

### 24.10 Twelfth-invocation verdict

**Progress, not closure.** The twelfth invocation adds the quantitative long-time theory of the
pinned finite heat kernel — Dirichlet form, variance identity, combinatorial Dirichlet gap,
Poincaré inequality, Gronwall energy decay, convergence to the equilibrium measure, and the
attained (sharp) complete-graph instance — with 56 new audited declarations (455 → 511) and two new
files (`FiniteErgodicity.lean`, `ErgodicityStatus.lean`); it closes no named blocker and does not
claim `D7-HEAT-KERNEL-EXISTENCE`. `exact_blockers_closed = []`. TASK_DONE is requested only as an
independent-acceptance request for this checked increment.
