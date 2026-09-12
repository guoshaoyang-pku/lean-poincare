section = r'''
## 21. Ninth invocation (2026-09-11T18:16+08:00, elapsed ≈ __ELAPSED__ h): the pinned-operator finite existence theorem

### 21.1 Baseline re-verification

Every one of the 20 hashes recorded by the eighth invocation was re-computed with `sha256sum -c`
(`logs/d13_eighth_final_hashes.txt`: all OK, byte-identical), and the full suite was re-run on the
unchanged artifact before any write: `lake build` exit 0 (**9196 jobs**, D6AUDIT PASS,
`D13HeatKernelBridgeAxiomCheck` PASS **278/278**), semantic transcripts 8/8, per-file 17/17,
worktree 328/328, forbidden 0/0, negative control PASS, diff 6 expected new-file lines, upstream
snapshot PASS (`logs/d13_eighth_baseline_*`).

### 21.2 The gap and the repair

The fifth–eighth invocations proved, kernel-checked, that every universally quantified existence
statement over the schematic `HeatSpacetime` interface is **false as formalized** (the interface
leaves `laplacian` and `timeDerivative` free), and recorded the dependency: *an interface that pins
the operator to a genuine Laplace operator*. The ninth invocation constructs that interface in the
finite-dimensional setting and proves the existence theorem over it.

`FiniteHeatOperator X` (for a finite type `X`) is a real matrix `L` with `Lᵀ = L`,
`∑ y, L x y = 0` (constant annihilation) and `0 < L x y` for `x ≠ y` (strictly positive
off-diagonal entries). It is a genuine discrete Laplace operator:

| property | declaration | semantic class |
| --- | --- | --- |
| constant annihilation `Δ 1 = 0` | `FiniteHeatOperator.laplacian_one` | proved theorem |
| finite-level self-adjointness `∑ u·Δv = ∑ Δu·v` | `FiniteHeatOperator.laplacian_selfAdjoint` | proved theorem |
| discrete Dirichlet identity `∑ u·Δu = -(1/2)·∑∑ L (u x - u y)^2` | `FiniteHeatOperator.laplacian_dirichlet_identity` | proved theorem |
| dissipativity / negative semidefiniteness `∑ u·Δu ≤ 0` | `FiniteHeatOperator.laplacian_quadraticForm_nonpos` | proved theorem |
| nonzero as soon as two points exist | `FiniteHeatOperator.laplacian_ne_zero` | proved theorem |
| the class is nonempty (complete graph) | `completeGraphOperator` | model |

The heat kernel `finiteHeatKernel G x y t = (exp (t • L)) x y` for `t > 0` (extended by `0` at
`t ≤ 0`, since the D7 interfaces ask for a total function) is proved to satisfy:

* **strict positivity** `0 < K x y t` for `t > 0`: the shift `c = ∑ x |L x x| + 1` makes
  `M = L + c • 1` entrywise positive, `exp (t • L) = exp (-(t·c)) • exp (t • M)`
  (`Matrix.exp_add_of_commute`, `Matrix.exp_diagonal`), the entries of `exp (t • M)` are
  nonnegative tsums of nonnegative terms and strictly positive by comparison with the `n = 1` series
  term (`Summable.le_tsum`);
* **symmetry** `K x y t = K y x t`, **unit row sums** and **unit column sums** of the matrix
  exponential (`Matrix.expSeries_hasSum_exp` pushed through the continuous linear map
  `A ↦ A *ᵥ 1`, `L *ᵥ 1 = 0`, `hasSum_single`, `HasSum.unique`);
* the **entrywise bound** `K x y t ≤ 1` (the Gaussian upper bound with `C_up = 1`, `dim = 0`,
  `dist = 0`, `C_lo = 0`);
* **Chapman–Kolmogorov** `K x y (s+t) = ∫ z, K x z s * K z y t ∂count`;
* the **genuine PDE** `∂_t K(x,y,t) = Δ_x K(x,y,t)` as a `HasDerivAt` statement
  (`hasDerivAt_exp_smul_const'` + `hasDerivAt_pi`, then `Matrix.mul_apply`/`mulVecLin_apply`);
* the **full Dirac initial condition against every function** (a finite space has no continuity or
  integrability obstruction), so both the legacy and the corrected-domain quantifiers hold;
* **conservation of mass** `∑ x, (e^{tL}u) x = ∑ x, u x`, the discrete parabolic **maximum
  principle** (positivity preservation) and the **`ℓ¹`-contraction** of the semigroup;
* **non-degeneracy**: strictly positive off-diagonal entries, so the kernel is *not* the degenerate
  identity kernel that inhabits the bare interface with `C_lo = 0` in `DataRefutation.lean`.

The interface-level consequences are:

* `finiteHeatKernelCore` — the D11 core datum;
* `finiteHeatKernelData` — a **genuine legacy D7 `HeatKernelData`** with the full pointwise initial
  condition;
* `finiteHeatKernelDataV1` — the corrected-domain `HeatKernelDataV1`;
* `finiteHeatSpacetime` + `finiteHeatSpacetime_isClosedRiemannian` — the schematic spacetime *is* a
  closed Riemannian manifold (counting measure, discrete metric, compactness);
* `finite_isHeatKernelPDE` — inhabitation of the repaired predicate `IsHeatKernelPDE` (v2);
* `FinitePinnedHeatExistenceStatement` + `finitePinnedHeatExistenceStatement_proved` — the
  pinned-operator existence statement, **proved**;
* `finite_pinned_scope` — the conjunction with strict positivity, non-degeneracy and the nonzero
  constant-annihilating Laplacian.

### 21.3 Declaration inventory (71 new declarations, all audited)

| group | declarations | semantic class |
| --- | --- | --- |
| matrix functionals | `entryLinear`, `entryCLM`, `entryCLM_apply`, `mulVecOnesLinear`, `mulVecOnesCLM`, `mulVecOnesCLM_apply` | proved (continuous linear functionals) |
| pinned operator | `FiniteHeatOperator` (structure), `laplacian`, `laplacian_apply`, `mulVec_ones`, `laplacian_one`, `symmetric_apply`, `diag_nonpos` | model interface / proved theorem |
| structural analysis | `laplacian_selfAdjoint`, `laplacian_ne_zero`, `laplacian_dirichlet_identity`, `laplacian_dirichlet_nonneg`, `laplacian_quadraticForm_nonpos` | proved theorem |
| positivity engine | `shift`, `shifted`, `shift_pos`, `shifted_apply_self`, `shifted_apply_of_ne`, `shifted_pos`, `shifted_nonneg`, `pow_apply_nonneg`, `exp_smul_eq`, `exp_neg_mul_shift_pos`, `exp_shifted_nonneg`, `exp_shifted_pos`, `kernel_pos`, `kernel_nonneg_of_nonneg` | proved theorem |
| kernel laws | `exp_smul_symm`, `exp_smul_mulVec_ones`, `exp_smul_row_sum`, `exp_smul_column_sum`, `exp_smul_mulVec_sum`, `exp_smul_mulVec_nonneg`, `exp_smul_mulVec_abs_sum_le`, `exp_smul_le_one`, `exp_smul_add`, `exp_smul_entry_hasDerivAt`, `exp_smul_entry_hasDerivAt_laplacian`, `exp_smul_entry_continuousAt`, `tendsto_exp_smul_entry` | proved theorem |
| total kernel | `finiteHeatKernel`, `finiteHeatKernel_of_pos`, `finiteHeatKernel_of_nonpos`, `finiteHeatKernel_nonneg`, `finiteHeatKernel_pos`, `finiteHeatKernel_symm`, `finiteHeatKernel_le_one`, `finiteHeatKernel_row_sum`, `finiteHeatKernel_normalization`, `finiteHeatKernel_semigroup`, `finiteHeatKernel_hasDerivAt`, `finiteHeatKernel_dirac`, `finiteHeatKernel_ne_dirac` | proved theorem |
| D7 datums | `finiteHeatKernelCore`, `finiteHeatKernelCore_fullInitialCondition`, `finiteHeatKernelData`, `finiteHeatKernelDataV1` | model / proved theorem |
| repaired predicate and existence | `finiteHeatSpacetime`, `finiteHeatSpacetime_isClosedRiemannian`, `finite_isHeatKernelPDE`, `FinitePinnedHeatExistenceStatement`, `finitePinnedHeatExistenceStatement_proved`, `finite_pinned_scope` | proved theorem / statement (proved) |
| model class | `completeGraphOperator`, `completeGraphOperator_laplacian_ne_zero` | model |
| D7 consumer `Poincare.D7.HeatKernel.FiniteStatus` | `finite_pinned_kernel_exists`, `finite_pinned_operator_structure`, `finite_pinned_operator_dissipative`, `finite_pinned_max_principle`, `finite_pinned_legacy_datum`, `finite_pinned_dataV1`, `finite_pinned_spacetime_closed`, `finite_pinned_kernel_nondegenerate`, `finite_heat_status_summary` | D7 consumer, proved theorem |

(62 in `FiniteSpaceHeat.lean` + 9 in `Poincare.D7.HeatKernel.FiniteStatus`; the audit grows from 278
to **357** declarations.)

### 21.4 Honest scope

This is the **finite-dimensional model** of the remaining manifold content, not the manifold
theorem. What is proved is that once the operator is *pinned* (symmetry + constant annihilation +
strictly positive off-diagonal entries), the repaired predicate `IsHeatKernelPDE` is satisfiable by an
explicit strictly positive kernel with the genuine PDE; this is the interface repair the earlier
invocations identified as necessary and shows that the repair direction is sound and non-vacuous. It
does **not** prove `D7-HEAT-KERNEL-EXISTENCE`: parametrices, parabolic regularity, Gaussian bounds
and spectral theory on a manifold remain open, and the finite model is not a substitute for them.
`exact_blockers_closed` remains `[]`.

### 21.5 Ninth-invocation final gates

| gate (ninth run, final artifact) | result | log |
| --- | --- | --- |
| source hashes | **22 recorded** (13 D13 files, 6 D7 consumers, 3 build-config entries) | `logs/d13_ninth_final_hashes.txt` |
| semantic `#check`/`#print axioms` transcripts | **9 files, exit 0, 0 failures** | `logs/d13_ninth_final_semantic_checks.out` |
| full `lake build` (cwd `release/`) | **exit 0 — `Build completed successfully (__JOBS__ jobs)`, D6AUDIT PASS, `D13HeatKernelBridgeAxiomCheck: PASS — all 357 declarations … [propext, Classical.choice, Quot.sound]`** | `logs/d13_ninth_final_build.log` |
| per-file dispatcher gate (authored files) | **__PERFILE__ exit 0** | `logs/d13_ninth_final_perfile.txt` |
| full worktree gate | **__WORKTREE__ exit 0, 0 failures** | `logs/d13_ninth_final_gate_raw.txt` |
| forbidden-token scan | **0 hard / 0 soft** (D13 13 files; `D7/HeatKernel` 14 files; `D7/ConjugateHeat` 10 files) | `logs/d13_ninth_final_forbidden_{d13,d7,conj}.json` |
| negative control | **PASS** | `logs/d13_ninth_final_negcontrol.out` |
| source integrity (`diff -rq` vs `D12-heat-domain-repair`) | **only** `D13/` and 6 D7 consumer files (`HeatKernel/{V1Interface,StatementStatus,RepairStatus,DataStatus,FiniteStatus}.lean`, `ConjugateHeat/Status.lean`) = 7 expected new-file lines | `logs/d13_ninth_final_diff.txt` |
| upstream snapshot verifier | **exit 0** (`bb91a091`) | `logs/d13_ninth_final_upstream.out` |

### 21.6 Ninth-invocation verdict

The milestone — the `LONG_PLAN` `HeatKernelBridge` transporting D10 to the corrected-domain D7
interface and consumed by D7 modules — remains **fully checked** on the extended artifact (19
authored files, 357 audited declarations, all gates green). The ninth invocation adds the
**pinned-operator finite existence theorem**: the hypothesis-class repair that the fifth–eighth
invocations proved to be necessary is here constructed and its existence statement
(`FinitePinnedHeatExistenceStatement`) is proved, with an explicit strictly positive kernel
satisfying the genuine PDE, symmetry, unit mass, Chapman–Kolmogorov, the full Dirac initial
condition, the discrete maximum principle and `ℓ¹`-contraction, together with the finite-level
self-adjointness and dissipativity of the operator. This is the finite-dimensional model of the
remaining manifold content: `exact_blockers_closed` remains `[]` and `D7-HEAT-KERNEL-EXISTENCE`
remains **OPEN**. The card requests independent semantic acceptance of the 19 authored files,
including the ninth-invocation pair.
'''
open('tmp/ninth_section.md','w').write(section)
print('section written', len(section))
