
## 23. Eleventh invocation (2026-09-11T19:25+08:00, elapsed ≈ 4.0 h): the scalar-curvature term — the second defect of the conjugate predicate and its repair

### 23.1 Baseline re-verification

Re-computed the 26 hashes recorded by the tenth invocation (`sha256sum -c
logs/d13_tenth_final_hashes.txt`): **26/26 OK, byte-identical**
(`logs/d13_eleventh_baseline_hashes_check.txt`). Full `lake build` on the untouched artifact:
**exit 0, `Build completed successfully (9202 jobs)`, D6AUDIT PASS,
`D13HeatKernelBridgeAxiomCheck PASS 409/409`** (`logs/d13_eleventh_baseline_build.log`). The tenth
invocation's artifact is reproducible; no completed work was restarted.

### 23.2 The gap: unit mass versus scalar curvature

The tenth invocation closed the conjugate half of the finite pinned problem for the predicate
`IsConjugateHeatKernelPDE` (v2), whose fields are strict positivity, the genuine backward PDE
`∂_t K(x,y,t) = -Δ_x K(·,y,t)(x) + R(x)·K(x,y,t)` on `t < t₀`, **unit mass**
`∫_M K x y t dV = 1` for all `t < t₀`, and the terminal Dirac limit on a D12 admissible class.
The transported D10 Euclidean datum always has `R = 0` (it is the kernel of the flat Laplacian,
whose scalar curvature vanishes), so v2 was sufficient for the transport. But the operator of a
genuine Ricci-flow conjugate heat equation carries the scalar-curvature term `R ≠ 0`, and for such
an operator unit mass is *not* the correct normalization: the mass of a solution changes at rate
`∫ R K dV`. The eleventh invocation isolates this defect, proves it, and supplies the corrected
predicate together with its finite well-posedness theorem.

### 23.3 The mass law and the obstruction (proved)

`ConjugateScalarCurvature.lean` first proves the **mass law**: for any finite pinned Laplace
operator `G` and any coefficient function `R`, a pointwise solution of the conjugate equation has

`d/dt ∑ x, K x y t = ∑ x, R x · K x y t`

(`hasDerivAt_sum_of_solvesPDE`). The Laplacian term drops out because the pinned matrix has
vanishing column sums (symmetry plus conservation), so the only contribution is the curvature term.

Consequently (`sum_scalarMul_eq_zero_of_isConjugateHeatKernelPDE`), every inhabitant of v2 over the
finite pinned spacetime satisfies `∑ x, R x · K x y t = 0` for every `t < t₀`: its mass is
identically `1`, so its derivative is `0`, while the mass law identifies the derivative with the
curvature mass. This is a genuine restriction, not a technicality:

* `not_exists_isConjugateHeatKernelPDE_of_nonneg_scalarMul` — if `R ≥ 0` and `R` is positive
  somewhere, v2 has **no inhabitant at all** over the finite pinned spacetime: strict positivity
  makes the curvature mass strictly positive at every `y` and `t < t₀`, while v2 forces it to
  vanish.
* `not_exists_isConjugateHeatKernelPDE_bool_scalarCurvature` — the concrete two-point instance with
  the complete-graph pinned operator and `R = 1` (non-vacuity of the refutation).

So the `normalized` field of v2, not its PDE field, is what excludes scalar curvature: v2 can only
ever describe the `R = 0` (or curvature-orthogonal) case.

### 23.4 The repaired predicate (v3) and the curvature kernel

The corrected predicate `IsConjugateHeatKernelPDEMassLaw` (version tag `.v3 = 3`) keeps strict
positivity, the genuine PDE and the terminal Dirac condition, and replaces the unit-mass field by

* the **mass law** `HasDerivAt (fun s => ∫ x, K x y s) (∫ x, R(x)·K x y t)` for `t < t₀`, and
* the **terminal normalization** `∫ x, K x y t → 1` as `t → t₀⁻`.

The explicit **curvature kernel**

`finiteConjKernelWith G R t₀ x y t = exp ((t₀ - t) • (L - diag R)) x y` for `t < t₀`, and `0`
for `t₀ ≤ t` (the anticausal clipping),

inhabits v3 for **every** coefficient function `R` (`finite_isConjugateHeatKernelPDEMassLaw`):

* *strict positivity*: with the shift `c = ∑ x, |L x x - R x| + 1`, the matrix
  `(L - diag R) + c • 1` has strictly positive entries (diagonal by the shift, off-diagonal by the
  pinned operator), so `exp (s • A) = exp (-(s c)) • exp (s • (A + c • 1))` is entrywise positive
  for `s > 0` (`exp_smul_shift_eq`, `exp_smul_pos_of_pos_entries`, `curvatureShifted_pos`);
* *the PDE*: the chain rule for the time reversal (`reversed_exp_entry_hasDerivAt`) and the
  generator identity
  `(A * exp (s • A)) x y = Δ_x (exp (s • A)) (·,y) − R x · exp (s • A) x y`
  (`scalarCurvatureGenerator_mul_exp_apply`);
* *the mass law and terminal mass*: `finiteConjKernelWith_mass_hasDerivAt` (from the general mass
  law) and `finiteConjKernelWith_mass_tendsto` (terminal mass `1`);
* *the terminal Dirac condition*: `finiteConjKernelWith_tendsto_singleFun` and
  `finiteConjKernelWith_dirac`, from continuity of the matrix exponential at `0`
  (`tendsto_exp_smul_entry`).

### 23.5 Well-posedness and no loss

Uniqueness needs no new energy argument: the Grönwall-weighted backward energy theorem of the tenth
invocation applies verbatim with the curvature bound `-(∑ x, |R x|) · E u ≤ ∑ x, u x · R x · u x`
(`scalarCurvature_energy_bound`). Hence

* `eq_finiteConjKernelWith_of_isConjugateHeatKernelPDEMassLaw` — every v3 inhabitant over the finite
  pinned spacetime (with singletons admissible) is the curvature kernel below `t₀`;
* `exists_unique_finiteConjKernelWith` — among anticausal kernels the curvature conjugate problem
  with the pointwise terminal Dirac data has exactly one solution;
* `isConjugateHeatKernelPDEMassLaw_of_isConjugateHeatKernelPDE` — every v2 inhabitant is a v3
  inhabitant (the mass law follows from the PDE, the terminal normalization from the Dirac limit
  against the constant function, which is admissible for the integrable class,
  `continuousIntegrableClass_const_one`). The repair therefore loses no solution; it only admits the
  curvature solutions that v2's normalization field excludes.

The new D7 consumer **`Poincare.D7.ConjugateHeat.ScalarCurvatureStatus`** records all of this at the
D7 level: `conjugate_normalization_forces_curvature_mass_zero`,
`no_conjugate_kernel_of_nonneg_scalar_curvature`, `finite_conjugate_mass_law`,
`finite_conjugate_scalar_curvature_witness`, `finite_conjugate_scalar_curvature_exists_unique`,
`finite_conjugate_scalar_curvature_canonical_unique` and
`conjugate_scalar_curvature_status_summary`.

### 23.6 Declaration inventory (46 new declarations, all audited)

| group | declarations | semantic class |
| --- | --- | --- |
| general matrix exponential | `exp_smul_shift_eq`, `exp_smul_pos_of_pos_entries`, `exp_smul_entry_hasDerivAt`, `reversed_exp_entry_hasDerivAt`, `tendsto_exp_smul_entry` | proved theorem (general matrix exponential) |
| scalar-curvature operator | `scalarMulLin`, `scalarMulLin_apply_apply`, `scalarMulLin_selfAdjoint`, `finiteConjugateSpacetimeWith`, `finiteConjugateSpacetimeWith_zero` | definition / proved theorem |
| mass law and v2 obstruction | `hasDerivAt_sum_of_solvesPDE`, `sum_scalarMul_eq_zero_of_isConjugateHeatKernelPDE`, `not_exists_isConjugateHeatKernelPDE_of_nonneg_scalarMul`, `not_exists_isConjugateHeatKernelPDE_bool_scalarCurvature` | proved theorem (refutation) |
| curvature generator | `FiniteHeatOperator.scalarCurvatureGenerator`, `curvatureShift`, `curvatureShifted`, `curvatureShift_pos`, `curvatureShifted_apply_self`, `curvatureShifted_apply_of_ne`, `curvatureShifted_pos` | definition / proved theorem |
| curvature kernel | `finiteConjKernelWith`, `finiteConjKernelWith_of_lt`, `finiteConjKernelWith_of_ge`, `finiteConjKernelWith_pos`, `scalarCurvatureGenerator_mul_exp_apply`, `finiteConjKernelWith_hasDerivAt`, `finiteConjKernelWith_mass_hasDerivAt`, `finiteConjKernelWith_tendsto_singleFun`, `finiteConjKernelWith_mass_tendsto`, `finiteConjKernelWith_dirac` | model / proved theorem |
| v3 predicate and well-posedness | `IsConjugateHeatKernelPDEMassLaw`, `.v3`, `finite_isConjugateHeatKernelPDEMassLaw`, `scalarCurvature_energy_bound`, `eq_finiteConjKernelWith_of_isConjugateHeatKernelPDEMassLaw`, `exists_unique_finiteConjKernelWith`, `isConjugateHeatKernelPDEMassLaw_of_isConjugateHeatKernelPDE`, `continuousIntegrableClass_const_one` | definition / proved theorem |
| D7 consumer `Poincare.D7.ConjugateHeat.ScalarCurvatureStatus` | `conjugate_normalization_forces_curvature_mass_zero`, `no_conjugate_kernel_of_nonneg_scalar_curvature`, `finite_conjugate_mass_law`, `finite_conjugate_scalar_curvature_witness`, `finite_conjugate_scalar_curvature_exists_unique`, `finite_conjugate_scalar_curvature_canonical_unique`, `conjugate_scalar_curvature_status_summary` | D7 consumer, proved theorem |

The fail-closed `AxiomAudit` grows from 409 to **455** declarations, all depending only on
`[propext, Classical.choice, Quot.sound]`.

### 23.7 Honest scope

This is the finite-dimensional pinned model of the conjugate heat equation with a scalar-curvature
term. It does **not** prove manifold conjugate existence or backward uniqueness, it does not change
the D10 transport (which is the special case `R = 0` and remains as in §3–§8), and it closes no
named blocker: `exact_blockers_closed = []`, and `D7-HEAT-KERNEL-EXISTENCE` and its conjugate
sibling remain **OPEN**. What it does establish is the exact shape of the honest normalized
statement for the conjugate half: the unit-mass field of `IsConjugateHeatKernelPDE` must be replaced
by the mass law plus terminal normalization as soon as `R ≠ 0`, and on the finite pinned model that
statement is well posed. The D7 consumer `Poincare.D7.ConjugateHeat.ScalarCurvatureStatus` is the
downstream checked use.

### 23.8 Eleventh-invocation final gates

| gate (eleventh run, final artifact) | result | log |
| --- | --- | --- |
| source hashes | **{HASHES} recorded** (16 `D13` files, 9 `D7` consumers, 3 build-config entries) | `logs/d13_eleventh_final_hashes.txt` |
| semantic `#check`/`#print axioms`/`example` transcripts | **{SEM_FILES} files, exit 0, {SEM_FAIL} failures** | `logs/d13_eleventh_final_semantic_checks.out` |
| full `lake build` (cwd `release/`) | **exit {BUILD_EXIT} — `Build completed successfully ({JOBS} jobs)`, D6AUDIT PASS, `D13HeatKernelBridgeAxiomCheck: PASS — all {AXIOM} declarations … [propext, Classical.choice, Quot.sound]`** | `logs/d13_eleventh_final_build.log` |
| per-file dispatcher gate (authored files) | **{PERFILE} exit 0, 0 failures** | `logs/d13_eleventh_final_perfile.txt` |
| full worktree gate | **{WORKTREE} exit 0, 0 failures** | `logs/d13_eleventh_final_gate_raw.txt` |
| forbidden-token scan | **0 hard / 0 soft** (D13 16 files; `D7/HeatKernel` 15 files; `D7/ConjugateHeat` 12 files) | `logs/d13_eleventh_final_forbidden_{d13,d7,conj}.json` |
| negative control | **PASS** (`sorryAx` and the `native_decide` axiom detected) | `logs/d13_eleventh_final_negcontrol.out` |
| source integrity (`diff -rq` vs `D12-heat-domain-repair`) | **{DIFF} expected new-file lines**: the `D13/` tree and the 9 new D7 consumers (`HeatKernel/{V1Interface,StatementStatus,RepairStatus,DataStatus,FiniteStatus,UniquenessStatus}.lean`, `ConjugateHeat/{Status,UniquenessStatus,ScalarCurvatureStatus}.lean`) | `logs/d13_eleventh_final_diff.txt` |
| upstream snapshot verifier | **exit 0 — all 7 checks true** (`bb91a091`) | `logs/d13_eleventh_final_upstream.out` |

### 23.9 Eleventh-invocation verdict

The milestone — the `LONG_PLAN` `HeatKernelBridge` transporting D10 to the corrected-domain D7
interface, consumed by D7 modules — remains **fully checked** on the extended artifact (25 authored
files, 455 audited declarations, all gates green). The eleventh invocation adds the scalar-curvature
half of the conjugate interface:

* the **mass law** `d/dt ∫ K dV = ∫ R K dV` of the conjugate heat equation, and the resulting
  **obstruction**: the unit-mass field of `IsConjugateHeatKernelPDE` (v2) forces `∫ R K dV = 0`
  identically, so v2 has no inhabitant whenever `R ≥ 0` is positive somewhere
  (`not_exists_isConjugateHeatKernelPDE_of_nonneg_scalarMul`);
* the corrected predicate `IsConjugateHeatKernelPDEMassLaw` (v3), inhabited for every `R` by the
  explicit curvature kernel `exp ((t₀ - t) • (L - diag R))` and well posed among anticausal kernels
  (`exists_unique_finiteConjKernelWith`), with every v2 inhabitant a v3 inhabitant;
* the D7-level consumer `Poincare.D7.ConjugateHeat.ScalarCurvatureStatus`.

This is the finite-dimensional model of the remaining manifold content: `exact_blockers_closed`
remains `[]`, `D7-HEAT-KERNEL-EXISTENCE` and its conjugate sibling remain **OPEN**, and no named
blocker is claimed closed. The card requests independent semantic acceptance of the 25 authored
files, including the eleventh-invocation pair `ConjugateScalarCurvature.lean` /
`ScalarCurvatureStatus.lean`.

TASK_DONE — `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7/longrun/results/D13-heatkernel-bridge-d10-d7.md`
(eleventh-invocation gates clean: baseline 26/26 hashes byte-identical, final artifact build **exit 0 ({JOBS} jobs)**,
`D13HeatKernelBridgeAxiomCheck PASS {AXIOM}/{AXIOM}`, semantic transcripts **{SEM_FILES} files exit 0**, per-file
**{PERFILE}**, worktree **{WORKTREE}**, forbidden **0 hard / 0 soft**, negative control PASS, source integrity clean
(**{DIFF} expected new-file lines**), upstream snapshot PASS, **{HASHES} hashes** recorded and re-verified. The
milestone is fully checked; the card requests independent semantic acceptance. **No named blocker is claimed closed**:
`exact_blockers_closed = []`. The eleventh invocation proves the mass law of the conjugate heat equation, the
incompatibility of the unit-mass field with a nonvanishing scalar-curvature term
(`not_exists_isConjugateHeatKernelPDE_of_nonneg_scalarMul`), and well-posedness of the corrected mass-law predicate
(`exists_unique_finiteConjKernelWith`) with the explicit curvature kernel; the D7 consumer
`Poincare.D7.ConjugateHeat.ScalarCurvatureStatus` records it. The finite model is not a substitute for the manifold
theorems, which remain OPEN.)
