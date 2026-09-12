# D7-levi-civita-smoothness — result card

- **Task id:** `D7-levi-civita-smoothness`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-levi-civita-smoothness`
- **Generated:** `2026-09-10T00:30:11+0800`
- **Verdict:** **TASK_DONE**
- **Lean:** `leanprover/lean4:v4.34.0-rc2`
- **mathlib:** `7974e751bece493b6ff508039423ca9fa2452fa8` (`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean`)
- **Authored:** 7 files, 1575 lines, all under `release/Poincare/D7/LeviCivita/`
- **Machine-readable card:** `longrun/results/D7-levi-civita-smoothness.json`

## 0. Scaffold

- Prescribed: `cp -al ../D7-riemann-curvature-tensor/. .`
- **Outcome: failed.** FAILED: the workspace sandbox rejects cross-tree hard links with Invalid cross-device link (EXDEV), although both trees are on /data3 (stat -c %d = 66313 for both).
- **Fallback:** cp -a ../D7-riemann-curvature-tensor/. . (byte-identical recursive copy, symlinks preserved: .lake -> release/.lake, release/.lake/packages -> shared mathlib packages)
- **Integrity:** diff -rq --exclude=.lake --exclude=LeviCivita against the source worktree reports no content differences; 287 copied files (excluding .lake build artifacts) are byte-identical, 0 changed, 0 missing. Additions are only release/Poincare/D7/LeviCivita/ (7 new Lean files) and longrun/logs/.

## 1. Mathlib probe (task item 1)

Method: grep over the pinned mathlib checkout plus the compilable probe release/Poincare/D7/LeviCivita/Probe.lean (#check present, #check_failure absent). Evidence: `longrun/logs/mathlib_probe_evidence.txt`.

### 1.1 Levi-Civita connection API — present and reused

- CovariantDerivative (Basic.lean:366)
- IsCovariantDerivativeOn (Basic.lean:92)
- CovariantDerivative.torsion (Torsion.lean:120)
- CovariantDerivative.torsion_antisymm (Torsion.lean:140)
- CovariantDerivative.torsion_eq_zero_iff (Torsion.lean:143)
- CovariantDerivative.IsMetricCompatible (Metric.lean:155)
- CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq (Metric.lean:160)
- CovariantDerivative.isMetricCompatible_iff (Metric.lean:170)
- CovariantDerivative.IsLeviCivitaConnection (LeviCivita.lean:201)
- CovariantDerivative.IsLeviCivitaConnection.apply_eq (Koszul formula, LeviCivita.lean:214)
- CovariantDerivative.IsLeviCivitaConnection.apply_eq_extend (LeviCivita.lean:239)
- CovariantDerivative.IsLeviCivitaConnection.uniqueness (LeviCivita.lean:255)
- CovariantDerivative.leviCivitaConnection (LeviCivita.lean:359)
- CovariantDerivative.isMetricCompatible_leviCivitaConnection (LeviCivita.lean:383)
- CovariantDerivative.torsion_leviCivitaConnection_eq_zero (LeviCivita.lean:396)
- CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection (LeviCivita.lean:408)

### 1.2 Smoothness statements that DO exist

- ContMDiffCovariantDerivativeOn (Basic.lean:108): cov sigma is C^k on a set for every C^(k+1) section sigma
- ContMDiffCovariantDerivativeOn.affine_combination (Basic.lean:250) and ContMDiffCovariantDerivativeOn.finite_affine_combination (Basic.lean:284): C^k is closed under affine combinations
- CovariantDerivative.ContMDiffCovariantDerivative (Basic.lean:412): the bundled global class
- CovariantDerivative.ContMDiffCovariantDerivative.affineCombination (Basic.lean:459) and .finiteAffineCombination (Basic.lean:472)
- IsContMDiffRiemannianBundle (VectorBundle/Riemannian.lean:67) and IsContMDiffRiemannianBundle.of_le (Riemannian.lean:74): smoothness of the metric, the hypothesis of the Levi-Civita smoothness theorem
- analytic engine reused: ContinuousLinearMap.contMDiff, ContMDiff.clm_apply, ContDiff.contDiff_fderiv_apply, ContDiff.fderiv_apply

### 1.3 Smoothness statements that DO NOT exist (the gap this layer names)

- CovariantDerivative.contMDiff_leviCivitaConnection (#check_failure passes)
- CovariantDerivative.leviCivitaConnection_contMDiff (#check_failure passes)
- ContMDiffCovariantDerivative.leviCivitaConnection (#check_failure passes)
- CovariantDerivative.leviCivitaConnection_isContMDiff (#check_failure passes)
- IsLeviCivitaConnection.isContMDiff (#check_failure passes)
- the module docstring of LeviCivita.lean lines 22-23 announces the result as a future PR: 'Future PRs will prove smoothness: if M is C^{n+2} and g is C^{n+1}, the Levi-Civita connection is a C^n connection.' No declaration proves it.

### 1.4 Curvature declarations — absent

- CovariantDerivative.curvature
- CovariantDerivative.riemann
- CovariantDerivative.IsContMDiff
- RiemannTensor
- RiemannianCurvature
- RicciTensor
- christoffelSymbol
- ChristoffelSymbol
- grep -ri curvature over the pinned Mathlib/ matches exactly one file: MeasureTheory/Measure/Doubling.lean:44 (a docstring)

## 2. Proved (kernel-checked) results

### 2a. The mean of two metric-compatible connections is metric-compatible

- Poincare.D7.LeviCivita.isMetricCompatible_affine: affine combinations of metric-compatible connections are metric-compatible
- Poincare.D7.LeviCivita.isMetricCompatible_mean: THE MEAN of two metric-compatible connections is metric-compatible
- Poincare.D7.LeviCivita.isTorsionFree_mean and isLeviCivita_mean: the same for the torsion-free and Levi-Civita properties for a common bracket
- Poincare.D7.LeviCivita.meanConnection_eq_left / _right: the mean of two Levi-Civita connections equals each of them (uniqueness coherence)
- Poincare.D7.Curvature.RiemannCurvatureData.meanData: the mean of two D7 curvature data sharing metric and bracket is again a RiemannCurvatureData
- Poincare.D7.LeviCivita.connectionCoefficient_mean and isMetricCompatible_coefficient_relation_affine: the same at the coefficient level

### 2b. The difference tensor of two torsion-free connections is symmetric

- Poincare.D7.LeviCivita.differenceTensor_symm: THE DIFFERENCE TENSOR of two torsion-free connections for the same bracket is symmetric
- Poincare.D7.LeviCivita.differenceTensor_metric_antisymm: the difference tensor of two metric-compatible connections is metric-antisymmetric
- Poincare.D7.LeviCivita.differenceTensor_eq_zero_of_isLeviCivita: the difference tensor of two Levi-Civita connections vanishes (difference-tensor form of uniqueness)
- Poincare.D7.Curvature.RiemannCurvatureData.differenceTensor_symm: the D7-data version
- Poincare.D7.LeviCivita.isTorsionFree_coefficient_relation and isTorsionFree_coefficient_relation_affine: the coefficient-level relation

### 2c. Smoothness of the connection-coefficients interface

- Poincare.D7.LeviCivita.contMDiff_coefficientField: a C^n connection field has C^n coefficients (ContMDiff.clm_apply + ContinuousLinearMap.contMDiff)
- Poincare.D7.LeviCivita.contMDiff_coefficientField_comp_chart: under the stated chart smoothness hypothesis (a C^n chart phi), the pulled-back coefficients are C^n
- Poincare.D7.LeviCivita.SmoothCoefficientSystem: the bundled interface (C^n coefficient functions + torsion and metric relations); .affineCombination/.mean preserve it, .pullback pulls it back along a C^n chart, .const inhabits it
- Poincare.D7.LeviCivita.contDiff_christoffelSymbol: if the chart metric coefficients are C^{n+1} and the inverse-metric coefficients are C^n, the Koszul Christoffel symbols are C^n (ContDiff.contDiff_fderiv_apply + closure under sums/products)
- Poincare.D7.LeviCivita.contDiff_fderiv_coefficient: directional derivative smoothness

### 2d. Coefficient algebra (supporting results)

- Poincare.D7.LeviCivita.sum_connectionCoefficient_smul: reconstruction nabla e_i e_j = sum_k Gamma^k_ij e_k
- Poincare.D7.LeviCivita.form_nabla_basis: <nabla e_i e_j, e_k> = Gamma^k_ij
- Poincare.D7.LeviCivita.isMetricCompatible_coefficient_relation: Gamma^k_ij + Gamma^j_ik = 0
- Poincare.D7.LeviCivita.connectionCoefficient_affine/_mean/_difference: coefficient functoriality

## 3. State-only Props with exact missing dependencies (task item 3)

### `Poincare.D7.LeviCivita.LeviCivitaSmoothnessStatement`

- statement: ContMDiffCovariantDerivative (leviCivitaConnection I M) n, i.e. if M is C^{n+2} and g is C^{n+1} then the Levi-Civita connection is C^n
- blocker: `B-D7-LC-SMOOTHNESS`
- missing mathlib dependencies:
  - the instance ContMDiffCovariantDerivative (leviCivitaConnection I M) n (class exists at Basic.lean:412, no instance)
  - the manifold-level smoothness proof announced in LeviCivita.lean lines 22-23 (docstring only)
  - a smoothness-preserving dual/musical-isomorphism construction for the Koszul form; the coordinate half is proved in contDiff_christoffelSymbol

### `Poincare.D7.LeviCivita.SmoothLeviCivitaExistenceStatement`

- statement: there exists a C^n torsion-free metric-compatible connection on a smooth Riemannian manifold
- blocker: `B-D7-LC-SMOOTHNESS`
- missing mathlib dependencies:
  - only the C^n part: mathlib provides the connection and its Levi-Civita property (checked reuse leviCivitaConnection_isLeviCivitaConnection)
  - the checked reduction smoothLeviCivitaExistence_of_smoothness shows the statement follows from LeviCivitaSmoothnessStatement

### `Poincare.D7.LeviCivita.CovariantDerivativeCurvatureMatchesD7`

- statement: there is a pointwise (1,3) tensor kappa equal to the candidate formula R(X,Y)Z = nabla_X nabla_Y Z - nabla_Y nabla_X Z - nabla_[X,Y] Z and satisfying first-pair antisymmetry and the first Bianchi identity (the D7 interface obligations)
- blocker: `B-D7-MANIFOLD-CURVATURE`
- missing mathlib dependencies:
  - CovariantDerivative.curvature (absent; grep of Mathlib/ for curvature matches only a docstring)
  - second covariant derivative of a section (no calculus of nabla_X nabla_Y Z, so the candidate formula cannot be proved tensorial)
  - smoothness of the connection to differentiate the section y |-> nabla_Y(y) Z (same gap as B-D7-LC-SMOOTHNESS)
  - the induced connection on the (1,3) tensor bundle for the second Bianchi identity (B-D7-NABLA-R)

## 4. Verification

### 4.1 Compile gate — `lake env lean <file> from the worktree root, every *.lean (skipping .lake)`

- files checked: **80**, exit 0: **80**, failures: **0** — **PASS**
- authored files checked: 7/7
- log: `longrun/logs/gate_replication.log`, json: `longrun/logs/gate/gate_replication.json`

### 4.2 Axiom audit — `#print axioms`

- declarations audited: **64**
- all axiom cones ⊆ `{propext, Classical.choice, Quot.sound}`: **True**
- forbidden axiom occurrences (project axiom / `sorryAx` / `native_decide` / `proof_wanted`): **0**
- log: `longrun/logs/axiom_audit.log`

### 4.3 Forbidden-token scan

- command: `python3 input/d5-tools/scan_forbidden.py release/Poincare/D7/LeviCivita`
- files scanned: 7, hard matches: **0**, soft flags: **0**
- log: `longrun/logs/forbidden_scan.json`

### 4.4 Full release package build

- command: `cd release && lake build` — exit **0** (8962 jobs)
- full release package build (all libraries Poincare/Probe/Ledger/Audit plus the new Poincare.D7.LeviCivita modules) succeeds

### 4.5 Copied-file integrity

- command: `diff -rq --exclude=.lake --exclude=LeviCivita ../D7-riemann-curvature-tensor .`
- 287 copied files checked, 0 changed, 0 missing; no content differences; only additions longrun/logs/ and release/Poincare/D7/LeviCivita/

## 5. Authored files

- `release/Poincare/D7/LeviCivita/Audit.lean` — 104 lines — #print axioms audit
- `release/Poincare/D7/LeviCivita/Basic.lean` — 361 lines — affine/mean connections and difference tensor (task items 2a, 2b) + lifting to RiemannCurvatureData
- `release/Poincare/D7/LeviCivita/Blocked.lean` — 256 lines — state-only Props and named blockers (task item 3)
- `release/Poincare/D7/LeviCivita/Coefficients.lean` — 356 lines — basis connection coefficients and the smooth coefficient interface (task item 2c)
- `release/Poincare/D7/LeviCivita/Koszul.lean` — 149 lines — chart-smoothness theorem for the Koszul Christoffel symbols (task item 2c, calculus)
- `release/Poincare/D7/LeviCivita/Probe.lean` — 224 lines — compilable mathlib declaration/smoothness probe (task item 1)
- `release/Poincare/D7/LeviCivita/Smoke.lean` — 125 lines — non-vacuity witnesses and computations

## 6. Honest boundary

- The D7 curvature data is the D2 abstract algebraic Koszul connection on a real vector space, not a mathlib CovariantDerivative on a smooth manifold; the bracket is abstract data.
- The manifold-level smoothness of leviCivitaConnection and the construction of CovariantDerivative.curvature are NOT proved; they are the explicit state-only Props LeviCivitaSmoothnessStatement/SmoothLeviCivitaExistenceStatement and CovariantDerivativeCurvatureMatchesD7 with named blockers.
- The Koszul theorem contDiff_christoffelSymbol is chart-level and takes the metric and inverse-metric coefficient smoothness as explicit hypotheses; positive definiteness and the derivation of inverse-metric smoothness from metric smoothness are not formalized.
- The candidate curvature formula is stated (stateable with FiberBundle.extend and VectorField.mlieBracket) but not proved to be a tensor.
- No claim is made about Ricci flow, Perelman monotonicity, surgery, or the Poincare conjecture.

## 7. Task-item coverage

- **1_mathlib_probe**: DONE: Probe.lean + mathlib_probe section
- **2a_mean_metric_compatible**: DONE: isMetricCompatible_mean (+ affine and D7-data lifting)
- **2b_difference_tensor_symmetric**: DONE: differenceTensor_symm (+ D7-data lifting)
- **2c_coefficient_smoothness_interface**: DONE: contMDiff_coefficientField, contMDiff_coefficientField_comp_chart, SmoothCoefficientSystem.pullback, contDiff_christoffelSymbol
- **3a_full_levi_civita_existence_prop**: DONE: SmoothLeviCivitaExistenceStatement + LeviCivitaSmoothnessStatement with missing-dependency records
- **3b_covariant_derivative_curvature_prop**: DONE: CovariantDerivativeCurvatureMatchesD7 + curvatureCandidate with missing-dependency records
- **4_no_forbidden_tokens**: DONE: 0 hard, 0 soft
- **5_compile_and_axioms**: DONE: gate exit 0 for every .lean; 64 declarations audited, all subset {propext, Classical.choice, Quot.sound}
- **6_results_card**: longrun/results/D7-levi-civita-smoothness.md + .json

**Status line: TASK_DONE**
