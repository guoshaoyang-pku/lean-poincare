# D7-surgery-neck-extinction — surgery with necks and extinction, interface level

- **Task:** `D7-surgery-neck-extinction`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-surgery-neck-extinction`
- **Verdict:** `TASK_DONE`
- **Lean:** `4.34.0-rc2` (`6a10ac8c22beadecabdbb0919c2b50214762f91d`)
- **mathlib:** `7974e751bece493b6ff508039423ca9fa2452fa8`
- **New Lean sources:** `release/Poincare/D7/SurgeryFlow/` (7 files, 1439 lines, 107 declarations)
- **Verification transcript:** `longrun/d7sne-logs/`

## 1. Summary

The task asks for the surgery/neck/extinction layer of the Perelman programme at interface level,
over the accepted D7 canonical-neighborhood layer (`Poincare.D7.Canonical`, the
`CanonicalNeighborhoodCertificate` with its `neck`/`cap`/`compactSpherical` alternatives) and the
accepted D3 surgery ledger (`Poincare.Longrun.Surgery`, `SurgeryDatum`, `SurgeryCertificate`,
`SurgeryChain`, `ToyRel`). The deliverable has four layers.

1. **Procedure data (`Basic.lean`).** `SurgeryProcedureData P D` consumes a
   canonical-neighborhood certificate: it bundles a D3 surgery datum `D` with its D3 preservation
   certificate, the canonical certificate at scale `r` (required to be of kind `neck`), an
   identification of the D3 cut neck with the certified pointed region, the surgery time, and the
   curvature threshold (with an opaque `curvatureExceedsThreshold` Prop). The extracted
   `SurgeryProcedureData.neck` is an `EpsilonNeck ε r X`; the curvature normalization
   (`curvatureScale`) and the metric noncollapsing shadow (`noncollapsing`) are exposed.
   `ProcedureChain` extends the D3 `SurgeryChain`: it forgets to a D3 chain
   (`ProcedureChain.toSurgeryChain`) and carries the D3 `ChainCertificate` assembled from the
   procedure ledgers (`ProcedureChain.certificate`), so every D3 chain-preservation theorem
   applies verbatim. `realLineProcedure` is a kernel-checked inhabitant built from the D7
   line-cylinder certificate, so the interface is not vacuous.
2. **Discrete surgery times (`Times.lean`).** `SurgerySchedule T` is a surgery-time sequence
   with a uniform positive gap. Kernel-checked: the times strictly increase
   (`strictMono`); the gap over a block of steps (`gap_mul_le_add`, `gap_mul_le_sub`) and
   between distinct times in absolute value (`gap_le_abs_sub`); at most one surgery time in any
   interval of length `gap` (`range_inter_Ioo_subsingleton`) and an isolated interval around each
   time (`range_inter_Ioo_eq_singleton`); the surgery-time set is discrete (`isDiscrete_range`),
   closed (`isClosed_range`), and has empty derived set (`derivedSet_range`, i.e. **no
   accumulation point**); only finitely many surgeries occur in any bounded interval
   (`finite_range_inter_Icc`, `finite_range_inter_Ioo`). The **stated curvature-bound
   interface** is `CurvatureBoundInterface T`: the opaque uniform curvature bound
   (`curvatureBound`) and the opaque maximum-principle/a-priori estimate (`maximumPrinciple`)
   turn into the uniform gap, and every discreteness conclusion is reproved under it
   (`CurvatureBoundInterface.derivedSet_range`, `isClosed_and_isDiscrete_range`, ...). The
   application `procedureTimes` records that the surgery times of a procedure family are covered.
3. **Extinction for the finite toy complexity relation (`Extinction.lean`).** Reusing the D3
   results (`toyRel_lt`, `ToyChain.value`, `ToyChain.no_infinite`): no infinite strictly
   decreasing natural sequence (`no_infinite_strict_decrease`), no infinite chain for a
   finite-complexity relation (`no_infinite_steps`), no infinite `ToyRel` chain
   (`no_infinite_toyRel`), **constructive toy extinction** `ToyChain m 1 (m - 1)` for every
   positive `m` (`toyChain_to_one`, `toy_extinction`), uniqueness of the extinction time
   (`toyChain_to_one_length`, `toy_extinction_time_unique`), the bound `k ≤ m`
   (`toy_extinction_time_le`) and the complete statement `toy_extinction_bound`.
4. **State-only Props and named missing inputs (`Statements.lean`).**
   `missingFullNeckAnalysis` (hypotheses bundle `NeckAnalysisHypotheses` refining the D3
   `NeckAnalysis` by the certified-neck data), `missingAPrioriCurvatureEstimates`
   (`curvatureBound ∧ maximumPrinciple`), `missingExtinctionTheorem` (`extinct ∧
   terminalSphere`) and the combined `missingSurgeryFlowTheorem` are `def ... : Prop`s that are
   **never asserted as theorems**. The checked reductions extract their consequences, and
   `surgeryFlow_consequences` assembles discreteness, target-invariant preservation, extinction
   and the terminal sphere. The ledger names 12 missing inputs (`surgeryFlowDependencies`) and
   6 blockers (`surgeryFlowBlockers`).

No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs in any authored file;
all **107** audited declarations have standard axiom cones (`{}` × 16, `{propext}` × 2,
`{Quot.sound, propext}` × 7, `{Classical.choice, Quot.sound, propext}` × 82).

## 2. Scaffold

`cp -al ../D7-canonical-neighborhood/. .` failed with `EXDEV Invalid cross-device link`
(directories were created, no files linked), so the documented fallback `cp -a` was used:
exit 0.  The source-integrity check compares 245 non-`.lake`, non-`longrun` files against the
scaffold: **0 changed, 0 removed, 0 added outside the new directory**.  As in every D7 sibling
task, the Lake package root is `release/`, so the new sources live in
`release/Poincare/D7/SurgeryFlow/`; the worktree-root `lakefile.toml` re-exposes `release/.lake`
through the `.lake` symlink, so the gate command
`lake env lean release/Poincare/D7/SurgeryFlow/<File>.lean` resolves the imports.

## 3. New files

| file | lines | decls | role |
|---|---:|---:|---|
| `Basic.lean` | 283 | 29 | `SurgeryProcedureData` consuming canonical neighborhoods, the extracted `neck`, `ProcedureChain` extending the D3 ledger, and the non-vacuous `realLineProcedure` |
| `Times.lean` | 334 | 26 | `SurgerySchedule`, the gap lemmas, discreteness/closedness/empty-derived-set, finitely many surgeries per bounded interval, `CurvatureBoundInterface` |
| `Extinction.lean` | 134 | 12 | finite-descent skeleton, no infinite `ToyRel` chain, constructive toy extinction and its uniqueness/bound |
| `Statements.lean` | 421 | 40 | the three state-only Props, `NeckAnalysisHypotheses`, `ExtinctionData`, checked reductions, 12 dependencies, 6 blockers |
| `All.lean` | 23 | 0 | umbrella module |
| `Probe.lean` | 122 | 0 | generated 107-declaration `#check` API probe |
| `Audit.lean` | 122 | 0 | generated 107-declaration `#print axioms` audit |

## 4. Main declarations

### 4.1 Procedure data consuming canonical neighborhoods (`Basic.lean`)

```lean
structure SurgeryProcedureData (P : LedgerPredicates.{u}) {X Y : TopSpace.{u}}
    (D : SurgeryDatum X Y) : Type (u + 2) where
  ledger : SurgeryCertificate P D
  epsilon : ℝ;  epsilon_pos : 0 < epsilon
  kappa : ℝ;    kappa_pos : 0 < kappa
  radius : ℝ;   radius_pos : 0 < radius
  neckRegion : PointedMetricSpace.{u}
  certificate : CanonicalNeighborhoodCertificate epsilon kappa radius neckRegion
  kind_eq_neck : certificate.kind = CanonicalKind.neck
  neckEquiv : D.neck.Carrier ≃ neckRegion
  time : ℝ
  curvatureThreshold : ℝ
  curvatureThreshold_pos : 0 < curvatureThreshold
  curvatureExceedsThreshold : Prop
```

Checked API: `neck` (the `EpsilonNeck` extracted from the certificate), `neck_model_radius`,
`neck_radius_pos`, `neck_approx_distortion`, `neck_antipodal_dist`, `curvatureScale`,
`noncollapsing`, `toSurgeryCertificate`, and the three D3 preservation projections
`compact_preserved`, `orientable_preserved`, `simplyConnected_preserved`.

D3-ledger extension:

```lean
inductive ProcedureChain (P : LedgerPredicates.{u}) : TopSpace.{u} → TopSpace.{u} → Type (u + 2)
  | nil (X : TopSpace.{u}) : ProcedureChain P X X
  | step {X Y Z : TopSpace.{u}} (D : SurgeryDatum X Y) (S : SurgeryProcedureData P D)
      (c : ProcedureChain P Y Z) : ProcedureChain P X Z

def ProcedureChain.toSurgeryChain : ProcedureChain P X Y → SurgeryChain X Y
theorem ProcedureChain.certificate : (c : ProcedureChain P X Y) → ChainCertificate P c.toSurgeryChain
theorem ProcedureChain.simplyConnected_preserved : P.SimplyConnected X → P.SimplyConnected Y
```

Non-vacuity: `realLineProcedure : SurgeryProcedureData toyLedger realLineDatum` uses the D3
trivial datum on the real line and the D7 `lineCylinder_certificate` (kind `neck`, scale 2), so
`exists_surgeryProcedureData` is inhabited.

### 4.2 Surgery times are discrete with no accumulation point (`Times.lean`)

```lean
structure SurgerySchedule (T : ℕ → ℝ) where
  gap : ℝ
  gap_pos : 0 < gap
  gap_le_next : ∀ n : ℕ, gap ≤ T (n + 1) - T n

structure CurvatureBoundInterface (T : ℕ → ℝ) where
  curvatureBound : Prop                    -- opaque uniform curvature bound
  maximumPrinciple : Prop                  -- opaque a-priori maximum-principle estimate
  gap : ℝ
  gap_pos : 0 < gap
  gap_le_next : curvatureBound → maximumPrinciple → ∀ n, gap ≤ T (n + 1) - T n
```

Kernel-checked consequences of `SurgerySchedule T`:

```lean
theorem strictMono : StrictMono T
theorem gap_mul_le_add (m d) : (d : ℝ) * gap ≤ T (m + d) - T m
theorem gap_le_abs_sub {m n} (hmn : m ≠ n) : gap ≤ |T n - T m|
theorem range_inter_Ioo_subsingleton (t) :
    (Set.range T ∩ Set.Ioo (t - gap / 2) (t + gap / 2)).Subsingleton
theorem range_inter_Ioo_eq_singleton (n) :
    Set.range T ∩ Set.Ioo (T n - gap / 2) (T n + gap / 2) = {T n}
theorem isDiscrete_range : IsDiscrete (Set.range T)
theorem not_accPt (t) : ¬ AccPt t (𝓟 (Set.range T))
theorem isClosed_range : IsClosed (Set.range T)
theorem derivedSet_range : derivedSet (Set.range T) = ∅
theorem isClosed_and_isDiscrete_range : IsClosed (Set.range T) ∧ IsDiscrete (Set.range T)
theorem finite_range_inter_Icc (a b) : (Set.range T ∩ Set.Icc a b).Finite
theorem finite_range_inter_Ioo (a b) : (Set.range T ∩ Set.Ioo a b).Finite
```

The same conclusions are reproved under `CurvatureBoundInterface` (with `toSchedule`), and
`procedureTimes_derivedSet_eq_empty` / `procedureTimes_finite_range_inter_Icc` record the
application to the surgery times of a procedure family.

### 4.3 Extinction for the finite toy complexity relation (`Extinction.lean`)

```lean
theorem no_infinite_strict_decrease (f : ℕ → ℕ) : ¬ ∀ n, f (n + 1) < f n
theorem no_infinite_steps (rel) (hdec : ∀ {m n}, rel m n → n < m) (f) :
    ¬ ∀ n, rel (f n) (f (n + 1))
theorem no_infinite_toyRel (f : ℕ → ℕ) : ¬ ∀ n, ToyRel (f n) (f (n + 1))
theorem toyChain_to_one : ∀ m, 0 < m → ToyChain m 1 (m - 1)
theorem toy_extinction (m) (hm : 0 < m) : ∃ k, ToyChain m 1 k ∧ k = m - 1
theorem toyChain_to_one_length {m k} (c : ToyChain m 1 k) : k = m - 1
theorem toy_extinction_bound (m) (hm : 0 < m) :
    (∃ k, ToyChain m 1 k ∧ k = m - 1) ∧ (∀ k, ToyChain m 1 k → k = m - 1) ∧
      (∀ n, ¬ ToyChain m n (m + 1))
```

`toyChain_to_one` is constructive: it removes one component at every step until one component
remains, and `ToyChain.value` fixes the length at `m - 1`.  This is the finite toy complexity
extinction relation built on the accepted D3 `ToyRel` results.

### 4.4 State-only Props and the named missing inputs (`Statements.lean`)

```lean
def missingFullNeckAnalysis (P) (D : SurgeryDatum X Y) (S : SurgeryProcedureData P D) : Prop :=
  ∃ N : NeckAnalysisHypotheses P D S,
    N.d3.highCurvatureRegion →
      N.certifiedNeckSeparating ∧ N.admissibleCutAndCap ∧ N.d3.realizesDatum ∧ N.scaleCompatible

def missingAPrioriCurvatureEstimates {T} (H : CurvatureBoundInterface T) : Prop :=
  H.curvatureBound ∧ H.maximumPrinciple

def missingExtinctionTheorem (E : ExtinctionData) : Prop := E.extinct ∧ E.terminalSphere

def missingSurgeryFlowTheorem (S) (H) (E) : Prop :=
  missingFullNeckAnalysis P D S ∧ missingAPrioriCurvatureEstimates H ∧ missingExtinctionTheorem E
```

`NeckAnalysisHypotheses` refines the D3 `NeckAnalysis` by the certified-neck data and four
implication fields; `ExtinctionData` carries `complexity`, the opaque `surgeryAt`, the
monotonicity and strict-decrease fields, the opaque `extinct`/`terminalSphere`, and the two
named missing implications.  The checked skeleton `ExtinctionData.finitelyMany_surgeries`
(only finitely many surgeries occur) is proved from the strict decrease, with no geometric
input.  Checked reductions: `discrete_times_of_missingAPrioriEstimates`,
`finitelyMany_of_missingAPrioriEstimates`, `extinct_of_missingExtinctionTheorem`,
`terminalSphere_of_missingExtinctionTheorem`, `surgeryFlow_consequences`,
`surgeryFlow_consequences_of_missing`.

Named missing inputs: **12** entries in `surgeryFlowDependencies` (SNE-1 … SNE-12, with
`surgeryFlowDependencies_length : ... = 12` and `..._all_named`), and **6** blockers in
`surgeryFlowBlockers` (`B-D7-SNE-NECK-SEPARATING`, `-CUT-AND-CAP`, `-SCALE-COMPATIBLE`,
`-APRIORI`, `-EXTINCTION`, `-TERMINAL-SPHERE`).

## 5. Verification

`bash longrun/d7sne-logs/run_verification.sh` runs five gates; the transcript is in
`longrun/d7sne-logs/`.

Exact per-file commands (from the worktree root, `lake env lean <file>.lean`, exit code in
parentheses):

```text
cd release && lake build                                                  (0)
lake env lean release/Poincare/D7/SurgeryFlow/Basic.lean                  (0)
lake env lean release/Poincare/D7/SurgeryFlow/Times.lean                  (0)
lake env lean release/Poincare/D7/SurgeryFlow/Extinction.lean             (0)
lake env lean release/Poincare/D7/SurgeryFlow/Statements.lean             (0)
lake env lean release/Poincare/D7/SurgeryFlow/All.lean                    (0)
lake env lean release/Poincare/D7/SurgeryFlow/Probe.lean                  (0)
lake env lean release/Poincare/D7/SurgeryFlow/Audit.lean                  (0)
```

`#print axioms` records for the main declarations (`longrun/d7sne-logs/axioms-print.out`):

```text
#print axioms Poincare.D7.SurgeryFlow.SurgeryProcedureData
  depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Poincare.D7.SurgeryFlow.SurgerySchedule.derivedSet_range
  depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Poincare.D7.SurgeryFlow.CurvatureBoundInterface.derivedSet_range
  depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Poincare.D7.SurgeryFlow.no_infinite_strict_decrease
  depends on axioms: [propext, Quot.sound]
#print axioms Poincare.D7.SurgeryFlow.toy_extinction
  depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Poincare.D7.SurgeryFlow.missingFullNeckAnalysis
  depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Poincare.D7.SurgeryFlow.surgeryFlow_consequences
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

| gate | result |
|---|---|
| full package build (`cd release && lake build`) | exit **0** |
| per-file `lake env lean` gate (7 files) | all exit **0** |
| forbidden-token scan (`input/d5-tools/scan_forbidden.py`) | 7 files, **0** hard, **0** soft |
| `#print axioms` audit (`Audit.lean`) | **107** declarations, **0** nonstandard |
| source integrity vs scaffold | 245 files, **0** changed/removed/added |

Axiom cones: `{}` × 16, `{propext}` × 2, `{Quot.sound, propext}` × 7,
`{Classical.choice, Quot.sound, propext}` × 82.  No `sorryAx`, no project axiom, no
`native_decide`.

## 6. Honest boundary

- The **full Perelman neck analysis** is not proved: the existence of a high-curvature neck, its
  separability in the simply connected case, the cut-and-cap construction and its admissibility
  are opaque Props (`missingFullNeckAnalysis`).
- The **a-priori curvature estimates** are not proved: `CurvatureBoundInterface` carries the
  curvature bound and the maximum-principle estimate as opaque `Prop` fields; only the
  metric/order-theoretic consequences of the resulting uniform gap are kernel-checked.
- The **geometric extinction theorem** is not proved: `ExtinctionData` carries `extinct` and
  `terminalSphere` as opaque Props and the two geometric implications as fields; only the
  finiteness skeleton is checked.
- The canonical-neighborhood certificate consumed by `SurgeryProcedureData` is the accepted D7
  metric-shadow interface, not a smooth manifold-level neck; `realLineProcedure` uses the D7
  line-cylinder metric model, not the smooth round cylinder `S² × ℝ`.
- The D3 toy relation `ToyRel` is a finite-component-count model; its extinction is the
  order-theoretic skeleton, not the geometric flow.

## 7. Artifacts

| artifact | file |
|---|---|
| authored sources | `release/Poincare/D7/SurgeryFlow/{Basic,Times,Extinction,Statements,All,Probe,Audit}.lean` |
| verification script | `longrun/d7sne-logs/run_verification.sh` |
| exit codes | `longrun/d7sne-logs/exit_codes.txt` |
| forbidden scan | `longrun/d7sne-logs/forbidden-scan.json` |
| axiom audit | `longrun/d7sne-logs/axioms.json`, `axioms-print.out` |
| source integrity | `longrun/d7sne-logs/source-integrity.json` |
| result card | `longrun/results/D7-surgery-neck-extinction.md`, `.json` |
