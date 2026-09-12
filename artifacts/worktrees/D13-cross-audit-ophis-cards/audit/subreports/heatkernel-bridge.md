# Independent adversarial audit — `D13-heatkernel-bridge-d10-d7`

**Audit target (card):** `audit/ophis/D13-heatkernel-bridge-d10-d7/longrun/results/D13-heatkernel-bridge-d10-d7.md`
(and `.json`), referred to below as **card.md / card.json**.
**Card D13 sources:** `audit/ophis/D13-heatkernel-bridge-d10-d7/release/Poincare/D13/HeatKernelBridge/*.lean`.
**D7 consumers consumed/edited:** `.../release/Poincare/D7/HeatKernel/{V1Interface,StatementStatus,RepairStatus,DataStatus,FiniteStatus,UniquenessStatus}.lean`,
`.../release/Poincare/D7/ConjugateHeat/{Status,UniquenessStatus}.lean` (new files, authored by this task), and the **pre-existing** D7 modules they import
(`D7/HeatKernel/{Basic,Blocked,Instance}.lean`, `D7/ConjugateHeat/Blocked.lean`).
**Auditor:** independent subagent (read-only except this report).
**Method:** source reading; declaration-site census; comment/string-aware forbidden-token scan
(`input/d5-tools/scan_forbidden.py`, stdout only); sha256 replay of the card's own hash manifest;
cross-check of the card's names against declaration positions; type-shape classification; scan for
hypothesis-smuggling patterns. No Lean build was run here (the parent's cold builds are the
authoritative compile evidence); no `.olean`/log files for this card were transported.

---

## Verdict (one paragraph)

For the **tenth-invocation artifact the card describes**, every headline declaration *exists* in the
sources with the claimed logical shape, the “refutations” are genuine `¬ P` statements with all
hypotheses explicit (not weaker per-model facts), `D7-HEAT-KERNEL-EXISTENCE` and its conjugate
sibling are genuinely open (`exact_blockers_closed = []`), the new D7 modules genuinely import and use
the D13 bridge, and no forbidden token occurs in any D13/D7 source. **Two card-named declarations do
not exist under the names printed** (one renamed by one letter, one by a dropped `is`; §F3), one proof attribution is **not** supported by
the quoted declarations (the dissipativity half of §18.2; §F2), two per-file declaration counts are
wrong (§F4), and — most importantly — **the transported tree contains an undocumented 16th D13 module
(`ConjugateScalarCurvature.lean`, 738 lines, 39 declarations, self-described “companion note 11”)
that the card neither lists, hashes, scans, nor axiom-audits** (§F1). The extra module’s mtime
(2026-09-11 23:13 +0800) postdates the card (19:18 +0800) and the task checkpoint (19:18/19:22), so it
is almost certainly post-card work; but as delivered, the card’s “15 D13 files / 23 authored files /
409 audited declarations, all gates green” no longer describes the artifact tree. All card *gate
numbers* (build 9202 jobs, PASS 409/409, worktree 339/339, …) are **undetermined from this relayed
snapshot** because no logs were transported.

---

## A. Claim census (verbatim quotes, card line numbers)

The card is a 1605-line, ten-invocation accretion. The headline claims, quoted verbatim:

### A1. Euclidean-to-D7 transport (every dimension, both admissible classes)

- card.md:114 — “| D10 → D7 transport | `flatHeatKernelDataV1_integrable n`, `flatHeatKernelDataV1_cc n` for **every `n : ℕ`**, both admissible classes; kernel = D10 `gaussianKernel` at `t > 0` |”
- card.md:115 — “| scope of the transport (checked) | every positive dimension: V1 datum exists **and** no legacy datum exists (`flat_v1_exists_not_legacy_of_pos`); dimension 0: full legacy datum (`flat_legacy_exists_zero`) |”
- card.md:203–204 (displayed interface) —
  `flatHeatKernelDataV1_integrable (n : ℕ) : HeatKernelDataV1 (EuclideanSpace ℝ (Fin n))`
  `flatHeatKernelDataV1_cc          (n : ℕ) : HeatKernelDataV1 (EuclideanSpace ℝ (Fin n))`
- card.md:9 (verdict) — “**THE `HeatKernelBridge` NAMED BY LONG_PLAN EXISTS AND IS CONSUMED BY A D7 MODULE — the D10 Euclidean heat kernel (`Poincare.D10.HeatKernelEuclidean`) is transported to the D7 heat-kernel interface on the D12-corrected admissible-test-function domain in every dimension, the corrected-domain datum upgrades to a genuine legacy `Poincare.D7.HeatKernel.HeatKernelData` in the compact finite-measure scope (with the upgrade proved a left inverse of the legacy embedding), and a new D7 module consumes the bridge by proving the blocked D7 existence statement equivalent to its corrected-domain restatement.**”

### A2. Compact finite-measure upgrade + left-inverse claim

- card.md:116 — “| compact finite-measure upgrade | `toHeatKernelData_of_integrableClass` / `toHeatKernelData_of_ccClass` : corrected-domain datum → genuine legacy `HeatKernelData`; `ofHeatKernelData_upgrade_eq` (left inverse) |”
- card.md:242–251 (displayed signatures) —
  `toHeatKernelData_of_integrableClass [CompactSpace X] [OpensMeasurableSpace X] (D : HeatKernelDataV1 X) [IsFiniteMeasure D.core.volume] (hC : D.IsIntegrableClassVariant) : Poincare.D7.HeatKernel.HeatKernelData X`
  `toHeatKernelData_of_ccClass [CompactSpace X] [OpensMeasurableSpace X] (D : HeatKernelDataV1 X) [IsFiniteMeasureOnCompacts D.core.volume] (hC : D.testClass = AdmissibleTestClass.continuousCompactSupportClass D.core.volume) : Poincare.D7.HeatKernel.HeatKernelData X`
- card.md:262–265 — “* `ofHeatKernelData_upgrade_eq`: the upgrade is a **left inverse of the legacy embedding** — on a compact space with finite volume, embedding a legacy datum and upgrading recovers it exactly, so the corrected-domain interface carries exactly the same data as the legacy interface there.”
- card.md:122 — “| compact-scope existential closure (fifth invocation) | `exists_v1_iff_exists_legacy`: for a fixed core on a compact finite-measure space, the existence of a corrected-domain V1 datum is **equivalent** to the existence of a legacy D7 `HeatKernelData` with that core |”

### A3. D7 consumer equivalence

- card.md:117 — “| D7 downstream consumption | `heatKernelExistenceStatement_iff_v1`: the blocked D7 manifold statement is **equivalent** to its corrected-domain restatement; `punit_v1_upgrade_eq` round trip on the existing D7 one-point instance |”
- card.md:294–296 — “* `heatKernelExistenceStatement_iff_v1`: **the blocked D7 existence statement is equivalent to its corrected-domain restatement** (both sides ascribed the same universe level). No additional hypothesis is added to the statement — the equivalence uses only the statement's own antecedent;”
- card.md:304–305 — “`HeatKernelExistenceStatementV1` remains an unproved `Prop` exactly like the legacy statement; the equivalence is a reduction of the blocked statement, not an existence proof.”

### A4. Predicate-semantics finding (snapshot operator vs PDE)

- card.md:118 — “| predicate-semantics companion (third invocation) | `PredicateSemantics.lean`, 16 kernel-checked declarations: the D7 predicate's heat-equation field is a snapshot operator identity, not the PDE; the D10 kernel does not satisfy `IsHeatKernelV1`/`IsHeatKernel` for the honest flat Euclidean spacetime in positive dimension (all other predicate fields hold). Recorded as a statement-repair dependency, **not** a blocker closure (§15) |”
- card.md:583–590 — “The D13 transport is **data-level**: `HeatKernelDataV1.heatEquation` is the genuine `HasDerivAt (fun s : ℝ => K x y s) (Δ_x K(·,y,t)) t` field inherited from the D11 core — the actual `∂ₜK = ΔK`. The D7 *statement-level* predicate `Poincare.D7.HeatKernel.IsHeatKernel` — and its corrected-domain copy `IsHeatKernelV1` — instead carries
  ```
  solves : ∀ y t, 0 < t → S.heatOperator (fun x => K x y t) = 0,
  ```”
- card.md:608–615 — consequences: data-level transport unaffected (i); equivalence unaffected but “a proof of the predicate as written would not be a proof of `∂ₜK = ΔK`” (ii); “This is a **statement-semantics finding**, not one of the seven named analytic blockers and **not** a blocker closure: `exact_blockers_closed` remains `[]`.” (iii)

### A5. v2 repair candidate `IsHeatKernelPDE`

- card.md:119 — “| PDE-repair companion (fourth invocation) | `PDERepair.lean`, 18 kernel-checked declarations: versioned predicate `IsHeatKernelPDE` (v2) whose heat-equation field is the genuine `HasDerivAt` PDE; `IsHeatKernelPDE.of_dataV1` transports any `HeatKernelDataV1` datum (with everywhere-positivity) to it; the D10 kernel inhabits it on the honest flat spacetime in **every dimension** on both classes, while the same kernel refutes the snapshot predicate (`flat_pde_repaired_scope`, `not_forall_isHeatKernelPDE_imp_isHeatKernelV1`). A model-level repair candidate, **not** an existence statement and **not** a blocker closure (§16) |”
- card.md:670 (field table) — “| `IsHeatKernelPDE S C K` | the D7 predicate with `solvesPDE : ∀ x y t, 0 < t → HasDerivAt (fun s => K x y s) (S.laplacian (fun z => K z x t) x) t` in place of the snapshot identity; … `S.timeDerivative` is retained by the ambient structure but does not occur |”
  (Note: the card prints `K z x t` here; the source has `K z y t`. See §F7.)

### A6. The statement-level refutations (including the one surviving `AnnihilatesConstants`)

- card.md:120 — “| statement-refutation companion (fifth invocation) | `StatementRefutation.lean`, 15 kernel-checked declarations: the D7 `HeatKernelExistenceStatement` and `HeatKernelExistenceStatementV1` are **refutable as formalized** — `IsClosedRiemannianManifold` does not constrain `laplacian`/`timeDerivative`, and the one-point spacetime (Dirac volume, `laplacian = id`, `timeDerivative = 0`) forces `K = 0` against positivity. Unconditional at universe 0; universe-polymorphic conditional schema; **not** a blocker closure, but the checked reason the blocker cannot be closed as stated (§17) |”
- card.md:124 — “| second statement-level refutation (sixth invocation) | `adversarialTimeDerivativeSpacetime` (`Δ = 0`, `timeDerivative = id`) satisfies `IsClosedRiemannianManifold ∧ AnnihilatesConstants` yet admits **no** snapshot kernel: the Laplacian-only repair of `D7-HEAT-KERNEL-EXISTENCE` is dead (§18.3) |”
- card.md:910–913 — “* `not_forall_annihilatesConstants_implies_exists_snapshot_kernel` (universe `0`) and `..._of_refuting` (universe-polymorphic conditional schema): the snapshot existence statement is **false even after imposing the constant-annihilation condition**. No repair that constrains only `S.laplacian` can restore it.”
- card.md:10 (seventh invocation) — “the two statement-level repairs added by the sixth invocation (`HeatKernelExistenceStatementPDE`, `HeatKernelDataExistenceStatement`) are **false as written**: the two-point closed Riemannian spacetime with the zero Laplacian (`Bool`, volume `δ_true + δ_false`, discrete metric, `dim = 0`) satisfies the whole repaired hypothesis class and admits no strictly positive datum; …”

### A7. Time-rescaling incomparability theorem

- card.md:125 — “| snapshot/PDE incomparability (sixth invocation) | `snapshot_pde_predicates_incomparable`: the time-rescaled D10 kernel inhabits the snapshot predicate on `flatSnapshotSpacetime` but fails the PDE, so the D7 heat-equation field is not equivalent to the PDE under any operator hypotheses — it must be *replaced* (§18.4) |”
- card.md:929–931 — “* `not_forall_isHeatKernelV1_imp_isHeatKernelPDE` and `snapshot_pde_predicates_incomparable`: together with the converse `not_forall_isHeatKernelPDE_imp_isHeatKernelV1` of §16, the two predicates are **incomparable**. The heat-equation field must be *replaced* by the `HasDerivAt` statement; no hypothesis on the operators can make it equivalent to the PDE.”

### A8. Non-self-adjointness refutation (`not_forall_laplacian_symmetric_flatLine`)

- card.md:986–988 — “* `not_forall_laplacian_symmetric_flatLine`: the all-functions Bochner-integral form of formal self-adjointness, `∀ u v, ∫ u · Δv = ∫ Δu · v`, is **false** for the honest flat operator: with `u = 1` and `v = log ∘ cosh` the left-hand side is `2` and the right-hand side is `0`.”
- card.md:9 — “… It also adds the **checked refutation of the naive self-adjointness axiom** for the honest 1-dimensional flat packaged Laplacian (`not_forall_laplacian_symmetric_flatLine`: `u = 1`, `v = log cosh` give `∫ 1·Δv = 2 ≠ 0 = ∫ Δ1·v`), so the classical integration-by-parts identity cannot be adjoined as a field of a repaired schematic interface.”

### A9. Statement-level repaired interface

- card.md:126 — “| statement-level repaired interface (sixth invocation) | `HeatKernelExistenceStatementPDE` / `HeatKernelDataExistenceStatement` (`def … : Prop`, **stated, not proved**), `heatKernelDataExistenceStatement_implies_pde`, model inhabitants (`heatKernelDataExistenceStatement_conclusion_{punit,adversarial}`) (§18.5) |”
- card.md:938–943 — “* `HeatKernelExistenceStatementPDE` — the legacy statement shape on the class `IsClosedRiemannianManifold ∧ AnnihilatesConstants`, with the heat equation stated as the genuine PDE (`IsHeatKernelPDE`);
  * `HeatKernelDataExistenceStatement` — the data-level form: a genuine legacy D7 `HeatKernelData` matching the spacetime's volume, distance, dimension and Laplacian, strictly positive at positive times, with positive lower Gaussian constant.
  They are **not proved**; the analytic content of `D7-HEAT-KERNEL-EXISTENCE` (parametrix, parabolic regularity, Gaussian bounds, spectral theory) remains open.”

### A10. (Context) finite pinned existence/uniqueness and conjugate bridge

- card.md:1337–1339 — “`FiniteHeatOperator X` (for a finite type `X`) is a real matrix `L` with `Lᵀ = L`, `∑ y, L x y = 0` (constant annihilation) and `0 < L x y` for `x ≠ y` (strictly positive off-diagonal entries). It is a genuine discrete Laplace operator”
- card.md:40–45 — “(`exists_unique_finiteHeatKernel`: existence **and** uniqueness among causal kernels); `FiniteConjugateUniqueness.lean` supplies the Grönwall-weighted energy for the *backward* conjugate equation, proves uniqueness of the repaired conjugate predicate below `t₀`, inhabits it with the canonical time-reversed kernel and proves `exists_unique_finiteConjugateKernel`.”
- card.md:128 — “| conjugate-heat refutation (eighth invocation) | `ConjugateHeatKernelExistenceStatement` is **false as formalized**: the two-point Riemannian conjugate-heat spacetime with `laplacian = LinearMap.id`, `scalarMul = 0`, `backwardTimeDerivative = 0` satisfies `IsRiemannianConjugateHeatSpacetime` and admits no kernel (§20.2) |”

---

## B. Declaration census (file:line + full type signature)

Legend: **Y** = declaration exists as named (modulo namespace), **F** = named declaration does not
exist under the card’s spelling. All signatures are quoted from the sources.

### B1. Corrected-domain interface (`release/Poincare/D13/HeatKernelBridge/Basic.lean`)

| card name | src | full statement |
|---|---|---|
| `HeatKernelDataV1` | Basic.lean:78–85 | `structure HeatKernelDataV1 (X : Type*) [TopologicalSpace X] [MeasurableSpace X] where`<br>`  core : Poincare.D11.HeatKernelBridge.HeatKernelCore X`<br>`  testClass : Poincare.D12.HeatDomain.AdmissibleTestClass X core.volume`<br>`  initialConditionFor : Poincare.D12.HeatDomain.WeakInitialConditionFor core testClass` |
| `HeatKernelDataV1.v1` | Basic.lean:70 | `def HeatKernelDataV1.v1 : ℕ := 1` |
| `ofHeatKernelData` | Basic.lean:215–221 | `def ofHeatKernelData (D : Poincare.D7.HeatKernel.HeatKernelData X) : HeatKernelDataV1 X` (fields: `core := D.toCore`, `testClass := …continuousIntegrableClass D.toCore.volume`, `initialConditionFor := (WeakInitialConditionFor.iff_integrableClass …).mp (…of_full D.toCore_fullInitialCondition)`) |
| `exists_toCore_eq_iff` | Basic.lean:242–245 | `theorem exists_toCore_eq_iff (D₀ : Poincare.D11.HeatKernelBridge.HeatKernelCore X) (C : AdmissibleTestClass X D₀.volume) : (∃ D : HeatKernelDataV1 X, D.toCore = D₀ ∧ HEq D.testClass C) ↔ WeakInitialConditionFor D₀ C` |
| `integrableClassVariant_weak_iff` | Basic.lean:257–260 | `theorem integrableClassVariant_weak_iff {D : HeatKernelDataV1 X} (hC : D.IsIntegrableClassVariant) : D.core.WeakInitialCondition ↔ WeakInitialConditionFor D.core (AdmissibleTestClass.continuousIntegrableClass D.core.volume)` — **the card spells this `integrabilityClassVariant_weak_iff` (§F3)** |
| `IsIntegrableClassVariant` | Basic.lean:154–155 | `def IsIntegrableClassVariant (D : HeatKernelDataV1 X) : Prop := D.testClass = AdmissibleTestClass.continuousIntegrableClass D.core.volume` |
| `kernel_nonneg`, `gaussianUpperBound`, `gaussianLowerBound`, `symmetry`, `semigroup`, `normalization`, `heatEquation`, `initialConditionFor_apply` | Basic.lean:167, 171, 176, 182, 186, 191, 196, 201 | field-transfer theorems; e.g. `theorem heatEquation (D) (x y) {t} (ht : 0 < t) : HasDerivAt (fun s : ℝ => D.kernel x y s) (D.laplacian (fun z => D.kernel z y t) x) t` |

### B2. Euclidean transport (`release/Poincare/D13/HeatKernelBridge/EuclideanTransport.lean`)

| card name | src | full statement |
|---|---|---|
| `flatHeatKernelDataV1_integrable` | :74–78 | `noncomputable def flatHeatKernelDataV1_integrable (n : ℕ) : HeatKernelDataV1 (EuclideanSpace ℝ (Fin n)) where core := flatHeatKernelCore n; testClass := AdmissibleTestClass.continuousIntegrableClass (flatHeatKernelCore n).volume; initialConditionFor := flatHeatKernelCore_weakInitialConditionFor_integrableClass n` |
| `flatHeatKernelDataV1_cc` | :86–91 | `noncomputable def flatHeatKernelDataV1_cc (n : ℕ) : HeatKernelDataV1 (EuclideanSpace ℝ (Fin n))` (C_c class; `initialConditionFor := flatHeatKernelCore_weakInitialConditionFor_ccClass n`) |
| `flatHeatKernelDataV1_integrable_kernel_eq_gaussian` | :139–142 | `theorem … (n) (x y) {t} (ht : 0 < t) : (flatHeatKernelDataV1_integrable n).kernel x y t = gaussianKernel n t (x - y)` |
| `flatHeatKernelDataV1_integrable_normalization` | :154–158 | `theorem … (n) (x) {t} (ht : 0 < t) : ∫ y, (flatHeatKernelDataV1_integrable n).kernel x y t ∂(…)volume = 1` |
| `flatHeatKernelDataV1_integrable_semigroup` | :162–168 | `theorem … (n) (x y) {s t} (hs : 0 < s) (ht : 0 < t) : (…).kernel x y (s + t) = ∫ z, (…).kernel x z s * (…).kernel z y t ∂(…).volume` |
| `flatHeatKernelDataV1_integrable_heatEquation` | :172–177 | `theorem … (n) (x y) {t} (ht : 0 < t) : HasDerivAt (fun s : ℝ => (flatHeatKernelDataV1_integrable n).kernel x y s) ((flatHeatKernelDataV1_integrable n).laplacian (fun z => (flatHeatKernelDataV1_integrable n).kernel z y t) x) t` |
| `flatHeatKernelDataV1_integrable_gaussianUpperBound` | :180–186 | Gaussian upper bound exactly as in the interface |
| `flatHeatKernelDataV1_integrable_initialCondition` | :190–195 | `theorem … (n) (x) {f} (hf : Continuous f) (hfi : Integrable f volume) : Tendsto (fun t : ℝ => ∫ y, (…).kernel x y t * f y) (𝓝[>] 0) (𝓝 (f x))` |
| `flatHeatKernelDataV1_cc_initialCondition` | :199–204 | same on the `C_c` class |
| `flatHeatKernelDataV1_cc_bump_initialCondition` | :212–216 | `theorem … (n) : Tendsto (fun t => ∫ y, (flatHeatKernelDataV1_cc n).kernel 0 y t * bump n y ∂…) (𝓝[>] 0) (𝓝 1)` |
| `flat_v1_exists_not_legacy_of_pos` | :227–230 | `theorem … (n : ℕ) (hn : 0 < n) : (∃ D : HeatKernelDataV1 (EuclideanSpace ℝ (Fin n)), D.toCore = flatHeatKernelCore n) ∧ ¬ ∃ D : Poincare.D7.HeatKernel.HeatKernelData (EuclideanSpace ℝ (Fin n)), D.toCore = flatHeatKernelCore n` |
| `flat_legacy_exists_zero` | :236–239 | `theorem flat_legacy_exists_zero : ∃ D : Poincare.D7.HeatKernel.HeatKernelData (EuclideanSpace ℝ (Fin 0)), D.toCore = flatHeatKernelCore 0` |
| `flat_v1_of_legacy_zero` | :242–244 | `theorem flat_v1_of_legacy_zero : (ofHeatKernelData flatHeatKernelData_zero).core = flatHeatKernelCore 0` |

### B3. Compact upgrade (`release/Poincare/D13/HeatKernelBridge/CompactUpgrade.lean`)

| card name | src | full statement |
|---|---|---|
| `toHeatKernelData_of_integrableClass` | :69–76 | `noncomputable def … [CompactSpace X] [OpensMeasurableSpace X] (D : HeatKernelDataV1 X) [IsFiniteMeasure D.core.volume] (hC : D.IsIntegrableClassVariant) : Poincare.D7.HeatKernel.HeatKernelData X` |
| `toHeatKernelData_of_ccClass` | :101–112 | `noncomputable def … [CompactSpace X] [OpensMeasurableSpace X] (D : HeatKernelDataV1 X) [IsFiniteMeasureOnCompacts D.core.volume] (hC : D.testClass = AdmissibleTestClass.continuousCompactSupportClass D.core.volume) : Poincare.D7.HeatKernel.HeatKernelData X` |
| `toHeatKernelData_of_integrableClass_toCore` | :80–84 | `theorem … : (toHeatKernelData_of_integrableClass (D := D) hC).toCore = D.core` |
| `toHeatKernelData_of_integrableClass_initialCondition` | :87–92 | `theorem … (x : X) (f : X → ℝ) (hf : Continuous f) : Tendsto (fun t => ∫ y, (…).kernel x y t * f y ∂(…).volume) (𝓝[>] 0) (𝓝 (f x))` |
| `toHeatKernelData_of_ccClass_initialCondition` | :123–129 | same for the `C_c` upgrade |
| `ofHeatKernelData_upgrade_eq` | :138–145 | `theorem … [CompactSpace X] [OpensMeasurableSpace X] (D : Poincare.D7.HeatKernel.HeatKernelData X) [IsFiniteMeasure D.toCore.volume] : toHeatKernelData_of_integrableClass (D := ofHeatKernelData D) (ofHeatKernelData_integrableClassVariant D) = D` |
| `exists_v1_iff_exists_legacy` | :153–157 | `theorem … {X} [TopologicalSpace X] [MeasurableSpace X] [CompactSpace X] [OpensMeasurableSpace X] (core : HeatKernelCore X) [IsFiniteMeasure core.volume] : (∃ D : HeatKernelDataV1 X, D.toCore = core ∧ D.IsIntegrableClassVariant) ↔ (∃ D : Poincare.D7.HeatKernel.HeatKernelData X, D.toCore = core)` |

### B4. D7 consumer interface (`release/Poincare/D7/HeatKernel/V1Interface.lean`)

| card name | src | full statement |
|---|---|---|
| `IsHeatKernelV1` | :67–78 | `structure IsHeatKernelV1 {M} [TopologicalSpace M] [MeasurableSpace M] (S : HeatSpacetime M) (C : AdmissibleTestClass M S.volume) (K : M → M → ℝ → ℝ) : Prop where`<br>`  positive : ∀ x y t, 0 < t → 0 < K x y t`<br>`  solves : ∀ y t, 0 < t → S.heatOperator (fun x => K x y t) = 0`<br>`  normalized : ∀ y t, 0 < t → ∫ x, K x y t ∂S.volume = 1`<br>`  dirac_limitFor : ∀ (f : M → ℝ), C.cls f → ∀ y : M, Tendsto (fun t : ℝ => ∫ x, K x y t * f x ∂S.volume) (𝓝[>] (0 : ℝ)) (𝓝 (f y))` |
| `HeatKernelExistenceStatementV1` | :87–91 | `def HeatKernelExistenceStatementV1 : Prop := ∀ (M : Type*) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] (S : HeatSpacetime M), IsClosedRiemannianManifold S → ∀ y₀ : M, ∃ K : M → M → ℝ → ℝ, IsHeatKernelV1 S (AdmissibleTestClass.continuousIntegrableClass S.volume) K` |
| `isHeatKernelV1_integrable_iff_of_closed` | :102–106 | `theorem … {M} [..] [BorelSpace M] (S : HeatSpacetime M) (hclosed : IsClosedRiemannianManifold S) (K : M → M → ℝ → ℝ) : IsHeatKernelV1 S (AdmissibleTestClass.continuousIntegrableClass S.volume) K ↔ IsHeatKernel S K` |
| `heatKernelExistenceStatement_iff_v1` | :120, 128–129 | `universe u` … `theorem heatKernelExistenceStatement_iff_v1 : (HeatKernelExistenceStatement.{u} : Prop) ↔ (HeatKernelExistenceStatementV1.{u} : Prop)` |
| `v1_flat_inhabited` | :143–147 | `theorem v1_flat_inhabited (n : ℕ) : ∃ D : HeatKernelDataV1 (EuclideanSpace ℝ (Fin n)), D.toCore = flatHeatKernelCore n ∧ D.IsIntegrableClassVariant` |
| `v1_flat_no_legacy_of_pos` | :152–154 | `theorem … (n) (hn : 0 < n) : ¬ ∃ D : HeatKernelData (EuclideanSpace ℝ (Fin n)), D.toCore = flatHeatKernelCore n` |
| `punit_v1_upgrade_eq` | :162–168 | `theorem punit_v1_upgrade_eq : @toHeatKernelData_of_integrableClass PUnit _ _ _ _ (ofHeatKernelData punitHeatKernelData) (by …) (ofHeatKernelData_integrableClassVariant punitHeatKernelData) = punitHeatKernelData` |

The legacy statements these compare against are the unmodified D7 sources:
`D7/HeatKernel/Blocked.lean:158–168` (`structure IsHeatKernel … solves : ∀ y t, 0 < t → S.heatOperator (fun x => K x y t) = 0 …`),
`D7/HeatKernel/Blocked.lean:188–191` (`def HeatKernelExistenceStatement : Prop := ∀ (M : Type*) [..] (S : HeatSpacetime M), IsClosedRiemannianManifold S → ∀ y₀ : M, ∃ K, IsHeatKernel S K`),
`D7/HeatKernel/Blocked.lean:76–77` (`def heatOperator (S) (u) : M → ℝ := S.timeDerivative u - S.laplacian u`),
`D7/HeatKernel/Blocked.lean:103–118` (`structure IsClosedRiemannianManifold` — exactly the seven fields claimed).

### B5. Predicate semantics (`release/Poincare/D13/HeatKernelBridge/PredicateSemantics.lean`)

| card name | src | full statement |
|---|---|---|
| `heatOperator_eq_zero_iff` | :88–89 | `theorem heatOperator_eq_zero_iff (S : HeatSpacetime M) (u : M → ℝ) : S.heatOperator u = 0 ↔ S.timeDerivative u = S.laplacian u` |
| `isHeatKernel_laplacian_snapshot_eq_timeDerivative` | :95–97 | `theorem … {S} {K} (hK : IsHeatKernel S K) (y) {t} (ht : 0 < t) : S.laplacian (fun x => K x y t) = S.timeDerivative (fun x => K x y t)` |
| `isHeatKernelV1_laplacian_snapshot_eq_timeDerivative` | :103–106 | same for `IsHeatKernelV1 S C K` |
| `isHeatKernel_laplacian_snapshot_eq_zero_of_timeDerivative_eq_zero` | :112–114 | `theorem … (hT : S.timeDerivative = 0) {K} (hK : IsHeatKernel S K) (y) {t} (ht : 0 < t) : S.laplacian (fun x => K x y t) = 0` |
| `isHeatKernelV1_…` | :120–123 | same for `IsHeatKernelV1` |
| `heatOperator_eq_zero_of_timeDerivative_eq_laplacian` | :131–132 | `theorem … (hT : S.timeDerivative = S.laplacian) (u : M → ℝ) : S.heatOperator u = 0` |
| `flatHeatSpacetime` | :141–146 | `noncomputable def flatHeatSpacetime (n : ℕ) : HeatSpacetime (EuclideanSpace ℝ (Fin n)) where volume := volume; laplacian := (flatHeatKernelCore n).laplacian; timeDerivative := 0; dist := fun x y => ‖x - y‖; dim := (n : ℝ)` |
| `flatKernel_laplacian_snapshot_ne_zero` | :163–164 | `theorem … (n) (hn : 0 < n) : (flatHeatKernelCore n).laplacian (fun z => flatKernel n z 0 1) 0 ≠ 0` |
| `flatHeatSpacetime_positive/_normalized/_dirac_limitFor` | :178, :184, :195 | the three other predicate fields for the D10 kernel / honest flat spacetime |
| `flatHeatSpacetime_not_isHeatKernelV1_integrableClass` | :220–223 | `theorem … (n) (hn : 0 < n) : ¬ IsHeatKernelV1 (flatHeatSpacetime n) (AdmissibleTestClass.continuousIntegrableClass (flatHeatSpacetime n).volume) (flatKernel n)` |
| `flatHeatSpacetime_not_isHeatKernel` | :234–235 | `theorem … (n) (hn : 0 < n) : ¬ IsHeatKernel (flatHeatSpacetime n) (flatKernel n)` |

### B6. PDE repair candidate (`release/Poincare/D13/HeatKernelBridge/PDERepair.lean`)

| card name | src | full statement |
|---|---|---|
| `IsHeatKernelPDE.v2` | :76 | `def IsHeatKernelPDE.v2 : ℕ := 2` |
| `IsHeatKernelPDE` | :91–102 | `structure IsHeatKernelPDE (S : HeatSpacetime M) (C : AdmissibleTestClass M S.volume) (K : M → M → ℝ → ℝ) : Prop where`<br>`  positive : ∀ x y t, 0 < t → 0 < K x y t`<br>`  solvesPDE : ∀ x y t, 0 < t → HasDerivAt (fun s : ℝ => K x y s) (S.laplacian (fun z => K z y t) x) t`<br>`  normalized : ∀ y t, 0 < t → ∫ x, K x y t ∂S.volume = 1`<br>`  dirac_limitFor : ∀ (f : M → ℝ), C.cls f → ∀ y : M, Tendsto (fun t : ℝ => ∫ x, K x y t * f x ∂S.volume) (𝓝[>] (0 : ℝ)) (𝓝 (f y))` |
| `IsHeatKernelPDE.solvesPDE_hasDerivAt` | :109–112 | `theorem … (h : IsHeatKernelPDE S C K) (x y) {t} (ht : 0 < t) : HasDerivAt (fun s : ℝ => K x y s) (S.laplacian (fun z => K z y t) x) t` |
| `HeatKernelDataV1.toHeatSpacetime` | :126–131 | `noncomputable def … (D : HeatKernelDataV1 X) : HeatSpacetime X where volume := D.volume; laplacian := D.laplacian; timeDerivative := 0; dist := D.dist; dim := D.dim` |
| `HeatKernelDataV1.kernel_pos_of_dist_le_one` | :157–158 | `theorem … (D) (hC : 0 < D.C_lo) {x y} {t} (ht : 0 < t) (hxy : D.dist x y ≤ 1) : 0 < D.kernel x y t` |
| `IsHeatKernelPDE.of_dataV1` | :173–178 | `theorem … {X} [TopologicalSpace X] [MeasurableSpace X] (D : HeatKernelDataV1 X) (hpos : ∀ x y t, 0 < t → 0 < D.kernel x y t) (C : AdmissibleTestClass X D.volume) (hsub : ∀ (f : X → ℝ), C.cls f → D.testClass.cls f) : IsHeatKernelPDE D.toHeatSpacetime C D.kernel` |
| `IsHeatKernelPDE.of_dataV1_integrableClass` | :200–204 | `theorem … (D) (hpos : …) (hC : D.IsIntegrableClassVariant) : IsHeatKernelPDE D.toHeatSpacetime (AdmissibleTestClass.continuousIntegrableClass D.volume) D.kernel` |
| `IsHeatKernelPDE.of_dataV1_ccClass` | :210–215 | same on the `C_c` class |
| `flat_isHeatKernelPDE_integrable` | :233–241 | `theorem … (n : ℕ) : IsHeatKernelPDE (flatHeatSpacetime n) (AdmissibleTestClass.continuousIntegrableClass (flatHeatSpacetime n).volume) (flatKernel n)` |
| `flat_isHeatKernelPDE_cc` | :246–259 | same on the `C_c` class |
| `flat_pde_repaired_scope` | :264–270 | `theorem … (n) (hn : 0 < n) : IsHeatKernelPDE (flatHeatSpacetime n) (…continuousIntegrableClass…) (flatKernel n) ∧ ¬ IsHeatKernelV1 (flatHeatSpacetime n) (…same class…) (flatKernel n)` |
| `not_forall_isHeatKernelPDE_imp_isHeatKernelV1` | :279–282 | `theorem … : ¬ (∀ (M : Type) [TopologicalSpace M] [MeasurableSpace M] (S : HeatSpacetime M) (C : AdmissibleTestClass M S.volume) (K : M → M → ℝ → ℝ), IsHeatKernelPDE S C K → IsHeatKernelV1 S C K)` |

### B7. Statement refutation (`release/Poincare/D13/HeatKernelBridge/StatementRefutation.lean`)

| card name | src | full statement |
|---|---|---|
| `refutingSpacetime` | :84–89 | `noncomputable def refutingSpacetime : HeatSpacetime PUnit where volume := Measure.dirac PUnit.unit; laplacian := LinearMap.id; timeDerivative := 0; dist := fun _ _ => 0; dim := 0` |
| `refutingSpacetime_isClosedRiemannianManifold` | :122–123 | `theorem … : IsClosedRiemannianManifold refutingSpacetime` |
| `subsingleton_measurableSpace_punit` | :181 | `theorem subsingleton_measurableSpace_punit : Subsingleton (MeasurableSpace PUnit)` |
| `not_isHeatKernel_of_laplacian_id_timeDerivative_zero` | :146–149 | `theorem … {M} [TopologicalSpace M] [MeasurableSpace M] [Nonempty M] (S : HeatSpacetime M) (hlapl : S.laplacian = LinearMap.id) (hT : S.timeDerivative = 0) (K : M → M → ℝ → ℝ) : ¬ IsHeatKernel S K` |
| `not_isHeatKernelV1_of_laplacian_id_timeDerivative_zero` | :162–166 | same schema for `IsHeatKernelV1 S C K`, arbitrary `C` |
| `not_heatKernelExistenceStatement_of_refuting` | :194–197 | `theorem … {M : Type u} [..] [BorelSpace M] [Nonempty M] (S) (hclosed) (hlapl : S.laplacian = LinearMap.id) (hT : S.timeDerivative = 0) : ¬ HeatKernelExistenceStatement.{u}` |
| `not_heatKernelExistenceStatementV1_of_refuting` | :203–206 | same for `¬ HeatKernelExistenceStatementV1.{u}` |
| `not_heatKernelExistenceStatement` | :214 | `theorem not_heatKernelExistenceStatement : ¬ HeatKernelExistenceStatement` |
| `not_heatKernelExistenceStatementV1` | :223 | `theorem not_heatKernelExistenceStatementV1 : ¬ HeatKernelExistenceStatementV1` |

### B8. Geometric repair, second refutation, rescaling, repaired statements (`release/Poincare/D13/HeatKernelBridge/GeometricRepair.lean`)

| card name | src | full statement |
|---|---|---|
| `AnnihilatesConstants` | :139–141 | `structure AnnihilatesConstants (S : HeatSpacetime M) : Prop where laplacian_one : S.laplacian 1 = 0` |
| `not_isAnnihilatesConstants_refutingSpacetime` | :156–157 | `theorem … : ¬ AnnihilatesConstants refutingSpacetime` |
| `exists_isClosedRiemannianManifold_not_isAnnihilatesConstants` | :166–167 | `theorem … : ∃ S : HeatSpacetime PUnit, IsClosedRiemannianManifold S ∧ ¬ AnnihilatesConstants S` |
| `punitDiracSpacetime` | :174–179 | `noncomputable def punitDiracSpacetime : HeatSpacetime PUnit` (Dirac volume, zero operators, zero distance, `dim = 0`) |
| `isAnnihilatesConstants_punitDiracSpacetime` | :217–219 | `theorem … : AnnihilatesConstants punitDiracSpacetime` |
| `flatHeatSpacetime_laplacian_one` | :225–226 | `theorem … (n) : (flatHeatSpacetime n).laplacian (1 : …) = 0` |
| `adversarialTimeDerivativeSpacetime` | :240–245 | `noncomputable def … : HeatSpacetime PUnit where volume := Measure.dirac PUnit.unit; laplacian := 0; timeDerivative := LinearMap.id; dist := …0; dim := 0` |
| `adversarialTimeDerivativeSpacetime_isClosedRiemannianManifold` | :266–267 | `theorem … : IsClosedRiemannianManifold adversarialTimeDerivativeSpacetime` |
| `isAnnihilatesConstants_adversarialTimeDerivativeSpacetime` | :286–288 | `theorem … : AnnihilatesConstants adversarialTimeDerivativeSpacetime` |
| `not_exists_isHeatKernelV1_adversarialTimeDerivativeSpacetime` | :293–297 | `theorem … : ¬ ∃ K : PUnit → PUnit → ℝ → ℝ, IsHeatKernelV1 adversarialTimeDerivativeSpacetime (…continuousIntegrableClass…) K` |
| `not_isHeatKernel_of_laplacian_zero_timeDerivative_id` | :311–314 | `theorem … (S) (hlapl : S.laplacian = 0) (hT : S.timeDerivative = LinearMap.id) (K) : ¬ IsHeatKernel S K` |
| `not_isHeatKernelV1_of_laplacian_zero_timeDerivative_id` | :327–330 | same schema for `IsHeatKernelV1 S C K` |
| `not_forall_annihilatesConstants_implies_exists_snapshot_kernel_of_refuting` | :344–352 | `theorem … {M : Type u} … (S) (hclosed) (hann : AnnihilatesConstants S) (hlapl : S.laplacian = 0) (hT : S.timeDerivative = LinearMap.id) : ¬ (∀ (M : Type u) [..] (S : HeatSpacetime M), IsClosedRiemannianManifold S → AnnihilatesConstants S → ∀ y₀ : M, ∃ K : M → M → ℝ → ℝ, IsHeatKernelV1 S (…continuousIntegrableClass…) K)` |
| `not_forall_annihilatesConstants_implies_exists_snapshot_kernel` | :362–367 | same negated schema, unconditional (universe 0) |
| `flatSnapshotSpacetime` | :381–386 | `noncomputable def flatSnapshotSpacetime (n) : HeatSpacetime (EuclideanSpace ℝ (Fin n)) where volume := volume; laplacian := (flatHeatKernelCore n).laplacian; timeDerivative := (flatHeatKernelCore n).laplacian; dist := …; dim := n` |
| `flatSnapshotSpacetime_heatOperator_eq_zero` | :409–411 | `theorem … (n) (u) : (flatSnapshotSpacetime n).heatOperator u = 0` |
| `flatKernelRescaled` | :414–416 | `noncomputable def flatKernelRescaled (n) (c) (x y) (t) : ℝ := flatKernel n x y (c * t)` |
| `flatKernelRescaled_isHeatKernelV1` | :421–424 | `theorem … (n) {c} (hc : 0 < c) : IsHeatKernelV1 (flatSnapshotSpacetime n) (…continuousIntegrableClass…) (flatKernelRescaled n c)` |
| `flatKernel_laplacian_snapshot_ne_zero_of_pos` | :442–443 | `theorem … (n) (hn : 0 < n) {t} (ht : 0 < t) : (flatHeatKernelCore n).laplacian (fun z => flatKernel n z 0 t) 0 ≠ 0` |
| `flatKernelRescaled_not_isHeatKernelPDE` | :461–464 | `theorem … (n) (hn : 0 < n) : ¬ IsHeatKernelPDE (flatSnapshotSpacetime n) (…continuousIntegrableClass…) (flatKernelRescaled n 2)` |
| `not_forall_isHeatKernelV1_imp_isHeatKernelPDE` | :485–488 | `theorem … : ¬ (∀ (M : Type) [..] (S) (C) (K), IsHeatKernelV1 S C K → IsHeatKernelPDE S C K)` |
| `snapshot_pde_predicates_incomparable` | :503–510 | `theorem … : (¬ ∀ … IsHeatKernelPDE S C K → IsHeatKernelV1 S C K) ∧ (¬ ∀ … IsHeatKernelV1 S C K → IsHeatKernelPDE S C K)` |
| `HeatKernelExistenceStatementPDE` | :519–523 | `def … : Prop := ∀ (M : Type*) [..] (S : HeatSpacetime M), IsClosedRiemannianManifold S → AnnihilatesConstants S → ∀ y₀ : M, ∃ K : M → M → ℝ → ℝ, IsHeatKernelPDE S (AdmissibleTestClass.continuousIntegrableClass S.volume) K` |
| `HeatKernelDataExistenceStatement` | :531–536 | `def … : Prop := ∀ (M : Type*) [..] (S), IsClosedRiemannianManifold S → AnnihilatesConstants S → ∀ y₀ : M, ∃ D : HeatKernelData M, D.volume = S.volume ∧ D.dist = S.dist ∧ D.dim = S.dim ∧ D.laplacian = S.laplacian ∧ (∀ x y t, 0 < t → 0 < D.kernel x y t) ∧ 0 < D.C_lo` |
| `heatKernelDataExistenceStatement_implies_pde` | :544–545 | `theorem … .{u} (h : HeatKernelDataExistenceStatement.{u}) : HeatKernelExistenceStatementPDE.{u}` |
| `heatKernelDataExistenceStatement_conclusion_punit` / `_adversarial` | :570–576 / :636–644 | explicit existential conclusions on the one-point models (matching volume/dist/dim/laplacian, positivity, `0 < C_lo`) |
| `heatKernelExistenceStatementPDE_conclusion_punit` / `_adversarial` | :613–617 / :624–629 | explicit `IsHeatKernelPDE` witnesses on the same models |
| `not_both_isClosedRiemannianManifold_and_annihilatesConstants_refutingSpacetime` | **does not exist**; source name :581–583 | `theorem not_both_isClosedRiemannianManifold_and_isAnnihilatesConstants_refutingSpacetime : ¬ (IsClosedRiemannianManifold refutingSpacetime ∧ AnnihilatesConstants refutingSpacetime)` — **the card drops the `is` (§F3)** |

### B9. Non-self-adjointness (`release/Poincare/D13/HeatKernelBridge/LaplacianSymmetryRefutation.lean`)

| card name | src | full statement |
|---|---|---|
| `flatLineSpacetime` | :107–112 | `noncomputable def flatLineSpacetime : HeatSpacetime ℝ where volume := volume; laplacian := laplacianLinearMap ℝ; timeDerivative := 0; dist := fun x y => |x - y|; dim := 1` |
| `laplacian_log_cosh` | :122–124 | `theorem … : (laplacianLinearMap ℝ) (fun x : ℝ => Real.log (Real.cosh x)) = fun x => 1 - Real.tanh x ^ 2` |
| `integral_one_sub_tanh_sq` | :182 | `theorem … : ∫ x : ℝ, (1 - Real.tanh x ^ 2) = 2` |
| `not_forall_laplacian_symmetric_flatLine` | :192–195 | `theorem … : ¬ (∀ u v : ℝ → ℝ, (∫ x, u x * flatLineSpacetime.laplacian v x ∂flatLineSpacetime.volume) = ∫ x, flatLineSpacetime.laplacian u x * v x ∂flatLineSpacetime.volume)` |

### B10. Data-level refutation and positive counterpart (`release/Poincare/D13/HeatKernelBridge/DataRefutation.lean`)

| card name | src | full statement |
|---|---|---|
| `eq_of_hasDerivAt_zero_of_pos` | :91 | time-constancy lemma for vanishing derivative on `(0,∞)` |
| `not_exists_isHeatKernelPDE_of_laplacian_eq_zero` | :111–115 | general schema: `S.laplacian = 0`, unit atom at `p`, indicator admissible, `p ≠ y` ⇒ no `IsHeatKernelPDE` inhabitant |
| `not_exists_heatKernelData_of_laplacian_eq_zero` | :147–153 | same at the legacy datum level: `¬ ∃ D : HeatKernelData M, D.volume = S.volume ∧ D.laplacian = S.laplacian ∧ (∀ x y t, 0 < t → 0 < D.kernel x y t)` |
| `twoPointSpacetime` | :194–199 | `noncomputable def twoPointSpacetime : HeatSpacetime Bool where volume := twoPointVolume; laplacian := 0; timeDerivative := 0; dist := fun x y => if x = y then 0 else 1; dim := 0` |
| `isClosedRiemannianManifold_twoPointSpacetime` | :220–221 | `theorem … : IsClosedRiemannianManifold twoPointSpacetime` |
| `isAnnihilatesConstants_twoPointSpacetime` | :263 | `theorem … : AnnihilatesConstants twoPointSpacetime` |
| `not_heatKernelExistenceStatementPDE_of_refuting` | :316–322 | `theorem … {M : Type u} … (S) (hclosed) (hlapl : S.laplacian = 0) {p} (hp) (hcls) {y} (hpy : p ≠ y) : ¬ HeatKernelExistenceStatementPDE.{u}` |
| `not_heatKernelDataExistenceStatement_of_refuting` | :331–336 | same hypotheses ⇒ `¬ HeatKernelDataExistenceStatement.{u}` |
| `not_exists_isHeatKernelPDE_twoPointSpacetime` | :344–347 | `theorem … : ¬ ∃ K : Bool → Bool → ℝ → ℝ, IsHeatKernelPDE twoPointSpacetime (…continuousIntegrableClass…) K` |
| `not_exists_heatKernelData_twoPointSpacetime` | :354–357 | `theorem … : ¬ ∃ D : HeatKernelData Bool, D.volume = twoPointSpacetime.volume ∧ D.laplacian = twoPointSpacetime.laplacian ∧ (∀ x y t, 0 < t → 0 < D.kernel x y t)` |
| `not_heatKernelExistenceStatementPDE` | :367 | `theorem not_heatKernelExistenceStatementPDE : ¬ HeatKernelExistenceStatementPDE.{0}` |
| `not_heatKernelDataExistenceStatement` | :380 | `theorem not_heatKernelDataExistenceStatement : ¬ HeatKernelDataExistenceStatement.{0}` |
| `twoPointIdentityKernel` / `twoPointDegenerateData` | :395 / :408 | identity kernel `if x = y then 1 else 0`; the degenerate `HeatKernelData Bool` with `C_lo = 0` |
| `twoPointDegenerateData_not_strictly_positive` | :525 | failure of strict positivity off-diagonal |
| `twoPoint_data_scope` | :536 | packages hypotheses + degenerate datum + no strictly positive datum |
| `FlatCorrectedDomainExistence` / `flatCorrectedDomainExistence_proved` | :559–563 / :568–576 | `def … : Prop := ∀ n, ∃ D : HeatKernelDataV1 (EuclideanSpace ℝ (Fin n)), D.IsIntegrableClassVariant ∧ (∀ x y t, 0 < t → 0 < D.kernel x y t) ∧ (∀ x y t, 0 < t → D.kernel x y t = gaussianKernel n t (x - y))`; proved |
| `correctedDomain_is_exact_scope` | :582–586 | `theorem … : FlatCorrectedDomainExistence ∧ ¬ HeatKernelDataExistenceStatement.{0} ∧ ¬ HeatKernelExistenceStatementPDE.{0}` |

### B11. Conjugate half (`release/Poincare/D13/HeatKernelBridge/ConjugateHeatBridge.lean` + D7 consumer)

| card name | src | full statement |
|---|---|---|
| `not_conjugateHeatKernelExistenceStatement` | ConjugateHeatBridge.lean:192–193 | `theorem … : ¬ ConjugateHeatKernelExistenceStatement.{0}` |
| `conjugateRefutingSpacetime` | :136–140 | two-point volume, `laplacian := LinearMap.id`, `scalarMul := 0`, `backwardTimeDerivative := 0` |
| `isRiemannianConjugateHeatSpacetime_conjugateRefuting` | :162–163 | `theorem … : IsRiemannianConjugateHeatSpacetime conjugateRefutingSpacetime` |
| `not_exists_isConjugateHeatKernel_conjugateRefuting` | :169–171 | `theorem … (t₀) : ¬ ∃ K : Bool → Bool → ℝ → ℝ, IsConjugateHeatKernel conjugateRefutingSpacetime t₀ K` |
| `IsConjugateHeatKernelPDE.v2` / `IsConjugateHeatKernelPDE` | :217 / :229–242 | `def … .v2 : ℕ := 2`; `structure … (S : ConjugateHeatSpacetime M) (t₀ : ℝ) (C) (K) : Prop where positive : ∀ x y t, t < t₀ → 0 < K x y t; solvesPDE : ∀ x y t, t < t₀ → HasDerivAt (fun s => K x y s) (-(S.laplacian (fun z => K z y t) x) + S.scalarMul (fun z => K z y t) x) t; normalized : …; dirac_limitFor : …` |
| `IsConjugateHeatKernelPDE.of_dataV1` (+ `_integrableClass`, `_ccClass`) | :303, :339, :350 | transports any corrected-domain datum to the repaired predicate by `t ↦ t₀ - t` |
| `flat_isConjugateHeatKernelPDE_integrableClass` / `_cc` | :399 / :411 | D10 kernel inhabits the repaired predicate in every dimension and terminal time |
| `flatConjugate_not_isConjugateHeatKernel` | :431–432 | `theorem … (n) (hn : 0 < n) (t₀) : ¬ IsConjugateHeatKernel (flatConjugateHeatSpacetime n) t₀ (flatConjugateKernel n t₀)` |
| `flat_conjugate_repaired_scope` | :452–456 | repaired predicate inhabited ∧ unrepaired refuted, same kernel/spacetime |
| `not_forall_isConjugateHeatKernelPDE_imp_isConjugateHeatKernel` | :465–469 | non-implication theorem |
| `flatConjugateKernel_symm` / `_mass` / `_mass_eq` / `_semigroup` | :485, :495, :503, :512–516 | symmetry; unit mass; mass equality; `flatConjugateKernel n t₀ x y (s + t - t₀) = ∫ z, flatConjugateKernel n t₀ x z s * flatConjugateKernel n t₀ z y t ∂…` under `s < t₀`, `t < t₀`, `t₀ < s+t`, `s+t < 2t₀` |
| `FlatConjugateCorrectedDomainExistence` / `flatConjugateCorrectedDomainExistence_proved` / `conjugateCorrection_is_exact_scope` | :535–538 / :542–544 / :550–552 | statement def + proof + `… ∧ ¬ ConjugateHeatKernelExistenceStatement.{0}` |
| D7 `Poincare.D7.ConjugateHeat.Status` names | `D7/ConjugateHeat/Status.lean:56, 65, 72, 79, 90, 99, 111, 122` | all 8 exist (see §F4 for the count claim) |

### B12. Finite pinned model (`FiniteSpaceHeat.lean`, `FiniteUniqueness.lean`, `FiniteConjugateUniqueness.lean`, consumers)

| card name | src | full statement |
|---|---|---|
| `FiniteHeatOperator` | FiniteSpaceHeat.lean:124–132 | `structure FiniteHeatOperator (X : Type*) [Fintype X] [DecidableEq X] where L : Matrix X X ℝ; symmetric : Lᵀ = L; conservative : ∀ x, ∑ y, L x y = 0; offdiag_pos : ∀ x y, x ≠ y → 0 < L x y` |
| `FiniteHeatOperator.laplacian` | :139–140 | `noncomputable def laplacian (G) : (X → ℝ) →ₗ[ℝ] (X → ℝ) := G.L.mulVecLin` |
| `laplacian_one`, `laplacian_selfAdjoint`, `laplacian_dirichlet_identity`, `laplacian_quadraticForm_nonpos`, `laplacian_ne_zero` | :154, :177, :194, :249, :258 | the five structural theorems claimed in card.md:1343–1347 |
| `finiteHeatKernel` | :578–579 | `noncomputable def finiteHeatKernel (G) (x y) (t) : ℝ := if 0 < t then (NormedSpace.exp (t • G.L)) x y else 0` |
| `finiteHeatKernel_pos/_symm/_row_sum/_normalization/_semigroup/_hasDerivAt/_dirac/_le_one/_ne_dirac` | :596, :601, :613, :618, :623, :632, :649, :608, :821 | kernel laws (card.md:1353–1371) |
| `FinitePinnedHeatExistenceStatement` / `finitePinnedHeatExistenceStatement_proved` | :807–812 / :815–816 | `def … : Prop := ∀ (X : Type*) [Fintype X] [DecidableEq X] [TopologicalSpace X] [MeasurableSpace X] [MeasurableSingletonClass X] (G : FiniteHeatOperator X), ∃ K : X → X → ℝ → ℝ, IsHeatKernelPDE (finiteHeatSpacetime G) (…continuousIntegrableClass (Measure.count)…) K`; proved |
| `exists_unique_finiteHeatKernel` | FiniteUniqueness.lean:372–378 | `theorem … (G : FiniteHeatOperator X) : ∃! K : X → X → ℝ → ℝ, (∀ x y t, t ≤ 0 → K x y t = 0) ∧ (∀ x y t, 0 < t → HasDerivAt (fun s => K x y s) (G.laplacian (fun z => K z y t) x) t) ∧ (∀ z y, Tendsto (fun t => K z y t) (𝓝[>] 0) (𝓝 (if z = y then 1 else 0)))` |
| `exists_unique_finiteConjugateKernel` | FiniteConjugateUniqueness.lean:424–430 | `theorem … (G) (t₀) : ∃! K, (∀ x y t, t₀ ≤ t → K x y t = 0) ∧ (∀ x y t, t < t₀ → HasDerivAt (fun s => K x y s) (-(G.laplacian (fun z => K z y t) x)) t) ∧ (∀ z y, Tendsto (fun t => K z y t) (𝓝[<] t₀) (𝓝 (if z = y then 1 else 0)))` |
| D7 consumers’ names | `D7/HeatKernel/{FiniteStatus,UniquenessStatus}.lean`, `D7/ConjugateHeat/UniquenessStatus.lean` | all named declarations exist (verified by declaration census) |

### B13. Declaration-name census result

A programmatic pass over all backticked identifiers in the card (455 candidates) against declaration
positions in the D13/D7 sources found **exactly two project declarations named by the card that do not
exist under the printed spelling** (`integrabilityClassVariant_weak_iff`,
`not_both_…_and_annihilatesConstants_…`; §F3). All other project names resolve in the D13/D7 sources;
names used by the D13 proofs but defined downstream (e.g. `flatKernel_of_pos`, `flatKernel_pos`,
`flatHeatKernelCore_weakInitialConditionFor_*`, `flatHeatKernelData_zero`,
`not_exists_heatKernelData_flat_of_pos`, `continuous_integrable_of_compactSpace_finiteMeasure`,
`punitHeatKernelData`) were checked separately and exist in D10/D11/D12/D7 sources (e.g.
`D11/HeatKernelBridge/EuclideanInstance.lean:60,88`, `D12/HeatDomain/FlatInstance.lean:55,66`,
`D12/HeatDomain/Counterexample.lean:313`, `D7/HeatKernel/Instance.lean:43`). Mathlib names such as
`Matrix.exp_add_of_commute`, `hasSum_single`, `mulVecLin_apply`, `Summable.le_tsum` are not in the
transported tree and were not independently checked.

A declaration-site census of the **23 card files** (15 D13 + 8 D7) found **411 declaration sites**;
409 of them are entries of `bridgeAuditedDeclarations` in `AxiomAudit.lean:420–829`, the other two
being `AxiomAudit`’s own `bridgeAuditedDeclarations` and `bridgeApprovedAxioms`. This **exactly
reproduces the card’s “409 audited declarations”** and supports the claim that every declaration of
the card files is in the audit list. (The audit list has 409 names; the file contains 280 literal
`#print axioms` commands, so the docstring’s “every declaration … is printed with `#print axioms`” is
literally false, while the enforceable 409-name `Lean.collectAxioms` check is complete — see §F6.)

---

## C. Semantic classification

Classification vocabulary: **general** (unconditional mathematical statement), **conditional**
(mathematical statement with hypotheses that are not discharged), **model** (statement about an
explicitly defined model/instance), **statement-only** (a `Prop` definition that is *not* proved),
**bookkeeping** (definitional projection/tag).

| headline declaration(s) | class | justification from the type |
|---|---|---|
| `HeatKernelDataV1`, `HeatKernelDataV1.v1`, `IsHeatKernelV1`, `IsHeatKernelPDE`, `IsConjugateHeatKernelPDE`, `FiniteHeatOperator`, `AnnihilatesConstants` | model / interface definitions; `v1`/`v2` are bookkeeping | structures/`def`s introducing data or predicates; no mathematical content asserted |
| `ofHeatKernelData`, `integrableClassVariant_weak_iff`, `exists_toCore_eq_iff` | general | unconditional (modulo typeclasses); embedding/tightness with no extra hypothesis |
| `flatHeatKernelDataV1_integrable`, `flatHeatKernelDataV1_cc` + transfer theorems (`…_kernel_eq_gaussian`, `…_normalization`, `…_semigroup`, `…_heatEquation`, `…_gaussianUpperBound`, `…_initialCondition`, `…_bump_initialCondition`) | model | explicit Euclidean model, unconditional in `n : ℕ` and `t > 0` |
| `flat_v1_exists_not_legacy_of_pos`, `flat_legacy_exists_zero`, `flat_v1_of_legacy_zero` | general (about a model family) | unconditional in `n`/`hn`; conjunction of an existence and a nonexistence about `flatHeatKernelCore` |
| `toHeatKernelData_of_integrableClass`, `toHeatKernelData_of_ccClass`, `…_toCore`, `…_initialCondition`, `ofHeatKernelData_upgrade_eq`, `exists_v1_iff_exists_legacy` | **conditional** (card calls them “general with fully expanded hypotheses”) | hypotheses are mathlib typeclasses `[CompactSpace X] [OpensMeasurableSpace X] [IsFiniteMeasure …]` plus the explicit class-variant hypothesis `hC`; none assumes the conclusion. Benign but logically conditional |
| `isHeatKernelV1_integrable_iff_of_closed`, `heatKernelExistenceStatement_iff_v1` | general | proved from the statements’ own antecedent; no extra hypothesis |
| `HeatKernelExistenceStatementV1` | statement-only | `def … : Prop`, never proved — and *refuted* (`StatementRefutation.lean:223`) |
| `v1_flat_inhabited`, `v1_flat_no_legacy_of_pos`, `punit_v1_upgrade_eq` | model / instance consumption | explicit witnesses on concrete objects |
| `heatOperator_eq_zero_iff`, snapshot identity theorems, `heatOperator_eq_zero_of_timeDerivative_eq_laplacian` | general | unconditional algebraic facts about the `HeatSpacetime` fields |
| `flatHeatSpacetime` + field lemmas, `flatKernel_laplacian_snapshot_ne_zero`, `flatHeatSpacetime_not_isHeatKernelV1_integrableClass`, `flatHeatSpacetime_not_isHeatKernel` | model (negative result about a model) | unconditonal in `n`, but requires `0 < n`; statements about the explicit flat model |
| `IsHeatKernelPDE.of_dataV1` (+ class specializations) | **conditional** | takes `hpos : ∀ x y t, 0 < t → 0 < D.kernel x y t` (strict positivity, not derivable from the core fields — see `kernel_pos_of_dist_le_one`) and a class-inclusion hypothesis. The positivity hypothesis is a *field of the conclusion*, but the card discloses this (§16.2) and the flat instances discharge it from `flatKernel_pos`; not circular |
| `flat_isHeatKernelPDE_integrable`, `flat_isHeatKernelPDE_cc`, `flat_pde_repaired_scope` | model | explicit D10 inhabitant in every dimension, plus snapshot refutation in positive dimension |
| `not_forall_isHeatKernelPDE_imp_isHeatKernelV1`, `not_forall_isHeatKernelV1_imp_isHeatKernelPDE`, `snapshot_pde_predicates_incomparable`, `not_forall_laplacian_symmetric_flatLine` | general (negative results) | universally quantified non-implications/falsity, no hypotheses |
| `refutingSpacetime` + certificate; `not_isHeatKernel[_V1]_of_laplacian_{id,zero}_timeDerivative_{zero,id}`; `not_heatKernelExistenceStatement[_V1]`; `not_heatKernelExistenceStatementV1_of_refuting` | model/counterexample (the concrete datum) + general negative result (the refutations) | the unconditional refutations have no hypotheses; the schemas take only the two operator equations |
| `AnnihilatesConstants`, `punitDiracSpacetime`, `adversarialTimeDerivativeSpacetime` + certificates | model/interface | explicit datums and a predicate |
| `not_forall_annihilatesConstants_implies_exists_snapshot_kernel[_of_refuting]` | general negative result (unconditional version) / conditional schema (suffix version) | negated universally quantified schema with the geometric hypothesis class |
| `flatSnapshotSpacetime`, `flatKernelRescaled`, `flatKernelRescaled_isHeatKernelV1`, `flatKernelRescaled_not_isHeatKernelPDE` | model | explicit time-rescaled kernel on the vacuous-`solves` flat spacetime |
| `HeatKernelExistenceStatementPDE`, `HeatKernelDataExistenceStatement` | statement-only | `def … : Prop`s, explicitly not proved; both later refuted (`DataRefutation.lean:367,380`) |
| `heatKernelDataExistenceStatement_implies_pde`, the four `…_conclusion_{punit,adversarial}` theorems | general implication / model witnesses | implication is non-circular (data-level hypotheses → predicate-level conclusion); witnesses are explicit |
| `FlatCorrectedDomainExistence` + proof, `correctedDomain_is_exact_scope` | statement definition + model theorem | existence only on the pinned flat family; proved from the transport |
| `twoPoint*` data, `not_exists_*_twoPointSpacetime`, `not_heatKernel{ExistenceStatementPDE,DataExistenceStatement}`, `twoPointDegenerateData*` | model/counterexample + general negative results | unconditional refutations at universe 0; the degenerate datum is a model inhabitant |
| finite layer: structural theorems over `FiniteHeatOperator`, `finiteHeatKernel*`, `finite_isHeatKernelPDE`, `FinitePinnedHeatExistenceStatement` (proved), `exists_unique_finiteHeatKernel`, `exists_unique_finiteConjugateKernel` | general (over an arbitrary pinned finite operator) + model (the explicit matrix-exponential kernel) | quantified over `(X) [Fintype X] … (G : FiniteHeatOperator X)`; no existence assumed; `∃!` proved |
| conjugate layer: `IsConjugateHeatKernelPDE*`, `flatConjugateKernel_*`, `flat_conjugate_repaired_scope`, `not_*isConjugateHeatKernel*`, `Flat*` | interface + general negative results + model | same pattern as the forward half |
| D7 consumer theorems | general/model consumption | restatements of D13 theorems in the D7 namespace; hypotheses explicit (e.g. `finite_pinned_interface_unique` carries `hL`, `hvol`, `hC`) |

### C1. Are the “refutation” theorems genuine `¬ P`, or weaker?

The exact negated statements (universe annotations as printed in the source):

1. **`not_heatKernelExistenceStatement`** (`StatementRefutation.lean:214`) negates
   `HeatKernelExistenceStatement` (`D7/HeatKernel/Blocked.lean:188–191`):
   ```
   ∀ (M : Type*) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
     (S : HeatSpacetime M), IsClosedRiemannianManifold S →
       ∀ y₀ : M, ∃ K : M → M → ℝ → ℝ, IsHeatKernel S K
   ```
   No hypotheses on the theorem; the proof instantiates the one-point `refutingSpacetime` and uses the
   proved certificate `refutingSpacetime_isClosedRiemannianManifold`. **Genuine, unconditional.**
   The card’s “universe 0” label is conservative (see §Undetermined); the companion
   `not_heatKernelExistenceStatement_of_refuting` is the explicit universe-polymorphic schema
   (`:194–197`).
2. **`not_heatKernelExistenceStatementV1`** (`:223`) negates `HeatKernelExistenceStatementV1`
   (`V1Interface.lean:87–91`), the same shape with `IsHeatKernelV1 S (continuousIntegrableClass S.volume) K`.
   **Genuine, unconditional.**
3. **`not_forall_annihilatesConstants_implies_exists_snapshot_kernel`** (`GeometricRepair.lean:362–367`)
   negates
   ```
   ∀ (M : Type) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
     (S : HeatSpacetime M), IsClosedRiemannianManifold S → AnnihilatesConstants S →
       ∀ y₀ : M, ∃ K : M → M → ℝ → ℝ,
         IsHeatKernelV1 S (AdmissibleTestClass.continuousIntegrableClass S.volume) K
   ```
   (`:363–367`). Unconditional; instantiated at `adversarialTimeDerivativeSpacetime` using
   `adversarialTimeDerivativeSpacetime_isClosedRiemannianManifold` and
   `isAnnihilatesConstants_adversarialTimeDerivativeSpacetime`. **Genuine.** Precise caveat: the
   negated object is the *corrected-domain* (`IsHeatKernelV1`) schema at `Type 0`, not literally
   `HeatKernelExistenceStatement` with a conjunct; the legacy phrasing follows through
   `isHeatKernelV1_integrable_iff_of_closed`/`heatKernelExistenceStatement_iff_v1`. The card’s §18.3
   wording (“the snapshot existence statement is false even after imposing the constant-annihilation
   condition”) is supported.
4. **`not_heatKernelExistenceStatementPDE : ¬ HeatKernelExistenceStatementPDE.{0}`**
   (`DataRefutation.lean:367`) negates the sixth-invocation repaired statement
   (`GeometricRepair.lean:519–523`, quoted in B8). Unconditional. **Genuine.**
5. **`not_heatKernelDataExistenceStatement : ¬ HeatKernelDataExistenceStatement.{0}`**
   (`DataRefutation.lean:380`) negates the data-level repaired statement
   (`GeometricRepair.lean:531–536`). Unconditional. **Genuine.**
6. **`not_conjugateHeatKernelExistenceStatement : ¬ ConjugateHeatKernelExistenceStatement.{0}`**
   (`ConjugateHeatBridge.lean:192–193`) negates
   `∀ (M : Type*) [..] (S : ConjugateHeatSpacetime M), IsRiemannianConjugateHeatSpacetime S → ∀ y₀ t₀, ∃ K, IsConjugateHeatKernel S t₀ K`
   (`D7/ConjugateHeat/Blocked.lean:172–175`). Unconditional at universe 0. **Genuine.**
7. **`not_forall_laplacian_symmetric_flatLine`** (`LaplacianSymmetryRefutation.lean:192–195`) negates
   `∀ u v : ℝ → ℝ, (∫ x, u x * flatLineSpacetime.laplacian v x) = ∫ x, flatLineSpacetime.laplacian u x * v x`,
   with no hypotheses. **Genuine**, but it refutes only the *self-adjointness* form (see §F2).
8. **`snapshot_pde_predicates_incomparable`** (`GeometricRepair.lean:503–510`) is a conjunction of two
   negated `∀`-statements (no implication either way) — **genuine non-implication**, consistent with
   the two independent witnesses (`flatKernelRescaled` for one direction,
   `flatKernel`/`flatHeatSpacetime` for the other).
9. Model-level refutations (`flatHeatSpacetime_not_isHeatKernelV1_integrableClass` `:220`,
   `flatHeatSpacetime_not_isHeatKernel` `:234`, `flatConjugate_not_isConjugateHeatKernel` `:431`,
   `not_exists_isHeatKernelV1_adversarialTimeDerivativeSpacetime` `:293`,
   `not_exists_*_twoPointSpacetime` `DataRefutation:344,354`, `not_exists_isConjugateHeatKernel_conjugateRefuting`
   `ConjugateHeatBridge:169`) are **model-level** `¬`/`¬∃` facts with explicit dimension hypotheses
   (`0 < n`); the card labels them as model/counterexample results, and they are not presented as
   statement-level refutations.

**No refutation is weaker than advertised.** The only precision caveats are (i) the
`AnnihilatesConstants` refutation negates the V1-form schema rather than the legacy
`HeatKernelExistenceStatement` syntactic form (bridge-equivalent), and (ii) all “unconditional at
universe 0” labels may understate a universe-polymorphic theorem (harmless direction).

---

## D. Blocker closure check

### D1. No conclusion smuggled in as a hypothesis

- **No `(h : P) : P` declaration exists.** A scan of every theorem/lemma statement in the D13/D7
  sources (16 D13 files, 26 D7 files) for a hypothesis binder whose type is the theorem’s conclusion produced
  only legitimate “analysis of an assumed witness” theorems (`…_laplacian_snapshot_eq_…`,
  `…_hasDerivAt` restatements, `…eq_of_same` uniqueness, `tendsto_singleFun`), never a proof of `P`
  from `h : P`. Representative hit list: `PDERepair.lean:109`, `PredicateSemantics.lean:95/103/112/120`,
  `FiniteUniqueness.lean:268/345/359`, `FiniteConjugateUniqueness.lean:227/302/404`,
  `UniquenessStatus.lean:73/85`, `ConjugateHeat/UniquenessStatus.lean:52/65` — all have the assumed
  inhabitant as an input and a *different* conclusion (a component identity, agreement of two
  inhabitants, etc.).
- **Structure-field check.** The predicates `IsHeatKernel`, `IsHeatKernelV1`, `IsHeatKernelPDE`,
  `IsConjugateHeatKernel`, `IsConjugateHeatKernelPDE` bundle the properties they talk about (that is
  what a predicate is), but no *existence* theorem takes the predicate as a hypothesis and returns it:
  - `HeatKernelDataExistenceStatement` and `HeatKernelExistenceStatementPDE` are `def … : Prop`,
    explicitly **not proved** (`GeometricRepair.lean:519,531`), and are then **refuted**
    (`DataRefutation.lean:367,380`).
  - `FinitePinnedHeatExistenceStatement` is proved from the constructed `finiteHeatKernel` and its
    verified fields (`FiniteSpaceHeat.lean:807–816`), not assumed.
  - `exists_unique_finiteHeatKernel` / `exists_unique_finiteConjugateKernel` prove `∃!` outright
    (`FiniteUniqueness.lean:372`, `FiniteConjugateUniqueness.lean:424`); their `∃!` conditions are
    explicit PDE + Dirac/anticausal conditions, not the statement being proved.
  - `FlatCorrectedDomainExistence` / `FlatConjugateCorrectedDomainExistence` are proved from the
    transport (`DataRefutation.lean:568`, `ConjugateHeatBridge.lean:542`).
- **The one conclusion-as-hypothesis overlap is disclosed**: `IsHeatKernelPDE.of_dataV1`
  (`PDERepair.lean:173–178`) takes `hpos : ∀ x y t, 0 < t → 0 < D.kernel x y t`, which is the
  `positive` field of its conclusion, plus a class-inclusion hypothesis for the Dirac field. The card
  states this explicitly (“everywhere-positivity is *not* a consequence of the core fields and is an
  explicit hypothesis of the transport”, card.md:673) and the flat instance proves positivity
  outright (`flatKernel_pos`, used at `PDERepair.lean:237`). Not a circular existence claim.
- **`FullInitialCondition` check.** Grep over the D13 tree finds it only at
  `Basic.lean:25` (docstring), `CompactUpgrade.lean:110` (a `have hfull` *derived* from the D12
  equivalence and the datum’s versioned condition), and `FiniteSpaceHeat.lean:708` (the *proved*
  theorem `finiteHeatKernelCore_fullInitialCondition`). No declaration assumes it to obtain an
  existence conclusion in positive dimension. This supports card.md:138–140.
- **Universe-0 statements are genuinely unproved** (not smuggled): `HeatKernelExistenceStatement`,
  `HeatKernelExistenceStatementV1` remain `def … : Prop` in the unmodified legacy/V1 sources.

### D2. Downstream consumption by D7 modules (import line + use site)

All eight D7 consumers are **new files** (authored by this task; card.md:501–504 discloses the
deviation from “edit an existing D7 builder”). Their imports and checked use sites:

| D7 module | import line | use site |
|---|---|---|
| `D7/HeatKernel/V1Interface.lean` | `:7 import Poincare.D13.HeatKernelBridge.All` | `:146 ⟨flatHeatKernelDataV1_integrable n, rfl, flatHeatKernelDataV1_integrable_integrableClassVariant n⟩` (inside `v1_flat_inhabited`); `:128–136` proves the statement equivalence using `isHeatKernelV1_integrable_iff_of_closed` (defined `:102` from D7 `IsHeatKernel`) |
| `D7/HeatKernel/StatementStatus.lean` | `:7 import Poincare.D7.HeatKernel.V1Interface`, `:8 import Poincare.D13.HeatKernelBridge.StatementRefutation` | `:55 (heatKernelExistenceStatement_iff_v1).mpr hV1`; `:63 Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatement` |
| `D7/HeatKernel/RepairStatus.lean` | `:7 import Poincare.D13.HeatKernelBridge.GeometricRepair` | `:57–60 ⟨adversarialTimeDerivativeSpacetime_isClosedRiemannianManifold, isAnnihilatesConstants_adversarialTimeDerivativeSpacetime⟩` |
| `D7/HeatKernel/DataStatus.lean` | `:7 import Poincare.D13.HeatKernelBridge.DataRefutation` | `:64 not_exists_heatKernelData_twoPointSpacetime`; `:86 not_heatKernelDataExistenceStatement`; `:95` both |
| `D7/HeatKernel/FiniteStatus.lean` | `:7 import Poincare.D13.HeatKernelBridge.FiniteSpaceHeat` | `:62 ⟨finiteHeatKernel G, finite_isHeatKernelPDE G⟩` |
| `D7/HeatKernel/UniquenessStatus.lean` | `:7 import Poincare.D13.HeatKernelBridge.FiniteUniqueness`, `:8 import Poincare.D7.HeatKernel.FiniteStatus` | `:68 eq_finiteHeatKernel_of_pde_of_dirac G hpde hdirac`; `:105 exists_unique_finiteHeatKernel G` |
| `D7/ConjugateHeat/Status.lean` | `:7 import Poincare.D13.HeatKernelBridge.ConjugateHeatBridge` | `:58 Poincare.D13.HeatKernelBridge.not_conjugateHeatKernelExistenceStatement`; `:83 flat_isConjugateHeatKernelPDE_integrableClass n t₀`; `:105 flatConjugateKernel_semigroup …` |
| `D7/ConjugateHeat/UniquenessStatus.lean` | `:7 import Poincare.D13.HeatKernelBridge.FiniteConjugateUniqueness`, `:8 import Poincare.D7.ConjugateHeat.Status` | `:81 exists_unique_finiteConjugateKernel G t₀`; `:60 IsConjugateHeatKernelPDE.eq_of_same …` |

So **yes**: a D7-namespaced module really consumes the bridge, and the “blocked D7 existence statement
⇔ corrected-domain restatement” equivalence is a proved theorem in the D7 namespace
(`V1Interface.lean:128–129`). The only nuance is that this consuming module is itself *new work of the
D13 task*, not a pre-existing D7 builder — the card says so (card.md:501–504) and the pre-existing D7
modules (`Basic.lean`, `Blocked.lean`, `Instance.lean`, `ConjugateHeat/Blocked.lean`, …) are
unmodified (see D3).

### D3. Blocker status

`card.json` records `"exact_blockers_closed": []`; `remaining_blockers` begins
“D7-HEAT-KERNEL-EXISTENCE (manifold heat-kernel existence: parametrix/Levi, Duhamel, short-time
existence) — OPEN. …”. card.md:443–452 says so as well, and §17.2 proves the statement the blocker
targets is refutable. No declaration closes it. Verified: no theorem in the D13 tree concludes
`HeatKernelExistenceStatement`, `HeatKernelExistenceStatementV1`, `HeatKernelExistenceStatementPDE`, or
`HeatKernelDataExistenceStatement`; the first two and the last two are *negated*.

Legacy-source integrity: mtime evidence is consistent with the card’s claim that no D7/D10/D11/D12
source was edited — 0 files under `D10/`, `D11/`, `D12/` have an mtime on 2026-09-11, and the only
2026-09-11 files under `D7/` are exactly the eight new consumers named by the card. (A byte-level
`diff -rq` against the D12 snapshot is not possible from the transport; see Undetermined.)

---

## E. Forbidden tokens (`sorry`, `axiom`, `admit`, `unsafe`, `native_decide`, `proof_wanted`)

Scan run with the card’s own comment/string-aware scanner
(`input/d5-tools/scan_forbidden.py`, hard tokens `sorry, axiom, unsafe, native_decide, proof_wanted,
sorryAx, admit`; soft `implemented_by, extern`):

| tree | files scanned | hard | soft |
|---|---|---|---|
| `release/Poincare/D13/HeatKernelBridge` (**16** files, incl. the undocumented `ConjugateScalarCurvature.lean`) | 16 | **0** | **0** |
| `release/Poincare/D7/HeatKernel` + `release/Poincare/D7/ConjugateHeat` (26 files) | 26 | **0** | **0** |

**None found** in code outside comments/strings. Many source files contain the *words* in
docstrings (e.g. “no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`”); the scanner
correctly ignores comments. The card’s own scan covered only **15** D13 files (card checkpoint
19:22 / card.md §22.8 “D13 15 files”); my scan additionally covers the 16th file, which is also clean.

---

## F. Over-claims / discrepancies

### F1 (major, scope/snapshot drift) — an undocumented 16th D13 module is not in the card, its hash manifest, its forbidden scan, or its axiom audit

The transported D13 tree contains
`release/Poincare/D13/HeatKernelBridge/ConjugateScalarCurvature.lean` (738 lines, 39 declaration
sites, self-described “**D13 heat-kernel bridge, companion note 11**” at `:21`). It introduces a new
versioned predicate `IsConjugateHeatKernelPDEMassLaw.v3` (`:528`) / `IsConjugateHeatKernelPDEMassLaw`
(`:541`) with a *mass-law* field, plus further refutations
(`not_exists_isConjugateHeatKernelPDE_of_nonneg_scalarMul` `:304`,
`not_exists_isConjugateHeatKernelPDE_bool_scalarCurvature` `:727`), a new existence/uniqueness pair
(`exists_unique_finiteConjKernelWith` `:657`) and a no-loss theorem (`:697`).

Evidence that it is outside the card’s claim boundary:
- card.md:99–101 “**Current totals (tenth invocation):** **23 authored files, 409 audited declarations** — **15 files** under `release/Poincare/D13/HeatKernelBridge/**, 6 D7 consumers … 2 under `release/Poincare/D7/ConjugateHeat/`”;
- `card.json.source_hashes` has exactly 26 entries, all 15 card-listed D13 modules + 8 D7 consumers + 3 build-config; `ConjugateScalarCurvature.lean` is **not** among them (replayed: 23/23 present Lean files match their recorded sha256 byte-for-byte; the 3 build-config files were not transported);
- `AxiomAudit.lean` does not import it (imports list `:7–25`) and none of its 39 declarations occurs in `bridgeAuditedDeclarations` (`:420–829`, 409 names) — grep for `MassLaw|scalarCurvature|ConjKernelWith` in `AxiomAudit.lean` returns 0;
- card.md §22.8 claims the forbidden scan covered “D13 15 files”; the module is a 16th.

Timing: the module’s mtime is `2026-09-11 23:13:08 +0800`; the card and checkpoint were written
19:18–19:22 +0800, and the transport ran 23:09–23:15. It is therefore very likely an *eleventh*
invocation that postdates the card. Consequence either way: **the card does not describe the delivered
tree**, and its “all declarations … fail-closed axiom checked” claim does not cover these 39
declarations. (They are at least forbidden-token clean; §E.) The parent’s worktree gate count
(card: 339/339) and AxiomAudit count (409) are stale for the same reason.

### F2 (over-claim) — §18.2 attributes the falsity of *both* the self-adjointness and the dissipativity Bochner forms to `LaplacianSymmetryRefutation.lean`, but only self-adjointness is formalized

card.md:885–894:
> “The stronger classical conditions (formal self-adjointness `∫ u · Δv = ∫ Δu · v`, dissipativity `∫ u · Δu ≤ 0`) are deliberately **not** fields of the structure. Stated with the schematic interface's Bochner integral over all functions they are false for the honest packaged flat Laplacian (proved in `LaplacianSymmetryRefutation.lean`, §18.7)…”

The file contains exactly 11 declarations (`hasDerivAt_tanh_real`, `tanh_eq_one_sub`,
`tendsto_tanh_atTop_real`, `tendsto_tanh_atBot_real`, `flatLineSpacetime`, `hasDerivAt_log_cosh`,
`contDiff_log_cosh`, `laplacian_log_cosh`, `integrable_one_sub_tanh_sq`, `integral_one_sub_tanh_sq`,
`not_forall_laplacian_symmetric_flatLine`). The only refutation is
`not_forall_laplacian_symmetric_flatLine : ¬ (∀ u v : ℝ → ℝ, ∫ u · Δv = ∫ Δu · v)`
(`:192–195`). There is **no** declaration refuting `∀ u, ∫ u · Δu ≤ 0`. The card later softens the
broader statement as an “informal remark” (card.md:123) and §18.7 states only the self-adjointness
result; but §18.2’s “(proved in `LaplacianSymmetryRefutation.lean`)” covers the dissipativity half
too. Unsupported as written.

### F3 (F-findings: named declarations that do not exist) — two card-named declarations are misspelled

1. card.md:194 and card.md:314 name **`integrabilityClassVariant_weak_iff`**. The source declaration is
   `HeatKernelDataV1.integrableClassVariant_weak_iff` (`Basic.lean:257`), also audited under that name
   (`AxiomAudit.lean:145, 458`). No declaration `integrabilityClassVariant_weak_iff` exists.
2. card.md:959 names **`not_both_isClosedRiemannianManifold_and_annihilatesConstants_refutingSpacetime`**.
   The source declaration is
   `not_both_isClosedRiemannianManifold_and_isAnnihilatesConstants_refutingSpacetime`
   (`GeometricRepair.lean:581`; audited at `AxiomAudit.lean:306, 608`). The card drops the `is`.

Both are pure naming errors (the intended declarations exist), but an independent reader grepping the
card’s names would fail to find them.

### F4 (count error) — §20.6 splits the eighth-invocation 50 declarations as “44 + 6”; the sources have 42 + 8

card.md:1287–1288: “(44 in `ConjugateHeatBridge.lean` + 6 in `Poincare.D7.ConjugateHeat.Status`; the
audit grows from 228 to **278** declarations.)”, and card.md:131: “`release/Poincare/D7/ConjugateHeat/Status.lean`, **6 declarations**”.
Actual counts: `ConjugateHeatBridge.lean` has **42** declaration sites (`grep` enumeration matches the
file’s 42 audited names), and `D7/ConjugateHeat/Status.lean` has **8** (`:56, :65, :72, :79, :90,
:99, :111, :122`). The total 50 (and 228→278) is correct; the split is not. Likewise §20.5 lists 8
items for a module the same card calls “6 declarations”.

### F5 (hypothesis omission in summary tables) — `eq_of_same` rows drop their hypotheses

- card.md:1496: “| `IsHeatKernelPDE.eq_of_same` | any two `IsHeatKernelPDE` inhabitants over the same finite spacetime agree | proved theorem |” — the actual theorem (`FiniteUniqueness.lean:359–363`) requires `(hL : S.laplacian = G.laplacian) (hvol : S.volume = Measure.count) (hC : ∀ y, C.cls (singleFun y))`.
- card.md:1517–1518: “`IsConjugateHeatKernelPDE.eq_of_same` — any two inhabitants over the same finite counting-measure spacetime agree below `t₀`” — the actual theorem (`FiniteConjugateUniqueness.lean:302–308`) additionally requires `(hR : ∀ u, -(C * G.energy u) ≤ ∑ x, u x * S.scalarMul u x)` (scalar-curvature quadratic form bounded below); the D7 wrapper `finite_conjugate_interface_unique` states it, but the card’s summary row does not. The card’s own D7 consumer docstring (`D7/ConjugateHeat/UniquenessStatus.lean:49–51`) is explicit about it.

### F6 (stale numbers inside the card) — the verdict bullet and §0 table carry older invocation counts

- card.md:9 (verdict, tenth-invocation context elsewhere): “**All 357 declarations are kernel-checked** …” — the card’s own §22.8 reports 409 (tenth invocation).
- card.md:8: “(13 files … **19 files, 357 audited declarations**)” vs §22.8’s 23 files/409.
- card.md:107–111: §0 table body is the eighth-invocation state (“17 Lean files, 278 audited declarations”, “D13 dir 10 files”), while §0’s header says 23/409; the card does annotate the table as historical (card.md:101–103), so this is a readability/provenance issue, not a false claim, but the unmarked line 9 “357” is a genuine inconsistency.
- card.md:159 “`AxiomAudit.lean` | 332 | 108 `#print axioms` …” vs the actual file (848 lines, 280 `#print axioms`, 409-name programmatic list). Historical table, same caveat.
- `AxiomAudit.lean:33–34` (source docstring): “Every declaration … is printed with `#print axioms` and then re-checked programmatically” — 280 printed vs 409 re-checked. The enforceable claim (409/409 `Lean.collectAxioms`) is supported by the source; the “printed” half is not literally true.

### F7 (minor transcription slip) — the `IsHeatKernelPDE.solvesPDE` field is printed with the wrong kernel argument order

card.md:670 prints `HasDerivAt (fun s => K x y s) (S.laplacian (fun z => K z x t) x) t`; the source
(`PDERepair.lean:96–97`) has `S.laplacian (fun z => K z y t) x` (source is the semantically intended
order; the field is about `K(·,y,t)`). Cosmetic in the card, no impact on the formal claims.

### F8 (minor qualification omission) — “every corrected-domain datum *is* a legacy D7 datum”

card.md:267–270: “on the intended closed (compact) manifold setting, whose Riemannian volume is
finite, **every corrected-domain datum *is* a legacy D7 datum**.” The upgrade theorem requires
`hC : D.IsIntegrableClassVariant` (or the explicit `C_c` class equality) in addition to
compactness/finiteness (`CompactUpgrade.lean:69–71, 101–103`). A V1 datum over a non-standard
admissible class does not upgrade. The card states the class hypotheses in the §4 signatures
(card.md:243–250) but the summary sentence over-generalises.

### F9 (not an over-claim, but worth recording) — the `AnnihilatesConstants` refutation is about the V1 predicate

`not_forall_annihilatesConstants_implies_exists_snapshot_kernel` (`GeometricRepair.lean:362–367`)
negates the corrected-domain (`IsHeatKernelV1`) schema, not the literal conjunction
`HeatKernelExistenceStatement ∧ AnnihilatesConstants`. The legacy form follows through
`heatKernelExistenceStatement_iff_v1` (`V1Interface.lean:128`) and both predicates share `solves`
(`V1Interface.lean:73`, `Blocked.lean:163`), so the card’s prose is materially correct; the exact
negated statement should be quoted as the V1 schema.

### Positive checks (card statements that are fully supported)

- Every quoted headline declaration exists with the claimed signature (§B).
- The “snapshot vs PDE” semantic claim is exactly right: `IsHeatKernel.solves` /
  `IsHeatKernelV1.solves` contain `S.heatOperator (fun x => K x y t) = 0`
  (`Blocked.lean:163`, `V1Interface.lean:73`) and `HeatSpacetime.heatOperator`
  (`Blocked.lean:76–77`) is a *space-variable* operator on a time snapshot; the machine-checked
  characterisation is `PredicateSemantics.lean:88–133`.
- `IsHeatKernelPDE`’s `solvesPDE` is the genuine `HasDerivAt` PDE (`PDERepair.lean:96–97`).
- The two statement refutations and the seventh-invocation refutations of the *repaired* statements
  are genuine and unconditional (§C1); `D7-HEAT-KERNEL-EXISTENCE` is genuinely open (`card.json`,
  §D3).
- The one-point and two-point counterexamples are certified, and `IsClosedRiemannianManifold` really
  comprises only the seven named fields, none touching the operators (`Blocked.lean:103–118`).
- Downstream consumption is real (§D2), and the 409-name audit list exactly matches the declaration
  sites of the 23 card files (§B13).
- Forbidden-token scan: 0 hard / 0 soft in all 16 D13 and 26 D7 source files (§E).
- The card’s own hash manifest is faithful: 23/23 transported Lean files match the recorded sha256
  byte-for-byte.

---

## Undetermined from the relayed snapshot

1. **Card gate numbers** (build `9202 jobs` exit 0; `D13HeatKernelBridgeAxiomCheck PASS 409/409`;
   semantic transcripts 11 files; per-file 23/23; worktree 339/339; negative control; diff 9 lines;
   upstream snapshot): the `logs/` referenced by the card were not transported. The sources contain the
   fail-closed `run_cmd` check (`AxiomAudit.lean:835–848`) and the 409-name list, but whether it
   elaborates/passes requires a build (the parent’s cold builds are the authority). Likewise the
   worktree count would now be ≥340 because of `ConjugateScalarCurvature.lean`.
2. **Exact universe elaboration of `not_heatKernelExistenceStatement` / `_V1`.** The card labels these
   “universe 0”; because `PUnit` and `HeatKernelExistenceStatement` are universe-polymorphic and the
   theorem has no universe annotation, Lean may generalize them to `.{u}` (a *stronger* result). The
   precise `#check` output requires elaboration; the card’s weaker label cannot be an over-claim.
3. **`diff -rq` against the D12 snapshot.** The baseline snapshot was not transported; the
   “no legacy file edited” claim is supported only by mtimes (D10/D11/D12 untouched on 2026-09-11;
   only the eight declared new D7 files dated 2026-09-11), not by a byte diff.
4. **Three build-config hashes** (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`) — the files
   are not in the transport; their recorded hashes cannot be replayed.
5. **Whether `ConjugateScalarCurvature.lean` is an eleventh-invocation artifact** (most likely, given
   the mtime) or was present when the card was written (it would then be an omission by the card).
   Either way the card’s inventory does not cover the tree as delivered; the distinction only affects
   whether this is “card stale” or “card incomplete”.
6. **Mathlib lemma names cited by the card** (`Matrix.exp_add_of_commute`, `Matrix.exp_diagonal`,
   `Matrix.mul_apply`, `mulVecLin_apply`, `hasSum_single`, `Summable.le_tsum`, `hasDerivAt_pi`,
   `hasDerivAt_exp_smul_const'`, `continuous_integrable_of_compactSpace_finiteMeasure`, …) were not
   checked against mathlib at the pinned revision; they are used in proofs, not claimed as results,
   and a compile is the arbiter.

---

## Findings summary

| id | severity | finding |
|---|---|---|
| F1 | high (scope) | Undocumented `ConjugateScalarCurvature.lean` (39 declarations, v3 predicate, further refutations) in the D13 tree, outside the card’s inventory, hash manifest, forbidden scan and 409-declaration axiom audit; mtime suggests post-card 11th invocation. Card does not describe the delivered tree. |
| F2 | medium | §18.2 claims the dissipativity Bochner form is “proved” false in `LaplacianSymmetryRefutation.lean`; only the self-adjointness form is formalized (11 declarations enumerated). |
| F3 | medium (F-findings) | Two card-named declarations do not exist: `integrabilityClassVariant_weak_iff` (actual `integrableClassVariant_weak_iff`) and `not_both_…_and_annihilatesConstants_…` (actual `…_and_isAnnihilatesConstants_…`). |
| F4 | low | Conjugate declaration split misstated: card says 44 + 6; sources have 42 + 8 (total 50 correct). §0 table also says “6 declarations” for the 8-declaration Status module. |
| F5 | low | §22.4/§22.5 `eq_of_same` rows omit the pinned-Laplacian/volume/singleton-class (and conjugate curvature-bound) hypotheses present in the theorems. |
| F6 | low | Stale invocation numbers inside the card (line 9 “357”, line 8 “19 files/357”, §0 table 278/10 files, §1 `All.lean` 25 lines, §8 108 `#print axioms`); `AxiomAudit.lean` prints 280 `#print axioms` for 409 audited names. |
| F7 | cosmetic | card.md:670 prints `K z x t` where the source has `K z y t` in the `solvesPDE` field. |
| F8 | low | card.md:267–270 over-generalises “every corrected-domain datum *is* a legacy D7 datum” (needs the class-variant hypothesis). |
| F9 | info | The `AnnihilatesConstants` refutation negates the V1-form schema, not the literal legacy conjunction; bridge-equivalent, card prose materially correct. |

**No finding contradicts the mathematical content of the headline claims.** The audit’s negative
results (statement refutations), the interface semantics finding, the (in)comparability theorem, the
non-self-adjointness refutation, the blocker-open status, and the D7 consumption are all supported by
declarations quoted above. The card’s principal defect is provenance/scope (F1) plus four bookkeeping
or transcription errors.
