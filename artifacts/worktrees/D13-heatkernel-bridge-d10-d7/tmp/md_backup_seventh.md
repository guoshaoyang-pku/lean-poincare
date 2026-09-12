# D13-heatkernel-bridge-d10-d7 — result card

- **Task id:** `D13-heatkernel-bridge-d10-d7`
- **Stage / lane:** D13 / integrator — the `HeatKernelBridge` module named by `LONG_PLAN`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7`
- **Generated (UTC):** 2026-09-11T05:04:00Z; third invocation opened 2026-09-11T06:45Z; fourth invocation opened 2026-09-11T06:52Z; fifth invocation opened 2026-09-11T08:21Z; sixth invocation opened 2026-09-11T16:38+08:00 (cumulative elapsed ≈ 4.05 h; the sixth invocation re-verifies the frozen fifth-invocation artifact from byte-identical hashes and adds the statement-level *repair* package: the sound constant-annihilation condition with the counterexample excluded, a second statement-level refutation showing the Laplacian-only repair is dead, the snapshot/PDE incomparability theorem, the data-level repaired statement, the checked refutation of the naive self-adjointness axiom, and a new D7 consumer)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`); mathlib `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by `lake-manifest.json`, unchanged)
- **Module root:** `release/Poincare/D13/HeatKernelBridge/` (10 files) + three new D7-namespaced consumers `release/Poincare/D7/HeatKernel/{V1Interface,StatementStatus,RepairStatus}.lean` (13 files, 188 audited declarations)
- **Verdict:** **THE `HeatKernelBridge` NAMED BY LONG_PLAN EXISTS AND IS CONSUMED BY A D7 MODULE — the D10 Euclidean heat kernel (`Poincare.D10.HeatKernelEuclidean`) is transported to the D7 heat-kernel interface on the D12-corrected admissible-test-function domain in every dimension, the corrected-domain datum upgrades to a genuine legacy `Poincare.D7.HeatKernel.HeatKernelData` in the compact finite-measure scope (with the upgrade proved a left inverse of the legacy embedding), and a new D7 module consumes the bridge by proving the blocked D7 existence statement equivalent to its corrected-domain restatement.** All 188 declarations are kernel-checked with no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`, in the single approved axiom cone `{propext, Classical.choice, Quot.sound}` (fail-closed check), and no D7/D10/D11/D12 source file was edited. The third invocation added a machine-checked semantic companion (`PredicateSemantics.lean`, 16 declarations) recording that the D7 *predicate's* heat-equation field is a snapshot operator identity, not the PDE. The fourth invocation adds the corresponding **repair candidate** (`PDERepair.lean`, 18 declarations): a versioned predicate `IsHeatKernelPDE` (v2) whose heat-equation field is the genuine `HasDerivAt` PDE, an explicit transport from `HeatKernelDataV1` data to it, and the checked theorem that the D10 Euclidean kernel inhabits it on the honest flat spacetime in every dimension — while the same kernel refutes the snapshot predicate. The data-level transport is unaffected and no blocker is claimed closed. The fifth invocation adds the **statement-level refutation** (`StatementRefutation.lean`, 15 declarations; D7 consumer `StatementStatus.lean`, 2 declarations): the D7 `HeatKernelExistenceStatement` and its corrected-domain restatement are **false as formalized**, because `IsClosedRiemannianManifold` constrains only the volume and the distance and leaves `laplacian`/`timeDerivative` free; the named blocker therefore needs an interface repair before it can be attacked. The fifth invocation also proves the compact-scope existential equivalence `exists_v1_iff_exists_legacy`. The sixth invocation adds the **statement-level repair package** (`GeometricRepair.lean`, 47 declarations; `LaplacianSymmetryRefutation.lean`, 11 declarations; D7 consumer `RepairStatus.lean`, 4 declarations): the sound constant-annihilation condition `AnnihilatesConstants` (`Δ 1 = 0`) that excludes the refuting spacetime while being verifiable for the honest flat operator; a **second, independent statement-level refutation** showing that even with that condition the snapshot statement is false (the adversarial one-point spacetime `Δ = 0`, `timeDerivative = id` satisfies the repaired hypotheses and admits no snapshot kernel), so constraining the Laplacian cannot repair the statement; the **time-rescaling theorem** showing that pinning `timeDerivative := laplacian` makes the snapshot field vacuous and that the snapshot and PDE predicates are **incomparable**, so the heat-equation field must be *replaced*, not constrained; and the statement-level repaired interface `HeatKernelExistenceStatementPDE` / `HeatKernelDataExistenceStatement` (stated, not proved, with model inhabitants including on the adversarial datum and the checked implication data-level → predicate-level). It also adds the **checked refutation of the naive self-adjointness axiom** for the honest 1-dimensional flat packaged Laplacian (`not_forall_laplacian_symmetric_flatLine`: `u = 1`, `v = log cosh` give `∫ 1·Δv = 2 ≠ 0 = ∫ Δ1·v`), so the classical integration-by-parts identity cannot be adjoined as a field of a repaired schematic interface. No named blocker is claimed closed; `D7-HEAT-KERNEL-EXISTENCE` remains open and is now known not to be attackable against the snapshot statement at all.

> **Second invocation (2026-09-11T05:04Z):** every gate was re-run from the recorded source hashes
> (all six hashes re-computed and identical to §9) on the unchanged artifact: full `lake build`
> exit 0 / 9185 jobs / D6AUDIT PASS, per-file gate 6/6, worktree gate 303/303, axiom audit PASS
> 74/74, forbidden scans 0/0, negative control PASS, source-integrity diff clean. See §14. This is a
> re-verification of the same artifacts by the task's own continuation, **not** the independent
> semantic review requested below.

> **Third invocation (2026-09-11T06:45Z):** five of the six delivered files are byte-identical to the
> §9 hashes (only `AxiomAudit.lean` was extended); one new companion file
> `D13/HeatKernelBridge/PredicateSemantics.lean` was added (16 declarations, audited)
> and `AxiomAudit.lean` was extended to 90 declarations. Full `lake build` exit 0 / 9186 jobs /
> D6AUDIT PASS, per-file gate 7/7, extended axiom audit PASS 90/90, worktree/forbidden/negative-control
> gates re-run; see §15 for the finding and the re-run evidence.

> **Fourth invocation (2026-09-11T06:52Z):** the ten third-invocation hashes were re-computed
> byte-identical and the full gate suite was re-run on the frozen artifact before any change
> (build 9186 jobs exit 0, per-file 7/7, worktree 305/305, scans 0/0, negative control PASS,
> source integrity clean, upstream snapshot PASS; §16.1). One new companion
> `D13/HeatKernelBridge/PDERepair.lean` (18 declarations) was then added, together with a small
> update of `All.lean`'s module docstring and an extension of `AxiomAudit.lean` to 108
> declarations. Final gates: build 9187 jobs exit 0, per-file 8/8, worktree 307/307, axiom audit
> PASS 108/108, scans 0/0, negative control PASS; see §16.2–§16.3.

> **Sixth invocation (2026-09-11T16:38+08:00, ≈ 0.8 h):** the thirteen fifth-invocation hashes were
> re-computed byte-identical and the full gate suite was re-run on the frozen artifact before any
> change (build 9189 jobs exit 0, D6AUDIT PASS, axiom audit PASS 126/126, per-file 10/10, worktree
> 313/313, forbidden 0/0, negative control PASS, source-integrity diff 3 expected lines, upstream
> snapshot PASS; §18.1). Three new files were then added — `D13/HeatKernelBridge/GeometricRepair.lean`
> (47 declarations), `D13/HeatKernelBridge/LaplacianSymmetryRefutation.lean` (11 declarations) and
> `D7/HeatKernel/RepairStatus.lean` (4 declarations) — together with a
> docstring update of `All.lean` and an extension of `AxiomAudit.lean` to **188** declarations. The
> sixth invocation proves: (i) the constant-annihilation condition excludes the old counterexample
> and is verifiable for the honest flat Laplacian, while the naive self-adjointness/dissipativity
> axioms are *not soundly stateable* over the schematic interface; (ii) a second statement-level
> refutation, so no repair that only constrains the Laplacian can restore the snapshot statement;
> (iii) the snapshot and PDE predicates are incomparable (time rescaling), so the field must be
> replaced; (iv) the data-level repaired statement `HeatKernelDataExistenceStatement` (stated, not
> proved) is non-vacuous and holds on the very datum that refutes the snapshot statement; (v) the
> naive self-adjointness axiom is false for the honest flat Laplacian (checked). See
> §18.2–§18.7; final gates in §18.9.


> This card requests independent acceptance (`compiled_only_until_independent_semantic_review`).
> No named blocker is claimed closed: see §10.

---

## 0. Bottom line

| item | result |
| --- | --- |
| new files | **13 Lean files, 188 audited declarations**: 10 under `release/Poincare/D13/HeatKernelBridge/` + 3 new D7 consumers `release/Poincare/D7/HeatKernel/{V1Interface,StatementStatus,RepairStatus}.lean` |
| `lake build` from `release/` | **exit 0** — `Build completed successfully (9192 jobs)`, D6AUDIT PASS (sixth invocation; §18.9) |
| compile gate (dispatcher form: `lake env lean <file>`, cwd = worktree root) | **12/12 authored files exit 0**; full worktree gate **319/319 exit 0** (`logs/d13_sixth_final_gate_raw.txt`) |
| axiom gate | **D13HeatKernelBridgeAxiomCheck: PASS — 188/188 declarations depend only on `[propext, Classical.choice, Quot.sound]`** (fail-closed programmatic `Lean.collectAxioms` re-check, `logs/d13_sixth_final_build.log`) |
| forbidden-token scan (comment/string aware) | **0 hard / 0 soft** (D13 dir 10 files; `D7/HeatKernel` all 12 files including the three new consumers) |
| negative control | **PASS** — the audit predicate detects `sorryAx` and the `native_decide` axiom (non-vacuous) |
| corrected-domain D7 interface | `HeatKernelDataV1 X` (core + admissible test class + versioned initial condition), v1 |
| D10 → D7 transport | `flatHeatKernelDataV1_integrable n`, `flatHeatKernelDataV1_cc n` for **every `n : ℕ`**, both admissible classes; kernel = D10 `gaussianKernel` at `t > 0` |
| scope of the transport (checked) | every positive dimension: V1 datum exists **and** no legacy datum exists (`flat_v1_exists_not_legacy_of_pos`); dimension 0: full legacy datum (`flat_legacy_exists_zero`) |
| compact finite-measure upgrade | `toHeatKernelData_of_integrableClass` / `toHeatKernelData_of_ccClass` : corrected-domain datum → genuine legacy `HeatKernelData`; `ofHeatKernelData_upgrade_eq` (left inverse) |
| D7 downstream consumption | `heatKernelExistenceStatement_iff_v1`: the blocked D7 manifold statement is **equivalent** to its corrected-domain restatement; `punit_v1_upgrade_eq` round trip on the existing D7 one-point instance |
| predicate-semantics companion (third invocation) | `PredicateSemantics.lean`, 16 kernel-checked declarations: the D7 predicate's heat-equation field is a snapshot operator identity, not the PDE; the D10 kernel does not satisfy `IsHeatKernelV1`/`IsHeatKernel` for the honest flat Euclidean spacetime in positive dimension (all other predicate fields hold). Recorded as a statement-repair dependency, **not** a blocker closure (§15) |
| PDE-repair companion (fourth invocation) | `PDERepair.lean`, 18 kernel-checked declarations: versioned predicate `IsHeatKernelPDE` (v2) whose heat-equation field is the genuine `HasDerivAt` PDE; `IsHeatKernelPDE.of_dataV1` transports any `HeatKernelDataV1` datum (with everywhere-positivity) to it; the D10 kernel inhabits it on the honest flat spacetime in **every dimension** on both classes, while the same kernel refutes the snapshot predicate (`flat_pde_repaired_scope`, `not_forall_isHeatKernelPDE_imp_isHeatKernelV1`). A model-level repair candidate, **not** an existence statement and **not** a blocker closure (§16) |
| statement-refutation companion (fifth invocation) | `StatementRefutation.lean`, 15 kernel-checked declarations: the D7 `HeatKernelExistenceStatement` and `HeatKernelExistenceStatementV1` are **refutable as formalized** — `IsClosedRiemannianManifold` does not constrain `laplacian`/`timeDerivative`, and the one-point spacetime (Dirac volume, `laplacian = id`, `timeDerivative = 0`) forces `K = 0` against positivity. Unconditional at universe 0; universe-polymorphic conditional schema; **not** a blocker closure, but the checked reason the blocker cannot be closed as stated (§17) |
| D7 statement-status consumer (fifth invocation) | `release/Poincare/D7/HeatKernel/StatementStatus.lean`, 2 declarations: the bridge equivalence `heatKernelExistenceStatement_iff_v1` transports the legacy refutation to the corrected-domain statement (cross-check of the direct refutation) |
| compact-scope existential closure (fifth invocation) | `exists_v1_iff_exists_legacy`: for a fixed core on a compact finite-measure space, the existence of a corrected-domain V1 datum is **equivalent** to the existence of a legacy D7 `HeatKernelData` with that core |
| sound geometric condition (sixth invocation) | `AnnihilatesConstants` (`Δ 1 = 0`): excludes the refuting spacetime, strictly stronger than the closed-manifold predicate, non-vacuous, and verified for the honest flat D10 Laplacian; the naive self-adjointness/dissipativity axioms are **not** fields (their Bochner-integral forms are false for the honest packaged operator — informal remark, §18.2) |
| second statement-level refutation (sixth invocation) | `adversarialTimeDerivativeSpacetime` (`Δ = 0`, `timeDerivative = id`) satisfies `IsClosedRiemannianManifold ∧ AnnihilatesConstants` yet admits **no** snapshot kernel: the Laplacian-only repair of `D7-HEAT-KERNEL-EXISTENCE` is dead (§18.3) |
| snapshot/PDE incomparability (sixth invocation) | `snapshot_pde_predicates_incomparable`: the time-rescaled D10 kernel inhabits the snapshot predicate on `flatSnapshotSpacetime` but fails the PDE, so the D7 heat-equation field is not equivalent to the PDE under any operator hypotheses — it must be *replaced* (§18.4) |
| statement-level repaired interface (sixth invocation) | `HeatKernelExistenceStatementPDE` / `HeatKernelDataExistenceStatement` (`def … : Prop`, **stated, not proved**), `heatKernelDataExistenceStatement_implies_pde`, model inhabitants (`heatKernelDataExistenceStatement_conclusion_{punit,adversarial}`) (§18.5) |
| D7 repair-status consumer (sixth invocation) | `release/Poincare/D7/HeatKernel/RepairStatus.lean`, 4 declarations: on one closed Riemannian datum satisfying the constant-annihilation condition the legacy `IsHeatKernel` has no witness while a genuine legacy `HeatKernelData` exists (`snapshot_refuted_data_exists_adversarialTimeDerivative`) |
| legacy definitions | **unchanged** (D7 `HeatKernelData`/`IsHeatKernel`/`HeatKernelExistenceStatement`, D11 `HeatKernelCore`, D12 `HeatDomain` — imported and consumed, never edited; verified by `diff -rq`) |

**Not claimed:** manifold heat-kernel existence (the named blocker `D7-HEAT-KERNEL-EXISTENCE` and the
other six `B-D7-*` blockers remain open — the bridge supplies the *interface* and the *model
inhabitant*, not the parametrix/regularity/spectral theory; and by §17 the D7 statement as written is
refutable, so it must be repaired before it can be proved); no Perelman/Poincaré theorem; no
weakened or assumed conclusion (no declaration assumes `FullInitialCondition` or anything
equivalent in any positive dimension; every upgrade hypothesis is expanded to a mathlib-level
regularity condition).

---

> **Fifth invocation:** the inventory below records the fourth-invocation artifact. The current
> inventory is 8 files under `release/Poincare/D13/HeatKernelBridge/` plus 2 D7 consumers
> (`V1Interface.lean`, `StatementStatus.lean`), **126 audited declarations**; the new files are in
> §17.3 and the final gates in §17.4.

## 1. What was built

| file | lines | role |
| --- | --- | --- |
| `D13/HeatKernelBridge/Basic.lean` | 264 | the corrected-domain D7 interface `HeatKernelDataV1` (v1), projections, transfer of the D7 analytic fields, legacy embedding `ofHeatKernelData`, tightness `exists_toCore_eq_iff` |
| `D13/HeatKernelBridge/EuclideanTransport.lean` | 246 | the D10 Euclidean heat kernel transported to the corrected-domain D7 interface in **every dimension**, both admissible classes; kernel/mass/semigroup/heat-equation transfer; non-vacuity; positive-dimension scope contrast; dimension-0 legacy re-embedding |
| `D13/HeatKernelBridge/CompactUpgrade.lean` | 147 | upgrade constructions to the genuine legacy D7 `HeatKernelData` in the compact finite-measure scope (integrable class and `C_c` class), round trips, left-inverse of the embedding |
| `D13/HeatKernelBridge/All.lean` | 25 | umbrella module (core transport; the companion notes import the umbrella, so they are audited separately rather than re-exported here) |
| `D13/HeatKernelBridge/PredicateSemantics.lean` | 243 | **third-invocation semantic companion** (16 audited declarations): exact content of the D7 `IsHeatKernel`/`IsHeatKernelV1` heat-equation field, the zero-time-derivative harmonicity consequence, the honest flat Euclidean spacetime and the proof that the D10 kernel does not satisfy either predicate there in positive dimension (while positivity, normalization and the admissible-class Dirac field hold), and the degenerate `T = Δ` vacuity direction |
| `D13/HeatKernelBridge/PDERepair.lean` | 292 | **fourth-invocation PDE-repair companion** (18 audited declarations): versioned predicate `IsHeatKernelPDE` (v2) with the genuine `HasDerivAt` heat-equation field; `HeatKernelDataV1.toHeatSpacetime`; near-diagonal positivity lemma; `IsHeatKernelPDE.of_dataV1` and its two class specializations; the D10 flat inhabitant on both classes in every dimension; the positive-dimension scope conjunction; and the non-implication from the repaired to the snapshot predicate |
| `D13/HeatKernelBridge/AxiomAudit.lean` | 332 | 108 `#print axioms` + fail-closed programmatic cone re-check + four downstream-use `example`s |
| `D7/HeatKernel/V1Interface.lean` | 169 | **new D7 consumer**: `IsHeatKernelV1`, `HeatKernelExistenceStatementV1`, the per-kernel and statement-level equivalences, flat inhabitation consumption, PUnit round trip |
| **total** | **1718** | |

Namespace: `Poincare.D13.HeatKernelBridge` (+ `Poincare.D7.HeatKernel.V1Interface` for the
consumer). Nothing else under `release/Poincare` was written (verified with
`diff -rq` against the `D12-heat-domain-repair` snapshot: the only differences are the new `D13/`
directory and `D7/HeatKernel/V1Interface.lean`). The root-level
`lakefile.toml` / `lake-manifest.json` / `lean-toolchain` / `.lake -> release/.lake` scaffold is
pure build configuration (same pattern as the D12 worktree, byte-identical files).

---

## 2. The corrected-domain D7 interface (v1)

`HeatKernelDataV1 X` is the D7 `HeatKernelData` interface with the defective field replaced by the
D12 repair, exactly as requested by D12-semantic-ledger request 2:

```
structure HeatKernelDataV1 (X) [TopologicalSpace X] [MeasurableSpace X] where
  core                : Poincare.D11.HeatKernelBridge.HeatKernelCore X
  testClass           : Poincare.D12.HeatDomain.AdmissibleTestClass X core.volume
  initialConditionFor : Poincare.D12.HeatDomain.WeakInitialConditionFor core testClass
```

* every analytic field of the D7 interface except the pointwise initial condition is carried by the
  core and transferred through named theorems (`kernel_nonneg`, `gaussianUpperBound`,
  `gaussianLowerBound`, `symmetry`, `semigroup`, `normalization`, `heatEquation`) — so a V1 datum
  *is* the D7 interface content, with the test-function domain an explicit part of the statement;
* `HeatKernelDataV1.v1 : ℕ := 1` is the version tag; the legacy definitions are never edited;
* **tightness** (`exists_toCore_eq_iff`): a V1 datum over a prescribed core and class exists iff
  the core satisfies the versioned condition for that class — the two fields added by the D12
  repair are exactly the difference between the core and the corrected-domain D7 interface;
* **legacy ⊆ corrected** (`ofHeatKernelData`): every legacy D7 datum is a V1 datum for the
  continuous-integrable class (no extra hypothesis; the legacy quantifier implies the class one);
  `integrabilityClassVariant_weak_iff` records that for integrable-class variants the corrected
  condition is exactly D11's weak condition (D12 `iff_integrableClass`) — the repair is an
  interface change, not a change of the proved mathematics.

---

## 3. The D10 Euclidean transport (every dimension)

```
flatHeatKernelDataV1_integrable (n : ℕ) : HeatKernelDataV1 (EuclideanSpace ℝ (Fin n))
flatHeatKernelDataV1_cc          (n : ℕ) : HeatKernelDataV1 (EuclideanSpace ℝ (Fin n))
```

Both assemble the D11 core `flatHeatKernelCore n` (all D10-proved fields) with the D12 versioned
weak initial condition (`flatHeatKernelCore_weakInitialConditionFor_integrableClass` /
`flatHeatKernelCore_weakInitialConditionFor_ccClass`). No dimension restriction, no extra
hypothesis. Transport theorems at the corrected-domain level:

| theorem | content | D10/D11/D12 input |
| --- | --- | --- |
| `flatHeatKernelDataV1_integrable_kernel_eq_gaussian` (and `_cc_`) | at `t > 0` the transported kernel is the genuine D10 `gaussianKernel n t (x - y)` | D11 `flatKernel_of_pos` |
| `flatHeatKernelDataV1_integrable_normalization` | `∫ y, K x y t = 1` for `t > 0` | D10 `gaussianKernel_integral` via the core |
| `flatHeatKernelDataV1_integrable_semigroup` | Chapman–Kolmogorov | D10 `gaussianKernel_convolution` via the core |
| `flatHeatKernelDataV1_integrable_heatEquation` | `∂ₜK = ΔK` (genuine D11 `laplacianLinearMap`) | D10 `hasDerivAt_gaussianKernel` / `laplacian_gaussianKernel` |
| `flatHeatKernelDataV1_integrable_gaussianUpperBound` | the D7 Gaussian upper bound | core field |
| `flatHeatKernelDataV1_{integrable,cc}_initialCondition` | corrected initial condition against the class | D11 `flatKernel_tendsto_integral(_of_hasCompactSupport)` via D12 |
| `flatHeatKernelDataV1_cc_bump_initialCondition` | non-vacuity: the nondegenerate bump `max 0 (1-‖z‖²)` converges to `1` | D12 `bump` machinery |

**The precise scope of the transport** (checked, not asserted):

```
flat_v1_exists_not_legacy_of_pos (n : ℕ) (hn : 0 < n) :
    (∃ D : HeatKernelDataV1 (EuclideanSpace ℝ (Fin n)), D.toCore = flatHeatKernelCore n) ∧
      ¬ ∃ D : Poincare.D7.HeatKernel.HeatKernelData (EuclideanSpace ℝ (Fin n)),
        D.toCore = flatHeatKernelCore n
```

— in every positive dimension the corrected-domain datum exists while **no legacy datum with the
explicit Euclidean core exists** (D12 `not_exists_heatKernelData_flat_of_pos`); in dimension 0 the
full legacy datum exists (`flat_legacy_exists_zero`, D11 `flatHeatKernelData_zero`) and re-embeds
into the corrected domain (`flat_v1_of_legacy_zero`). The corrected admissible-test-function
domain is therefore exactly the D7-level interface available for the D10 Euclidean kernel, and the
bridge supplies its inhabitant.

---

## 4. The compact finite-measure upgrade (to the genuine legacy D7 type)

```
toHeatKernelData_of_integrableClass [CompactSpace X] [OpensMeasurableSpace X]
    (D : HeatKernelDataV1 X) [IsFiniteMeasure D.core.volume] (hC : D.IsIntegrableClassVariant) :
    Poincare.D7.HeatKernel.HeatKernelData X

toHeatKernelData_of_ccClass [CompactSpace X] [OpensMeasurableSpace X]
    (D : HeatKernelDataV1 X) [IsFiniteMeasureOnCompacts D.core.volume]
    (hC : D.testClass = AdmissibleTestClass.continuousCompactSupportClass D.core.volume) :
    Poincare.D7.HeatKernel.HeatKernelData X
```

These are constructions, not propositions: the versioned condition is re-typed to the D11 weak
condition (`iff_integrableClass`), which equals the legacy full condition in this scope (D12
`weakInitialCondition_iff_full_of_compact_finiteMeasure`, respectively the `C_c` equivalence), and
the unchanged D11 map `HeatKernelCore.toHeatKernelData` produces a genuine legacy datum. The
`C_c` variant additionally proves `[IsFiniteMeasure]` from `[IsFiniteMeasureOnCompacts]` +
compactness (`lt_top_of_isCompact isCompact_univ`). Consequences, all kernel-checked:

* `..._toCore`: the upgrade forgets back to the original core;
* `..._initialCondition`: the upgraded datum carries the legacy literal initial condition (its D7
  field) — for every continuous test function, so nothing is weakened in this scope;
* `ofHeatKernelData_upgrade_eq`: the upgrade is a **left inverse of the legacy embedding** — on a
  compact space with finite volume, embedding a legacy datum and upgrading recovers it exactly,
  so the corrected-domain interface carries exactly the same data as the legacy interface there.

This is the transport **to the D7 `HeatKernelData` interface**: the corrected domain is needed only
where the legacy quantifier is overstrong (noncompact spaces such as `ℝⁿ`); on the intended closed
(compact) manifold setting, whose Riemannian volume is finite, every corrected-domain datum *is* a
legacy D7 datum.

---

## 5. Downstream consumption by a D7 module

A **new** D7-namespaced module (no existing D7 file edited) consumes the bridge:

`release/Poincare/D7/HeatKernel/V1Interface.lean` (namespace `Poincare.D7.HeatKernel`):

* `IsHeatKernelV1 S C K`: the D7 `IsHeatKernel` predicate (positivity, normalization, the Dirac
  convergence, and the legacy `solves` field) with the Dirac convergence quantified over the
  admissible class `C`. **Precision note (third invocation):** the legacy `solves` field is the
  snapshot operator identity `S.laplacian (fun x => K x y t) = S.timeDerivative (fun x => K x y t)`,
  *not* the PDE `∂ₜK = ΔK`; see §15 for the machine-checked analysis. The genuine `HasDerivAt` heat
  equation lives in the D13 data (`HeatKernelDataV1.heatEquation`), not in this predicate field;
* `HeatKernelExistenceStatementV1`: the blocked D7 manifold existence statement restated on the
  corrected domain;
* `isHeatKernelV1_integrable_iff_of_closed`: for a heat spacetime satisfying
  `IsClosedRiemannianManifold`, the corrected-domain predicate for the continuous-integrable class
  and the legacy `IsHeatKernel` predicate are **equivalent for every kernel**. The proof expands
  the antecedent's own fields: `compact_univ` gives `CompactSpace`, `volume_lt_top univ
  compact_univ` gives `IsFiniteMeasure`, `[BorelSpace]` gives `OpensMeasurableSpace`, and D12
  `continuous_integrable_of_compactSpace_finiteMeasure` makes the class certificate automatic;
* `heatKernelExistenceStatement_iff_v1`: **the blocked D7 existence statement is equivalent to its
  corrected-domain restatement** (both sides ascribed the same universe level). No additional
  hypothesis is added to the statement — the equivalence uses only the statement's own antecedent;
* `v1_flat_inhabited n`: the corrected-domain D7 interface is inhabited by the D10 Euclidean heat
  kernel in every dimension (a checked witness with `D.toCore = flatHeatKernelCore n`);
* `v1_flat_no_legacy_of_pos`: no legacy datum exists in any positive dimension (the D7-level
  summary of the bridge scope);
* `punit_v1_upgrade_eq`: the bridge round trip on the existing D7 one-point instance recovers
  `punitHeatKernelData` exactly.

`HeatKernelExistenceStatementV1` remains an unproved `Prop` exactly like the legacy statement; the
equivalence is a reduction of the blocked statement, not an existence proof.

---

## 6. Semantic classification (per acceptance rules)

| declaration group | class | justification |
| --- | --- | --- |
| `HeatKernelDataV1`, `IsHeatKernelV1`, `HeatKernelExistenceStatementV1`, variant predicates | model/interface (v1 definitions) | definitional; nothing assumed; the version tag `v1` is explicit |
| `ofHeatKernelData`, D7-field transfer theorems, `exists_toCore_eq_iff`, `integrabilityClassVariant_weak_iff` | genuine-general | definitional or tautological-in-the-good-sense tightness; no extra hypothesis |
| `flatHeatKernelDataV1_{integrable,cc}` + kernel/mass/semigroup/heat-equation/Gaussian-bound transfer + bump non-vacuity | model — explicit Euclidean model, unconditional in `n` | proved from D10/D11 theorems (themselves kernel-checked) + D12 re-typing; no dimension restriction |
| `flat_v1_exists_not_legacy_of_pos`, `flat_legacy_exists_zero`, `flat_v1_of_legacy_zero` | general, unconditional in `n` | from D12 `Counterexample` and D11 `ZeroDimension`, both kernel-checked |
| `toHeatKernelData_of_{integrableClass,ccClass}`, `..._toCore`, `..._initialCondition`, `ofHeatKernelData_upgrade_eq` | general with fully expanded hypotheses `[CompactSpace X] [OpensMeasurableSpace X] [IsFiniteMeasure]` (+ `[IsFiniteMeasureOnCompacts]` for `C_c`) | hypotheses expanded to mathlib regularity conditions, proved automatic in the intended closed-manifold setting; genuine constructions |
| `isHeatKernelV1_integrable_iff_of_closed`, `heatKernelExistenceStatement_iff_v1` | genuine-general (statement reduction) | proved unconditionally from the statement's own antecedent; the existence statements themselves remain statement-only |
| `v1_flat_inhabited`, `v1_flat_no_legacy_of_pos`, `punit_v1_upgrade_eq` | model/instance-level consumption | checked witnesses on concrete objects |
| `PredicateSemantics.lean` (16 declarations): `heatOperator_eq_zero_iff`, the snapshot identities, the harmonicity consequences, `flatHeatSpacetime` + its field lemmas, `flatKernel_laplacian_snapshot_ne_zero`, the two non-satisfaction theorems | genuine-general (semantic analysis), model witness for the flat case | every lemma proved unconditionally; the flat witness is the explicit D10 kernel and the honest flat spacetime; the non-satisfaction theorems are *negative* results about the D7 predicate, not about the D13 data |
| `PDERepair.lean` (18 declarations): `IsHeatKernelPDE` (v2) + `solvesPDE_hasDerivAt`, `HeatKernelDataV1.toHeatSpacetime` + field lemmas, `kernel_pos_of_dist_le_one`, `IsHeatKernelPDE.of_dataV1` + both class specializations, `flatHeatSpacetime_eq_toHeatSpacetime`, `flat_isHeatKernelPDE_{integrable,cc}`, `flat_pde_repaired_scope`, `not_forall_isHeatKernelPDE_imp_isHeatKernelV1` | interface repair candidate (v2 definition), genuine-general transport, model witness for the flat case | definitional predicate with the honest PDE field; `of_dataV1` takes everywhere-positivity as an *explicit* hypothesis because the core's Gaussian lower bound only gives it near the diagonal (`kernel_pos_of_dist_le_one`); the flat instances are proved from the D10/D11 theorems; the non-implication theorem is a checked *negative* comparison of the two predicates. No existence statement is introduced |
| conditional | none | no declaration assumes `FullInitialCondition` (or anything equivalent) in any positive dimension; the compact upgrade is from the proved D12 equivalence, not from an assumed full condition; `IsHeatKernelPDE.of_dataV1`'s positivity hypothesis is a mathlib-level pointwise statement, discharged for the flat model by the proved `flatKernel_pos` |

No theorem is a restatement of an assumption; every hypothesis is expanded to a mathlib-level
regularity condition and consumed by a downstream theorem.

---

> **Fifth invocation:** the commands below are the fourth-invocation record; the current
> (fifth-invocation) gate evidence, including the statement-refutation transcript, is in §17.4.

## 7. Compile evidence

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7

# 0. semantic transcript of the new PDE-repair declarations (fourth invocation)
cd "$WT"
lake env lean tmp/d13_pde_repair_checks.lean          # exit 0; exact #check types in logs/d13_final_semantic_checks.out

# 1. full build of the release package (cwd = release/) — fourth invocation
cd "$WT/release"
lake build                                     # exit 0: "Build completed successfully (9187 jobs)"; D6AUDIT PASS
                                               # D13HeatKernelBridgeAxiomCheck PASS (108 decls) in logs/d13_final_build.log

# 2. per-file gate exactly as the dispatcher runs it (cwd = worktree root)
cd "$WT"
for f in release/Poincare/D13/HeatKernelBridge/{Basic,EuclideanTransport,CompactUpgrade,All,PredicateSemantics,PDERepair,AxiomAudit}.lean \
         release/Poincare/D7/HeatKernel/V1Interface.lean; do
  lake env lean "$f"                          # 8/8 exit 0 (logs/d13_final_perfile.txt)
done

# 3. full worktree gate (cwd = worktree root; third_party excluded as in the D12 pattern)
find . -name '*.lean' -not -path './.lake/*' -not -path './.git/*' -not -path './.dshpkg/*' \
  -not -path './third_party/*' -print0 | xargs -0 -n1 -P8 \
  sh -c 'lake env lean "$0" > /dev/null 2>&1; echo "$?:$0"' > logs/d13_final_gate_raw.txt
                                               # 307/307 exit 0, 0 failures

# 4. forbidden-token scan (comment/string aware)
python3 input/d5-tools/scan_forbidden.py release/Poincare/D13/HeatKernelBridge  # 7 files, 0 hard / 0 soft
python3 input/d5-tools/scan_forbidden.py release/Poincare/D7/HeatKernel        # 10 files, 0 hard / 0 soft

# 5. negative control, source integrity, upstream snapshot
lake env lean negcontrol/NegativeControl.lean   # exit 0: NegativeControl: PASS
diff -rq release/Poincare <D12-snapshot>/release/Poincare
                                               # only "D13" and "D7/HeatKernel/V1Interface.lean"
python3 tmp/verify_frenzymath_snapshot.py       # exit 0: all seven upstream-snapshot checks true
```

Evidence files: `logs/d13_final_perfile.txt` (8/8), `logs/d13_final_gate_raw.txt` (307/307),
`logs/d13_final_build.log` (108 `#print axioms` lines + PASS), `logs/d13_final_hashes.txt`,
`logs/d13_final_semantic_checks.out`, `logs/d13_final_diff.txt`, `logs/d13_final_negcontrol.out`,
`logs/d13_final_forbidden_{d13,d7}.json`, `logs/d13_final_upstream.out`; pre-change baseline re-run:
`logs/d13_fourth_build.log`, `logs/d13_fourth_perfile.txt`, `logs/d13_fourth_gate_raw.txt`,
`logs/d13_fourth_baseline_hashes.txt`, `logs/d13_fourth_forbidden_{d13,d7}.json`,
`logs/d13_fourth_negcontrol.out`, `logs/d13_fourth_diff.txt`, `logs/d13_fourth_upstream.out`.
Third-invocation evidence: `logs/d13_third_*`; second: `logs/d13_*_verify.*`.

---

> **Fifth invocation:** the audit has been extended to **126 declarations** and passes 126/126
> (`logs/d13_fifth_final_build.log`); the table below records the fourth-invocation 108-declaration
> run, and §17.4 the current one.

## 8. Axiom evidence (kernel trust, separate from compilation)

`release/Poincare/D13/HeatKernelBridge/AxiomAudit.lean` prints `#print axioms` for all 108
declarations and re-checks every cone programmatically with `Lean.collectAxioms`, **failing the
build** on any axiom outside `{propext, Classical.choice, Quot.sound}` (fail-closed `run_cmd`
`throwError`).

| item | value |
| --- | --- |
| `#print axioms` declarations | **108 / 108** — 2 depend on no axioms (`HeatKernelDataV1.v1`, `IsHeatKernelPDE.v2`), 106 depend on subsets of the approved cone |
| programmatic re-check | `D13HeatKernelBridgeAxiomCheck: PASS — all 108 declarations of the D13 heat-kernel bridge depend only on [propext, Classical.choice, Quot.sound]` (fourth invocation, `logs/d13_final_build.log` / `logs/d13_final_axiom_audit.out`; third invocation PASS 90/90 in `logs/d13_axiom_audit_third.out`; second PASS 74/74 in `logs/d13_axiom_audit_verify.out`) |
| `sorryAx` / project axiom / `unsafe` / `native_decide` / `proof_wanted` / `admit` | **0 / 0 / 0 / 0 / 0 / 0** |
| negative control | `negcontrol/NegativeControl.lean` exit 0: the same audit logic **detects** `sorryAx` and the `native_decide` axiom (`NegativeControl: PASS`), so the PASS verdict above is not vacuous |

`Classical.choice` enters only through mathlib's classical lemmas (measure theory, the D11
Laplacian, the D10 kernel machinery); no project axiom is introduced.

---

> **Fifth invocation:** the current hashes are recorded in §17.4
> (`logs/d13_fifth_final_hashes.txt`); the table below is the fourth-invocation record and is
> retained for provenance. The two D7 files are new (authored by this task); no legacy D7/D10/D11/D12
> source was modified.

## 9. Source integrity and hashes

`diff -rq` against the `D12-heat-domain-repair` release snapshot: the only differences are the new
`release/Poincare/D13/` directory (7 files) and `release/Poincare/D7/HeatKernel/V1Interface.lean`
(1 file). **No D7/D10/D11/D12 builder source file was modified.**

**Fourth-invocation hashes (final artifact).** `All.lean` (module docstring extended) and
`AxiomAudit.lean` (extended to 108 declarations) changed; `PDERepair.lean` is new; the other five
authored files are byte-identical to the third invocation.

| file | sha256 |
| --- | --- |
| `release/Poincare/D13/HeatKernelBridge/Basic.lean` | `96328402d9633274536400a91b75a8194f932609afc2f6dcbccea0e2d2474d63` |
| `release/Poincare/D13/HeatKernelBridge/EuclideanTransport.lean` | `1bc54d6d38c6a6ccbb90c74e8dd023774fd2fb2e1ad4858fe395351abb555598` |
| `release/Poincare/D13/HeatKernelBridge/CompactUpgrade.lean` | `c93915ba64fbd1a56dbf6b21e32f7baede95a43be5f6a98192050f3786cbc6fb` |
| `release/Poincare/D13/HeatKernelBridge/All.lean` (docstring extended) | `65fccc50ef07fab81cc1cf03c1788d12cdf6c7983a39c8a405669a90ed36b863` |
| `release/Poincare/D13/HeatKernelBridge/PredicateSemantics.lean` (third invocation) | `ef5d789ee795810081fc8771a944b1dfc01dc1fa29b248fbac7347044500118f` |
| `release/Poincare/D13/HeatKernelBridge/PDERepair.lean` (fourth invocation, new) | `bdaaf609ed5bec6055f90dafb356f7585a30d8d1e5683f237ae99bf976a99d0e` |
| `release/Poincare/D13/HeatKernelBridge/AxiomAudit.lean` (extended fourth invocation, 108 decls) | `740a6bf881ff3df08c4e0853863dc1af34af4c7f55dd1f13e92cfec583aab259` |
| `release/Poincare/D7/HeatKernel/V1Interface.lean` | `8d5fa5b5a7dfdc728ccc0f288f48153e02a9b1b852679055af2813f44d6b86e8` |
| root `lakefile.toml` (build config only) | `b56f13927f2c63a07221b0fde9a31d20d42f99b80e90d4330aa7c06de6c642fa` |
| root `lake-manifest.json` (build config only) | `cbc45ee0bd591606b3bb5ba38c38e41f3d317c59f99cb2dfb0adc7d33b32c3d0` |
| root `lean-toolchain` (build config only) | `8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88` |

The ten third-invocation hashes were re-computed byte-identical at the start of the fourth
invocation, before any change (`logs/d13_fourth_baseline_hashes.txt`; identical to
`logs/d13_third_hashes.txt`), which is the artifact on which the §16.1 baseline gates ran.

---

## 10. Blockers

- **`exact_blockers_closed = []`.** In particular the named blocker
  `D7-HEAT-KERNEL-EXISTENCE` (manifold heat-kernel existence: parametrix/Levi method, parabolic
  regularity, Sobolev theory, spectral theorem, Gaussian bounds on manifolds, parabolic maximum
  principle) is **not closed** by this task and remains open. What is delivered and
  kernel-checked is its *interface*: the corrected-domain D7 interface inhabited by the D10
  Euclidean kernel in every dimension (§3), the compact finite-measure upgrade to the genuine
  legacy `HeatKernelData` type (§4), and the D7-consumer equivalence
  `heatKernelExistenceStatement_iff_v1` showing the blocked statement is exactly its
  corrected-domain restatement on closed manifolds (§5) — a constructed downstream checked use,
  not an existence proof, and not claimed as a blocker closure.
- **Resolved by prior tasks and now bridged (not claimed as new closures):** the D7
  `initialCondition` defect validated by D12-semantic-ledger and repaired by
  D12-heat-domain-repair is now transported end-to-end: the D10 kernel inhabits the versioned
  interface in every dimension, and in the compact finite-measure scope the versioned datum is
  literally a legacy D7 datum (`ofHeatKernelData_upgrade_eq`).
- **`remaining_blockers`:** `D7-HEAT-KERNEL-EXISTENCE` and the other six `B-D7-*` analytic
  blockers (parabolic regularity, Sobolev embedding, spectral theorem, Dirac delta, Gaussian
  bounds, maximum principle) — unchanged; the corrected-domain restatement
  `HeatKernelExistenceStatementV1` is the ready target statement for the tasks that will
  construct them.
- **Interface-level statement repair (found in the third invocation, given a checked repair
  candidate in the fourth, and shown to be *necessary* in the fifth; NOT closed):** the D7
  predicate's heat-equation field is a snapshot operator identity, not the PDE (§15,
  `PredicateSemantics.lean`). The fourth invocation adds a versioned, kernel-checked repair
  candidate: `IsHeatKernelPDE` (v2) with the genuine `HasDerivAt` PDE field, a transport from
  `HeatKernelDataV1` data to it, and the theorem that the D10 kernel inhabits it in every dimension
  while refuting the snapshot predicate (§16.2, `PDERepair.lean`). **The fifth invocation proves the
  stronger statement-level fact: the D7 `HeatKernelExistenceStatement` and its corrected-domain
  restatement `HeatKernelExistenceStatementV1` are *false as formalized*** (§17,
  `StatementRefutation.lean`, `StatementStatus.lean`): `IsClosedRiemannianManifold` constrains only
  the volume measure and the distance, so the one-point spacetime with Dirac volume,
  `laplacian = id` and `timeDerivative = 0` is admissible, and its `solves` field forces
  `K x y t = 0`, contradicting strict positivity. Consequently **no proof of the D7 blocked
  statement as written can exist**: the interface itself must be repaired (pin `laplacian` to a
  geometric Laplace–Beltrami operator and replace/constrain `timeDerivative`). This is *not* one of
  the seven named analytic blockers and is *not* a closure — it is the machine-checked reason why
  those blockers cannot be discharged against the present statement. It does not affect the D13
  data-level transport, `HeatKernelDataV1`, which carries the genuine `HasDerivAt` heat equation and
  is inhabited by the D10 kernel in every dimension; `exact_blockers_closed` remains `[]`.

## 11. Reuse and licenses

mathlib4 is consumed at the pinned revision `7974e751bece493b6ff508039423ca9fa2452fa8`
(Apache 2.0) through `lake`; the pinned frenzymath snapshot
`third_party/frenzymath/Poincare-Conjecture` @ `bb91a091f0b968f8bbe8d861e025a88d82b161be` was
consulted per `docs/UPSTREAM-INTEGRATION.md` and no foundation was recreated: the bridge imports
the existing local adapter modules (`Poincare.D10.HeatKernelEuclidean`,
`Poincare.D11.HeatKernelBridge`, `Poincare.D12.HeatDomain`, `Poincare.D7.HeatKernel`) which are
themselves the D10/D11/D12 stages of the upstream-integration order. No source was copied from any
external development and no admitted proof was imported.

## 12. Honest scope and deviations

- **Proved and unconditional:** the corrected-domain interface and its tightness; the D10
  Euclidean transport in every dimension (both classes) with kernel/mass/semigroup/heat-equation
  transfer; non-vacuity; the positive-dimension scope contrast; the compact finite-measure
  upgrades with expanded hypotheses; the left-inverse round trip; the D7 consumer's per-kernel and
  statement-level equivalences and the concrete PUnit round trip.
- **Deviation from the plan wording:** the "consumed downstream by a D7 module" requirement is met
  by a *new* D7-namespaced module (`release/Poincare/D7/HeatKernel/V1Interface.lean`) rather than
  by editing an existing D7 builder file — no existing D7/D10/D11/D12 file was touched (the D12
  precedent).
- **Not claimed:** manifold heat-kernel existence, parametrix, parabolic regularity, Sobolev or
  spectral theory, Gaussian bounds on manifolds, anything about the Poincaré conjecture or Ricci
  flow. `HeatKernelExistenceStatementV1` is statement-only, exactly like the legacy statement it
  reduces. `IsHeatKernelPDE` is a *predicate* repair candidate (v2) with a proved flat-model
  inhabitant; no existence statement is introduced for it (§16.2), because `HeatSpacetime` does not
  constrain `laplacian` to be the geometric Laplace–Beltrami operator.

## 13. Next dependency requests

1. **Independent acceptance** of this card (`compiled_only_until_independent_semantic_review`):
   a fresh rebuild of the 10 authored modules from the recorded fifth-invocation hashes (§17.4), re-run
   of the fail-closed axiom check (126 declarations) and the negative control, and a semantic review of
   `HeatKernelDataV1`, `heatKernelExistenceStatement_iff_v1`, the compact upgrade hypotheses,
   `exists_v1_iff_exists_legacy`, the `PredicateSemantics.lean` findings of §15, the
   `IsHeatKernelPDE` repair candidate of §16, and the statement-level refutation of §17.
2. D12-heat-semigroup-analysis / D13-deturck-shorttime-producer may consume
   `flatHeatKernelDataV1_integrable` / `flatHeatKernelDataV1_cc` as the checked model datum on the
   corrected domain.
3. The manifold-side tasks that will eventually close `D7-HEAT-KERNEL-EXISTENCE` should target the
   **data-level form** — the genuine `HasDerivAt` heat equation carried by `HeatKernelDataV1` — or
   the versioned predicate `IsHeatKernelPDE` supplied in §16.2, which states that equation at the
   D7 predicate level and is inhabited by the D10 kernel in every dimension. The snapshot field of
   `IsHeatKernel`/`IsHeatKernelV1` must not be read as `∂ₜK = ΔK`: the reduction
   `heatKernelExistenceStatement_iff_v1` is a legitimate equivalence between the legacy and
   corrected-domain statements (both share the field), but a proof of the predicate as written would
   not be a proof of the PDE (§15) — and, by §17, **cannot exist**, because the statement is refuted
   as formalized.
4. Downstream users of the legacy `HeatKernelData` in compact finite-measure settings can consume
   `toHeatKernelData_of_integrableClass` / `toHeatKernelData_of_ccClass` to upgrade corrected-domain
   data, and `exists_v1_iff_exists_legacy` to transfer *existence* of data across the two interfaces
   for a fixed core; no changes to the legacy interface are requested.
5. **Statement-repair request (v2 adoption, now blocking for the named blocker):** the
   machine-checked refutation of §17 shows that `HeatKernelExistenceStatement` /
   `HeatKernelExistenceStatementV1` are false as formalized, so the named blocker
   `D7-HEAT-KERNEL-EXISTENCE` cannot be closed against them. A future statement-level task must
   define the existence statement over an enriched `HeatSpacetime` whose `laplacian` is pinned to the
   Laplace–Beltrami operator of a Riemannian metric (and replace or constrain the snapshot
   `timeDerivative` field); the current card does not introduce such a statement because the
   schematic `HeatSpacetime` does not determine the operator, so an existence `Prop` over it would
   not be the manifold theorem. Until then, the data-level interface `HeatKernelDataV1` of this
   bridge is the only honest D7 target.

Machine-readable card: `longrun/results/D13-heatkernel-bridge-d10-d7.json`.

## 14. Second-invocation re-verification (2026-09-11T05:04Z, ≈ 0.1 h)

The task was re-entered; no completed work was restarted. All six authored source hashes were
re-computed and match §9 byte for byte, so the existing artifact was re-checked rather than
rebuilt from modified sources.

| gate (second run) | result | log |
| --- | --- | --- |
| `lake build` (cwd `release/`) | **exit 0** — `Build completed successfully (9185 jobs)`, D6AUDIT PASS (`project_axioms 0`, `sorry 0`, `unsafe 0`, `native_decide 0`, `proof_wanted 0`) | `logs/d13_rebuild_verify.log` |
| `lake build Poincare.D13.HeatKernelBridge.AxiomAudit` | **exit 0** — `D13HeatKernelBridgeAxiomCheck: PASS — all 74 declarations … [propext, Classical.choice, Quot.sound]` (8901 jobs) | `logs/d13_axiom_audit_verify.out` |
| per-file dispatcher gate (6 authored files, cwd worktree root) | **6/6 exit 0** | — |
| full worktree gate (`.lake`/`.git`/`.dshpkg`/`third_party` excluded) | **303/303 exit 0, 0 failures** | `logs/d13_gate_verify_raw.txt` |
| forbidden-token scan (comment/string aware) | **0 hard / 0 soft** (`D13/HeatKernelBridge` 5 files; `D7/HeatKernel` 10 files) | — |
| negative control | **PASS** — detects `sorryAx` and the `native_decide` axiom | `logs/d13_negcontrol_verify.out` |
| source integrity (`diff -rq` vs `D12-heat-domain-repair`) | only `release/Poincare/D13/` (5 new files) and `release/Poincare/D7/HeatKernel/V1Interface.lean` (1 new file); 288 vs 282 `.lean` files; **no legacy source modified** | — |
| audit coverage | every declaration appearing in the 6 new source files is present in the 74-declaration audit list and in the 74 `#print axioms` transcripts | — |
| assumption audit | no declaration assumes `FullInitialCondition` (or an equivalent); its only D13 occurrences are the legacy-datum input of `ofHeatKernelData` and the *proved* conclusion `hfull` of the `C_c` upgrade; the compact-upgrade hypotheses are mathlib-level (`[CompactSpace X]`, `[OpensMeasurableSpace X]`, `[IsFiniteMeasure …]`) | `release/Poincare/D13/HeatKernelBridge/CompactUpgrade.lean` |

This second run confirms the card's compile and axiom evidence on the frozen artifacts. It does not
substitute for the independent semantic acceptance requested in §13 item 1, and it does not change
the blocker status of §10: `exact_blockers_closed = []`, `D7-HEAT-KERNEL-EXISTENCE` remains open.

Machine-readable card: `longrun/results/D13-heatkernel-bridge-d10-d7.json`.

## 15. Third-invocation semantic finding and gate re-run (2026-09-11T06:45Z, ≈ 0.4 h)

No completed work was restarted. Five of the six pre-existing authored files are byte-identical to
§9 (`Basic.lean`, `EuclideanTransport.lean`, `CompactUpgrade.lean`, `All.lean`,
`D7/HeatKernel/V1Interface.lean`); `AxiomAudit.lean` was extended in place and one **new semantic
companion** was added: `release/Poincare/D13/HeatKernelBridge/PredicateSemantics.lean` (243 lines,
16 audited declarations). No legacy D7/D10/D11/D12 file was touched (`diff -rq` unchanged, §15.2).

### 15.1 The finding: the D7 predicate's heat-equation field is not the PDE

The D13 transport is **data-level**: `HeatKernelDataV1.heatEquation` is the genuine
`HasDerivAt (fun s : ℝ => K x y s) (Δ_x K(·,y,t)) t` field inherited from the D11 core — the actual
`∂ₜK = ΔK`. The D7 *statement-level* predicate `Poincare.D7.HeatKernel.IsHeatKernel` — and its
corrected-domain copy `IsHeatKernelV1` — instead carries

```
solves : ∀ y t, 0 < t → S.heatOperator (fun x => K x y t) = 0,
```

where `S.timeDerivative : (M → ℝ) →ₗ[ℝ] (M → ℝ)` acts on functions of the **space** variable and
`fun x => K x y t` is a time **snapshot** (it does not depend on `t`). `PredicateSemantics.lean`
proves, unconditionally and with no extra hypotheses:

| declaration | content |
| --- | --- |
| `heatOperator_eq_zero_iff` | the field is exactly `S.timeDerivative u = S.laplacian u` for `u = fun x => K x y t` |
| `isHeatKernel_laplacian_snapshot_eq_timeDerivative`, `isHeatKernelV1_laplacian_snapshot_eq_timeDerivative` | exact content of the field for both predicates |
| `isHeatKernel_laplacian_snapshot_eq_zero_of_timeDerivative_eq_zero`, `isHeatKernelV1_…` | with the zero forward time derivative on a time-independent snapshot, the field **forces** `Δ_x K(·,y,t) = 0` at every `t > 0` |
| `heatOperator_eq_zero_of_timeDerivative_eq_laplacian` | conversely `T = Δ` makes the field hold for **every** kernel: the other degenerate direction, in which it is vacuous |
| `flatHeatSpacetime` + `flatHeatSpacetime_{volume,laplacian,timeDerivative}` | the honest flat Euclidean spacetime: Lebesgue volume, the D10 Laplacian, **zero** forward time derivative, Euclidean distance, dimension `n` |
| `flatKernel_laplacian_snapshot_ne_zero` | `(flatHeatKernelCore n).laplacian (fun z => flatKernel n z 0 1) 0 = K(0,0,1)·(-n/2) ≠ 0` for every `n > 0` |
| `flatHeatSpacetime_positive`, `flatHeatSpacetime_normalized`, `flatHeatSpacetime_dirac_limitFor` | the other three predicate fields **do** hold for the D10 kernel and the honest flat spacetime (Dirac against the continuous-integrable class) |
| `flatHeatSpacetime_not_isHeatKernelV1_integrableClass` | in every positive dimension the D10 Euclidean heat kernel does **not** satisfy the corrected-domain predicate for the honest flat spacetime; only `solves` fails |
| `flatHeatSpacetime_not_isHeatKernel` | the same for the legacy predicate (its Dirac field additionally fails for the D12-validated reason) |

**Consequences, recorded precisely.** (i) The D13 data-level transport is unaffected. (ii) The
equivalence `heatKernelExistenceStatement_iff_v1` is unaffected — both statements share the field, so
the reduction remains legitimate — but a proof of the predicate as written would not be a proof of
`∂ₜK = ΔK`. (iii) A manifold-side construction intended to close `D7-HEAT-KERNEL-EXISTENCE` should
target the genuine `HasDerivAt` form carried by `HeatKernelDataV1`, or the D7 predicate should first
receive the same kind of statement repair D12 gave the initial-condition field. This is a
**statement-semantics finding**, not one of the seven named analytic blockers and **not** a blocker
closure: `exact_blockers_closed` remains `[]`.

### 15.2 Third-invocation gate re-run

| gate (third run) | result | log |
| --- | --- | --- |
| full `lake build` (cwd `release/`) | **exit 0** — `Build completed successfully (9186 jobs)`, D6AUDIT PASS | `logs/d13_third_build.log` |
| `lake build Poincare.D13.HeatKernelBridge.AxiomAudit` | **exit 0** — `D13HeatKernelBridgeAxiomCheck: PASS — all 90 declarations … [propext, Classical.choice, Quot.sound]` | `logs/d13_axiom_audit_third.out` |
| per-file dispatcher gate (7 authored files, cwd worktree root) | **7/7 exit 0** | `logs/d13_third_perfile.txt` |
| full worktree gate (`.lake`/`.git`/`.dshpkg`/`third_party` excluded) | **305/305 exit 0, 0 failures** (previous 303 + `PredicateSemantics.lean` + the `tmp/` `#check` transcript) | `logs/d13_third_gate_raw.txt` |
| forbidden-token scan (comment/string aware) | **0 hard / 0 soft / 0 matches** (`D13/HeatKernelBridge` 6 files; `D7/HeatKernel` 10 files) | `logs/d13_third_forbidden_{d13,d7}.json` |
| negative control | **PASS** — detects `sorryAx` and the `native_decide` axiom | `logs/d13_third_negcontrol.out` |
| source integrity (`diff -rq` vs `D12-heat-domain-repair`) | **only** `release/Poincare/D13/` (6 files) and `release/Poincare/D7/HeatKernel/V1Interface.lean`; **no legacy source modified** | `logs/d13_third_diff.txt` |
| upstream snapshot verifier (`tmp/verify_frenzymath_snapshot.py`, commit `bb91a091`) | **exit 0** — tracked-file count, Lean file/line counts, package roots, no build caches, toolchain pin and mathlib pin all `true` | `logs/d13_third_upstream.out` |
| hashes | 7 authored Lean files + 3 build-config files recorded; five pre-existing sources unchanged from §9 | `logs/d13_third_hashes.txt` |

This third run confirms the compile, axiom, scan and integrity evidence on the frozen artifacts and
adds the §15.1 finding. It does not substitute for the independent semantic acceptance requested in
§13 item 1, and it does not change the blocker status of §10: `exact_blockers_closed = []`,
`D7-HEAT-KERNEL-EXISTENCE` remains open.

Third-invocation terminal status (superseded by §16 below) — `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7/longrun/results/D13-heatkernel-bridge-d10-d7.md`
(third-invocation gates re-run clean: build 9186 jobs exit 0, axiom audit PASS 90/90, per-file 7/7, worktree 305/305, scans 0/0, negative control PASS, source integrity clean; the milestone — the LONG_PLAN HeatKernelBridge consumed by a D7 module — is fully checked; requests independent semantic acceptance; no named blocker is claimed closed; the §15.1 predicate-semantics finding is recorded as a statement-repair dependency, not a closure)

## 16. Fourth-invocation re-verification and PDE repair candidate (2026-09-11T06:52Z, ≈ 0.6 h)

No completed work was restarted. This invocation (a) re-ran every gate on the frozen
third-invocation artifact before changing anything, and (b) turned the §15.1 statement finding into
a checked repair candidate by adding one versioned companion module, `PDERepair.lean` (18 audited
declarations), with the corresponding small extensions of `All.lean` (docstring) and
`AxiomAudit.lean` (108 declarations). No legacy D7/D10/D11/D12 source file was touched.

### 16.1 Baseline re-verification (frozen third-invocation artifact; before any change)

| gate (fourth-run baseline) | result | log |
| --- | --- | --- |
| hashes of the 10 recorded files | **all byte-identical** to the third invocation (`logs/d13_third_hashes.txt`) | `logs/d13_fourth_baseline_hashes.txt` |
| full `lake build` (cwd `release/`) | **exit 0** — `Build completed successfully (9186 jobs)`, D6AUDIT PASS | `logs/d13_fourth_build.log` |
| per-file dispatcher gate (7 authored files, cwd worktree root) | **7/7 exit 0** | `logs/d13_fourth_perfile.txt` |
| full worktree gate | **305/305 exit 0, 0 failures** | `logs/d13_fourth_gate_raw.txt` |
| forbidden-token scan | **0 hard / 0 soft** (D13 6 files; `D7/HeatKernel` 10 files) | `logs/d13_fourth_forbidden_{d13,d7}.json` |
| negative control | **PASS** | `logs/d13_fourth_negcontrol.out` |
| source integrity (`diff -rq` vs `D12-heat-domain-repair`) | only `D13/` and `D7/HeatKernel/V1Interface.lean` | `logs/d13_fourth_diff.txt` |
| upstream snapshot verifier | **exit 0** — all seven checks true (`bb91a091`) | `logs/d13_fourth_upstream.out` |

### 16.2 The PDE-repair companion (`PDERepair.lean`)

The §15.1 finding was that the legacy D7 predicate's `solves` field is a time-snapshot operator
identity and is refuted by the honest flat Euclidean spacetime for the D10 kernel in positive
dimension. This invocation supplies the matching repair as a **new versioned D13 predicate**, with
no legacy file edited:

| declaration | content | evidence class |
| --- | --- | --- |
| `IsHeatKernelPDE.v2` | version tag `2` | definition (no axioms) |
| `IsHeatKernelPDE S C K` | the D7 predicate with `solvesPDE : ∀ x y t, 0 < t → HasDerivAt (fun s => K x y s) (S.laplacian (fun z => K z y t) x) t` in place of the snapshot identity; positivity, normalization and the admissible-class Dirac field as in `IsHeatKernelV1`. `S.timeDerivative` is retained by the ambient structure but does not occur | model/interface definition (v2) |
| `IsHeatKernelPDE.solvesPDE_hasDerivAt` | restatement of the field as a `HasDerivAt` fact | genuine-general |
| `HeatKernelDataV1.toHeatSpacetime` + 5 field lemmas | the spacetime attached to a bridge datum (volume/Laplacian/distance/dimension of the core; `timeDerivative := 0`, unused) | model/interface |
| `HeatKernelDataV1.kernel_pos_of_dist_le_one` | the core's Gaussian lower bound gives strict positivity only for `dist x y ≤ 1`; everywhere-positivity is *not* a consequence of the core fields and is an explicit hypothesis of the transport | genuine-general |
| `IsHeatKernelPDE.of_dataV1` | **predicate-level transport**: `HeatKernelDataV1` datum + everywhere-positivity → `IsHeatKernelPDE D.toHeatSpacetime C D.kernel` for any class contained in the datum's class (normalization and Dirac use kernel symmetry to match the D7 argument order); `of_dataV1_integrableClass` and `of_dataV1_ccClass` specialize to the two standard classes | genuine-general |
| `flat_isHeatKernelPDE_integrable`, `flat_isHeatKernelPDE_cc` | the D10 Euclidean kernel inhabits the repaired predicate on the honest flat spacetime, on both classes, **in every dimension**; positivity everywhere is the proved explicit Gaussian fact `flatKernel_pos` | model — explicit Euclidean model |
| `flat_pde_repaired_scope` | for every `n > 0`: repaired predicate inhabited **and** snapshot predicate refuted, by the same kernel on the same spacetime | model + negative result |
| `not_forall_isHeatKernelPDE_imp_isHeatKernelV1` | the repaired predicate does **not** imply the snapshot predicate (refuted by the flat model); the repair is a genuine statement change, not a definitional weakening | negative result, genuine-general |

**What this does and does not establish.** Proved: the repaired predicate is a well-formed,
versioned D7-level statement whose heat-equation field is the actual PDE; the D13 data-level bridge
transports into it (with an explicit, mathlib-level positivity hypothesis that the flat model
discharges); and the exact D10 kernel inhabits it in every dimension on both admissible classes,
while the snapshot predicate remains refuted there. Not established and not claimed: any existence
statement for the repaired predicate on manifolds, any closure of `D7-HEAT-KERNEL-EXISTENCE`, or any
change to the legacy D7 predicate. No repaired *existence* `Prop` is introduced on purpose: the
schematic `HeatSpacetime` leaves `laplacian` unconstrained, so a statement over it would not be the
manifold heat-kernel existence theorem; a statement-level repair must first pin `laplacian` to the
geometric Laplace–Beltrami operator (§13 item 5). `exact_blockers_closed` remains `[]`.

### 16.3 Fourth-invocation final gates (with `PDERepair.lean`)

| gate (fourth run, final artifact) | result | log |
| --- | --- | --- |
| semantic `#check` transcript of the new declarations | **exit 0** — exact types as intended (`IsHeatKernelPDE`, `of_dataV1`, flat inhabitants, scope, non-implication) | `logs/d13_final_semantic_checks.out` |
| full `lake build` (cwd `release/`) | **exit 0** — `Build completed successfully (9187 jobs)`, D6AUDIT PASS; `D13HeatKernelBridgeAxiomCheck: PASS — all 108 declarations … [propext, Classical.choice, Quot.sound]` | `logs/d13_final_build.log`, `logs/d13_final_axiom_audit.out` |
| per-file dispatcher gate (8 authored files) | **8/8 exit 0** | `logs/d13_final_perfile.txt` |
| full worktree gate | **307/307 exit 0, 0 failures** (305 baseline + `PDERepair.lean` + the new `tmp/d13_pde_repair_checks.lean` transcript) | `logs/d13_final_gate_raw.txt` |
| forbidden-token scan | **0 hard / 0 soft** (D13 7 files; `D7/HeatKernel` 10 files) | `logs/d13_final_forbidden_{d13,d7}.json` |
| negative control | **PASS** | `logs/d13_final_negcontrol.out` |
| source integrity (`diff -rq` vs `D12-heat-domain-repair`) | **only** `D13/` (7 files) and `D7/HeatKernel/V1Interface.lean`; no legacy source modified | `logs/d13_final_diff.txt` |
| upstream snapshot verifier | **exit 0** — all seven checks true (`bb91a091`) | `logs/d13_final_upstream.out` |
| hashes | 8 authored Lean files + 3 build-config files recorded | `logs/d13_final_hashes.txt` |

This fourth run confirms the compile, axiom, scan and integrity evidence on the current artifact and
adds the §16.2 repair candidate. It does not substitute for the independent semantic acceptance
requested in §13 item 1, and it does not change the blocker status of §10:
`exact_blockers_closed = []`, `D7-HEAT-KERNEL-EXISTENCE` remains open.

## 17. Fifth-invocation re-verification, statement-level refutation, and existential closure (2026-09-11T08:21Z, ≈ 1.4 h)

The fourth invocation was cut off mid-gate-run by the invocation limit (the build and axiom audit had
completed; the remaining gate steps were interrupted). The task was re-entered and **no completed
work was restarted**: the frozen fourth-invocation artifact was re-verified first, byte-identical
hashes included, and the results below were added on top.

### 17.1 Baseline re-verification (frozen fourth-invocation artifact, before any change)

| gate (baseline re-run) | result | log |
| --- | --- | --- |
| the 11 recorded fourth-invocation hashes | **re-computed byte-identical** | `logs/d13_fifth_baseline_hashes.txt` |
| full `lake build` (cwd `release/`) | **exit 0** — `Build completed successfully (9187 jobs)`, D6AUDIT PASS | `logs/d13_fifth_baseline_build.log` |
| axiom audit (inside the build) | **PASS 108/108** | ″ |
| per-file dispatcher gate (8 authored files) | **8/8 exit 0** | `logs/d13_fifth_baseline_perfile.txt` |
| full worktree gate | **307/307 exit 0, 0 failures** | `logs/d13_fifth_baseline_gate_raw.txt` |
| forbidden-token scan (`D13/HeatKernelBridge`, `D7/HeatKernel`) | **0 hard / 0 soft** | `logs/d13_fifth_baseline_forbidden_{d13,d7}.json` |
| negative control | **PASS** | `logs/d13_fifth_baseline_negcontrol.out` |
| source integrity (`diff -rq` vs `D12-heat-domain-repair`) | exactly the 2 expected new-file lines | `logs/d13_fifth_baseline_diff.txt` |
| upstream snapshot verifier | **PASS** — all seven checks true (`bb91a091`) | `logs/d13_fifth_baseline_upstream.out` |

### 17.2 The finding: the D7 existence statements are **false as formalized**

The D7 blocked statement (unmodified upstream source, `release/Poincare/D7/HeatKernel/Blocked.lean`)
is

```lean
def HeatKernelExistenceStatement : Prop :=
  ∀ (M : Type*) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (S : HeatSpacetime M), IsClosedRiemannianManifold S →
      ∀ y₀ : M, ∃ K : M → M → ℝ → ℝ, IsHeatKernel S K
```

and the heat-equation field it requires is the *snapshot* identity
`solves : ∀ y t, 0 < t → S.timeDerivative (fun x => K x y t) = S.laplacian (fun x => K x y t)`
(§15). The key observation of this invocation is that `IsClosedRiemannianManifold` consists of
exactly seven fields — `compact_univ`, `volume_pos`, `volume_lt_top`, `dist_self`, `dist_pos`,
`dist_symm`, `dist_triangle` — **none of which mentions `S.laplacian` or `S.timeDerivative`**.
Therefore adversarial but formally admissible operator fields refute the statement:

* the **one-point counterexample spacetime** `refutingSpacetime : HeatSpacetime PUnit` with
  `volume = Measure.dirac PUnit.unit`, `laplacian = LinearMap.id`, `timeDerivative = 0`,
  `dist = 0`, `dim = 0` is certified to satisfy `IsClosedRiemannianManifold`
  (`refutingSpacetime_isClosedRiemannianManifold`: compact, Dirac volume positive on the unique
  nonempty open set and finite on compacts, zero distance a metric on a subsingleton);
* on it the heat operator is negation (`refutingSpacetime_heatOperator`), so `solves` at any
  `x = y`, `t = 1` forces `K x x 1 = 0`, while `positive` requires `0 < K x x 1` — a contradiction
  (`not_isHeatKernel_of_laplacian_id_timeDerivative_zero`, a universe-polymorphic schema needing
  only `Nonempty M`, `S.laplacian = LinearMap.id`, `S.timeDerivative = 0`);
* hence **`not_heatKernelExistenceStatement : ¬ HeatKernelExistenceStatement`** (unconditional at
  universe `0`; `subsingleton_measurableSpace_punit` supplies the `BorelSpace PUnit` instance that
  mathlib does not register), and the same schema refutes `.{u}` at every universe
  (`not_heatKernelExistenceStatement_of_refuting`). A universe-polymorphic proof of the statement
  cannot exist, since it would specialise to the refuted universe-`0` instance.

The corrected-domain restatement is refuted by the same field: `not_heatKernelExistenceStatementV1`
(direct, universe `0`, schema at every universe), and the new D7 consumer
`release/Poincare/D7/HeatKernel/StatementStatus.lean` **transports the refutation through the bridge
equivalence** — `not_heatKernelExistenceStatementV1_of_legacy_refutation
(h : ¬ HeatKernelExistenceStatement.{u}) : ¬ HeatKernelExistenceStatementV1.{u}` uses
`heatKernelExistenceStatement_iff_v1.mpr`, cross-checking the direct proof.

**Consequences, stated precisely.**

1. The named blocker `D7-HEAT-KERNEL-EXISTENCE` **cannot be closed by proving the statement as it
   currently stands**: the statement is not merely unproved, it is refutable, so any proof attempt
   must fail. The interface needs a repair that pins `laplacian` (and constrains or replaces the
   `timeDerivative` snapshot field) to the geometric operators of a Riemannian metric — exactly the
   repair direction of §16.2 (`IsHeatKernelPDE`, v2), which is still stated over the schematic
   spacetime and therefore is a predicate-level candidate, not a statement-level repair.
2. This strictly strengthens the §15 finding: §15 refutes the predicate for the *honest flat
   Euclidean model*; §17 refutes the *existential statement itself*, independently of any model, by
   exhibiting an admissible closed Riemannian datum on which the predicate is contradictory.
3. The counterexample measures the *formal interface*, not the intended geometry: on a genuine
   closed Riemannian manifold the Laplace–Beltrami operator is not the identity. The point is that
   the formal predicate does not record this, so the formal statement cannot serve as the target for
   the manifold existence proof.
4. **The data-level bridge is unaffected.** `HeatKernelDataV1` carries the genuine `HasDerivAt` heat
   equation (§2–§3) and is inhabited by the D10 kernel in every dimension; the compact finite-measure
   scope upgrades it to the legacy type (§4). The new theorem
   `exists_v1_iff_exists_legacy` (below) makes the losslessness *existential*: for a fixed core on a
   compact finite-measure space, corrected-domain data exists **iff** legacy D7 data exists.
5. `exact_blockers_closed` remains `[]`; this is a statement-repair finding and a blocker-direction
   correction, not a closure.

### 17.3 New declarations of the fifth invocation (18, all audited)

| declaration | kind | content | semantic class |
| --- | --- | --- | --- |
| `refutingSpacetime` | def | the one-point counterexample `HeatSpacetime` | model/counterexample |
| `refutingSpacetime_volume` / `_laplacian` / `_laplacian_apply` / `_timeDerivative` / `_timeDerivative_apply` / `_heatOperator` | thm ×6 | field computations; heat operator is negation | counterexample lemmas |
| `refutingSpacetime_isClosedRiemannianManifold` | thm | the counterexample satisfies the D7 closed-manifold predicate | counterexample certificate |
| `subsingleton_measurableSpace_punit` | thm | all measurable spaces on `PUnit` coincide (supplies the missing `BorelSpace PUnit` instance) | formal infrastructure |
| `not_isHeatKernel_of_laplacian_id_timeDerivative_zero` | thm | universe-polymorphic schema: `laplacian = id`, `timeDerivative = 0` ⇒ no `IsHeatKernel` kernel | negative result, general |
| `not_isHeatKernelV1_of_laplacian_id_timeDerivative_zero` | thm | same schema for the corrected-domain predicate, any admissible class | negative result, general |
| `not_heatKernelExistenceStatement_of_refuting` | thm | universe-polymorphic: any such closed Riemannian datum refutes `HeatKernelExistenceStatement.{u}` | negative result, general |
| `not_heatKernelExistenceStatementV1_of_refuting` | thm | same for `HeatKernelExistenceStatementV1.{u}` | negative result, general |
| `not_heatKernelExistenceStatement` | thm | unconditional refutation at universe `0` | negative result, unconditional |
| `not_heatKernelExistenceStatementV1` | thm | unconditional refutation at universe `0` | negative result, unconditional |
| `exists_v1_iff_exists_legacy` | thm | compact finite measure: `∃` V1 datum with a fixed core (integrable-class variant) ↔ `∃` legacy `HeatKernelData` with that core | general, existential closure |
| `Poincare.D7.HeatKernel.not_heatKernelExistenceStatementV1_of_legacy_refutation` | thm | the bridge equivalence transports a refutation of the legacy statement to the V1 statement | D7 consumer, cross-check |
| `Poincare.D7.HeatKernel.not_heatKernelExistenceStatementV1` | thm | D7-level refutation via the bridge equivalence | D7 consumer, cross-check |

Files: new `release/Poincare/D13/HeatKernelBridge/StatementRefutation.lean` (15 declarations), new
`release/Poincare/D7/HeatKernel/StatementStatus.lean` (2 declarations), and one new theorem in
`release/Poincare/D13/HeatKernelBridge/CompactUpgrade.lean`; plus docstring updates in `All.lean` and
`V1Interface.lean` and the `AxiomAudit.lean` extension to **126** declarations. No D7/D10/D11/D12
file was edited (the two D7 files are new, authored by this task).

### 17.4 Fifth-invocation final gates (with the new files)

| gate (fifth run, final artifact) | result | log |
| --- | --- | --- |
| semantic `#check`/`#print axioms` transcripts (PDE repair + statement refutation) | **exit 0** — exact types as intended; 8 + 1 axiom transcripts | `logs/d13_fifth_final_semantic_checks.out` |
| full `lake build` (cwd `release/`) | **exit 0** — `Build completed successfully (9189 jobs)`, D6AUDIT PASS; `D13HeatKernelBridgeAxiomCheck: PASS — all 126 declarations … [propext, Classical.choice, Quot.sound]` | `logs/d13_fifth_final_build.log` |
| per-file dispatcher gate (10 authored files) | **10/10 exit 0** | `logs/d13_fifth_final_perfile.txt` |
| full worktree gate | **310/310 exit 0, 0 failures** | `logs/d13_fifth_final_gate_raw.txt` |
| forbidden-token scan | **0 hard / 0 soft** (D13 8 files; `D7/HeatKernel` 11 files) | `logs/d13_fifth_final_forbidden_{d13,d7}.json` |
| negative control | **PASS** | `logs/d13_fifth_final_negcontrol.out` |
| source integrity (`diff -rq` vs `D12-heat-domain-repair`) | **only** `D13/` (8 files), `D7/HeatKernel/V1Interface.lean`, `D7/HeatKernel/StatementStatus.lean`; no legacy source modified | `logs/d13_fifth_final_diff.txt` |
| upstream snapshot verifier | **exit 0** — all seven checks true (`bb91a091`) | `logs/d13_fifth_final_upstream.out` |
| hashes | 10 authored Lean files + 3 build-config files recorded | `logs/d13_fifth_final_hashes.txt` |

Recorded fifth-invocation hashes (`logs/d13_fifth_final_hashes.txt`; unchanged files match §9/§16):
`Basic.lean 96328402…`, `EuclideanTransport.lean 1bc54d6d…`, `PDERepair.lean bdaaf609…`,
`PredicateSemantics.lean ef5d789e…`, `All.lean e08994f0…`, `CompactUpgrade.lean 4f514a48…`,
`AxiomAudit.lean 859dcdf3…`, `StatementRefutation.lean 7f65cb75…`,
`V1Interface.lean a16e54a1…`, `StatementStatus.lean dc49b11a…`.

### 17.5 Fifth-invocation verdict

The milestone — the `LONG_PLAN` `HeatKernelBridge` transporting D10 to the corrected-domain D7
interface, consumed by D7 modules — remains **fully checked** on the extended artifact (126 audited
declarations, all gates green). The fifth invocation adds a machine-checked **statement-level
refutation** that changes the *direction* of the named blocker: `D7-HEAT-KERNEL-EXISTENCE` cannot be
closed against the present statement and requires the interface repair described in §17.2. No named
blocker is claimed closed; `exact_blockers_closed = []`. The card requests independent semantic
acceptance of the 10 authored modules (§13 item 1).


---

## 18. Sixth-invocation statement-level repair package (2026-09-11T16:38+08:00, ≈ 0.8 h)

### 18.1 Baseline re-verification (frozen fifth-invocation artifact, before any change)

| gate (baseline run, before any sixth-invocation write) | result | log |
| --- | --- | --- |
| source hashes | **13/13 OK** — `sha256sum -c` on the fifth-invocation manifest is byte-identical | `logs/d13_fifth_final_hashes.txt` |
| full `lake build` (cwd `release/`) | **exit 0** — `Build completed successfully (9189 jobs)`, D6AUDIT PASS; `D13HeatKernelBridgeAxiomCheck: PASS — 126/126` | `logs/d13_sixth_baseline_build.log` |
| per-file dispatcher gate | **10/10 exit 0** | `logs/d13_sixth_baseline_perfile.txt` |
| full worktree gate | **313/313 exit 0, 0 failures** | `logs/d13_sixth_baseline_gate_raw.txt` |
| forbidden-token scan | **0 hard / 0 soft** | `logs/d13_sixth_baseline_forbidden_{d13,d7}.json` |
| negative control | **PASS** | `logs/d13_sixth_baseline_negcontrol.out` |
| source integrity (`diff -rq` vs `D12-heat-domain-repair`) | exactly the 3 expected new-file lines (no legacy source modified) | `logs/d13_sixth_baseline_diff.txt` |
| upstream snapshot verifier | **exit 0** (all seven checks, `bb91a091`) | `logs/d13_sixth_baseline_upstream.out` |

### 18.2 The sound geometric condition, and why the naive geometric axioms are not stateable

`GeometricRepair.lean` introduces the operator condition that the sixth invocation can actually
verify:

* `AnnihilatesConstants S := (S.laplacian 1 = 0)` — a Laplace–Beltrami operator on a closed manifold
  annihilates constants (no boundary). It is *the one* geometric necessary condition that is
  expressible over the schematic interface and verifiable for the honest flat operator;
* `not_isAnnihilatesConstants_refutingSpacetime`: the fifth-invocation counterexample
  (`laplacian = id`) is **excluded**, so the condition genuinely removes the datum that refutes the
  legacy statement;
* `exists_isClosedRiemannianManifold_not_isAnnihilatesConstants`: it is a **strict** strengthening of
  `IsClosedRiemannianManifold` (the refuting datum witnesses the difference);
* `punitDiracSpacetime`, `isAnnihilatesConstants_punitDiracSpacetime`: the condition is
  **consistent**, satisfied by the honest zero-dimensional model (one point, Dirac volume, zero
  operators);
* `flatHeatSpacetime_laplacian_one`: the honest flat D10 Laplacian (the D11 packaged `Δ`) satisfies
  the condition, so the intended flat operator is **not** excluded.

The stronger classical conditions (formal self-adjointness `∫ u · Δv = ∫ Δu · v`, dissipativity
`∫ u · Δu ≤ 0`) are deliberately **not** fields of the structure. Stated with the schematic
interface's Bochner integral over all functions they are false for the honest packaged flat
Laplacian (proved in `LaplacianSymmetryRefutation.lean`, §18.7): with `u = 1` and `v = log cosh` on
`ℝ` one has `Δv = 1 - tanh²` and `Δu = 0`, so the left-hand side is
`∫ (1 - tanh²) = [tanh]_{-∞}^{∞} = 2` while the right-hand side is `∫ 0 · v = 0`. Their `C_c`/`C²`
forms need a smooth normed structure that `HeatSpacetime` does not carry. This is recorded as a
**semantic-class distinction**: the constant annihilation is a checked necessary condition; the
self-adjointness/dissipativity formulations are *checked false* at the interface, not merely
unavailable.

### 18.3 Second, independent statement-level refutation: the Laplacian-only repair is dead

The natural repair attempt "add geometric hypotheses on the Laplacian, keep the `solves` field" is
refuted by a *new* datum whose Laplacian satisfies the geometric condition:

* `adversarialTimeDerivativeSpacetime`: one point, Dirac volume, `laplacian = 0` (so
  `AnnihilatesConstants` holds), `timeDerivative = LinearMap.id`;
* `adversarial_datum_repaired_hypotheses`,
  `not_exists_isHeatKernelV1_adversarialTimeDerivativeSpacetime`: it satisfies
  `IsClosedRiemannianManifold ∧ AnnihilatesConstants` and admits **no** snapshot kernel — the heat
  operator is the identity, so `solves` forces `K = 0` against strict positivity;
* `not_isHeatKernel_of_laplacian_zero_timeDerivative_id`,
  `not_isHeatKernelV1_of_laplacian_zero_timeDerivative_id`: the general schema, for the legacy and
  the corrected-domain predicate and an arbitrary admissible class;
* `not_forall_annihilatesConstants_implies_exists_snapshot_kernel` (universe `0`) and
  `..._of_refuting` (universe-polymorphic conditional schema): the snapshot existence statement is
  **false even after imposing the constant-annihilation condition**. No repair that constrains only
  `S.laplacian` can restore it.

### 18.4 Time rescaling: the snapshot field is not the PDE; the predicates are incomparable

The complementary repair attempt "pin `timeDerivative := laplacian`" makes the `solves` field
vacuous (`flatSnapshotSpacetime_heatOperator_eq_zero`) and still fails to capture the heat equation:

* `flatSnapshotSpacetime`: the flat spacetime with `timeDerivative := laplacian`;
* `flatKernelRescaled_isHeatKernelV1`: the time-rescaled D10 kernel `K(x,y,c·t)` inhabits the
  snapshot predicate for every `c > 0` (positivity, normalization, and the Dirac limit are preserved
  by the homeomorphism `t ↦ c·t` of `(0,∞)`);
* `flatKernel_laplacian_snapshot_ne_zero_of_pos` (all positive times, generalizing the fifth
  invocation's `t = 1` case) and `flatKernelRescaled_not_isHeatKernelPDE`: for `c = 2` the
  time-rescaled kernel is **not** a solution of the heat equation — at `x = y = 0`, `t = 1` the
  chain rule gives derivative `2·ΔK(·,0,2)` while the PDE field requires `ΔK(·,0,2)`, and
  `ΔK(0,0,2) = K(0,0,2)·(-n/4) ≠ 0` in every positive dimension;
* `not_forall_isHeatKernelV1_imp_isHeatKernelPDE` and `snapshot_pde_predicates_incomparable`:
  together with the converse `not_forall_isHeatKernelPDE_imp_isHeatKernelV1` of §16, the two
  predicates are **incomparable**. The heat-equation field must be *replaced* by the `HasDerivAt`
  statement; no hypothesis on the operators can make it equivalent to the PDE.

### 18.5 The statement-level repaired interface (stated, not proved)

Two versioned `def … : Prop`s are introduced, exactly in the style of the legacy blocked statement:

* `HeatKernelExistenceStatementPDE` — the legacy statement shape on the class
  `IsClosedRiemannianManifold ∧ AnnihilatesConstants`, with the heat equation stated as the genuine
  PDE (`IsHeatKernelPDE`);
* `HeatKernelDataExistenceStatement` — the data-level form: a genuine legacy D7 `HeatKernelData`
  matching the spacetime's volume, distance, dimension and Laplacian, strictly positive at positive
  times, with positive lower Gaussian constant.

They are **not proved**; the analytic content of `D7-HEAT-KERNEL-EXISTENCE` (parametrix, parabolic
regularity, Gaussian bounds, spectral theory) remains open. What *is* checked is that the repair is
faithful and non-vacuous:

* `heatKernelDataExistenceStatement_implies_pde`: the data-level statement implies the
  predicate-level one (legacy `HeatKernelData` fields are the PDE, positivity, normalization and the
  full Dirac condition);
* `heatKernelDataExistenceStatement_conclusion_punit`,
  `heatKernelExistenceStatementPDE_conclusion_punit`: the conclusions hold on the honest
  zero-dimensional model;
* `heatKernelDataExistenceStatement_conclusion_adversarial`,
  `heatKernelExistenceStatementPDE_conclusion_adversarial`: the conclusions hold on the **adversarial
  datum that refutes the snapshot statement** — the sharpest contrast between the defective snapshot
  interface and the honest PDE/data interface;
* `not_both_isClosedRiemannianManifold_and_annihilatesConstants_refutingSpacetime`: the old
  counterexample cannot be used against the repaired statement at all.

### 18.6 D7-level consumption of the repair (`Poincare.D7.HeatKernel.RepairStatus`)

New D7-namespaced module (no existing D7 file edited), 4 audited declarations:
`adversarial_datum_repaired_hypotheses`;
`not_exists_isHeatKernel_adversarialTimeDerivativeSpacetime`;
`exists_heatKernelData_adversarialTimeDerivativeSpacetime`;
`snapshot_refuted_data_exists_adversarialTimeDerivative` — on one closed Riemannian datum satisfying
the constant-annihilation condition, the legacy D7 predicate `IsHeatKernel` has **no** witness while
a genuine legacy `HeatKernelData` (matching volume, distance, dimension, Laplacian) exists.

### 18.7 Companion note 5: the naive self-adjointness axiom is refuted for the honest flat Laplacian

`LaplacianSymmetryRefutation.lean` (11 audited declarations) turns the §18.2 statement into a checked
theorem for the honest one-dimensional flat operator (the D11 packaged `laplacianLinearMap ℝ`):

* `flatLineSpacetime`: the honest flat spacetime on `ℝ` (Lebesgue volume, packaged Laplacian,
  Euclidean distance, dimension `1`);
* `hasDerivAt_tanh_real` (`(tanh)' = 1 - tanh²`), `tanh_eq_one_sub`, `tendsto_tanh_atTop_real`
  (`tanh → 1`), `tendsto_tanh_atBot_real` (`tanh → -1`);
* `hasDerivAt_log_cosh`, `contDiff_log_cosh`, `laplacian_log_cosh`: the second-derivative identity
  `Δ (log ∘ cosh) = 1 - tanh²` for the packaged Laplacian;
* `integrable_one_sub_tanh_sq`, `integral_one_sub_tanh_sq`: `∫ x, (1 - tanh x ^ 2) = 2` (fundamental
  theorem of calculus on the whole real line; integrability comes from the one-sided FTC lemmas plus
  the reflection substitution);
* `not_forall_laplacian_symmetric_flatLine`: the all-functions Bochner-integral form of formal
  self-adjointness, `∀ u v, ∫ u · Δv = ∫ Δu · v`, is **false** for the honest flat operator: with
  `u = 1` and `v = log ∘ cosh` the left-hand side is `2` and the right-hand side is `0`.

Consequence: the schematic `HeatSpacetime` interface cannot be repaired by adjoining the classical
integration-by-parts/dissipativity identities as fields — in that Bochner-integral form they are
false for the honest operator. Together with §18.3 (the Laplacian-only repair is refuted by the free
forward time derivative) and §18.4 (the snapshot field is incomparable with the PDE), this settles
the repair direction: the honest target is the data-level PDE interface supplied by the bridge.

### 18.8 New declarations of the sixth invocation (62, all audited)

| group | declarations | semantic class |
| --- | --- | --- |
| constant annihilation (`AnnihilatesConstants`, `laplacian_one`, `laplacian_one_apply`) | 3 | proved theorem / interface predicate |
| counterexample exclusion and strictness (`not_isAnnihilatesConstants_refutingSpacetime`, `exists_isClosedRiemannianManifold_not_isAnnihilatesConstants`) | 2 | proved theorem |
| zero-dimensional model (`punitDiracSpacetime` + 5 field lemmas + `punitDiracSpacetime_isClosedRiemannianManifold` + `isAnnihilatesConstants_punitDiracSpacetime`) | 8 | model |
| honest flat operator check (`flatHeatSpacetime_laplacian_one`) | 1 | proved theorem |
| adversarial time derivative (`adversarialTimeDerivativeSpacetime` + 3 field lemmas + `_heatOperator` + `_isClosedRiemannianManifold` + `isAnnihilatesConstants_...`) | 7 | model / counterexample |
| adversarial refutations (`not_exists_isHeatKernelV1_adversarialTimeDerivativeSpacetime`; `not_isHeatKernel_of_laplacian_zero_timeDerivative_id`; `not_isHeatKernelV1_of_laplacian_zero_timeDerivative_id`; `not_forall_annihilatesConstants_implies_exists_snapshot_kernel`; `..._of_refuting`) | 5 | negative result, general |
| flat snapshot spacetime (`flatSnapshotSpacetime` + 5 field lemmas + `flatSnapshotSpacetime_heatOperator_eq_zero`) | 7 | model |
| time rescaling (`flatKernelRescaled`, `flatKernelRescaled_isHeatKernelV1`, `flatKernel_laplacian_snapshot_ne_zero_of_pos`, `flatKernelRescaled_not_isHeatKernelPDE`) | 4 | proved theorem / counterexample |
| incomparability (`not_forall_isHeatKernelV1_imp_isHeatKernelPDE`, `snapshot_pde_predicates_incomparable`) | 2 | proved theorem |
| repaired statements and consistency (`HeatKernelExistenceStatementPDE`, `HeatKernelDataExistenceStatement`, `heatKernelDataExistenceStatement_implies_pde`, `exists_isHeatKernelPDE_of_punit_dirac_zero`, `heatKernelExistenceStatementPDE_conclusion_punit`, `heatKernelExistenceStatementPDE_conclusion_adversarial`, `heatKernelDataExistenceStatement_conclusion_punit`, `heatKernelDataExistenceStatement_conclusion_adversarial`, `not_both_...`) | 9 | statement-only / conditional interface / model |
| D7 consumer `Poincare.D7.HeatKernel.RepairStatus` | 4 | D7 consumer, proved theorem |
| `LaplacianSymmetryRefutation.lean` (companion note 5) | 11 | proved theorem / counterexample (real analysis, D11 packaged flat Laplacian) |

47 declarations in `GeometricRepair.lean` + 11 in `LaplacianSymmetryRefutation.lean` + 4 in
`RepairStatus.lean` = **62**; the audit grows from 126 to **188** declarations.

### 18.9 Sixth-invocation final gates (authoritative run)

| gate (sixth run, final artifact) | result | log |
| --- | --- | --- |
| semantic `#check`/`#print axioms` transcripts (6 files) | **exit 0** | `logs/d13_sixth_final_semantic_checks.out` |
| full `lake build` (cwd `release/`) | **exit 0** — `Build completed successfully (9192 jobs)`, D6AUDIT PASS; `D13HeatKernelBridgeAxiomCheck: PASS — all 188 declarations … [propext, Classical.choice, Quot.sound]` | `logs/d13_sixth_final_build.log` |
| per-file dispatcher gate (12 authored files) | **12/12 exit 0** | `logs/d13_sixth_final_perfile.txt` |
| full worktree gate | **319/319 exit 0, 0 failures** | `logs/d13_sixth_final_gate_raw.txt` |
| forbidden-token scan | **0 hard / 0 soft** (D13 10 files; `D7/HeatKernel` 12 files) | `logs/d13_sixth_final_forbidden_{d13,d7}.json` |
| negative control | **PASS** | `logs/d13_sixth_final_negcontrol.out` |
| source integrity (`diff -rq` vs `D12-heat-domain-repair`) | **only** `D13/` (9 files), `D7/HeatKernel/{V1Interface,StatementStatus,RepairStatus}.lean`; no legacy source modified | `logs/d13_sixth_final_diff.txt` |
| upstream snapshot verifier | **exit 0** — all seven checks true (`bb91a091`) | `logs/d13_sixth_final_upstream.out` |
| hashes | 16 recorded (13 authored Lean files + 3 build-config entries; `GeometricRepair.lean`, `LaplacianSymmetryRefutation.lean` and `RepairStatus.lean` new) | `logs/d13_sixth_final_hashes.txt` |

### 18.10 Sixth-invocation verdict

The milestone — the `LONG_PLAN` `HeatKernelBridge` transporting D10 to the corrected-domain D7
interface and consumed by D7 modules — remains **fully checked** on the extended artifact (13
authored files, 188 audited declarations, all gates green). The sixth invocation closes the *repair
direction* of the named blocker as far as it can honestly be closed: the snapshot statement is
refuted twice over (the original counterexample and the constant-annihilating adversarial datum),
the snapshot and PDE predicates are proved incomparable, and the only viable interface is the
data-level PDE one. `D7-HEAT-KERNEL-EXISTENCE` itself remains **open** — the analytic existence
theorem (parametrix, parabolic regularity, Gaussian bounds, spectral theory) is not in mathlib at the
pinned revision — and `exact_blockers_closed` remains `[]`. The card requests independent semantic
acceptance of the 12 authored modules (§13 item 1, extended in §18).

TASK_DONE — `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7/longrun/results/D13-heatkernel-bridge-d10-d7.md`
(sixth-invocation gates clean: the frozen fifth-invocation artifact was re-verified from byte-identical hashes (13/13 OK; build 9189 jobs, axiom audit 126/126, per-file 10/10, worktree 313/313, scans 0/0, negative control PASS, diff 3 expected lines, upstream PASS), and the final artifact is build **9192 jobs exit 0**, `D13HeatKernelBridgeAxiomCheck PASS 188/188`, per-file **12/12**, worktree **319/319**, forbidden **0 hard / 0 soft**, negative control PASS, source integrity clean (only the 10 D13 files and the 3 new D7 consumers), upstream snapshot PASS, 16 hashes recorded. The milestone — the LONG_PLAN `HeatKernelBridge` consumed by D7 modules — is fully checked; the card requests independent semantic acceptance. **No named blocker is claimed closed**: `exact_blockers_closed = []`. The sixth invocation adds the statement-level repair package (§18): the sound constant-annihilation condition excluding the refuting datum, a second independent statement-level refutation (the adversarial datum `Δ = 0`, `∂_t = id` satisfies the repaired hypotheses and admits no snapshot kernel), the time-rescaling theorem proving the snapshot and PDE predicates incomparable (so the heat-equation field must be replaced, not constrained), the data-level repaired statement `HeatKernelDataExistenceStatement` (stated, not proved, non-vacuous and instantiated on the adversarial datum), its D7-level consumption in `Poincare.D7.HeatKernel.RepairStatus`, and the checked refutation of the naive self-adjointness axiom (the classical integration-by-parts identity is false for the honest flat packaged Laplacian, so the repair cannot proceed by adjoining such fields). `D7-HEAT-KERNEL-EXISTENCE` remains OPEN: the analytic existence theorem (parametrix, parabolic regularity, Gaussian bounds, spectral theory) is absent from mathlib at the pinned revision, and the honest target is now the data-level PDE interface supplied by the bridge.)
