# SEMREV-D13-cross-audit-ophis — independent semantic review of `D13-cross-audit-ophis-cards`

- **Task id:** `SEMREV-D13-cross-audit-ophis`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/SEMREV-D13-cross-audit-ophis`
- **Parent artifact under review:** `D13-cross-audit-ophis-cards`
  (`/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-ophis-cards`)
- **Review host:** `zp-nc71` — the **source host** of the parent audit's relayed snapshot (ophis-gpu),
  with the origin card worktrees readable at `/data3/.../worktrees/D13-*` and `/data1/.../offload/worktrees/D13-*`
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2`; mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`
  (identical pin in all ten cards; private prebuild copy at `review/packages`)
- **Reviewed:** 2026-09-12 00:05–01:00 (+08:00)
- **Verdict:** **`TASK_DONE` — parent card ACCEPTED WITH REVISIONS.** The parent card's transport,
  hash replay, cold-build and fail-closed-kernel-audit claims all reproduce. Five items need revision
  (the B1 closure row, F2's collision count, F7/F13's time scope, F10b's upstream count, F12's
  precision), the F28 mechanism is rejected, and the audit's coverage is strengthened.
  **This is a review, never a Poincaré proof.**

---

## 0. Scope and independence measures actually taken

I did **not** re-run the parent's scripts for its headline numbers. I wrote my own tooling
(`review/tools/`) and ran it against the **transported snapshot** (`audit/ophis/<task>/release`) and,
where possible, against the **origin worktrees** on this host:

1. **Origin-level transport check** (`review/tools/compare_transport.py`): every file in the transported
   tree was compared byte-for-byte with the same relative path in the origin card worktree.
2. **Independent source-hash replay** (`review/tools/replay_hashes.py`): sha256 recomputed from the
   transported bytes **and** from origin, compared with the parent's recorded
   `audit/evidence/<task>/release-hashes.txt`.
3. **Duplicate-declaration inventory** (`review/tools/dup_scan.py`): a namespace-tracking source parser
   over every `.lean` file of every card, grouping fully-qualified declaration names by defining module.
4. **Cold rebuilds** (`review/tools/cold_build_all.sh`): fresh copy of the transported sources, empty
   `.lake/build`, only the pinned package prebuild (my own copy) linked in; `lake build`, full log.
5. **Independent fail-closed census probes** (`review/tools/gen_census2.py`): my own detector over every
   declaration of every card-owned (non-D6-baseline) module; approved cone exactly
   `{propext, Classical.choice, Quot.sound}`; aborts on project axiom / unsafe / `sorryAx` /
   `native_decide` / unapproved axiom / `proof_wanted` / `collectAxioms` failure.
6. **Negative controls**: the same detector run on the cards' documented `False`-axiom modules, expected
   to fail.
7. **Use probes and citation compile checks** (`review/tools/gen_useprobe.py`): existence, type-level and
   value-level occurrence of every claimed closure pair (`ConstantInfo.value? true`,
   `Expr.getUsedConstants`), reverse users, plus `#check @name` / `#print axioms name` on every cited
   declaration.
8. **Toolchain-level tests** for the F27/F28 boundaries (olean rebuilds, `Expr` equality semantics).

No file under `audit/` in the parent worktree and no origin card file was modified.

---

## 1. Verdicts at a glance

| # | claim class (parent card) | verdict | basis |
| --- | --- | --- | --- |
| 1 | Transport of the ten cards | **ACCEPT** | 8/10 byte-identical to origin for *all* files; heat-kernel drift and 360-cards staging-tree exclusions explained |
| 2 | Source-hash replay | **ACCEPT** | recorded hashes match independent recomputation exactly for 9/10 cards; heat-kernel 323/323 match the transported snapshot |
| 3 | Cold-build evidence | **ACCEPT (one scope revision)** | all nine buildable/blocked exit codes reproduced; job counts identical (9339/9337/9003/8999); heat-kernel failure reproduced at the same file:line |
| 4 | Independent fail-closed axiom audit | **ACCEPT (strengthened)** | my censuses cover 971–10436 declarations per card (1.0–8.0× the parent's per-card counts); zero forbidden cones anywhere |
| 5 | Negative controls | **ACCEPT** | detector fails with the expected unapproved cones on the documented `False` axioms |
| 6 | Closure records (4 accepted, 2 rejected) | **REVISE ONE ROW** | SR-4, SR-5, KV-10/NCF-9, and the I4/U7 and U8 rejections stand; the **B1 row's "downstream checked use" cells are reversed** (they are dependencies, not consumers) |
| 7 | Findings F1–F17 | **ACCEPT 13, REVISE 4** | revised: F2 (collision count), F7/F13 (time scope), F10b (upstream count), F12 (precision); the rest confirmed — see §7 |
| 8 | F27 boundary (olean provenance) | **ACCEPT and RESOLVED** | 3/3 manifest source hashes match; fresh oleans differ from all 3 recorded olean hashes, and two independent fresh builds agree byte-for-byte |
| 9 | F28 boundary (`Expr` BEq) | **REJECT as to mechanism** | `BEq Expr` is `Expr.eqv` (alpha-equivalence), not a hash comparison; the practical advice stands |
| 10 | Four "undetermined" items | **3 of 4 RESOLVED** | topping logs, upstream ev-logs, 360-cards staging trees and `/data3` baselines are readable from this host |

---

## 2. Transport fidelity and source hashes

`review/transport/transport-compare.json` (all files under the transported tree vs origin):

| card | transported files | origin files | hash mismatches | transported-only | origin-only |
| --- | --- | --- | --- | --- | --- |
| D13-integrated-kernel-audit | 1234 | 1234 | 0 | 0 | 0 |
| D13-critical-path-review | 817 | 817 | 0 | 0 | 0 |
| D13-upstream-adapter-audit | 645 | 645 | 0 | 0 | 0 |
| D13-morgan-tian-adapter-plan | 418 | 418 | 0 | 0 | 0 |
| D13-topping-ricci-adapter-plan | 403 | 403 | 0 | 0 | 0 |
| D13-deturck-shorttime-producer | 389 | 389 | 0 | 0 | 0 |
| D13-vankampen-recognition | 169 | 169 | 0 | 0 | 0 |
| D13-manifold-ibp-volume-form | 172 | 172 | 0 | 0 | 0 |
| D13-heatkernel-bridge-d10-d7 | 374 | 608 | **6** | 1 (`probe-spec.json`) | 235 |
| D13-cross-audit-360-cards | 113 | 4898 | 0 | 0 | 4785 (`audit360/` 4712 + `a3d2d3/` 73) |

The eight exact cards, and every transported file of the other two, are byte-identical to origin. The
heat-kernel differences are **time drift, not transport loss**: the origin was still being written by a
post-card invocation (twelfth invocation, checkpoint 23:54) and changed
`ConjugateScalarCurvature.lean` (23:13 → 23:18), `All.lean`, `AxiomAudit.lean`, the card `.md`/`.json`
(19:18 → 23:30), `checkpoint.json`, and added `FiniteErgodicity.lean` and other files, plus 235
`logs/` files. The parent transported the 23:11–23:13 state, which is exactly the state it reports on.

Hash replay (`review/evidence/hash-replay-independent.json`): for the nine non-heat-kernel cards the
parent's `release-hashes.txt` entries match **both** the transported and the origin recomputation with
zero mismatches (120–462 files per card). For heat-kernel, **323/323 recorded entries match the
transported snapshot**, while 6 origin files now differ — consistent with the drift above.

---

## 3. Cold-build evidence

`review/logs/<task>-cold-build.log`; fresh sources + empty `.lake/build`; shared pinned prebuild only.

| card | `.lean` files | my exit | jobs (my / parent) | parent claim | reproduced |
| --- | --- | --- | --- | --- | --- |
| D13-integrated-kernel-audit | 456 | 0 | 9339 / 9339 | 0 | yes |
| D13-critical-path-review | 454 | 0 | 9337 / 9337 | 0 | yes |
| D13-upstream-adapter-audit | 315 | 0 | 9198 / — | 0 | yes |
| D13-morgan-tian-adapter-plan | 322 | 0 | 9205 / — | 0 | yes |
| D13-topping-ricci-adapter-plan | 322 | 0 | 9205 / — | 0 | yes |
| D13-manifold-ibp-volume-form | 121 | 0 | 9003 / 9003 | 0 | yes |
| D13-deturck-shorttime-producer | 339 | 0 | 9222 / — | 0 | yes |
| D13-vankampen-recognition | 116 | 0 | 8999 / — | 0 | yes |
| D13-heatkernel-bridge-d10-d7 | 320 | **1** | — | 1 | yes |
| D13-cross-audit-360-cards | 63 | 0 | 8946 / n/a | n/a | n/a |

The heat-kernel failure reproduces exactly:

```text
error: Poincare/D13/HeatKernelBridge/ConjugateScalarCurvature.lean:497:8: invalid `▸` notation,
       expected result type of cast is Tendsto (fun t => ∑ x, finiteConjKernelWith G R t₀ x y t) ...
error: build failed                                       (COLD_BUILD_EXIT 1)
```

**Scope revision (R2).** The origin tree no longer has this defect. A frozen copy of the origin release
tree taken at 00:25 (325 `.lean` files,
`ConjugateScalarCurvature.lean` sha256 `8b2451ef…`) **cold-builds successfully (9208 jobs, exit 0)** in
`review/logs/ORIGIN-heatkernel-cold-build.log`, and the origin card was rewritten at 23:30. The parent's
F7/F13 must therefore be read as *"the relayed 23:13 snapshot did not build"*. The parent's own caveat
("the ophis queue still lists the task as running, consistent with a post-card invocation") anticipates
this, but the finding text says "the delivered tree does not build" without the time qualifier.

The parent's queue table was also re-verified against the relayed `audit-remote/ophis_queue.json`:
all ten statuses match (heat-kernel `running`, 360-cards `paused`, this audit `queued`).

---

## 4. Independent fail-closed axiom audit

My censuses import **every card-owned module** (files not in the D6 baseline) and audit every constant
owned by them. They are a strict superset of the parent's per-card clean-probe sets, and they exclude
the duplicate-declaration modules, which cannot be imported with the rest (see §7, F2/R3); those are
audited in dedicated isolated probes (`*-census-isolated`).

| card | census decls / theorems | isolated decls | project axioms | unsafe | sorry cones | native_decide | unapproved | VERDICT |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| D13-integrated-kernel-audit | 10427 / 6579 | 326 | 0 | 0 | 0 | 0 | 0 | PASS |
| D13-critical-path-review | 10436 / 6582 | 326 | 0 | 0 | 0 | 0 | 0 | PASS |
| D13-deturck-shorttime-producer | 7336 / 4347 | 326 | 0 | 0 | 0 | 0 | 0 | PASS |
| D13-heatkernel-bridge-d10-d7 | 6803 / 3976 | 326 | 0 | 0 | 0 | 0 | 0 | PASS |
| D13-topping-ricci-adapter-plan | 6784 / 3940 | 326 | 0 | 0 | 0 | 0 | 0 | PASS |
| D13-morgan-tian-adapter-plan | 6732 / 3922 | 326 | 0 | 0 | 0 | 0 | 0 | PASS |
| D13-upstream-adapter-audit | 6669 / 3875 | 326 | 0 | 0 | 0 | 0 | 0 | PASS |
| D13-vankampen-recognition | 2597 / 1433 | — | 0 | 0 | 0 | 0 | 0 | PASS |
| D13-manifold-ibp-volume-form | 971 / 724 | — | 0 | 0 | 0 | 0 | 0 | PASS |
| D13-cross-audit-360-cards | no card-owned modules | — | — | — | — | — | — | n/a |

Every declaration's full cone was printed (`XDECL` lines). Across all censuses the observed cones are
exactly `{}` (3425 declarations), `{propext}` (2980), `{Classical.choice}` (21), `{Quot.sound}` (28),
`{propext, Quot.sound}` (501) and `{propext, Classical.choice, Quot.sound}` (54182) — all subsets of the
approved set, with no `sorryAx`, `native_decide`/`ofReduceBool`, project axiom or unapproved axiom. The
parent's per-card counts (2099, 971, 1552, 1743, 1971, 2073, 839, 1271, 8161/4343) are **lower bounds**,
because the parent imported only D13-namespace roots while I import every card-owned module; all
additional declarations are equally clean.

Cross-check of the parent's integrated numbers: I re-ran the parent's own `FullClosureProbe.lean`
unmodified in my rebuilt tree and obtained **exactly 237 modules / 8161 declarations / 5301 theorems /
20 partial definitions / 0 of everything / PASS** (`review/logs/rerun-parent-fullclosure.log`),
matching the parent's log line for line. The 279-module source-level import closure differs only by
**42 reachable modules that declare nothing** (audit drivers and umbrella modules such as
`Audit.GeometryAudit`, `Poincare.Longrun.CurvatureODE`, `Poincare.D12.VolumeIBP`).

---

## 5. Negative controls

The cards' documented `False`-axiom modules were excluded from the clean censuses and fed to the same
detector separately (`*‑negcontrol.log`). The detector fired every time and aborted elaboration:

| card | negative-control modules | detector result |
| --- | --- | --- |
| D13-integrated-kernel-audit | `Poincare.D12.TriangulationTopology.NegControl.NegControl`, `Poincare.D12.VolumeIBP.Audit` | `VERDICT FAIL`, exit ≠ 0 |
| D13-critical-path-review | the two above + `Poincare.D13.CriticalPathReview.NegControl` | `VERDICT FAIL`, exit ≠ 0 |
| D13-manifold-ibp-volume-form | `Poincare.D12.VolumeIBP.Audit`, `Poincare.D13.Audit` | `VERDICT FAIL`, 2 unapproved cones, exit ≠ 0 |
| the other seven cards | none declared in their trees | n/a |

This reproduces the parent's negative-control claim on an independently written detector.

---

## 6. Cited declarations: source hashes and semantic class

Every declaration cited by the parent card's closure table, its findings, and its cross-findings was
`#check`ed and `#print axioms`ed in the rebuilt environments (`review/probes/<task>/Cited.lean`,
`review/evidence/cited-declarations.json`). All resolve; the only unresolved "identifier" is the
namespace name `Poincare.D13.CriticalPathReview.NegControl` (not a constant). Every cone is a subset of
`{propext, Classical.choice, Quot.sound}`. File hashes are sha256 of the transported snapshot file.

| declaration | file | sha256 (16) | class | cone |
| --- | --- | --- | --- | --- |
| `…VanKampenRecognition.simplyConnectedPieces_of_v2` | `Poincare/D13/VanKampenRecognition/SR4Closure.lean` | e8162d1156d5b5c0 | unconditional theorem about a V2 decomposition datum | approved |
| `…ConnectedSumDecomposition.mkV2Complete` | same | e8162d1156d5b5c0 | constructor (V2 data → D7 certificate) | approved |
| `…RemainingRecognitionHypothesesV4.toRemainingV3` | same | e8162d1156d5b5c0 | implication between hypothesis bundles | approved |
| `…SurgeryRecognition.ConnectedSumDecomposition.mkV2` | `Poincare/D12/SurgeryRecognition/SphereOfSpheres.lean` | cbcca916042bb1e3 | constructor, conditional on the simply-connectedness hypothesis | approved |
| `…stage6Target_of_v4hypotheses_from_certificates` | `…/VanKampenRecognition/SR4Closure.lean` | e8162d1156d5b5c0 | conditional Stage6 assembly (extinction + canonical + V4 inputs) | approved |
| `…CriticalPathReview.b1_dimension_one` | `Poincare/D13/CriticalPathReview/B1DimensionOne.lean` | 6609efdb26f17cf6 | model/partial-scope theorem, **dimension 1 only** | approved |
| `…CriticalPathReview.kernelTangent_scalarField_iff` | same | 6609efdb26f17cf6 | **input** of `b1_dimension_one` (not a consumer) | approved |
| `…CriticalPathReview.scalar_forward_invariance` | `…/CriticalPathReview/ScalarViability.lean` | e73fbeb8a3c11291 | **input** of `b1_dimension_one` (not a consumer) | approved |
| `…SurgeryRecognition.iteratedSphereSum_homeo_sphere` | `Poincare/D12/SurgeryRecognition/SphereOfSpheres.lean` | cbcca916042bb1e3 | theorem, 0 retained consumers | approved |
| `…MorganTianAdapter.BishopGromov.flatModel_ballVolumeComparison` | `Poincare/D13/MorganTianAdapter/BishopGromov.lean` | 42d83791a5eef953 | **flat ℝ³ model only** | approved |
| `…BishopGromov.flatModel_kappaNoncollapsingCertificate` | same | 42d83791a5eef953 | certificate constructor, flat model only | approved |
| `…ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional` | `Poincare/D13/ManifoldIBP/PartialChartModelPOU.lean` | d8815e5da15ee669 | **model** theorem (explicit half-space atlas, arbitrary `ChartMetric`) | approved |
| `…halfSpaceAtlas_dirichletEnergy`, `…greenIdentity` | same | d8815e5da15ee669 | genuine consumers (`value=true`) | approved |
| `…halfSpaceAtlas_laplacianIntegralZero`, `…integrable_dirichlet` | same | d8815e5da15ee669 | claimed consumers, **`value=false`** | approved |
| `…DeturckProducer.PicardModel.of_metric` | `Poincare/D13/DeturckProducer/PicardModel.lean` | 61a2b0316ce8447e | constructor from `S, F, u₀, DuhamelSetup` (+ symbol certificate) | approved |
| `…RicciDeTurckPicardModel.existsUnique_mildSolution_of_model` | same | 61a2b0316ce8447e | delegation to `P.duhamel` | approved |
| `…PicardModel.MildClassicalOutput` | same | 61a2b0316ce8447e | hypothesis structure ≡ `DeTurckShortTimeExistence` unpacked | approved |
| `…deTurckShortTimeExistence_of_classicalOutput` | same | 61a2b0316ce8447e | `(h : MildClassicalOutput P) : DeTurckShortTimeExistence P` | approved |
| `…PicardModel.ricciFlow_of_model` | same | 61a2b0316ce8447e | conditional end-to-end assembly | approved |
| `…DeturckProducer.FlatInstance.flatPicardModel` | `…/DeturckProducer/FlatInstance.lean` | 721a87cf1f04709e | flat instance | approved |
| `RicciDeTurckPicardModel.strictParabolic` (field projector) | `…/PicardModel.lean` | 61a2b0316ce8447e | certificate field, **0 consumers** | approved |
| `Poincare.D7.HeatKernel.HeatKernelData` | `Poincare/D7/HeatKernel/Basic.lean` | b713a85460e8160e | legacy structure | approved |
| `Poincare.D13.HeatKernelBridge.HeatKernelDataV1` | `…/HeatKernelBridge/Basic.lean` | 96328402d9633274 | corrected-domain structure, 89 users | approved |
| `…HeatKernelBridge.exists_v1_iff_exists_legacy` | `…/HeatKernelBridge/CompactUpgrade.lean` | 4f514a48df413fa9 | equivalence, **0 direct users** | approved |
| `Poincare.D7.HeatKernel.heatKernelExistenceStatement_iff_v1` | `Poincare/D7/HeatKernel/V1Interface.lean` | a16e54a15c859836 | statement equivalence | approved |
| `…not_heatKernelExistenceStatementV1_of_legacy_refutation` | `Poincare/D7/HeatKernel/StatementStatus.lean` | dc49b11a9f5f50d8 | refutation transport | approved |
| `Poincare.D7.ConjugateHeat.ConjugateHeatData` | `Poincare/D7/ConjugateHeat/Basic.lean` **and** `Poincare/D7/Monotonicity/ConjugateHeatCertificate.lean` | — / d96dcc573653137a | **duplicated declaration** (F2) | approved |
| `Poincare.D12.HeatSemigroup.heatOperatorBCF_comp` | `…/HeatSemigroup/Semigroup.lean` | 9ae5669795243d5d | theorem, **not** used by the claimed consumer | approved |
| `…heatOperator_gaussianKernel_L1_tendsto_seq` | `…/HeatSemigroup/StrongContinuityL1.lean` | 03eac2364b862374 | claimed consumer, `value=false` | approved |
| `Poincare.D12.ConnectionCurvature.leviCivitaExists` | `…/ConnectionCurvature/MilnorLeviCivita.lean` | b682206dbae42a57 | theorem, only audit-wrapper user | approved |
| `Poincare.D12.EntropyVariation.fDerivativeStatement_of_corrected_of_idempotent` | `…/EntropyVariation/EntropyDerivative.lean` | d677c5d2d6406003 | theorem, only audit-wrapper user | approved |
| `Poincare.D12.SurgeryRecognition.finiteFreeOrbit_isQuotientCoveringMap` | `…/SurgeryRecognition/CoveringRecognition.lean` | 86b419978ae26cc1 | theorem, 2 users, both V3/space-form route | approved |

---

## 7. Findings on the parent card, one by one

### Accepted as stated

* **F1 — coverage over-claim.** Reproduced exactly (237/8161/5301, PASS). Refinement: 42 of the 279
  source-reachable tree modules own no declarations, so "219 modules outside the closure" includes
  declaration-free umbrella/audit modules; the number of declaration-owning modules outside the closure
  is smaller (≈106 by my parser, an undercount because it ignores `instance`). The over-claim stands.
* **F3 — manifold-IBP headline scope.** Confirmed: the D6 accepted ledger still has `U7` (and `I4`)
  `status: open` (`/data3/.../D6_weekly_release/manifest/blockers.json`), and no mathlib-manifold
  instantiation exists in the card's tree.
* **F4 — manifold-IBP accounting.** Confirmed by my independent pair probe:
  `halfSpaceAtlas_weightedIBP_unconditional → halfSpaceAtlas_laplacianIntegralZero` **value=false** and
  `→ halfSpaceAtlas_integrable_dirichlet` **value=false**, while `→ dirichletEnergy` and
  `→ greenIdentity` are `value=true`.
* **F5 — DeTurck certificate disconnect.** Confirmed at source and by probe: `existsUnique_mildSolution_of_model`
  is `P.duhamel.existsUnique_mildSolution`; the `strictParabolic` projector has **0 direct users**.
* **F6 — DeTurck wording vs shape.** Confirmed: `MildClassicalOutput` has exactly the fields of
  `DeTurckShortTimeExistence`, and `deTurckShortTimeExistence_of_classicalOutput` has
  `type=true, value=true` for the constructor occurrence — a repackaging.
* **F7 — delivered tree vs card.** Confirmed for the snapshot: `ConjugateScalarCurvature.lean`
  (mtime 23:13, snapshot sha256 `f06c6e46…`) is absent from the transported card, its manifest and its
  audit list. (See R2 for the time scope.)
* **F8 — unformalized dissipativity claim.** Confirmed: `LaplacianSymmetryRefutation.lean` contains
  11 declarations and only `not_forall_laplacian_symmetric_flatLine`; no dissipativity refutation.
* **F9 — unbacked mapping row.** Confirmed: the Topping/Evans mapping row claims "identity via the Evans
  theorem (rfl-transport)" for D12 `gaussianReducedVolume_eq_one`, but there are **0**
  `gaussianReducedVolume` occurrences under `release/Poincare/D13`.
* **F10a — dangling section reference.** Confirmed: the Morgan–Tian card cites "§6.3" but its section 6
  ("Compile evidence") has no subsection.
* **F10c — credited D12 modules absent.** Confirmed: the topping tree contains only
  `Poincare/D12/{EntropyVariation,HeatDomain,KappaVariational}`; `Poincare.D12.HeatSemigroup` and
  `Poincare.D12.ParabolicLocal` are absent although the mapping table credits them.
* **F10d — undetermined from the relay.** The relay indeed contains no build logs. **Partly resolved here**
  (see §8b): the topping card's job-count, per-file and negative-control claims are all backed by origin
  artifacts; the upstream card's six per-file logs exist and are clean, but its 8909/8960 `lake build`
  job counts still have no log at origin, so that parent caveat stands.
* **F11 — 360-cards internal contradictions.** Confirmed: ten consecutive contradictory "Round-11
  headline" paragraphs (four with 304 cones / 8-of-9 / `TASK_BLOCKED`, six with 324 cones / nine-of-nine /
  `TASK_DONE`), and the JSON reuses `F27` and `F28` for two different findings each (round-12
  definition-listing/scope-limit findings vs round-13 olean-provenance/instrument findings).
* **F14/F15/F16/F17 — verified positives.** SR-4, SR-5 and the flat-model KV-10/NCF-9 closure satisfy
  constructor + checked use + rebuild; the B1 dimension-1 constructor is kernel-clean and rebuilds but
  has **no** downstream consumer (R1). The heat-kernel precision point also holds:
  `exists_v1_iff_exists_legacy` has **0** direct users (my probe), while `HeatKernelDataV1` has **89**
  direct users in my (broader) environment. The remaining cross-findings I spot-checked also hold:
  `sturm_comparison` has 0 occurrences in the integrated tree; `leviCivitaExists` and
  `fDerivativeStatement_of_corrected_of_idempotent` have only audit-wrapper users
  (`Poincare.D13.IntegratedAudit.Nonvacuity.d13_consumer_*`), which confirms the producer sense of the
  360-card's F20; and `finiteFreeOrbit_isQuotientCoveringMap`'s only two users are on the V3/space-form
  route (F26).

### To be revised

* **R1 (parent's B1 closure row) — the "downstream checked use" is reversed.** The parent's
  cross-audit card records for `D13-critical-path-review`/B1:
  `kernelTangent_scalarField_iff -> b1_dimension_one (value=true)` and
  `scalar_forward_invariance -> b1_dimension_one (value=true)`. The parent's **own** probe log shows the
  direction: `D13XPAIR kernelTangent_scalarField_iff b1_dimension_one value=true` means
  **`b1_dimension_one`'s value uses the other theorem**, i.e. these are *upstream inputs* of the
  constructor, not consumers of it. The same log records `D13XUSE b1_dimension_one direct_users 0`.
  My independent probe confirms: constructor→`kernelTangent_scalarField_iff` `value=false`,
  constructor→`scalar_forward_invariance` `value=false`, reverse users of `b1_dimension_one` = **0**.
  Under the task's own rule (constructor + downstream checked use + independent rebuild), the B1 record
  fails the second component; it should read "constructor exists, rebuilds and is kernel-clean; **no
  downstream consumer**; dimension-1 scope only — B1 not closed". The *mathematical* verdict (partial
  scope, B1 open) is unchanged.
* **R2 (F7/F13 time scope).** As of this review the origin heat-kernel tree **does** cold-build
  (exit 0, 9208 jobs; frozen 00:25 copy) and the card was updated at 23:30 with new material
  (`FiniteErgodicity.lean` etc.). The finding should be titled "the relayed 23:13 snapshot did not
  cold-build", not "the delivered tree does not build".
* **R3 (F2 undercounts the collision problem).** The parent reports **one** in-package duplicate
  (`Poincare.D7.ConjugateHeat.ConjugateHeatData`). My namespace-tracking inventory finds **three**
  duplicate groups in every full tree — `ConjugateHeatData` (29 names), `BochnerCertificate` (20 names,
  `Poincare.D7.Bochner.Basic` vs `Poincare.D7.Monotonicity.BochnerCertificate`), `GradientCertificate`
  (10 names, `Poincare.D7.Bochner.GradientEstimate` vs `Poincare.D7.Monotonicity.BochnerGradientEstimate`)
  — i.e. **59 duplicated qualified names**, plus a fourth group in the heat-kernel tree
  (`Poincare.D11.HeatKernelBridge.AxiomAudit` vs `Poincare.D13.HeatKernelBridge.AxiomAudit`, 2 names).
  The parent's conclusion ("the 456-module package is not importable in one environment") is correct and
  understated; `lake build` and the per-file gate cannot see it because no single file imports both
  sides, and the redundant copies are importable only in isolation (my `*-census-isolated` probes cover
  them: 326 declarations each, all clean).
* **R4 (F28 mechanism).** The 360-card's F28 asserts that "`Expr`'s `BEq` instance in
  `leanprover/lean4:v4.34.0-rc2` is hash-based (a == b true for structurally different sums with equal
  hash)". The toolchain source (`Lean/Expr.lean:811`) defines `instance : BEq Expr where beq := Expr.eqv`,
  documented as alpha-equivalence; `Expr.equal` is the binder-name/annotation-sensitive comparison. My
  empirical checks: `lam x … == lam y …` is `true`, `Expr.equal` is `false` (same for binder-info
  variants); different arguments/heads/projections compare `false`; `mdata` is not ignored. So the
  observed screen false positives are **alpha-equivalence**, not hash collisions. The practical
  recommendation ("use `Expr.equal` for syntactic comparisons") remains correct; the mechanism and the
  phrase "hash-based" are rejected. The parent card carried F28 into its undetermined list without
  challenging the mechanism.
* **R5 (F10b count).** The parent writes "10 transcribed Topping Core theorems vs 9 upstream theorem
  declarations". Upstream `Topping/Topping/MaximumPrinciple/Core.lean` has **8** `theorem` declarations;
  the local `Core.lean` has 10, of which 8 are verbatim transcriptions and 2 are local additions
  (`isLocalMaxOn_of_isMaxOn`, `nonpos_of_forall_isMax_time_deriv_le_of_pos'`) — and the card itself
  explicitly labels the latter as local. The direction of the finding (the "10 transcribed" wording
  over-states the upstream count) is right; both numbers need correction.
* **R6 (F12 counting).** The parent says the critical-path card claims "two" in-glob `False` axioms
  while three exist. There are indeed three in the `Poincaré.+` glob
  (`D12.TriangulationTopology.NegControl`, `D12.VolumeIBP.Audit`, `D13.CriticalPathReview.NegControl`),
  but the card's text says "the two **pre-existing** negative-control modules", and it acknowledges its
  own third one separately. This is defensible wording, not an error; downgrade F12's third-axiom item
  to a precision note. The other F12 items stand: the card cites 9329 jobs where its repair log and my
  rebuild show **9337**, and its `authored-hashes.txt` entry is stale.

### Rejected

* **F28's stated mechanism** (see R4). Nothing else in the parent card was rejected: every other
  load-bearing claim I could test reproduced.

### New findings from this review

* **N1 — collision inventory** (extends F2/R3): 3 duplicate groups / 59 names in every full tree,
  a 4th group (2 names) in heat-kernel; isolated probes cover the redundant copies.
* **N2 — B1 closure direction** (R1): the strongest substantive defect found in the parent card.
* **N3 — F27 confirmed with stronger evidence** (below).
* **N4 — heat-kernel origin drift** (R2): the audited snapshot is a moving target; the parent's F13 is
  snapshot-scoped.
* **N5 — undetermined list reduced**: the topping build/per-file/negative-control artifacts and the
  360-cards staging trees exist on the source host (topping claims verified; upstream per-file logs
  verified but its job counts still unbacked); `/data3` baselines exist here (the D6 `U7` open status
  and the D12-semantic-ledger 37/37 source hashes were verified directly).
* **N6 — coverage strengthened**: the parent's per-card declaration counts are lower bounds; my
  superset censuses (971–10436 declarations per card) are all kernel-clean.

---

## 8. F27/F28 boundaries

**F27 (olean provenance) — CONFIRMED and RESOLVED.** From
`D12-semantic-ledger/manifest/d12-rebuild-manifest.json` I took three modules and compared:

| module | manifest source sha256 | actual source sha256 | manifest olean sha256 | fresh olean sha256 |
| --- | --- | --- | --- | --- |
| `Poincare.D7.HeatKernel.Basic` | b713a854… | b713a854… | 8b3da2a8… | **27ab35b4…** |
| `Poincare.D7.HeatKernel.Grid` | db7c1cdf… | db7c1cdf… | 02c11270… | **b816a89e…** |
| `Poincare.D7.HeatKernel.Content` | d9070f3f… | d9070f3f… | dbce028f… | **af5c82cf…** |

All three source hashes match; all three fresh oleans differ from the recorded ones. Crucially, the
`Basic` olean is **byte-identical across two independent fresh builds in two different build trees**
(deturck-snapshot tree and integrated tree, `27ab35b4…`), so olean bytes are reproducible here and the
manifest's values cannot have come from the recorded source under the pinned toolchain — exactly the
card's F27 claim ("the manifest records reused oleans from a build cache that no longer exists"). The
manifest's `attempts ∈ {1,2,3,4}`, `seconds: 0.0` fields are consistent with that story.

**F28 (`Expr` BEq) — REJECTED as to mechanism.** `BEq Expr` is `Expr.eqv`, i.e. alpha-equivalence
(binder names and binder annotations ignored); it is *not* a hash comparison, and I found no evidence of
hash-collision acceptance. The observed false positives are explained by binder-name/annotation
insensitivity. `Expr.equal` remains the right tool for syntactic comparison. The parent card's own
"undetermined" entry for F28 should not have treated the mechanism as merely unverified: it is
refutable from the toolchain source and from three lines of Lean.

---

## 8b. Resolution of the parent's four "undetermined" items

The parent could not resolve these from its relay; I am on the source host and checked them directly.

1. **Topping build logs, per-file exits, negative control** — **RESOLVED, card claims supported.**
   `tmp/build-All.log` ends `Build completed successfully (8911 jobs)`, `tmp/build-Audit.log`
   `(8912 jobs)`, matching the card's exit-0 claims; `tmp/lean-{Core,Slab,Scalar,ShortTime,Volume,Audit}.log`
   exist with 0 errors (6/6); `tmp/negcontrol.log` records the expected fail-closed rejection
   (`dependentOnFakeAxiom depends on unapproved axioms [d13AuditFakeAxiom]; detected unapproved axioms`).
   The `/tmp/d13neg/NegativeAudit.lean` file itself was transient, but its log survives.
2. **Upstream-adapter 8909/8960 job counts, `/tmp/d13neg` identity** — **PARTLY RESOLVED.**
   The six per-file logs `longrun/ev-logs/lean-{All,Audit,EvansHeat,EvansParametric,KleinerLottKappa,MorganTianShrinker}.log`
   exist and contain 0 errors. No `lake build` log with the 8909 or 8960 job counts exists anywhere in
   the origin worktree (`grep -rl "8909\|8960"` finds nothing), so those two counts remain
   **unbacked by any artifact** even at origin. A `negcontrol/NegativeControl.lean` exists in the
   worktree; the exact `/tmp/d13neg` file is gone.
3. **360-cards staging trees (`audit360/`, `a3d2d3/`)** — **PARTLY RESOLVED.** Both trees exist at
   origin (4712 and 73 files). I resolved the load-bearing items that the parent listed: F27 (olean
   provenance, confirmed with three modules), F28 (mechanism, refuted), F11 (contradictory headlines and
   duplicated F27/F28 ids, confirmed) and F26 (`finiteFreeOrbit_isQuotientCoveringMap` users, confirmed:
   exactly two, both on the V3/space-form route, none through `mkV2`/`stage6Target_of_v2hypotheses`).
   The remaining 360-card findings (F3, F6, F9, F10, F12b/c, F13, F18–F25) are audit-internal staging
   items and were not exhaustively re-derived here.
4. **Byte-identity of the `/data3` accepted baselines** — **RESOLVED for the load-bearing manifest.**
   `/data3` and `/data1` paths are readable from this host. The D12-semantic-ledger manifest's **37/37
   snapshot source hashes** match the actual sources in
   `/data1/.../D11-bochner-manifold/release` (recomputed here, 0 mismatches), which both confirms the
   360-card's "sources 37/37 correct" claim and isolates F27 to the olean field. The D6 accepted
   ledger's `U7`/`I4` `status: open` was also read directly from
   `/data3/.../D6_weekly_release/manifest/blockers.json` (basis of F3).

---

## 9. Honest boundaries of this review

* This review certifies **transport, hashes, compilation, kernel cones, citation existence, and
  consumer direction**. It does **not** certify mathematical meaning: a kernel-clean theorem about a
  flat model, an abstract atlas, a finite matrix or a hypothesis bundle is not a theorem about Ricci
  flow on closed 3-manifolds, and no card here claims one.
* I did not re-run the parent's per-file gate for every card; instead I cold-built the trees (a stronger
  whole-tree property) and reproduced the one failing file directly. File counts (456/454/315/322/322/121/339/116/320/63)
  match the parent exactly.
* I did not independently verify every staging-tree item behind the 360-card findings F3, F6, F9, F10,
  F12b/c, F13, F18–F26; I resolved F11 (headlines/duplicate ids), F27 and F28 from the origin tree, and
  spot-checked F26 (`finiteFreeOrbit_isQuotientCoveringMap` has exactly 2 users, both on the
  V3/space-form route, none through `mkV2`/`stage6Target_of_v2hypotheses`). Those residual items remain
  undetermined from this review.
* I did not re-verify all 30 integrated blocker pairs; I spot-checked four load-bearing ones
  (`heatOperatorBCF_comp` `value=false`; `leviCivitaExists` and
  `fDerivativeStatement_of_corrected_of_idempotent` each have exactly one *audit-wrapper* user;
  `finiteFreeOrbit_isQuotientCoveringMap` as above) and they agree with the parent's caveats. Note the
  parent reported 0 direct users for `leviCivitaExists` and
  `fDerivativeStatement_of_corrected_of_idempotent`; my broader scan finds one audit-nonvacuity wrapper
  each (`Poincare.D13.IntegratedAudit.Nonvacuity.d13_consumer_*`), so "0 *mathematical* consumers" is
  the accurate form.
* This review introduces **no** `sorry`, `axiom`, `admit`, `unsafe`, `native_decide` or
  `proof_wanted`. Its censuses exclude the cards' documented negative controls and audit them
  separately, where the detector must fail (and does).
* No audited file was modified; the review's own artifacts live under `review/`.

---

## 10. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/SEMREV-D13-cross-audit-ophis

python3 review/tools/compare_transport.py review/transport/transport-compare.json
python3 review/tools/replay_hashes.py                       # review/evidence/hash-replay-independent.json
python3 review/tools/dup_scan.py                            # review/evidence/duplicate-names.json
bash    review/tools/cold_build_all.sh <task> ...           # review/logs/<task>-cold-build.log
python3 review/tools/gen_census2.py
python3 review/tools/gen_useprobe.py
bash    review/tools/run_probes.sh <task> ...               # census, isolated, negcontrol, useprobe, cited
```

Key artifacts: `review/transport/transport-compare.json`, `review/evidence/{hash-replay-independent,duplicate-names,cited-declarations}.json`,
`review/logs/*-cold-build.log`, `review/logs/*-census.log`, `review/logs/*-negcontrol.log`,
`review/logs/*-useprobe.log`, `review/logs/*-cited.log`, `checkpoint.json`.

---

## 11. Repair addendum — release-package transport fix and dispatcher-gate replay (2026-09-12 01:00–01:12 +08:00)

**Symptom.** The dispatcher's gate run at `2026-09-12T00:38:12+0800` failed in `lake build` with
`error: RPC failed; curl 16 … mathlib: cloning … fatal: expected flush after ref listing` — Lake tried
to fetch mathlib from GitHub, which this host cannot reach. The release sources were never implicated:
the package fingerprint recorded by the failed gate, `75e8231d…`, is byte-identical to the one recorded
by the **passing** parent gate (`longrun/state/D13-cross-audit-ophis-cards/gate.json`, 63/63 files
exit 0). This is a repair of the transported build environment, not of any review conclusion.

**Root cause (transport, not source).** This worktree's `release/.lake/packages` arrived as an **empty
directory** (preserved at `release/.lake/packages.transport-failure-20260912004503`, 0 entries), so Lake
attempted a network fetch. The parent worktree keeps the same field as a symlink to the shared pinned
prebuild (`…/poincare-lab/.lake/packages`), which holds all nine manifest packages at exactly the
revisions pinned in `release/lake-manifest.json` — mathlib `7974e751…`, batteries `4cac2177…`, aesop
`18889deb…`, Qq `507746ab…`, proofwidgets `a8acbfd8…`, importGraph `1681d78d…`, LeanSearchClient
`ba67e212…`, Cli `ab3a82db…`, plausible `d9598f07…` — with mathlib's prebuilt oleans present.

**Repair.** The empty directory was preserved and `release/.lake/packages` was re-pointed at that same
shared prebuild (the fleet's `longrun/repair_cache.py` performs exactly this move; filesystem times
place it at 00:45), mirroring the parent. **No file of the audited release package was created, deleted
or edited:** the dispatcher's source fingerprint is `75e8231d…` before and after every build below, and
still equals the parent gate's fingerprint.

**Fresh compilation evidence (both gate stages, from this worktree).**
* Full build with an empty `release/.lake/build`: `lake build` → **exit 0, 8946 jobs, 73.7 s**
  (`review/logs/repair-release-cold-build.log`, sha256 `d488e67e…`). The D6 audit compiled into the
  release reports `D6AUDIT\tVERDICT\tPASS — no sorryAx, no project axiom, no unsafe, no native_decide,
  no unapproved axiom, no proof_wanted`.
* Dispatcher-gate replica (`review/tools/gate_replay.py`, a faithful copy of
  `longrun/bin/dispatch_loop.py:compile_gate`, including its exact file walk, cwd, environment,
  timeout and 4-worker per-file stage): `lake build` **exit 0, 8946 jobs**
  (`review/logs/gate-replay-build.log`, sha256 `0d5d124e…`), then `lake env lean <relative>` for every
  authored file: **63/63 exit 0** (histogram `{"0": 63}`), with `fingerprint_before ==
  fingerprint_after`. Summary: `review/logs/gate-replication.json` (sha256 `204b07ac…`),
  `gate_ok_replicated: true`.

**Residual infrastructure blocker (bookkeeping only; no mathematical content).** The dispatcher caches
gate results: `compile_gate` returns the stored `gate.json` unchanged whenever `version` and
`source_sha256` match, regardless of `ok` (`bin/dispatch_loop.py:147–150`). Because this review
correctly leaves the audited release unmodified, the fingerprint is unchanged, so the dispatcher would
return the stale 00:38 transport failure **without re-running `lake build`**. This worker cannot
invalidate the entry: a write/rename probe under `longrun/state/SEMREV-D13-cross-audit-ophis/` returned
`Permission denied` (path outside the sandbox workspace), and the escalation to full access failed
closed (`sandbox escalation … requires approval, but no approval channel is available`). **Operator
action (one line):** `rm longrun/state/SEMREV-D13-cross-audit-ophis/gate.json` (or rename it) — the
next dispatcher tick re-runs the gate unchanged and it passes on the evidence above. Deliberately
**not** done: editing `release/` (e.g. a comment in `lakefile.toml`) purely to force a fingerprint
cache-miss — that would alter the artifact under review to satisfy the gate.

### 11.1 Repair attempt 2 — re-verification from the release package and cache clearance (2026-09-12 01:05–01:12 +08:00)

The second repair round re-ran the gate from the **release package** (`release/`, never the worktree
root) and re-derived every quantity above from the live filesystem:

* `release/.lake/packages` is still the repaired symlink to the shared pinned prebuild; the 0-entry
  `release/.lake/packages.transport-failure-20260912004503` directory is preserved untouched.
* Independent recomputation of `dispatch_loop.source_hash('release')`: **63 Lean files**, fingerprint
  `75e8231d2345c5ca2e2cbdce8b8c80d47d1648e2e26b4843bd09d48bfed88012` — byte-identical to both the stale
  gate entry and the **passing** parent gate
  (`longrun/state/D13-cross-audit-ophis-cards/gate.json`: `ok: true`, `build_exit: 0`, 63/63 files
  exit 0). The same sources therefore already passed a dispatcher gate; only the transported package
  cache differed.
* Fresh dispatcher-gate replica, cwd `…/SEMREV-D13-cross-audit-ophis/release`, checked at
  `2026-09-12T01:09:00+0800`: `lake build` **exit 0, 8946 jobs** (`review/logs/gate-replay-build.log`,
  sha256 `0d5d124e585a192353e23b3e6bd3cb9d645b739384447da5ba342167241fb609`), then `lake env lean
  <relative>` for all 63 authored files: **63/63 exit 0**, `fingerprint_before == fingerprint_after ==
  75e8231d…`, `gate_ok_replicated: true` (`review/logs/gate-replication.json`, sha256
  `a76fd2763b1d08e417459b759062f4c7bbefec1395778a458c101231e0b45290`). The D6 audit compiled into the
  release again reports `D6AUDIT\tVERDICT\tPASS — no sorryAx, no project axiom, no unsafe, no
  native_decide, no unapproved axiom, no proof_wanted`.
* Cited-declaration cones re-checked: every `#print axioms` line in the seven `review/logs/*-cited.log`
  files lists only `propext`, `Classical.choice`, `Quot.sound`; zero `sorryAx`. The three negative
  controls (`review/logs/*-negcontrol.log`) still report `VERDICT FAIL` as required.
* Fresh recompilation spot-check of the review's own cited-declaration probe: from the independent
  cold-build tree `review/build/D13-vankampen-recognition/release`, `lake env lean
  review/probes/D13-vankampen-recognition/Cited.lean` → **exit 0**, all 6 `depends on axioms` cones
  exactly `{propext, Classical.choice, Quot.sound}`, zero `sorryAx`.

**Cache clearance (external, 01:07:52 +08:00).** The residual blocker recorded above was cleared by the
operator: the stale `gate.json` was renamed to
`gate.transport-failure-preserved-20260912010752.json` (contents identical to the 00:38 entry; the
transport-failure `gate-build.log` is preserved alongside it). With no cached entry the dispatcher's
next `compile_gate` tick is a guaranteed cache miss and re-runs both gate stages against the repaired
tree, which the evidence above shows is green. This worker again confirmed it cannot write in that
directory (`touch` → `Permission denied`; escalation → `requires approval, but no approval channel is
available`), so the entry was not touched from this session.

These repair attempts change nothing in §0–§10: all verdicts, hashes and scope statements stand, no
audited file was modified, and this remains an independent review, never a Poincaré proof.

TASK_DONE
