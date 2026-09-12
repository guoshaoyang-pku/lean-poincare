# L1-lean-baseline — result card

- **Task id:** `L1-lean-baseline` · **worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L1-lean-baseline`
- **Lane:** integrator · **Named blockers in scope:** `M1`, `A1`, `P5`
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (`release/lean-toolchain`, sha256 `8190e75a…8ae88`) · Lean commit `6a10ac8c22beadecabdbb0919c2b50214762f91d` · Lake `5.0.0-src+6a10ac8`
- **mathlib:** `7974e751bece493b6ff508039423ca9fa2452fa8` (`release/lake-manifest.json`, sha256 `cbc45ee0…2c3d0`; git HEAD and clean status confirmed)
- **Snapshot audited:** `release/`, 462 files (456 `.lean`), byte-stable across all four invocations (re-hashed at every invocation entry: 462/462 unchanged; the A1 restatement was deliberately applied to byte-copies, never to this tree; after the fourth invocation's in-place clean rebuild the sources are still 462/462 and all 454 oleans are byte-identical to the invocation-1 build)
- **Generated:** first invocation 2026-09-11 23:12–23:52 (+08:00); continuation re-verification and cross-checks 2026-09-11 23:51 – 2026-09-12 00:40 (+08:00); third invocation (A1 restatement, P5 gate, independent replay) 2026-09-12 00:41 – 01:06 (+08:00); fourth invocation (fresh same-path clean rebuild, repaired artifact defects F9a/F9b, independent verifier contexts V1–V4) 2026-09-12 01:08 – (+08:00); each invocation well inside its 4 h cap
- **Verdict:** `TASK_DONE` for the **M1 baseline deliverable** — clean pinned build, full declaration/axiom-cone enumeration, fail-closed kernel audit, exact drift and queue reconciliation. The third invocation replayed the frozen tree from scratch (12,361 declaration rows and types identical), constructed/built/re-audited the A1 upstream restatement on a byte-copy and turned P5 into an executable fail-closed gate. The fourth invocation re-ran the pinned clean build at the same path (**454/454 oleans byte-identical**, upgrading the determinism claim from 377/377), re-ran both fail-closed audits (`L1AXVERDICT PASS`), and supplied the **independent** closure legs from four fresh verifier contexts: V1 `INDEPENDENT-REPLAY-IDENTICAL`, V2 A1 `INDEPENDENT-REVIEW-PASS`, V3 `INDEPENDENT-HASH-CHECK-PASS`/`INDEPENDENT-PATCH-DRIFT-MATCH`, V4 semantic review with corrections C1–C5 adopted and one new finding (F10). `A1` and `P5` are closure-ready with all four legs supplied; **no named blocker is self-certified closed**, adoption/external acceptance is requested, and **no Perelman/Poincaré claim is made or implied**.

---

## 0. Claims and non-claims

**Claims (all reproduced by commands recorded below, logs under `baseline/`):**

1. `lake build` from `release/` with `release/.lake/build` moved aside: **exit 0**, `Build completed successfully (9339 jobs)`, 2 m 06 s, 454 modules freshly compiled; the two root drivers outside Lake's `defaultTargets` (`D6LedgerProbe`, `ReleaseClaims`) compile separately with `lake env lean …`, **exit 0** each. All **377/377** pre-existing oleans are byte-identical to the fresh rebuild (`baseline/pre-rebuild/olean-rebuild-comparison.json`).
2. **Zero source drift since D13 integration:** 462/462 files match `D13-integrated-kernel-audit/audit-evidence/final-release-hashes.txt`; 286/286 match its pre-integration snapshot (176 files added); 63/63 D6 files and 66/66 D12 files are byte-identical (399 and 396 files added since).
3. **Fail-closed axiom audit over the entire package:** the package is *not* jointly importable (finding F1), so all 454 built modules were audited in two import-disjoint partitions — G1 (440 modules) and G2 (14 modules), **both exit 0**. Union: **12,543 declaration rows / 12,361 distinct names / 343 modules with declarations**; every axiom cone is contained in `{propext, Classical.choice, Quot.sound}` **except the three intentionally-forbidden negative-control declarations, all of which the detector flagged**; **0** unexpected violations, **0** `sorryAx`, **0** unsafe, **0** `native_decide`, **0** `proof_wanted`, **0** collector failures. The continuation's per-module probe sweep finds **12,364 distinct names**; the 3 extra generated `*.congr_simp` declarations are cone-checked separately (exit 0), so the union is clean too (§12).
4. **Authored-file scan:** exactly **2** declaration-form forbidden-token hits in 456 files — both documented negative controls (`axiom d12NegControlBadAxiom`, `axiom negativeControl`). No `sorry`, `admit`, `unsafe`, `native_decide`, `proof_wanted` declaration anywhere.
5. **Two negative-control axioms remain inside the release library glob** (finding F2). They are confined to their own files: `d12NegControlBadAxiom` appears in exactly one other cone — `d12NegControlBadTheorem`, its companion in the same module — and `Poincare.D12.VolumeIBP.Audit.negativeControl` appears in no other cone. `baseline/audit/downstream-use-comparison.json` confirms the only proof-level consumer of the first axiom is that companion theorem. This is a hygiene/quarantine item, not a soundness defect.
6. **Three authored declaration clusters are duplicated across two modules each** (finding F1): 153 kernel-level duplicate names; L5's independent `.ilean` count of 58 source-level collisions across the same three pairs is consistent under a different counting rule. L5 already queued `L5-C8-release-import-closure`.
7. **Queue/result-card reconciliation** (frozen queue snapshot sha256 `65e3c50c…dee8f`, `updated_at 2026-09-11T23:47:08+0800`, preserved at `baseline/reconcile/queue-card-reconciliation-20260911T154742Z.json`): 119 tasks — 85 verified, 5 running, 27 queued, 1 paused, 1 blocked; 91 with cards, 28 without (all running/queued); 5 reconciliation flags (F4).
8. **A1 upstream restatement constructed, built and re-audited (third invocation).** The three promoted theorems `Poincare.Longrun.Evolution.{gibbsTerm_strictAnti, gibbsTerm_step_lt, perelmanF_step_lt}` now carry the sharp hypothesis `1 ≤ c` / `∀ i, 1 ≤ c i` in `baseline/a1/patched-release/` (byte-copy of the frozen tree), delivered as `baseline/a1/a1-restatement.patch`. The patched tree builds from scratch (`lake build` exit 0, 9340 jobs, 0 errors, 0 `sorry`), the frozen fail-closed `AxiomAudit_G{1,2}` re-run there passes (G1: 12,072 declarations, 0 unexpected, 3 expected negative controls), the D7 `ReleaseAudit` passes over 880 declarations, and a new sharp-only consumer `perelmanF_step_lt_at_threshold_one` (at `c ≡ 1`, untypeable against the old hypothesis) plus the pre-existing D7 sharp layer provide kernel-checked downstream use (§13). The frozen `release/` tree is untouched.
9. **P5 is now an executable fail-closed gate (third invocation).** `baseline/tools/p5_hash_gate.py` re-hashes the tree, compares against all four accepted manifests and the three pins, and exits 1 on any changed/absent recorded file. On the frozen tree with `--fail-on-added`: **PASS, 0 drift** (462/462, 286/286, 63/63, 66/66); on the A1-patched tree: FAIL listing exactly the 7 changed files, which is the fail-closed demonstration (§13).

**Not claimed:** no theorem of Riemannian geometry, Ricci flow, surgery, extinction or sphere recognition is proved, strengthened or promoted here; **no named blocker is self-certified closed** (A1/P5 are closure-ready pending independent semantic review and adoption); the frozen `release/` tree was not modified by this task (the A1 restatement lives on a byte-copy plus a patch).

---

## 1. Pinned release build — commands and exits

| # | command | cwd | exit | evidence |
|---|---|---|---|---|
| 1 | `mv .lake/build ../baseline/pre-rebuild/build-tree` | `release/` | 0 | preserved 1.7 GB of prior artifacts; `baseline/pre-rebuild/build-artifact-inventory.txt` |
| 2 | `lake build` | `release/` | **0** | `baseline/logs/clean-build.log`: `Build completed successfully (9339 jobs)`, wall 2 m 06 s |
| 3 | `lake build D6LedgerProbe ReleaseClaims` | `release/` | 1 | `unknown target` — both are outside every `lean_lib` glob; recorded, then compiled per-file |
| 4 | `lake env lean D6LedgerProbe.lean` | `release/` | **0** | `baseline/logs/lean-D6LedgerProbe.log` (262 `#check`s) |
| 5 | `lake env lean ReleaseClaims.lean` | `release/` | **0** | `baseline/logs/lean-ReleaseClaims.log` (193 `#check`s) |
| 6 | `python3 baseline/tools/forbidden_scan.py release …` | worktree | 1 | `baseline/logs/forbidden-scan.json`, 456 files, 2 declaration-form hits (both negative controls) |
| 7 | `lake env lean ../baseline/audit/AxiomAudit_G1.lean` | `release/` | **0** | `baseline/logs/axiom-audit-G1.log`, 12,071 declarations, PASS |
| 8 | `lake env lean ../baseline/audit/AxiomAudit_G2.lean` | `release/` | **0** | `baseline/logs/axiom-audit-G2.log`, 472 declarations, PASS |
| 9 | `python3 baseline/tools/reconcile.py` | worktree | 0 | `baseline/reconcile/*.json` |
| 10 | `python3 baseline/tools/parse_axiom_audit.py` | worktree | 0 | `baseline/audit/axiom-audit.json`, `declarations.tsv`, `dep-edges.tsv` |

Build determinism: of the 377 oleans present before the rebuild, **377 are byte-identical** afterwards; 77 modules were compiled for the first time by this baseline (list in `baseline/pre-rebuild/modules-first-built-by-baseline.txt`, including `D6AuditReport`, `ReleaseCheck`, `ReleaseAudit`, all of `D11.ReducedVolume`, `D12.{EntropyVariation,HeatSemigroup,KappaVariational,SurgeryRecognition}`, `D13.IntegratedAudit.*`, and the `D7.{Canonical,Compactness,EvolutionSharp,Kappa,Limit,Recognition,Reduced,ShortTime,SurgeryFlow}` audit modules).

Warnings: 170 linter warnings in the build log (style/unused-variable class), none of them `error:`; no `sorry` warning.

---

## 2. Source hashes and drift

Full 462-file sha256 manifest: `baseline/reconcile/source-hash-drift.json` (`current_hashes`), and the 456 `.lean` subset in `baseline/hashes/release-sources-pre-rebuild.json`. Comparison against every historical manifest:

| baseline manifest | recorded | matched | changed | absent now | added since |
|---|---|---|---|---|---|
| D13 `final-release-hashes.txt` | 462 | **462** | 0 | 0 | 0 |
| D13 `base-release-hashes-preintegration.txt` | 286 | **286** | 0 | 0 | 176 |
| D6 `weekly-release-manifest.json` `package.files` | 63 | **63** | 0 | 0 | 399 |
| D12 `d12-semantic-ledger.json` `package_lean_files` | 66 | **66** | 0 | 0 | 396 |

The D13 snapshot is therefore an exact superset snapshot of the current tree: no post-D13 source drift. The pre-rebuild olean inventory (377) was 79 modules short of the 456 sources — 77 outside fresh oleans plus the 2 non-target drivers — which is the concrete "M1 baseline was not actually established before this task" gap.

---

## 3. Declaration enumeration

Machine-readable: `baseline/audit/declarations.tsv` (**one row per distinct declaration name — 12,361 rows**; the 12,543 raw partition rows collapse because 182 declarations occur in more than one module and appear once, and 3 all-duplicate original modules are therefore not separate TSV modules: 340 TSV modules vs 343 raw declaring modules — correction C4 of the fourth-invocation independent review; columns: name, kind, module, axiom cone, extra axioms, internal flag, transitive downstream-consumer count) and `baseline/audit/axiom-audit.json`.

| metric | value |
|---|---|
| declaration rows (sum of partitions) | **12,543** |
| distinct declaration names | **12,361** |
| names declared in more than one module | **182** (153 non-companion + 29 compiler companions) |
| modules with declarations | **343** of 454 built modules (111 are import/probe-only aggregators) |
| theorems / defs / partial defs | 7,655 / 4,015 / 22 (`_unsafe_rec` companions of `partial def`) |
| inductive / ctor / recursor / opaque | 217 / 230 / 217 / 3 |
| authored `axiom` declarations | **2** (both negative controls) |
| objects with unsafe safety | **0** |

Axiom-cone histogram over the 12,361 distinct names:

| cone | count |
|---|---|
| `{propext, Classical.choice, Quot.sound}` | 10,629 |
| `{}` (axiom-free) | 764 |
| `{propext}` | 628 |
| `{propext, Quot.sound}` | 323 |
| `{Quot.sound}` | 11 |
| `{Classical.choice}` | 3 |
| negative-control cones | 3 |

Direct intra-package dependency edges: **40,252** distinct pairs (`baseline/audit/dep-edges.tsv`); transitive downstream-consumer counts in `baseline/audit/downstream-use.json`. The most-depended-on declarations are interface structures (`Poincare.Longrun.Geometry.MetricData` 777, `Poincare.Longrun.Surgery.TopSpace` 682, `Poincare.Longrun.Geometry.LieBracketData` 662, `Poincare.D7.Compactness.PointedMetricSpace` 526), which is expected for an interface-first development.

### Downstream checked use of named-blocker / main-chain declarations

Counts are **transitive** consumers; `v1` is the first-invocation graph, whose theorem-user edges are type-level only (defect F6), `v2` is the corrected proof-level graph (`downstream-use-comparison.json`). `#check` sites are checked use, not proof use.

| declaration | kind | cone | v1 type-level | v2 proof-level | representative v2 consumers |
|---|---|---|---|---|---|
| `Poincare.Longrun.Evolution.perelmanF_step_lt` (A1) | theorem | standard | 0 | **1** | `Poincare.D7.EvolutionSharp.perelmanF_step_lt_promoted` (restatement wrapper) |
| `Poincare.Longrun.Evolution.gibbsTerm_strictAnti` (A1) | theorem | standard | 0 | **25** | `D4Audit.gibbsTerm_strictAnti_of_one_le`, `D4Audit.gibbsTerm_step_lt_of_one_le`, sharp-step lemmas |
| `Poincare.Longrun.Evolution.gibbsTerm_step_lt` (A1) | theorem | standard | 0 | **3** | `..._promoted`, `Poincare.Longrun.Evolution.perelmanF_step_lt` |
| `D4Audit.perelmanF_step_lt_of_one_le` (sharp) | theorem | standard | 0 | **1** | `D4Audit.strict_step_positive_control` |
| `Poincare.D7.EvolutionSharp.perelmanF_step_lt_of_one_le` (sharp) | theorem | standard | 0 | **6** | `..._old_recovered`, `..._strictly_generalizes`, sharp certificates |
| `Poincare.D7.EvolutionSharp.gibbsTerm_strictAnti_of_one_le` (sharp) | theorem | standard | 0 | **15** | `..._old_recovered`, `..._step_lt_of_one_le`, `..._strictly_generalizes` |
| `Poincare.D7.HeatKernel.HeatKernelData` | inductive | standard | **70** | **70** | D11 HeatKernelBridge |
| `Poincare.D12.SemanticLedger.not_initialCondition_gaussian` | theorem | standard | 0 | **2** | `..._quantified`, `D13...d13_consumer_defect_gaussian` |
| `Poincare.D10.HeatKernelEuclidean.heat_equation` | theorem | standard | 0 | **1** | `heat_equation_fun` |
| `Poincare.D7.Recognition.stage6Target_of_certificates` | theorem | standard | 0 | **4** | `D12.SurgeryRecognition.stage6Target_of_v{2,3}*`, `D7.Recognition.finalHomeomorphismConstruction_of_certificateFamily` |
| `ReleaseClaims.lean` / `D6LedgerProbe.lean` | drivers | — | — | — | 455 `#check`s, exit 0 (checked use only) |

**Corrected reading of A1 (replaces the first card's "0 proof-level consumers"):** the promoted statements *are* consumed at proof level — internally by the sharp-proof developments in `Audit/CounterexampleAudit.lean` and `Poincare/D7/EvolutionSharp/` (where the `1 < c` case is used and the `c = 1` case handled separately), and at the top by one restatement wrapper. The sharp forms have their own proof-level consumers (`_old_recovered`, `_strictly_generalizes`, witnesses). What is absent is a **main-chain mathematical consumer** of the monotonicity, and the exported `Poincare.Longrun.Evolution.*` statements still carry `1 < c`. A1 therefore remains **open on the statement side**, not on a "no consumer at all" side; the missing "downstream consumer" leg of the closure rule refers to main-chain use.

---

## 4. Fail-closed axiom audit

**Partitioning (finding F1).** `AxiomAuditAll.lean` (all 456 modules in one import) fails immediately: `import Poincare.D7.Monotonicity.ConjugateHeatCertificate failed, environment already contains 'Poincare.D7.ConjugateHeat.ConjugateHeatData' from Poincare.D7.ConjugateHeat.Basic`. The generator therefore computes the import graph, takes the three duplicated clusters as "vendored" seeds, and partitions every module into exactly one of two import-disjoint groups (every module is a seed exactly once, so each declaration is audited exactly once):

- **G1** — 440 modules (`baseline/audit/AxiomAudit_G1.lean`): 12,071 declarations in 333 modules, 47,098 raw dep rows, **PASS**.
- **G2** — 14 modules (`baseline/audit/AxiomAudit_G2.lean`): 472 declarations in 10 modules, 1,749 raw dep rows, **PASS**.

Both audits use `Lean.collectAxioms` (the kernel-trusted collector behind `#print axioms`) on every constant declared in the partition's modules, and `throwError` unless every cone ⊆ `{propext, Classical.choice, Quot.sound}` with exactly the documented negative controls flagged.

**Positive control.** The detector fired on exactly the three expected declarations and nothing else:

| declaration | kind | module | cone |
|---|---|---|---|
| `d12NegControlBadAxiom` | axiom | `Poincare.D12.TriangulationTopology.NegControl.NegControl` | `{d12NegControlBadAxiom}` |
| `d12NegControlBadTheorem` | theorem | same | `{d12NegControlBadAxiom}` |
| `Poincare.D12.VolumeIBP.Audit.negativeControl` | axiom | `Poincare.D12.VolumeIBP.Audit` | `{Poincare.D12.VolumeIBP.Audit.negativeControl}` |

**Process note (kept for auditability).** The first G1 run exited 1 with `unexpected=2, expected_seen=1`. Both "unexpected" rows were the two `NegControl` declarations, which are declared **without a namespace** (`d12NegControlBadAxiom`, not `Poincare.D12.…d12NegControlBadAxiom`); the expectation list was wrong, not the release. The failed log is preserved as `baseline/logs/axiom-audit-G1-firstrun-FAIL-vs-wrong-expectation-list.log`; the corrected run is the one reported above. No source or generated audit logic was weakened — only the expected-name literals were corrected to the names the kernel actually reports.

**Partial definitions (informational).** 22 `._unsafe_rec` companions of `partial def`s (e.g. `Poincare.Longrun.Surgery.SurgeryChain.append._unsafe_rec`, the `HatcherLib` van Kampen chains, `D13` audit traversals). Their cones are clean; D6 and D13 reported the same class. They are *not* `unsafe` declarations (safety = partial) and are listed for the record.

---

## 5. Authored-file forbidden-token scan

`baseline/tools/forbidden_scan.py` strips nested comments, string/char literals and guillemet identifiers, then scans for `sorry`, `axiom`, `admit`, `unsafe`, `native_decide`, `proof_wanted`, `sorryAx`.

- 456 files scanned; **2** declaration-form hits, both the documented negative controls; **0** other hits in code position (the raw scan also ignores `.«unsafe»` pattern-match arms in the audit modules, which are identifier references, not `unsafe` declarations).
- Because the two negative controls are *intentionally* inside the tree, the scan verdict is `REVIEW`, not `PASS`: a strict "no `axiom` in release/" rule would fail. Child task `L1-C3` proposes quarantining them; see finding F2.

**Conclusion-equivalent / fake-theorem screen (provenance-marked).** The task forbids "fake/weakened theorem" and "conclusion-equivalent assumptions". For this baseline:
- My own check is structural: every declaration's compiled type and axiom cone is recorded (12,361 names), so a theorem whose cone contains its own hypothesis-as-axiom would surface as an unapproved axiom — **none does**.
- *Upstream evidence, re-read from the clean-build log:* the in-tree `Poincare/D13/IntegratedAudit/StatementAudit.lean` scanned **3,196 theorems** and reported `hyp_eq_concl 0`, `hyp_defeq_concl 0`, `concl_in_hyp 0` (`D13STMT` lines in `baseline/logs/clean-build.log`), i.e. no hypothesis syntactically equal/def-equal to its own conclusion **within that screen's scope — the `Poincare.D11`/`Poincare.D12`/`Poincare.VKPort` modules it imports** (`StatementAudit.lean:63-68`). It is not a package-wide result; the fourth-invocation independent review found one self-implication outside it (finding F10).
- *Upstream evidence (queue note, not re-run here):* L5-topology-audit's vacuous/circular/unused screen reports 0 hits over 596 D2/D3 declarations.
- **Not performed here:** a fresh counterexample search (that is A3 / L5 scope; the D9 audit of the D6 snapshot found statement-level weaknesses such as assumption inflation and proof-shape-trivial theorems, which remain disclosure items rather than soundness defects). L1 therefore classifies the "fake/weakened theorem" check as *screened by cone + upstream statement audits, not exhaustively re-attacked*.

---

## 6. Findings (exact drift and defects)

**F1 — the release is not import-closed (integrity defect).** Three authored clusters are vendored copies of declarations that already exist elsewhere, so no single Lean environment imports both sides:

| pair | duplicate names (kernel count) |
|---|---|
| `Poincare.D7.Bochner.Basic` ↔ `Poincare.D7.Monotonicity.BochnerCertificate` | 41 |
| `Poincare.D7.Bochner.GradientEstimate` ↔ `Poincare.D7.Monotonicity.BochnerGradientEstimate` | 27 |
| `Poincare.D7.ConjugateHeat.Basic` ↔ `Poincare.D7.Monotonicity.ConjugateHeatCertificate` | 85 |
| **total** | **153** |

The `Monotonicity/*` copies carry a header stating they are vendored "verbatim" because the task worktree could only add files under `Poincare/D7/Monotonicity/`. L5-topology-audit independently measured **58** duplicate declaration names over the same three pairs using `.ilean` data; the difference is counting rule (kernel-level companions such as `ctorIdx`, `mk.inj`, `_abel_*` are included in my 153, excluded by the ilean reader). The cluster set agrees exactly. Consequence: whole-package single-environment screening is impossible until repaired; repair is owned by queued task `L5-C8-release-import-closure`.

**F2 — negative-control axioms inside the library glob (hygiene).** `axiom d12NegControlBadAxiom : False` (+ a dependent theorem) and `axiom negativeControl : False` are real declarations under `release/`. Both modules are imported by nothing (string references only in `D13/IntegratedAudit/ExpectedModules.lean` / `FullAudit.lean`). The axiom `d12NegControlBadAxiom` appears in exactly one other cone, `d12NegControlBadTheorem` (its companion in the same file); `Poincare.D12.VolumeIBP.Audit.negativeControl` appears in no other cone. They are the only reason a strict forbidden-token audit cannot return `PASS`.

**F3 — prior audit coverage was bounded, not wrong.** The in-tree drivers report `D6AUDIT project_declarations 1619` and `D13FULLVERDICT PASS — 8161 declarations in 237 modules`; my package-wide enumeration is 12,361 distinct names over 343 modules. Both in-tree audits are correct over their own import closures (D13 explicitly audits only the closure of `SnapshotRoot` + drivers and excludes the two negative-control modules). The new baseline is the first pass that enumerates every built module and reports the counts that the closure-bounded audits could not see.

**F4 — queue/card reconciliation flags.** `baseline/reconcile/queue-card-reconciliation-20260911T154742Z.json` (live queue keeps growing; this is the frozen snapshot used by this card):
- `D9-adversarial-audit-release` — queue `verified`, card verdict is a split: PASS on soundness, FAIL on disclosure completeness (4 undisclosed statement-level weaknesses, 1 measurement-inflation finding). Queue status conflates "verified" with "clean".
- `D13-heatkernel-bridge-d10-d7` — queue `running`, card `TASK_DONE` on disk (queue lag).
- `L1-lean-baseline`, `L3-analytic-critical-path`, `L4-geometric-critical-path` — queue `running`, cards `TASK_DONE` on disk; these are the live leader wave finishing in parallel (this card is one of them), so the flag is expected bookkeeping lag, not lost work.
- 28 tasks have no card, all `running`/`queued` — expected, no verified task lacks a card.

**F5 — input drift.** `CANONICAL-DAG.md` and `HANDOFF-PRIMARY-CONTROLLER.md`, named in the task text, do not exist anywhere in this worktree or under `longrun/` (searched 23:15 and again 00:10 +08:00). The reconciliation used `queue.json`, `leader-registry.json` and the D6/D12/D13 cards/manifests instead; recorded in `comms/inbox/2026-09-11-intake.md`.

**F6 — dependency graph was type-level for theorem users (found and corrected in the continuation invocation; affects A1's evidence, not the axiom audit).** The first invocation's drivers computed edges as `ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]`. In Lean v4.34.0-rc2 `ConstantInfo.value?` returns `none` for `.thmInfo`/`.opaqueInfo` unless `allowOpaque := true` (`Lean/Declaration.lean` line 483), so for every theorem user only the constants of its *statement* were recorded: proof-body edges were invisible, and `downstream_count` was a statement-level metric. Evidence: raw G1 log lacks `L1DEP Poincare.D7.EvolutionSharp.perelmanF_step_lt_old_recovered → …perelmanF_step_lt_of_one_le` although `Implications.lean:153` uses it; `baseline/audit/depcheck/ValueProbe.lean` prints `value?=false` for every theorem tested. **The axiom audit is unaffected**: `Lean.collectAxioms` matches `.thmInfo v` and traverses `v.value` directly (`Lean/Util/CollectAxioms.lean`); a probe prints `collectAxioms=[probeAx]` for a theorem proved from an axiom while `value?=false`, and the `d12NegControlBadTheorem` cone is still `{d12NegControlBadAxiom}`. Correction artifacts: `baseline/audit/DepAudit_G{1,2}.lean` (generated by `gen_dep_audit.py`; G1 exit 0, 4 m 45 s) → `dep-edges-v2.tsv` (**50,433** distinct pairs; G1 73,648 + G2 2,503 rows), `downstream-use-v2.json`, `downstream-use-comparison.json`. Corrected counts and their A1 reading are in §3.

**F7 — three generated declarations were outside the grouped audit's enumeration (found by the probe cross-check; gap closed).** The per-module probe inventory has 12,364 distinct names versus the audit table's 12,361. The three extras are generated `*.congr_simp` theorems (`BoundedContinuousFunction.mkOfBound.congr_simp`, `LinearMap.mk₂.congr_simp`, `ContinuousMap.Homotopy.affine.congr_simp`); in a whole-partition environment `Environment.getModuleIdxFor?` is first-wins (`insertIfNew`, `Lean/Environment.lean:2344`) and resolves them to non-target modules, so the target-module filter dropped them. Seven further generated `*.eq_1`/`*.congr_simp` names are attributed to two modules by single-module probes but only one in the whole-partition environment. All are compiler/attribute-generated, none is written literally in a source file. Gap closed by `baseline/audit/depcheck/MissedDeclConeCheck.lean` (**exit 0**, cones `{propext, Classical.choice, Quot.sound}`, `{propext, Quot.sound}`, `{propext, Classical.choice, Quot.sound}`; 0 unexpected). See `baseline/audit/probe-crosscheck-resolution.json`: coverage after resolution **12,364 names, 0 unexplained differences**.

**F10 — one self-implication theorem outside the D13 statement screen (found by the fourth-invocation independent semantic review; disclosure item, not a soundness defect).** A full-population textual screen of all **7,655** theorem types in the frozen type dumps (`baseline/v4-independent/fake_screen2.py`, deterministic; 31-row sample also clean) found exactly one declaration whose type is a self-implication: `Poincare.D7.SurgeryFlow.realLineProcedureChain_simplyConnected : toyLedger.SimplyConnected realLineTop → toyLedger.SimplyConnected realLineTop` (`release/Poincare/D7/SurgeryFlow/Basic.lean:277-279`, proof term `ProcedureChain.simplyConnected_preserved` at `X = Y`). It is a tautology: its cone is `{propext, Classical.choice, Quot.sound}`, it introduces no axiom, it proves nothing unconditionally, and it has **0 proof-level downstream consumers** in the v2 graph. It lies outside `D13 StatementAudit`'s D11/D12/VKPort-only scope, which is why the upstream `hyp_eq_concl 0` figure does not contradict it. The screen is textual/pretty-printed and cannot decide definitional equality (5,409 of 7,655 types have no top-level arrow in printed form), so the pattern is not exhaustively settled; child task `L1-child-self-implication-audit` (outbox, imported by the dispatcher, verifier lane) re-decides it with the kernel (`isDefEq`) over all 12,543 rows. This is the finding that makes the "fake/weakened theorem" check *screened and partially enumerated*, not exhaustive.

---

## 7. Semantic classification

Vocabulary required by the task: `proved`, `conditional`, `model`, `statement-only`, `upstream source claim`. Classification below is mine at cluster level, with provenance marked; the D12 ledger's per-entry classification is adopted only where marked *(upstream)*, and every cone/count claim is re-derived from the fresh audit above. Machine-readable form: `baseline/audit/semantic-classes.json` (ten clusters, local/upstream provenance, evidence links).

| cluster (evidence path) | class | basis |
|---|---|---|
| Axiom-cone cleanliness of all 12,361 names | **proved** (kernel) | fresh `Lean.collectAxioms` pass, G1+G2 exit 0; 3 documented exceptions |
| Rebuild reproducibility / determinism | **proved** | 377/377 oleans byte-identical; `lake build` exit 0 |
| `D10` Euclidean heat kernel / max principle / Bochner / Jacobi | **proved** *(upstream: D12 ledger "genuine-general")* | cone clean, sources byte-identical to D12/D13 snapshots; statements not re-reviewed line-by-line here |
| `D7.EvolutionSharp` sharp corrections | **proved** *(upstream)* + locally cone-checked | sharp statements exist, cone clean; v2 graph: proof-level consumers are the recovery/strictness lemmas in the same cluster and `D4Audit`, none in the main chain |
| `Poincare.Longrun.Evolution.*` promoted monotonicity (A1 targets) | **conditional** on overstrong hypotheses, otherwise proved | `1 < c` instead of `1 ≤ c`; sharp form and `old_of_sharp`/`old_recovered` bridges exist in `release/Poincare/D7/EvolutionSharp/Implications.lean`; corrected consumers 25/3/1 (§3) but no main-chain consumer |
| `D7.SphereRecognition.stage6Target_of_certificates` | **conditional** *(upstream: D12 §4)* | kernel-checked implication over unproved interface antecedents (extinction, canonical neighbourhoods, piece recognition, van Kampen); 4 real downstream consumers in `D12.SurgeryRecognition`/`D7.Recognition` |
| `D7.HeatKernel.HeatKernelData.initialCondition` field | **model / defective interface** | D12 counterexample (`not_initialCondition_gaussian`) cone clean; field is unsatisfiable on ℝ with the Gaussian kernel |
| Discrete/grid/toy developments (`D2` discrete max principle, `D3` toy surgery, `L-D1` toy, `VKPort` finite chains, `HatcherLib` sweeps) | **model** | finite/discrete models of the intended geometry |
| State-only interface Props (**re-grounded in-tree** at `release/Poincare/D7/SurgeryFlow/Statements.lean:125/157/237/269` plus the analogous Canonical/ShortTime/Kappa statement modules; the D12-ledger names `P-LONG`/`P-HARNACK` are external provenance and occur nowhere in this worktree — correction C5 of the fourth-invocation independent review) | **statement-only** | the Props are defined and never asserted as theorems; conic audit only confirms their declarations add no axioms |
| D1–D4 promoted release content, D6/D13 audit reports | **upstream source claim** | cards/manifests consumed as inputs; not re-derived semantically here beyond cone/hash checks |

No cluster is promoted by this card; the classification is descriptive evidence for the acceptor.

---

## 8. Blocker status (four-part closure rule applied)

| blocker | status after this task | constructed input | downstream consumer | independent rebuild | semantic review |
|---|---|---|---|---|---|
| **M1** | **evidence delivered; NOT closed** — closure requires independent acceptance | audit generators + card + manifests + v2 dependency graph + probe cross-check | next release integrator; children `L1-C1`/`L1-C4` | clean build here (same agent); re-verified 29/29 read-only checks in the continuation | this card; independent replay is child `L1-C1` |
| **A1** | **open** — promoted statements unchanged | sharp proofs + `old_of_sharp`/`promoted`/`old_recovered` bridges exist (`D4Audit.*_of_one_le`, `D7.EvolutionSharp.*`) | proof-level consumers exist (25/3/1 corrected), but **no main-chain consumer**; the top `perelmanF_step_lt` consumer is a restatement wrapper; only `#check` probes from outside | yes (this build) | D12 ledger note + this card; F6 corrects the earlier "0 consumers" evidence |
| **P5** | **open (recurring)**; re-run on this snapshot at 15:54Z (0 changed / 0 removed) | hash manifests + `reconcile.py` | release gate (proposed `L1-C4`) | yes (this build) | this card |

No named blocker is claimed closed. M1's acceptance rule (`compiled_and_axiom_audited_until_independent_semantic_review`) is satisfied on the "compiled and axiom-audited" side and explicitly left pending on the "independent" side.

---

## 9. Reconciliation summary

- **Source hashes:** see §2 — 0 changed / 0 removed against every historical manifest; 399/396/176 files added since D6/D12/D13-base respectively.
- **Queue:** frozen snapshot sha256 `65e3c50c070e44da4b6ae4338c3a5e4cb9cbe6b8278825bde97766a73b2dee8f` (119 tasks; `updated_at 2026-09-11T23:47:08+0800`; report `baseline/reconcile/queue-card-reconciliation-20260911T154742Z.json`). 85 verified / 5 running / 27 queued / 1 paused / 1 blocked; 91 with a card, 28 without (none verified).
- **Queue re-run (continuation, 2026-09-11T23:54:20+08:00):** live queue now 129 tasks, 86 verified / 4 running / 37 queued / 1 paused / 1 blocked; 91 with a card, 38 without; 4 flags. Exact drift in `baseline/reconcile/queue-drift-20260911T1554Z.json`: **+10 tasks, 0 removed, 1 status transition** (`L3-analytic-critical-path` running → verified, its `queue_lagging_card_done` flag cleared), flags 5 → 4. The 10 additions are the 3 L1 hot children, 4 L4 children and 3 M2 tasks. `L1-lean-baseline` is still `running` (this task). Hash re-check on the same re-run: 462/462 / 286/286 / 63/63 / 66/66, **0 changed, 0 removed**.
- **Result cards:** all 87 available cards parsed; 3 flags (F4); the two `TASK_DONE`-but-`running` cases are live siblings/queue lag, not lost work.
- **Leader registry:** sha256 `446175479bd0e78aac59a08511de31bdcc049f8bf33666e81e8c7c97e80c559b`; L1's entry (`integrator`, `requires_lean`, host pool `ophis-gpu`) matches this task.

---

## 10. Child tasks (outbox)

Imported into the queue 23:39 (+08:00) — the dispatcher renamed each to `*.json.imported` as its delivery ack:
`comms/outbox/L1-C1-independent-axiom-replay.json.imported` (verifier, M1) ·
`L1-C2-a1-promoted-restatement.json.imported` (builder, A1) ·
`L1-C3-negative-control-quarantine.json.imported` (integrator, P5) ·
`L1-C4-p5-hash-gate.json.imported` (integrator, P5).

Hot-dispatch children 23:52 (+08:00), `L1-child-` prefix per `comms/inbox/primary-hot-1789141005344.md`:
`L1-child-partial-def-soundness-review.json` (verifier, M1; audit the 22 `partial def`/`._unsafe_rec` constants) ·
`L1-child-declaration-ledger-export.json` (integrator, M1; canonical semantic-ledger export + fail-closed cone diff) ·
`L1-child-queue-verdict-gate.json` (integrator, P5; executable F4 queue-vs-card gate).

Each is JSON with `id, group_id, parent_node, deps, lane, acceptance, host_pool, requires_lean, max_hours` and a concrete objective, and each is independently verifiable. `L5-C8-release-import-closure` already owns F1 and is **not** duplicated.

---

## 11. Reproducibility

```
export PATH=/data3/guoshaoyang/workdir/lean_poincare/elan/bin:$PATH
cd release && lake build                        # exit 0
python3 ../baseline/tools/forbidden_scan.py . ../baseline/logs/forbidden-scan.json
python3 ../baseline/tools/gen_grouped_audit.py  # regenerates AxiomAudit_G1/G2
cd release && lake env lean ../baseline/audit/AxiomAudit_G1.lean   # exit 0
cd release && lake env lean ../baseline/audit/AxiomAudit_G2.lean   # exit 0
python3 ../baseline/tools/parse_axiom_audit.py
python3 ../baseline/tools/reconcile.py

# continuation (2026-09-12)
python3 baseline/tools/verify_baseline.py                    # 29 read-only checks; see §12
python3 baseline/tools/gen_dep_audit.py                      # regenerates DepAudit_G1/G2
cd release && lake env lean ../baseline/audit/DepAudit_G1.lean > ../baseline/logs/dep-audit-G1.log   # exit 0
cd release && lake env lean ../baseline/audit/DepAudit_G2.lean > ../baseline/logs/dep-audit-G2.log   # exit 0
python3 baseline/tools/parse_dep_audit_v2.py                 # dep-edges-v2.tsv, downstream-use-v2.json
python3 baseline/tools/named_targets_downstream.py           # v1 + v2 counts, #check sites
bash baseline/tools/run_probes.sh                            # 454/454, resumable, per-probe exit files
python3 baseline/tools/parse_probe_inventory.py              # cross-check vs declarations.tsv
cd release && lake env lean ../baseline/audit/depcheck/MissedDeclConeCheck.lean   # exit 0
cd release && lake env lean ../baseline/audit/depcheck/ValueProbe.lean            # F6 evidence
python3 baseline/tools/queue_drift.py \
  baseline/reconcile/queue-card-reconciliation-20260911T154742Z.json \
  baseline/reconcile/queue-card-reconciliation.json \
  baseline/reconcile/queue-drift-20260911T1554Z.json
python3 baseline/tools/gen_manifest.py
python3 baseline/tools/verify_baseline.py                    # re-run after MANIFEST regen
```

Artifact hashes: `axiom-audit.json` sha256 `17445c0eff16fa3c0de2f62f28ccc44edd5d49437b37cb5e56674e6d7616d9fb`; `forbidden-scan.json` sha256 `07e579597c18fdc36786215bf044554384830b7f04e9a2173208c359d7da9891`. Prior artifacts preserved in `baseline/pre-rebuild/build-tree/` (the original `release/.lake/build`) and, for the continuation, the interrupted probe sweep in `baseline/logs/probes-interrupted-20260911T1550Z/` + `baseline/audit/probes-v1-interrupted/`.

---

## 12. Continuation verification (2026-09-12, second invocation)

The second invocation of this task did not restart anything: it re-verified the frozen evidence, finished the interrupted per-module probe sweep, found and corrected the dependency-graph defect F6, closed the enumeration gap F7, and refreshed this card. Nothing in `release/` was touched (`B1`: 462/462 files byte-identical to the frozen manifest at 00:00 +08:00).

- **Read-only re-verification:** `baseline/tools/verify_baseline.py` — **29 checks, 29 PASS, 0 FAIL** (`baseline/logs/verify-baseline.json`): **3270/3270** evidence-manifest entries as of that invocation's MANIFEST (the earlier "913/913" figure was a stale pre-regeneration count; `A2_manifest_hashes_match` reported 0 mismatched — correction C1 of the fourth-invocation independent review. The manifest grows with each invocation's evidence: the final fourth-invocation MANIFEST has **4,764** entries, and its own re-run of the same 29 checks reports 29/29 PASS again; note also that this paragraph was itself found to make the card's numbers depend on a moving file, so the count is cited per-invocation rather than as a package constant); release tree 462/462; clean-build marker + 0 build errors + 0 `declaration uses 'sorry'` + 170 lint warnings; G1/G2 `L1AXVERDICT PASS` with 0 unexpected violations / 0 sorry / 0 unsafe / 0 native_decide; both non-default drivers exit 0 (262 + 193 `#check`s); forbidden scan 456 files / exactly 2 declaration-form hits (both documented negative controls); G1∪G2 = the 454 built olean modules and G1∩G2 = ∅; declaration rows 12,361 = 12,543 partition rows minus 182 duplicates (153 authored + 29 generated); 377/377 olean determinism and the 77 first-built modules; preserved build tree present; v2 dependency graph; probe sweep; missed-declaration cones; card references.
- **P5 re-run at 15:54Z:** all four historical manifests still match with 0 changed / 0 removed.
- **Queue re-run at 15:54Z:** exact drift recorded (§9); flags 5 → 4.
- **Per-module probe cross-check (F7):** 454/454 probes exit 0; 343 modules declare (111 import-only), matching the grouped audit; 0 kind mismatches; 12,364 distinct names; all differences explained by generated declarations and whole-environment module attribution; the 3 probe-only declarations cone-checked clean by a targeted driver (exit 0).
- **F6 correction:** proof-level dependency graph rebuilt; A1's evidence corrected from "0 proof-level consumers" to "proof-level consumers exist (25/3/1), but no main-chain consumer and the exported statements keep `1 < c`". A1 remains open.
- **New artifacts:** `baseline/tools/{verify_baseline,gen_dep_audit,parse_dep_audit_v2,named_targets_downstream,parse_probe_inventory,queue_drift,gen_manifest}.py`, `baseline/audit/{dep-edges-v2.tsv,downstream-use-v2.json,downstream-use-comparison.json,named-targets-downstream.json,semantic-classes.json,probe-inventory-crosscheck.json,probe-crosscheck-resolution.json,DepAudit_G1.lean,DepAudit_G2.lean,depcheck/*}`, `baseline/logs/{verify-baseline.json,dep-audit-G1.log,dep-audit-G2.log,missed-decl-cone-check.log,run-probes-v2.log,probes/*}`, `baseline/reconcile/{queue-drift-20260911T1554Z.json,*-20260911T1554Z.json}`, `research-brief-2026-09-12.md`.
- **Still not claimed:** no named blocker self-certified closed; no theorem promoted beyond the finite D4 restatement; no Poincaré claim. A1/P5 need independent semantic review and adoption; M1's replay is in §13.

---

## 13. Third invocation (2026-09-12, 00:41–01:06 +08:00): A1 restatement, P5 gate, from-scratch replay

This invocation did not restart anything. On entry it re-ran `baseline/tools/verify_baseline.py` on the frozen snapshot: **29 checks, 29 PASS, 0 FAIL**. It then executed the three queued children's construction work (L1-C1 replay, L1-C2 restatement, L1-C4 gate) as *constructed inputs*; the children remain queued for independent replay/adoption.

### 13.1 A1 — upstream restatement (the D12 criterion)

The D12 ledger closes A1 only on *upstream restatement*: the three promoted theorems must carry `1 ≤ c`. That restatement is delivered as a patch and verified on a byte-copy; the frozen `release/` tree was **not** modified (`baseline/a1/patched-drift.json`: 7 changed, 1 added, 0 removed; `release/` still 462/462).

| item | value |
| --- | --- |
| patch | `baseline/a1/a1-restatement.patch`, 304 lines, sha256 `c58333743effbe7f8ba9e1ba823c02aaf3a11e995428169d7796ddb6eec2ac8a`, applies at `release/` with `patch -p1` (verified: `patch -p1 --dry-run --forward` exits 0 on the frozen tree, all 8 files checked) |
| patched tree | `baseline/a1/patched-release/` (463 files; reproducible via `baseline/a1/make_patch.py`, 12 anchors each asserted unique) |
| changed files | `Poincare/Longrun/Evolution/{Gibbs,Discrete}.lean`, `Poincare/Longrun/Evolution.lean`, `Poincare/D7/EvolutionSharp/{GibbsSharp,Implications,AxiomAudit}.lean`, `Audit/CounterexampleAudit.lean` |
| added file | `Poincare/D7/EvolutionSharp/SharpOnlyConsumers.lean` |
| evidence bundle | `baseline/a1/a1-evidence.json` |

Restated signatures (printed by `baseline/a1/verify/A1Probe.lean`, exit 0; the first two `example`s in that file are *positive* signature checks that only typecheck with the sharp hypothesis):

```
gibbsTerm_strictAnti : ∀ (c : ℝ), 1 ≤ c → StrictAnti (gibbsTerm c)
gibbsTerm_step_lt    : ∀ {c x u : ℝ}, 1 ≤ c → 0 < u → gibbsTerm c (x + u) < gibbsTerm c x
perelmanF_step_lt    : ∀ {ι} [Fintype ι] (F : ReactionField ι) {c : ι → ℝ}, (∀ i, 1 ≤ c i) →
                       0 < h → DiscreteEvolution F h traj → 0 < F.eval (traj n) i →
                       perelmanF c (traj (n+1)) < perelmanF c (traj n)
```

Semantics: the conclusion of each theorem is unchanged and the hypothesis is weakened (`1 < c` → `1 ≤ c`), so this is a **strengthening**, not a weakened/fake theorem; the `c = 1` case is the flat spot `x = 1` of `(1 + x²) e^{-x}`, handled by gluing the two one-sided strict antitonicity statements (`strictAntiOn_of_deriv_neg` on `Iic 1` and `Ici 1`). The `perelmanF` step is the existing `Finset.sum_lt_sum` argument with the strict component supplied by the now-sharp `gibbsTerm_step_lt` and all other components by `gibbsTerm_step_le` (already `1 ≤ c`). Four old-format call sites were converted with `le_of_lt`; no conclusion changed; no hypothesis was added. **Semantic class:** `proved` inside the finite D4 model (the D4 approximation boundary — a finite reaction ODE and a finite sum, *not* Perelman's `F` along Ricci flow — is unchanged and remains stated in the module docstrings).

**Downstream consumer** (the leg a bare restatement does not supply): `SharpOnlyConsumers.lean` proves `perelmanF_step_lt_at_threshold_one` at `c ≡ 1` — an application that is *impossible* against the old `∀ i, 1 < c i` statement — plus `gibbsTerm_strictAnti_at_threshold_one` and the backward-compatibility lemma `perelmanF_step_lt_sharp_of_lt`. Proof-level consumer declarations (`baseline/a1/verify/ConsumerCone.lean`; the log's `A1USEN` consumer rows number **13**, over **1,106** raw `A1USE` constant-reference lines — the earlier "13 edges" wording conflated the two counts, correction C2 of the fourth-invocation independent review) include `perelmanF_step_lt_at_threshold_one → Poincare.Longrun.Evolution.perelmanF_step_lt` and `perelmanF_step_lt_promoted → …perelmanF_step_lt`; the pre-existing D7 sharp layer (`gibbsTerm_strictAnti_of_one_le`, `perelmanF_step_lt_of_one_le`, the D3 certificate layer) and `D4Audit.*` are further consumers.

### 13.2 A1 — independent rebuild and fail-closed re-audit of the patched tree

| # | command (cwd `baseline/a1/patched-release`) | exit | result |
| --- | --- | --- | --- |
| 1 | `lake build` | **0** | `Build completed successfully (9340 jobs)`, 0 errors, 0 `declaration uses 'sorry'`, 170 lint warnings (same count as the frozen build) — `baseline/a1/logs-patched-build.log` |
| 2 | `lake env lean ../../../baseline/audit/AxiomAudit_G1.lean` | **0** | `L1AXVERDICT PASS`, 12,072 declarations (12,071 frozen + 1 generated `_simp_1_1` from the new proof), 0 unexpected violations, 3 expected negative controls seen, 0 sorry/unsafe/native, 0 collector failures |
| 3 | `lake env lean ../../../baseline/audit/AxiomAudit_G2.lean` | **0** | `L1AXVERDICT PASS`, 472 declarations, 0 unexpected |
| 4 | `lake env lean Poincare/D7/EvolutionSharp/ReleaseAudit.lean` | **0** | environment-wide D7 gate: 880 project declarations, 0 sorryAx, 0 project axiom, 0 unsafe, 0 native_decide, 0 unapproved cones |
| 5 | `lake env lean ../../../baseline/a1/verify/A1Probe.lean` | **0** | sharp signatures above; all eight printed cones are `{propext, Classical.choice, Quot.sound}` |
| 6 | `python3 ../../../baseline/tools/forbidden_scan.py . …` | 1 (expected) | 457 files, exactly the 2 documented negative-control axioms, no other declaration-form hit |

### 13.3 P5 — executable fail-closed hash gate

`baseline/tools/p5_hash_gate.py` turns "any future release must re-run the hash check" into a gate: hash the tree (excluding `.lake/`), compare every file recorded by the four accepted manifests (D13 final, D13 pre-integration base, D6, D12), verify the three pins, exit 1 on any changed/absent recorded file (and on any added file with `--fail-on-added`).

| invocation | exit | result |
| --- | --- | --- |
| frozen `release/` with `--fail-on-added` | **0** | PASS, 0 drift: 462/462, 286/286, 63/63, 66/66; pins match — `baseline/logs/p5-hash-gate.json` |
| A1-patched tree | **1** | FAIL: **7 distinct changed paths + 1 added**; the report's `drift` array holds **22 entries, all of kind `changed`** (7 for D13-final + 7 for D13-base + 4 for D6 + 4 for D12 = the same 7-path set spread across the four manifests — all 7 in each D13 manifest, 4 in D6 and 4 in D12, since the three `Poincare/D7/EvolutionSharp/*` paths are absent from the D6/D12 baselines); the 1 added file is reported separately under `added_vs_union_of_manifests`, not in `drift` — correction C3 of the fourth-invocation independent review (fail-closed demonstration) — `baseline/a1/logs/p5-hash-gate-patched.json` |

### 13.4 M1 / L1-C1 — replay from a from-scratch rebuild (same-agent constructed input for the queued child L1-C1)

A second byte-copy of the frozen sources was built in a different directory (`baseline/c1/replay-release/`), the frozen fail-closed drivers were re-run there, and the result was compared declaration-by-declaration against the frozen evidence (`baseline/c1/compare_replay.py` → `baseline/c1/replay-comparison.json`):

| dimension | result |
| --- | --- |
| build | `Build completed successfully (9339 jobs)`, exit 0 — `baseline/c1/logs-replay-build.log` |
| replayed audits | `AxiomAudit_G1` PASS (12,071 declarations, 0 unexpected, 3 negative controls, 0 sorry/unsafe/native, 0 collector failures); `AxiomAudit_G2` PASS (472 declarations) |
| declaration table | **12,361 / 12,361 rows field-identical** (name, kind, module, axiom cone, extra, internal) |
| declaration types | **12,361 / 12,361 character-identical** (independent `TypeAudit_G{1,2}` dumps over the frozen partition, `baseline/c1/typeaudit/`) |
| oleans | 454 common; **422 byte-identical**, 32 differ only by the embedded absolute source path (size delta 16/24 = 8-byte alignment of the 19-char path difference; each side contains its own root path), **0 unexplained** |

**Finding F8 (new, from the replay):** olean bytes are not path-independent. The 32 differing modules embed the absolute source path of the file they were compiled from, so a rebuild in a different directory is not byte-reproducible for them even though the term content is identical. Same-path byte determinism is re-confirmed: the prior 377/377 result, plus a re-compile of `Poincare/D12/VolumeIBP/Compat.lean` in the replay tree with the exact lake flags reproducing sha256 `750f1631…2e5f1` byte-for-byte. **No soundness impact** — the declaration table and all 12,361 declaration types are identical, and both replayed audits pass.

### 13.5 A1/P5/M1 closure legs (third invocation)

| blocker | constructed input | downstream consumer | independent rebuild | semantic review | status |
| --- | --- | --- | --- | --- | --- |
| **A1** | patch + byte-copy (§13.1) | `SharpOnlyConsumers` at `c ≡ 1` + D7 sharp layer + `D4Audit` (§13.1) | patched tree built and re-audited from scratch (§13.2) | **requested** from the independent acceptor; semantic analysis in §13.1 | closure-ready, **not self-certified closed**; adoption + review requested in `comms/outbox/2026-09-12-L1-a1-restatement-handoff.md` |
| **P5** | gate script + both runs (§13.3) | the gate is the consumer (exit code) | gate run against a byte-copy that the gate itself flags as drift | **requested** | gate delivered; recurring obligation now executable, not self-closed |
| **M1** | frozen baseline (invocations 1–2) | replay audits + type dumps (§13.4) | from-scratch rebuild in a separate directory; 12,361 rows and types identical | independent replay performed; independent human/agent review requested via this card | replay evidence complete; M1 available for independent acceptance (L1-C1) |

### 13.6 Queue/card/source-hash reconciliation on this snapshot

Re-run 2026-09-11T16:48Z (`baseline/reconcile/*-20260911T1648*.json`): **135 tasks** — 86 verified, 7 running, 40 queued, 1 paused, 1 blocked; 95 with cards, 40 without; 8 reconciliation flags (1 verified-but-split, 6 queue-lagging `TASK_DONE` cards including this one, 1 queued `TASK_DONE`). Drift vs the 15:54Z frozen snapshot: +6 tasks, 0 removed, 1 status transition, 3 card/flag changes (`baseline/reconcile/queue-drift-20260911T164848Z.json`). Source hashes on this snapshot: 0 changed / 0 removed against all four manifests.

---

## 14. Fourth invocation (2026-09-12, 01:08 – +08:00): fresh same-path rebuild, repaired artifact defects, independent verification

This invocation did not restart anything; the frozen evidence and §§1–13 are preserved. It (i) re-ran the pinned build and fail-closed audits from scratch at the same path, (ii) repaired two stale-artifact defects found by the entry re-verification, and (iii) for the first time supplied the **independent** legs of the M1/A1/P5 closure rule from fresh verifier-agent contexts.

### 14.1 Entry re-verification and two repaired defects (F9)

`verify_baseline.py` on entry returned **27/29** (not 29/29 as at the end of invocation 3), with both failures explained and repaired:

- **F9a — stale manifest entry (pre-existing, from invocation 3).** `baseline/logs/p5-hash-gate.json` was rewritten at 01:07:41, **21 s after** `baseline/MANIFEST.json` (01:07:20), so its recorded sha256 was stale. Only the report's `generated_at` differs; the verdict is the same PASS / 0 drift. Repaired by regenerating the report and then the MANIFEST in this invocation, so the report→manifest order is now enforced.
- **F9b — self-inflicted, repaired byte-for-byte.** An accidental `forbidden_scan.py --help` call at 01:10:44 treated `--help` as the tree path and overwrote `baseline/logs/forbidden-scan.json` with a 0-file report. The original bytes were recovered exactly by exhaustive search over the only varying field (`generated_at`, window 15:00–15:59Z on 2026-09-11): the recovered timestamp is **2026-09-11T15:19:38Z** and the sha256 is again `07e579597c18fdc36786215bf044554384830b7f04e9a2173208c359d7da9891`, identical to the value recorded in the first card. No evidence was lost; the incident is recorded rather than hidden.

### 14.2 Fresh pinned build and fail-closed audits (same path)

| step | command (cwd) | exit | result |
| --- | --- | --- | --- |
| move build tree | `mv release/.lake/build baseline/pre-rebuild/build-tree-inv1-20260912T0118Z` | 0 | 454 oleans preserved |
| clean build | `lake build` (release/) | **0** | `Build completed successfully (9339 jobs)`, 2 m 26 s, 0 `error:`, 0 `declaration uses 'sorry'`, 170 lint warnings — `baseline/logs/fourth/clean-build.log` |
| drivers | `lake env lean D6LedgerProbe.lean` / `ReleaseClaims.lean` | 0 / 0 | 262 / 193 `#check` commands; outputs byte-identical to the frozen logs apart from the trailing `time` lines |
| forbidden scan | `forbidden_scan.py release …` | 1 (REVIEW) | 456 files, exactly **2** declaration-form hits (both documented negative controls) |
| axiom audit G1 | `lake env lean ../baseline/audit/AxiomAudit_G1.lean` (release/) | **0** | `L1AXVERDICT PASS`: 12,071 declarations / 333 modules / 47,098 dep edges / 0 unexpected / 3 expected negative controls / 0 sorry / 0 unsafe / 0 native / 0 collect failures |
| axiom audit G2 | `lake env lean ../baseline/audit/AxiomAudit_G2.lean` (release/) | **0** | `L1AXVERDICT PASS`: 472 declarations / 10 modules / 1,749 dep edges / 0 unexpected |
| in-build D6/D13 gates | (from the build log) | — | `D6AUDIT VERDICT PASS`; `D13FULLVERDICT PASS`; `D13STMT theorems_scanned 3196`, `hyp_eq_concl 0`, `hyp_defeq_concl 0`, `concl_in_hyp 0` (scope: D11/D12/VKPort only, see F10) |
| D7 sharp release audit | `lake env lean Poincare/D7/EvolutionSharp/ReleaseAudit.lean` | **0** | `D7SharpReleaseAudit: PASS` — 0 sorryAx/project axiom/unsafe/native_decide in any dependency cone |

**Same-path olean determinism upgraded from 377/377 to 454/454** (`baseline/logs/fourth/olean-same-path-comparison.json`, sha256 `3316c3e2…e084cc`): the invocation-1 build tree and this fresh rebuild in the identical directory are byte-identical for all 454 oleans (0 differing, 0 only-in-either). Combined with §13.4 (422/454 byte-identical across *different* directories; 32 path-embedded, F8), the determinism claim now covers all 454 modules at the same path.

### 14.3 Independent verification supplied by fresh agent contexts

Four independent verifier agents ran read-only against the frozen artifacts and wrote only under their own directories. Their reports (with sha256) are the independent legs:

| leg | verifier | report | verdict |
| --- | --- | --- | --- |
| M1 independent rebuild + replay | V1 | `baseline/v1-independent/independent-report.{json,md}` (`308c3fa8…`, `face464c…`) | `INDEPENDENT-REPLAY-IDENTICAL` |
| A1 independent semantic review | V2 | `baseline/a1/review-independent/review.{json,md}` (`1f26bc99…`, `d978a0c1…`) | `INDEPENDENT-REVIEW-PASS` (two framing corrections adopted, see §14.4) |
| P5 independent hash + patch check | V3 | `baseline/v3-independent/report.{json,md}` (`0488d203…`, `d702978d…`) | `INDEPENDENT-HASH-CHECK-PASS` + `INDEPENDENT-PATCH-DRIFT-MATCH` |
| M1 independent semantic/traceability review | V4 | `baseline/v4-independent/review.{json,md}`, `review-corrected.json` | `INDEPENDENT-SEMANTIC-REVIEW-FAIL` on the **pre-correction** §12/§13.1/§13.3 wording (C1–C3); all ten §7 classifications, all checked cones/counts, F1/F2/F6/F7 and the §5 disclaimer were found supported. Corrections C1–C5 were adopted (§14.4) and the bounded re-review (`review-corrected.json`) confirmed them, reducing the remaining issues to one gloss about which manifests record which of the 7 changed paths; that clause has now been fixed exactly as the reviewer specified ("all 7 in each D13 manifest, 4 in D6 and 4 in D12"), which the reviewer stated was the sole remaining item for this lane — no semantic finding remains open |

V1 rebuilt a fresh byte-copy from scratch (`lake build` exit 0, 9339 jobs, 149 s, 454 oleans), re-derived the enumeration with its own parser (**12,361/12,361 rows, 0 mismatches**), reproduced both type dumps byte-for-byte, re-ran the frozen drivers (`L1AXVERDICT PASS`) and independently `#print axioms`-checked **610** sampled declarations (**610 agree, 0 disagreements**; 9 `_private.*` names unreachable by the second harness, covered by the full enumeration). V3 wrote its own hash checker *before* reading the gate, reproduced all four manifest comparisons with 0 changed/absent, recomputed the three pins, and reproduced the patch drift exactly (7 changed + 1 added; whole-tree diff vs `patched-release` empty). V2 re-applied the patch to a fresh copy (byte-identical to `patched-release`), re-derived the `c = 1` gluing proof and the `Finset.sum_lt_sum` step, confirmed the sharp-only consumer is untypeable against the old hypothesis, and independently proved `(∀ i, c i = 1) → ¬(∀ i, 1 < c i)`.

### 14.4 Corrections adopted from the independent reviews

- **C1** — "913/913 evidence-manifest hashes" was a stale pre-regeneration count; corrected to **3270/3270** entries throughout (§12).
- **C2** — "13 `A1USE` edges" conflated two counts; the log has **13 `A1USEN` consumer declarations** over **1,106** raw `A1USE` constant-reference lines (§13.1).
- **C3** — the patched-tree P5 FAIL has **7 distinct changed paths + 1 added**, with **22 entries in the report's `drift` array, all of kind `changed`** (7 + 7 + 4 + 4 across the four manifests; the added file is listed separately under `added_vs_union_of_manifests`); this is expected source-hash drift, not an unresolved failure — consistent with V2's review (§13.3, and the `a1-evidence.json` field should be read as EXPECTED-DRIFT).
- **C4** — `declarations.tsv` is name-deduplicated (12,361 rows; 340 TSV modules vs 343 raw declaring modules; the 182 cross-module duplicate names and the 3 all-duplicate original modules are not separate rows), and the upstream `hyp_eq_concl 0` screen covers only the 3,196 D11/D12/VKPort theorems it imports (§3, §5).
- **C5** — the "statement-only" cluster is re-grounded on in-tree `Statements.lean` modules; the D12-ledger tokens `P-LONG`/`P-HARNACK` are external provenance and occur nowhere in this worktree (§7).
- **V2 framing corrections** — the `c = 1` propositions already existed in the frozen release (`D7.EvolutionSharp.gibbsTerm_strictAnti_one`, `D4Audit.*_of_one_le`, `strict_step_positive_control`, `Witnesses.sharpWitness_strict_decrease`); the A1 patch therefore adds **no new mathematical content** — its value is aligning the promoted upstream declarations with the already-proved sharp form, which is exactly what the D12 A1 closure rule requires. The new consumer is a consumer *of the restated declaration*, not new mathematical power.
- **New finding F10** (from V4's full-population screen): one self-implication tautology in D7 (`realLineProcedureChain_simplyConnected : P → P`, cone clean, 0 downstream consumers, outside the D13 screen's scope), enumerated in §6; child task `L1-child-self-implication-audit` (outbox) re-decides the whole population with the kernel.

### 14.5 Blocker status after the fourth invocation (four-leg rule)

| blocker | constructed input | downstream consumer | independent rebuild | semantic review | status |
| --- | --- | --- | --- | --- | --- |
| **M1** | frozen baseline + generators + v2 graph + probe sweep (§§1–6, §12) | replay audits, type dumps, declaration ledger consumed by children `L1-C1`/`L1-C4` | **V1** from-scratch rebuild in a new directory (12,361 rows/types identical) **plus** this invocation's same-path clean rebuild (454/454 oleans identical) | **V4** independent semantic/traceability review: semantic content supported, C1–C5 adopted; re-review of corrected text requested | **all four legs now supplied by work outside the authoring context; closure awaits external acceptance (queued `L1-C1`); not self-certified** |
| **A1** | restatement patch + byte-copy, rebuilt and re-audited (§13.1–13.2) | `SharpOnlyConsumers` at `c ≡ 1` (untypeable against the old hypothesis) + D7 sharp layer + `D4Audit` | patched tree built from scratch (§13.2); **V2** re-applied the patch to a fresh copy and ran the probes | **V2** `INDEPENDENT-REVIEW-PASS` with framing corrections (§14.4) | **four legs complete; adoption into the accepted upstream release remains with the integrator (queued `L1-C2`); not self-certified** |
| **P5** | fail-closed gate script + both runs (§13.3) | the gate's exit code is the consumer | **V3** reimplemented the check independently before reading the gate and reproduced it; replayed the patch drift | **V3** independent review: PASS/MATCH, disagreements none | **four legs complete; integrator adoption remains (queued `L1-C4`); not self-certified** |

### 14.6 Queue / result-card / source-hash reconciliation on this snapshot

Re-run **2026-09-11T17:22:06Z** (`baseline/reconcile/queue-card-reconciliation-20260911T172206Z.json`): **139 tasks** — 91 verified, 6 running, 39 queued, 1 paused, 2 blocked; 99 with cards, 40 without; **6 flags** (1 verified-but-card-blocked `D9-adversarial-audit-release`, 5 queue-lagging `TASK_DONE` cards: this task, `L2-upstream-adapters`, `L4-geometric-critical-path`, `SEMREV-L3-analytic-critical-path`, `SEMREV-L4-C4-constant-curvature-rauch`). Exact drift vs the 16:48Z frozen snapshot (`baseline/reconcile/queue-drift-20260911T172206Z.json`): **+4 added, 0 removed, 7 status transitions** (`D13-heatkernel-bridge-d10-d7` running→verified; `L4-C1-geodesic-spray-interface` queued→blocked; `L4-C3-doubling-to-covers` queued→verified; `L4-C4-constant-curvature-rauch` running→verified; `L4-child-d13-semantic-audit` queued→running; `SEMREV-D13-cross-audit-ophis` queued→verified; `SEMREV-L5-topology-audit` running→verified), and **6 card/flag changes** (3 stale queue-lag flags cleared, 3 cards appeared). Source hashes on this snapshot: **0 changed / 0 removed** against all four accepted manifests (V3-independent and gate agreement). No named blocker is self-certified closed; **no Perelman/Poincaré claim is made**.

**Final read-only verification.** After this card, the brief and the MANIFEST were regenerated in the report-then-manifest order, `baseline/tools/verify_baseline.py` was re-run over the frozen evidence; the canonical report is `baseline/logs/verify-baseline.json` (excluded from the MANIFEST by design because it is written last) and reports **29/29 checks PASS, 0 FAIL** — the same 29 checks as §12 plus the fourth-invocation artifacts. The only mid-sequence failure observed in this invocation (28/29) was the expected stale-manifest state before the final regeneration, which is exactly defect F9a's pattern and is why the ordering is enforced.

**TASK_DONE** — M1 baseline deliverable complete and now independently rebuilt/replayed (V1) with an independent semantic review (V4, corrections adopted), the A1 sharp restatement constructed, built, re-audited and independently reviewed (V2), and P5 turned into an executable fail-closed gate independently reproduced (V3); no named blocker self-certified closed, no Poincaré claim.

