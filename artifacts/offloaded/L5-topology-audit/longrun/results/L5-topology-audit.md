# L5-topology-audit — result card

- **Task id:** `L5-topology-audit` · **worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L5-topology-audit`
- **Lane:** auditor · **Verdict:** `TASK_DONE` for the **audit deliverable** — the recheck, replay and
  blocker isolation are complete and independently reproduced. **No mathematical blocker is
  closed by this card**, `M8` remains unbound, `A3`/`I6`/`I7` remain open, and **the Poincaré
  conjecture is not proved, assumed or promoted here.** (If the acceptor requires the *named
  blockers themselves* to be closed for `TASK_DONE`, read this card as `TASK_BLOCKED`; the audit
  work and its evidence are identical either way.)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (`release/lean-toolchain`) · Lake `5.0.0-src+6a10ac8`
  · Lean commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`
- **mathlib:** `7974e751bece493b6ff508039423ca9fa2452fa8` (`release/lake-manifest.json`, unchanged)
- **Generated:** 2026-09-11 23:15–23:5x (+08:00), worktree-local; all evidence under `audit-evidence/`.

## 0. Claims and non-claims

**Claims (machine-checked in this worktree):**

1. `lake build` of `release/` with the pinned toolchain: **exit 0, 9347 jobs**; per-file
   elaboration of **all 464 authored `.lean` files** (including the two root modules `lake build`
   does not reach): **0 failures**.
2. An **independently authored, fail-closed kernel audit** (not a rerun of the D12/D13 audit
   scripts) covers **all 462 buildable modules** of the release in **two collision-free passes**:
   12 136 + 12 091 declarations audited, **0** unexpected project axioms, **0** `sorryAx` cones,
   **0** `native_decide` cones, **0** `unsafe` declarations, **0** unapproved-axiom
   declarations, **0** collection failures. Only `{propext, Classical.choice, Quot.sound}` is
   allowed.
3. The audit is **fail-closed in both directions**: the registered negative-control cluster
   (3 forbidden axioms + 2 consumer theorems) is reported by name with its exact cone; a *fresh*
   forbidden axiom outside the release, and the release's own `negativeControl` axiom audited
   with an empty exclusion list, each make the **same detector exit 1** naming the axiom.
4. Recognition, triangulation and surgery evidence was rechecked against the compiled
   environment: declaration counts, axiom cones, retained downstream consumers, statement shape.
5. Exact remaining blockers `M8`, `A3`, `I6`, `I7` are isolated with reproducible evidence and
   split into 9 independently verifiable child tasks (`comms/outbox/`).
6. Adversarial findings (below) include **conclusion-equivalent assumptions**, a **vacuous
   toy theorem**, an **audit-list coverage drift**, a **non-import-closed union release**, and
   **two root modules outside `lake build`**.

**Not claimed:** no theorem of Ricci flow, surgery, extinction, recognition or Moise
triangulation is proved here; no named blocker is closed; `stage6Target_of_v3hypotheses` is a
conditional implication, **not** the Poincaré conjecture; no upstream/conditional claim is
promoted to a proved claim. No `release/` source file was modified (all 464 sha256 match the
pre-audit baseline byte-for-byte, §4).

---

## 1. Build and authored-file checks

| check | command (cwd = `release/`) | result | evidence |
|---|---|---|---|
| pinned build | `lake build` | **exit 0**, `Build completed successfully (9347 jobs).` | `logs/build-L5-run2.log`, `logs/build-L5-run2.exit`, `logs/build-L5-env.txt` |
| per-file gate | `lake env lean <f>` for every `.lean` under `release/` (12 workers) | **464 files, 0 failures**, 156.5 s | `audit-evidence/perfile-check.json`, `audit-evidence/logs/perfile-check.log` |
| root modules not in `lake build` | `lake env lean ReleaseClaims.lean` / `D6LedgerProbe.lean` | exit 0 each (no olean is produced by `lake build`: neither is in `defaultTargets` nor imported by a built target) | `logs/orphan-ReleaseClaims.log`, `logs/orphan-D6LedgerProbe.log` |

Toolchain/rev capture: `logs/build-L5-env.txt`.

## 2. Fail-closed axiom audit (independent detector)

Detector: `audit-evidence/probes/L5Detector{A,B}.lean` (shared body `_l5_body.lean`, generated
by `tools/l5_generate_probes.py`); positive roots `L5AuditPositive{A,B}.lean`; driver
`tools/l5_run_audit.sh`; assertions `tools/l5_check_audit_log.py`.

| metric | pass A | pass B |
|---|---:|---:|
| modules audited | 448 | 437 |
| declarations audited | 12 136 | 12 091 |
| theorems | 7 483 | 7 464 |
| unexpected project axioms | **0** | **0** |
| `sorryAx` cones | **0** | **0** |
| `native_decide` cones | **0** | **0** |
| `unsafe` declarations | **0** | **0** |
| unapproved-axiom declarations (outside registered cluster) | **0** | **0** |
| `proof_wanted` declarations | **0** | **0** |
| `collectAxioms` failures | **0** | **0** |
| registered negative-control cluster (reported with cones) | 5 | 5 |

Union of the two passes = **all 462 buildable modules** (`modules_missing_from_both = []`,
`union_covers_all = true` in `audit-evidence/audit-summary.json`). Both verdicts
`L5VERDICT PASS`; the post-processor exited 0 with all eight assertions true
(`logs/audit-assertions.log`).

**Negative controls (same detector, empty exclusion list):**

| control | module | expected | observed |
|---|---|---|---|
| fresh axiom outside `release/` | `L5NegControlFresh` (`axiom l5FreshNegControlAxiom : False`) | exit 1 naming it | **exit 1**, `L5PKGFAIL project_axiom l5FreshNegControlAxiom` (`logs/L5Audit-negative-fresh.log`) |
| release control | `Poincare.D12.VolumeIBP.Audit` (`axiom negativeControl`) | exit 1 naming it | **exit 1**, `L5PKGFAIL project_axiom Poincare.D12.VolumeIBP.Audit.negativeControl` (`logs/L5Audit-negative-release.log`) |

Registered cluster (positive run, reported by name and cone):
`d12NegControlBadAxiom`, `d12NegControlBadTheorem`,
`Poincare.D12.VolumeIBP.Audit.negativeControl`,
`Poincare.D13.CriticalPathReview.NegControl.negControlBadAxiom`,
`Poincare.D13.CriticalPathReview.NegControl.negControlBadTheorem`. No other declaration in the
release has a cone outside the three allowed axioms.

## 3. Forbidden-token scan of authored sources

`tools/l5_forbidden_scan.py` (nested-comment/string-aware, independent implementation):
464 files scanned, **14 hits**, all classified:

- `axiom` ×3 — the three intentional negative-control axiom declarations (§2);
- `unsafe` ×10 — all are `.«unsafe»` **pattern matches** inside audit tooling
  (`D6AuditReport.lean`, `Poincare/D13/.../AuditCore|FullAudit|SelfAudit|AxiomAudit`,
  `Poincare/D7/EvolutionSharp/ReleaseAudit.lean`, `ReleaseAudit.lean`), never an `unsafe def`;
- `sorryAx` ×1 — the **name literal** `` ``sorryAx `` used by an audit checker, not a proof.

`sorry`, `admit`, `native_decide`, `proof_wanted`: **0** textual hits. The environment-level
audit (§2) is authoritative and agrees.

## 4. Source hashes and an import-closure defect

- `audit-evidence/source-hashes.txt`: sha256 of all **464** `.lean` files under `release/`
  (excluding `.lake`). Compared against the pre-audit baseline `union-release-hashes.txt`:
  **0 differing `.lean` entries** — this audit modified no release source.
- **Defect (new finding): the union release is not import-closed.** `tools/l5_module_conflicts.py`
  (ilean-based, exact) finds **58 constant names declared by two modules each**, in three pairs:

  | original | duplicate copy | duplicate names |
  |---|---|---:|
  | `Poincare.D7.Bochner.Basic` | `Poincare.D7.Monotonicity.BochnerCertificate` | 19 |
  | `Poincare.D7.Bochner.GradientEstimate` | `Poincare.D7.Monotonicity.BochnerGradientEstimate` | 10 |
  | `Poincare.D7.ConjugateHeat.Basic` | `Poincare.D7.Monotonicity.ConjugateHeatCertificate` | 29 |

  Consequently **no single Lean environment can import every module** (`lake build` passes only
  because no built target imports both sides). 25 modules import the original side, 14 the
  duplicate side, 423 are neutral; the whole-release axiom screen therefore runs as the two
  passes of §2. Evidence: `audit-evidence/collisions.json`, `logs/collisions.log`; child task
  `L5-C8-release-import-closure`.

## 5. Recognition evidence recheck (D12-surgery-recognition)

All cones below are exactly `{propext, Classical.choice, Quot.sound}` unless stated; consumer
counts are retained package consumers recomputed from the compiled environment
(`L5USE`, pass A).

| claim (card) | declaration | cone | consumers | semantic class after recheck |
|---|---|---|---:|---|
| SR-5 gluing of two balls | `D12.SurgeryRecognition.doubleBallHomeoSphere` | allowed | 1 (`sphereConnectSum_homeo_sphere`) | **proved** (unconditional) |
| `𝕊³ # 𝕊³ ≃ₜ 𝕊³` | `...sphereConnectSum_homeo_sphere` | allowed | 1 (`sphereConnectSum_transported`) | **proved** |
| iteration / SR-5 closure | `...iteratedSphereSum_homeo_sphere` | allowed | **0** | **proved but redundant**: it restates the `iteratedSphereSum.sumHomeo` structure field, and `mkV2` consumes that field directly, so the named theorem is bypassed |
| SR-5 constructor | `ConnectedSumDecomposition.mkV2` | allowed | 1 (`stage6Target_of_v2decomposition`) | **constructed bridge** |
| covering recognition | `...finiteFreeOrbit_isQuotientCoveringMap` | allowed | 2 (`SphericalSpaceFormModel.coveringQuotient`, …) | **proved** |
| `coveringTrivial` | `...deckTrivial_of_simplyConnected_quotient` | allowed | 2 (`RemainingRecognitionHypothesesV3.toRemainingV2`, `sphericalPieceRecognition_of_spaceForm`) | **proved** (monodromy; no van Kampen assumed) |
| V2/V3 bridges | `stage6Target_of_v2decomposition` → `_v2hypotheses` → `_v3hypotheses` | allowed | 1 → 1 → **0** (terminal) | **conditional implications** |
| D7 assembly | `Poincare.D7.Recognition.stage6Target_of_certificates` | allowed | 2 | **conditional** |

- **Declaration coverage:** the module set `Poincare.D12.SurgeryRecognition.*` contains **172**
  constants (ilean-exact); the card's fail-closed list has **171** entries. The difference is
  `Poincare.D12.SurgeryRecognition.AntipodalGroup` (an `abbrev`, **empty cone**, 46 consumers) —
  a stale-list drift, not a soundness gap; it **is** covered by L5's environment audit. Finding
  recorded; child task `L5-C1`/`L5-C9` context.
- **van Kampen / SR-4:** the ported cluster is axiom-clean (`HatcherLib.vanKampenMap`,
  `vanKampenMap_surjective`, `vanKampen_ker_eq_normalSubgroup_of_factorizationsConnected`, … all
  in `{propext, Classical.choice, Quot.sound}`, 682 declarations audited) but **no D7/D12/Stage6
  proof module imports `Poincare.VKPort`** — the only importers are D13 audit modules
  (`SnapshotRoot`). SR-4 is therefore **open, with the machinery present and unwired**; child task
  `L5-C9-sr4-vankampen-wire`.

## 6. Triangulation evidence recheck (D12-triangulation-topology, D10-triangulation-low-dim)

- Headline declarations exist and are clean: `diskGlueQuotHomeoSphere` (6 consumers, incl.
  `sphereOfTwoDisks`, `diskGlueQuotHomeoSphere_refl_apply`), `alexanderHomeo` (12 consumers,
  incl. the nondegeneracy `alexanderHomeo_eq_refl_iff`), `sphereOfTwoDisks` (1 consumer:
  `sphereOfTwoDisks_hemisphere_instance`, the non-vacuity instance). Card claim **348/348**
  reconciled exactly: 350 module constants = 348 audited + the 2 negative-control declarations.
- `Poincare.D10.TriangulationLowDim.*` contains **96** constants versus the card's 71-entry audit
  list (25 uncovered, including the `FiniteAbstractSimplicialComplex` structure and API). All 96
  are covered by L5's environment audit with clean cones; the gap is a **coverage-list scope
  difference**, not a violation. `MoiseTriangulationTheorem` is a `def : Prop` (statement-only,
  no inhabitant, no consumer proving it) — Moise remains open.
- Adversarial: `Poincare.Longrun.Topology.stage6Target_of_sphereRecognition` and
  `...stage6Target_of_compactThreeManifold` are flagged by the conclusion-equivalence scan
  (§9a); `realLineProcedureChain_simplyConnected` is a syntactic `P → P` (§9b).

## 7. Surgery evidence recheck and I6 isolation

- `Poincare.D7.SurgeryFlow.*` (107 constants) and `Poincare.Longrun.Surgery.*` are audited clean.
  The I6 interfaces are statement-only and **uninhabited**:
  `NeckAnalysisHypotheses` (induct, 58 consumers — all hypothesis-taking),
  `missingFullNeckAnalysis` (`def : Prop`, 7 consumers),
  `missingExtinctionTheorem` (`def : Prop`, 11 consumers),
  `missingSurgeryFlowTheorem` (`def : Prop`, 4 consumers),
  `Poincare.Longrun.Surgery.ExtinctionTheorem` / `MissingInputs` (structures, 84/34 consumers,
  **no construction anywhere in the source**; source grep in
  `release/Poincare/Longrun/Surgery/` returns only `#print axioms` and consumer theorems).
- **I6 status: OPEN, unchanged.** Exact missing content: (i) a geometric neck analysis deriving
  a separating/cut-and-cap neck from canonical-neighbourhood data
  (`missingFullNeckAnalysis`), (ii) finite-time extinction from a strictly decreasing complexity
  plus finitely many surgeries (`missingExtinctionTheorem`/`ExtinctionTheorem`). Child tasks
  `L5-C3-i6-neck-analysis`, `L5-C4-i6-extinction`.
- Toy lane note: `realLineProcedureChain_simplyConnected : toyLedger.SimplyConnected realLineTop →
  toyLedger.SimplyConnected realLineTop` is vacuous (§9b); it must not be read as surgery
  evidence.

## 8. I7 isolation

- `Poincare.Longrun.Evolution.Bridge`: `FiniteRepresentsContinuousPerelman` (`def : Prop`),
  `FiniteMeshConvergence` (`def : Prop`), `PerelmanEvolutionBoundary` (structure). **No
  inhabitant of any of the three exists** (source grep; all consumers take them as hypotheses).
- Partial model progress exists and is classified as **model**: `Poincare.D7.Limit.HeatMeshConvergence`
  is discharged for a 1-D heat mesh **conditionally on a stability input**
  (`heatMeshConvergence_of_stability`, `finiteMeshConvergence_of_stability`) with 9 consumers,
  including the conjecture-shaped `HeatMeshConvergenceTheorem` (`def : Prop`, no inhabitant).
- **I7 status: OPEN, unchanged**; the `FDissipation = 0` part of the blocker statement predates
  the accepted `D12-EntropyVariation` correction (`FDissipationCorrected`, with a kernel-checked
  model showing the literal derivative and the uncorrected dissipation differ). Child tasks
  `L5-C5-i7-heat-mesh-interface`, `L5-C6-i7-perelman-boundary`.

## 9. Adversarial findings (new, all independently reproducible)

**(a) Conclusion-equivalent assumptions (2).** The statement-shape scan (`L5EQUIV`, syntactic +
definitional) finds hypotheses definitionally equal to the conclusion in
`Poincare.Longrun.Topology.stage6Target_of_sphereRecognition` and
`...stage6Target_of_compactThreeManifold`:
`Nonempty (M ≃ₜ SphereThree) → poincareConjectureTopologicalThree M` (defeq because the target is
a `def : Prop` alias). These are **circular bridges with zero mathematical content**; the first
carries a docstring saying exactly that, and both have **0 package consumers**. They must never
be counted as progress on Poincaré.

**(b) Vacuous toy theorem (1).**
`Poincare.D7.SurgeryFlow.realLineProcedureChain_simplyConnected : P → P` (syntactically
`P → P`) — a degenerate "preservation" statement in the toy lane; **0 consumers**.

**(c) Audit-list drift.** `AntipodalGroup` uncovered by the D12 recognition audit list despite
being used 46 times (§5); D10 list covers 71 of 96 constants (§6).

**(d) Union release not import-closed** (§4).

**(e) `lake build` coverage gap.** `ReleaseClaims.lean` and `D6LedgerProbe.lean` are not built by
`lake build` (not in `defaultTargets`, not imported); they do elaborate with exit 0 and are
covered by the per-file gate.

**(f) A3 mechanical screen (partial, D2/D3).** `audit-evidence/probes/L5A3Screen.lean` screened
596 declarations / 327 theorems / 504 hypotheses of `Poincare.Longrun.CurvatureODE.*`,
`Entropy.*`, `PDE.*`, `Poincare.Stage1.*`: **0** trivial conclusions, **0** `False` hypotheses,
**0** circular hypotheses, **0** tautological `Prop` defs, **0** hypotheses unused in the proof
term, **0** analysis errors. This is a defect screen, **not** a counterexample search: **A3 stays
OPEN** (D2/D3 still lack counterexample searches); child tasks `L5-C1`, `L5-C2`.

## 10. Named-blocker ledger (exact status)

| id | class | status after audit | evidence / exact residual |
|---|---|---|---|
| **M8** | control-plane identifier | **UNBOUND** | no manifest/queue/card entry defines `M8`; the only occurrence in the project is `docs/orchestration_reuse.md` §4 (program milestone "pilot experiment"). Cannot be closed as a mathematical blocker; child task `L5-C7-m8-bind-identifier`. |
| **A3** | audit-residual-finding | **OPEN** | D4 cluster covered (D4 audit + D12 D7-heat counterexample); D2/D3 counterexample searches absent. L5 adds a clean mechanical defect screen (§9f) — not a closure. Child tasks `L5-C1`, `L5-C2`. |
| **I6** | explicit-unproved-interface | **OPEN** | `NeckAnalysisHypotheses`/`missingFullNeckAnalysis`/`missingExtinctionTheorem`/`missingSurgeryFlowTheorem`/`Longrun.Surgery.ExtinctionTheorem`/`MissingInputs` all statement-only/uninhabited (§7). Child tasks `L5-C3`, `L5-C4`. |
| **I7** | explicit-unproved-interface | **OPEN** | `FiniteMeshConvergence`/`FiniteRepresentsContinuousPerelman`/`PerelmanEvolutionBoundary` uninhabited (§8); only the 1-D heat-mesh model is conditionally proved. Child tasks `L5-C5`, `L5-C6`. |

No named blocker is closed: none of the four has the constructed input + downstream consumer +
independent rebuild + semantic review that closure would require.

## 11. Outbox child tasks

`comms/outbox/` (JSON; each has `id`, `group_id`, `parent_node`, `deps`, `lane`, `acceptance`,
`host_pool`, `requires_lean`), indexed in `comms/outbox-index.json`:

`L5-C1-a3-d2-counterexample` · `L5-C2-a3-d3-counterexample` · `L5-C3-i6-neck-analysis` ·
`L5-C4-i6-extinction` · `L5-C5-i7-heat-mesh-interface` · `L5-C6-i7-perelman-boundary` ·
`L5-C7-m8-bind-identifier` · `L5-C8-release-import-closure` · `L5-C9-sr4-vankampen-wire`
(the dispatcher imported all nine; index at `comms/outbox-index.json`).

Per the hot-dispatch instruction `comms/inbox/primary-hot-1789141005744.md`, three further
`L5-child-` tasks were created with `max_hours` and one dedicated worktree each:
`L5-child-moise-geometric-realization` (Moise/geometric-realization frontier),
`L5-child-recognition-spaceform` (the last `spaceForm` hypothesis of the V3 bridge),
`L5-child-surgery-nontrivial-datum` (a non-vacuous surgery-chain instance replacing the toy
`P → P` witness). They were schema-validated against the imported tasks and have since been imported by the dispatcher (12/12 task files in `comms/outbox/`).

## 12. Reproduce

```bash
cd <worktree>
bash audit-evidence/tools/l5_run_audit.sh          # ~50 s: collisions, 2-pass axiom audit, controls, scan, hashes, assertions
python3 audit-evidence/tools/l5_perfile_check.py release audit-evidence/perfile-check.json 12   # ~160 s, 464 files
python3 audit-evidence/tools/l5_module_conflicts.py release audit-evidence/collisions.json
cd release && lake build                            # exit 0 (9347 jobs)
cd release && LEAN_PATH="$(lake env printenv LEAN_PATH):$(realpath ../audit-evidence/probes)" \
  lean -R "$(realpath ../audit-evidence/probes)" ../audit-evidence/probes/L5A3Screen.lean
python3 audit-evidence/tools/l5_verify_card_claims.py .   # self-check of this card's numbers vs the evidence
```

## 13. Artifacts

`audit-evidence/` : `audit-summary.json`, `perfile-check.json`, `collisions.json`,
`forbidden-scan.json`, `source-hashes.txt`, `union-release-hashes.txt` (pre-audit baseline),
`probes/` (detector A/B, positive roots, A3 screen, shared body), `negcontrol/` (fresh axiom +
two negative roots), `tools/` (6 scripts incl. the card self-check), `logs/` (all raw logs incl.
both negative-control failures and the final driver re-run), `checkpoint.json` (worktree root),
`comms/outbox/` (9 imported child tasks + 3 `L5-child-` tasks awaiting dispatch) + `comms/outbox-index.json`, this card and its `.json`
twin.

**Verdict: `TASK_DONE` for the audit (recheck + replay + blocker isolation complete, independently
reproducible). No mathematical blocker closed; M8 unbound; A3/I6/I7 open; no promotion of
conditional recognition to Poincaré; Poincaré not proved.**

TASK_DONE
