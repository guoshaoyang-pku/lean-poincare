# SEMREV-L5-topology-audit — independent semantic review card

- **Task id:** `SEMREV-L5-topology-audit` · **lane:** independent reviewer (semantic review of a leader audit)
- **Review worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/SEMREV-L5-topology-audit`
- **Parent artifact reviewed:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L5-topology-audit`
- **Parent card hashes (recorded before and re-checked after the review):**
  - `longrun/results/L5-topology-audit.md` sha256 `bab8e022a3d2828a4ae3945093ec6235635c576561d5bd41644191e2a2acc213`
  - `longrun/results/L5-topology-audit.json` sha256 `bd9d975964db2ec166fd5f7a26b4db5fb6cc20cad1a767e8fcc2aadec2d1feea`
  - `checkpoint.json` sha256 `f863293deb11299e5df67735c660aaeb1fa0f1a037e1d6c387a5265d64bdd192`
  - `audit-evidence/{audit-summary,collisions,forbidden-scan,perfile-check}.json` unchanged (hashes in `review/evidence/hash-replay.json`)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (direct toolchain binary) · mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`
- **Replay environment:** reviewer-authored probes in this worktree, elaborated against the **parent release's 462 prebuilt oleans** (read-only `LEAN_PATH`); no write ever touched the parent artifact.
- **Generated:** 2026-09-12 (worktree-local). All reviewer evidence under `review/`.

## 0. Verdict

- **Review verdict: `TASK_DONE`** — the independent semantic review is complete and reproducible.
  This card is a review of an audit; **it is not a Poincaré proof and closes no mathematical blocker**.
- **Parent `L5-topology-audit` verdict: confirmed, subject to corrections C1–C3 (§8).**
  Every headline number, cone, consumer count, hash and blocker status in the L5 card was
  independently reproduced from sources/oleans — except the `lake build` job count, which was
  verified from the recorded exit-0 logs (`EXIT=0`, `FINAL_BUILD_EXIT=0`, "9347 jobs") together
  with an independent 464-file elaboration replay rather than by rebuilding inside the parent
  artifact. Three L5 *wording claims* are over-strong or imprecise and are corrected below; none
  of them changes a mathematical status, promotes anything, or closes a blocker.
- **Exact remaining blockers: `M8` UNBOUND, `A3` OPEN, `I6` OPEN, `I7` OPEN.**
  No blocker is closed by the L5 audit or by this review. `poincare_proved = false`,
  `promotions = []` — confirmed against the parent card/JSON and the release artifacts.
- **Dispatcher bookkeeping (repair attempts 1–2, §12–§13, no mathematical content).** The gate's
  cached `00:31` transport failure was cleared from the dispatcher state directory at
  `2026-09-12T01:07:52+0800`; the release package now builds (`EXIT 0`, 8946 jobs) and its 63-file
  gate stage replays **63/63 exit 0**, so the next dispatcher tick re-runs the gate green. This
  changes no verdict below.

## 1. Method (what was actually replayed)

| replay | reviewer tool | result |
|---|---|---|
| exact types of all cited declarations | `review/tools/gen_probe.py` → `SemRevTypes.lean` | 51/51 resolved, exact types in `review/logs/SemRevTypes.log` |
| printed definitions (semantic class) | `SemRevShapes.lean` | `review/logs/SemRevShapes.log` |
| fail-closed axiom audit of the cited declarations | reviewer's own `run_cmd` detector `SemRevAxioms.lean` | **PASS** (`review/logs/SemRevAxioms.log`) |
| whole-release fail-closed audit | own detector over two collision-free passes, `review/tools/gen_passes.py` | pass A 12 136 decls / pass B 12 091 decls, 0 unexpected axioms (`PassA.log`, `PassB.log`) |
| negative controls of the reviewer's detector | fresh `axiom`, `sorry`, `native_decide` outside the release | detector exits **1**, naming all four forbidden cones (`SemRevNegControl.log`) |
| per-file elaboration of the release | own 12-worker `lean` replay, `review/tools/perfile_replay.py` | **464 files, 0 failures**, 151.0 s (`logs/perfile-replay.json`) |
| collisions / import closure / consumers | own `.ilean` parser `review/tools/ilean_scan.py` | 58 duplicate names in 3 pairs; 462/462 covered by 2 passes (`evidence/collisions-replay.json`) |
| environment-level consumer counts | own `getUsedConstants` scan in both passes | reproduces **every** L5 consumer number exactly (`evidence/semantic-class-table.md`) |
| forbidden-token scan | own comment/string-aware lexer `review/tools/forbidden_scan.py` | sorry 0, admit 0, axiom 3, unsafe 10, native_decide 0, proof_wanted 0 (`logs/forbidden-replay.log`) |
| source hashes | recomputed sha256 of all 464 `.lean` files | 464/464 identical to L5's list and to the pre-audit baseline (`evidence/hash-replay.json`) |
| A3 defect screen | replayed `L5A3Screen.lean` | summary lines **byte-identical** to L5's log (`logs/L5A3Screen-replay.log`) |
| conclusion-equivalence scan | own whole-package implementation | 3 hits in the audited lane (matches L5) + 6 outside it (correction C3) |
| kernel-checked inhabitant witnesses | `SemRevInhabitants.lean` | refutes L5 §8 "no inhabitant" for two I7 predicates (correction C1) |

## 2. Exact types and domains (independent replay)

All cones below are kernel-computed by the reviewer; `env consumers` is the reviewer's
environment-level count (identical method to L5's, independently implemented). Full table:
`review/evidence/semantic-class-table.md` (51 rows).

### 2.1 Recognition / end-game bridges

| declaration | exact kind and domain (replayed) | cone | env consumers | review class |
|---|---|---|---:|---|
| `Poincare.D12.SurgeryRecognition.doubleBallHomeoSphere` | `def : DoubleBall ≃ₜ S3` (unconditional homeomorphism) | allowed | 1 (`sphereConnectSum_homeo_sphere`) | proved-unconditional |
| `...sphereConnectSum_homeo_sphere` | `def : Nonempty (sphereConnectSum.Carrier ≃ₜ S3)` | allowed | 1 (`sphereConnectSum_transported`) | proved-unconditional |
| `...sphereConnectSum_transported` | `def : (X ≃ₜ S3) → (Y ≃ₜ S3) → Nonempty (connectedSum … ≃ₜ S3)` | allowed | 3 | proved-unconditional |
| `...iteratedSphereSum_homeo_sphere` | `theorem (pieces) (h : ∀ P ∈ pieces, Nonempty (P ≃ₜ S3)) : Nonempty ((iteratedSphereSum pieces h).sum ≃ₜ S3)`; proof is the structure field `sumHomeo` | allowed | **0** | proved-but-bypassed (confirmed: `mkV2` uses `D.sumHomeo` and the `iteratedSphereSum` field, not the named theorem) |
| `...ConnectedSumDecomposition.mkV2` | `def (D : ConnectedSumDecompositionV2 X pieces) (vanKampen) : D7.Recognition.ConnectedSumDecomposition X pieces` | allowed | 1 | constructed-bridge |
| `...finiteFreeOrbit_isQuotientCoveringMap` | `theorem (Γ) [Group Γ] [Fintype Γ] [MulAction Γ S3] [ContinuousConstSMul …] (free) : IsQuotientCoveringMap (orbitRel quotient) Γ` | allowed | 2 | proved-unconditional |
| `...deckTrivial_of_simplyConnected_quotient` | `theorem (M : SphericalSpaceFormModel) [SimplyConnectedSpace M.quotient.Carrier] : Subsingleton M.Γ` (monodromy proof; no van Kampen assumed) | allowed | 2 | proved-unconditional |
| `...stage6Target_of_v2decomposition` | conditional: `CompactSpace/T2Space/ChartedSpace ℝ³/SimplyConnectedSpace` + `ExtinctionCertificate X` + `ConnectedSumDecompositionV2 X E.pieces` + vanKampen + `CanonicalNeighborhoodInput` + `SphericalPieceRecognition` ⟹ `Stage6.poincareConjectureTopologicalThree X` | allowed | 1 (`_v2hypotheses`) | conditional-implication |
| `...stage6Target_of_v2hypotheses` | same hypotheses with `RemainingRecognitionHypothesesV2` (vanKampen + spaceForm + coveringTrivial) | allowed | 1 (`_v3hypotheses`) | conditional-implication |
| `...stage6Target_of_v3hypotheses` | as above with `RemainingRecognitionHypothesesV3` (vanKampen + spaceForm) | allowed | **0** (terminal) | conditional-implication, terminal |
| `Poincare.D7.Recognition.stage6Target_of_certificates` | conditional: `ExtinctionCertificate` + `CanonicalNeighborhoodInput` + `SphericalPieceRecognition` ⟹ Stage6 target | allowed | 2 | conditional-implication |
| `Poincare.D12.SurgeryRecognition.AntipodalGroup` | `abbrev := Multiplicative (ZMod 2)` | **empty** | **46** | abbrev, used 46× |
| `HatcherLib.vanKampenMap` / `_surjective` / `vanKampen_ker_eq_normalSubgroup_of_factorizationsConnected` | ported upstream cluster | allowed | — | upstream-proved; **only** `Poincare.D13.IntegratedAudit.SnapshotRoot` imports `Poincare.VKPort` (verified from `.ilean`) |

**Verdict 2.1: MATCH.** No cited recognition declaration is missing, mis-typed or mis-classified
in a way that promotes it; the V2→V3 chain is a chain of conditional implications ending in a
0-consumer terminal theorem.

### 2.2 Triangulation

| declaration | exact kind and domain | cone | env consumers | review class |
|---|---|---|---:|---|
| `alexanderHomeo` | `def (n : ℕ) (h : Sphere n ≃ₜ Sphere n) : Disk (n+1) ≃ₜ Disk (n+1)` | allowed | 12 | proved-unconditional |
| `alexanderHomeo_eq_refl_iff` | `theorem (n) (h) : alexanderHomeo n h = refl ↔ h = refl` | allowed | 0 | proved, unconsumed |
| `diskGlueQuotHomeoSphere` | `def (n) (h : Sphere n ≃ₜ Sphere n) : DiskGlueQuot n h ≃ₜ Sphere (n+1)` | allowed | 6 | proved-unconditional |
| `sphereOfTwoDisks` | `def (n) {X} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B) (closed, cover, disk homeos) : …` | allowed | 1 | proved-unconditional |
| `sphereOfTwoDisks_hemisphere_instance` | non-vacuity instance of the above | allowed | 1 | proved-unconditional (non-vacuity) |
| `Poincare.D10.TriangulationLowDim.MoiseTriangulationTheorem` | `def : Prop` (`∀ M, … → AdmitsFiniteTriangulation M`); **no declaration concludes in it** (whole-release inhabitant scan) | allowed (definition body only) | — | statement-only Prop |
| `FiniteAbstractSimplicialComplex` | structure | allowed | — | structure |

**Verdict 2.2: MATCH.** `MoiseTriangulationTheorem` is a statement-only `def : Prop`; no
inhabitant exists anywhere in the 462-module release (scan over both passes). The card's
localised-glue numbers reproduce exactly (see §5).

### 2.3 I6 / I7 interfaces and adversarial findings

| declaration | exact kind | cone | env consumers | review class |
|---|---|---|---:|---|
| `NeckAnalysisHypotheses` | structure (Type) with opaque Prop fields | allowed | **58** | statement-only interface |
| `missingFullNeckAnalysis` | `def … : Prop` (existential over the above) | allowed | **7** | statement-only Prop |
| `missingExtinctionTheorem` | `def … : Prop` | **empty** | **11** | statement-only Prop |
| `missingSurgeryFlowTheorem` | `def … : Prop` | allowed | **4** | statement-only Prop |
| `Poincare.Longrun.Surgery.ExtinctionTheorem` | structure (Type) | **empty** | **84** | statement-only interface |
| `Poincare.Longrun.Surgery.MissingInputs` | structure (Type) | **empty** | **34** | statement-only interface |
| `Poincare.Longrun.Evolution.FiniteRepresentsContinuousPerelman` | `def … : Prop` | allowed | 25 | **inhabited at parameters** (correction C1) |
| `Poincare.Longrun.Evolution.FiniteMeshConvergence` | `def … : Prop` | allowed | 2 | **inhabited at parameters** (correction C1) |
| `Poincare.Longrun.Evolution.PerelmanEvolutionBoundary` | `structure : Prop` | allowed | 17 | statement-only interface (no construction found) |
| `Poincare.Longrun.Evolution.ContinuousPerelmanFMonotonicity` | `def … : Prop` | allowed | — | **inhabited at toy parameters** (correction C1) |
| `Poincare.D7.Limit.HeatMeshConvergence` | `def … : Prop` | allowed | **9** | model-conditional conclusion |
| `Poincare.D7.Limit.HeatMeshConvergenceTheorem` | `def … : Prop` | allowed | 2 | statement-only Prop |
| `Poincare.Longrun.Topology.stage6Target_of_sphereRecognition` | `theorem`, hypothesis literally `Nonempty (M ≃ₜ SphereThree)` and conclusion the definitionally identical alias | allowed | **0** | circular, conclusion-equivalent |
| `Poincare.Longrun.Topology.stage6Target_of_compactThreeManifold` | same, with an unused `_h : CompactThreeManifold M` argument | allowed | **0** | circular, conclusion-equivalent |
| `Poincare.D7.SurgeryFlow.realLineProcedureChain_simplyConnected` | `theorem : toyLedger.SimplyConnected realLineTop → toyLedger.SimplyConnected realLineTop` | allowed | **0** | vacuous `P → P` |

**Verdict 2.3: MATCH with correction C1.** The two conclusion-equivalent wrappers and the
vacuous toy theorem are exactly as the L5 card describes (kernel-checked in
`review/logs/SemRevEquivDebug.log`: `defeq=true` between hypothesis and conclusion). The
blanket "no inhabitant of any of the three" sentence in L5 §8 is over-strong (C1).

## 3. Fail-closed axiom audit (only `propext`, `Classical.choice`, `Quot.sound`)

**Cited declarations (reviewer detector, `SemRevAxioms.log`).** 51 cited declarations:
19 theorems, 22 defs; **0 missing, 0 `unsafe`, 0 `partial`, 0 `sorryAx`, 0 unapproved axiom
cones**; 41 cones are exactly `{propext, Classical.choice, Quot.sound}`, 5 are empty
(`AntipodalGroup`, `missingExtinctionTheorem`, `ExtinctionData`, `Longrun.Surgery.ExtinctionTheorem`,
`MissingInputs`), and 5 are the registered negative-control cones (each carrying exactly its one
forbidden axiom). The detector **fails to compile** on a missing declaration, an `unsafe`/`partial`
declaration, `sorryAx`, or any axiom outside the allow-list.

**Whole release (reviewer detector, own two-pass split).**

| metric | pass A | pass B | L5 pass A/B | match |
|---|---:|---:|---|---|
| modules | 448 | 437 | 448/437 | ✅ |
| declarations | 12 136 | 12 091 | 12 136/12 091 | ✅ |
| theorems | 7 483 | 7 464 | 7 483/7 464 | ✅ |
| registered project axiom declarations (excused by name) | 3 | 3 | 3/3 | ✅ |
| unexpected axioms | **0** | **0** | 0/0 | ✅ |
| `unsafe` | **0** | **0** | 0/0 | ✅ |
| `partial` (reported separately) | 22 | 19 | 22/19 | ✅ |
| `sorryAx` cones | **0** | **0** | 0/0 | ✅ |
| `native_decide` cones | **0** | **0** | 0/0 | ✅ |
| `proof_wanted` | **0** | **0** | 0/0 | ✅ |
| unapproved-axiom declarations (unexpected) | **0** | **0** | 0/0 | ✅ |
| `collectAxioms` failures | **0** | **0** | 0/0 | ✅ |

**Negative controls of the reviewer's own detector.** A fresh module outside the release with
`axiom semrevFreshBadAxiom : False`, its consumer theorem, a `sorry` proof and a `native_decide`
proof makes the detector exit **1**, naming `semrevFreshBadAxiom`, `sorryAx` and the generated
native axiom (`review/logs/SemRevNegControl.log`). Both L5 negative-control runs (`exit 1`,
naming `l5FreshNegControlAxiom` and `Poincare.D12.VolumeIBP.Audit.negativeControl`) were re-read
and are consistent with their card.

**Forbidden-token scan (reviewer lexer).** 464 files: `sorry` 0, `admit` 0, `native_decide` 0,
`proof_wanted` 0, `axiom` 3 (the registered controls), `unsafe` 10 (all `.«unsafe»` pattern
matches in audit tooling). `sorryAx` occurs 14× as an audit-tooling *name literal*
(`"sorryAx".toName` / `` `sorryAx `` / `#print axioms … sorryAxiom`), never as a proof term;
L5 counted the double-backtick literal only (×1). No forbidden construct reaches a proof.

**Note N1 (`partial` declarations).** L5's detector records 22/19 `partial` declarations but the
card never mentions them. Reviewer check: Lean 4.34 refuses `partial` definitions whose return
type is not inhabited and `partial` functions do not reduce definitionally (verified with a
scratch probe: `partial def badLoop (n) : False` is rejected; `badBool 0 = true` is not `rfl`).
The 22 partials therefore cannot forge a proof of an uninhabited proposition and do not weaken
the "0 unsafe / 0 sorry" trust claim. Non-issue, recorded for completeness.

## 4. Blocker ledger — per-blocker verdicts

| id | L5 status | reviewer verdict | independent evidence |
|---|---|---|---|
| **M8** | UNBOUND (control-plane identifier) | **UNBOUND — confirmed; evidence sentence corrected (C2)** | No manifest/blocker/queue entry defines M8; `docs/orchestration_reuse.md` §4 uses M8 for the "pilot experiment" program milestone. However M8 *does* occur in `longrun/leader-registry.json` (and `longrun/longrun/leader-registry.json`) as a `named_blockers` entry of the L5 task itself, in `longrun/prompts/L5-topology-audit.md:19` and its state copies, and in the L5-created child task `L5-C7-m8-bind-identifier` (`parent_node: M8`). All are control-plane references without a definition/status/evidence record, so "not bound to a mathematical blocker" holds. |
| **A3** | OPEN (D2/D3 counterexample searches absent) | **OPEN — confirmed** | `manifest/blockers.json` A3: "the adversarial audit only covers the D4 evolution cluster". The only counterexample modules are `Audit/CounterexampleAudit.lean` (D4) plus the D12 D7-heat counterexample; `results/D12-semantic-ledger.md` states "D2/D3 counterexample audits remain absent". The reviewer replayed L5's mechanical screen: 596 declarations, 327 theorems, 504 hypotheses, **0** trivial conclusions / false hypotheses / circular hypotheses / tautological Prop defs / unused hypotheses / errors, verdict `SCREEN_COMPLETE — no counterexample search; A3 remains open` (summary lines byte-identical to L5's log). A screen is not a closure. |
| **I6** | OPEN (neck analysis + extinction statement-only) | **OPEN — confirmed** | `NeckAnalysisHypotheses` (58 consumers), `missingFullNeckAnalysis` (7), `missingExtinctionTheorem` (11), `missingSurgeryFlowTheorem` (4), `Longrun.Surgery.ExtinctionTheorem` (84), `MissingInputs` (34): all statement-only; the whole-release inhabitant scan finds no declaration proving any of them (only structure projections/constructors). The D3/D6 conditional reductions (`surgeryFlow_consequences*`, `ExtinctionData.extinct_of_skeleton`) take the missing inputs as hypotheses. |
| **I7** | OPEN (mesh limit / Perelman boundary uninhabited) | **OPEN — confirmed; §8 wording corrected (C1)** | `PerelmanEvolutionBoundary` has no construction; the general `FiniteMeshConvergence`/`FiniteRepresentsContinuousPerelman` statements for a Perelman mesh are not discharged; the only mesh result is the 1-D conditional model (`HeatMeshConvergence`, 9 consumers) plus degenerate D4 witnesses. The `FDissipation = 0` wording in the old blocker text is indeed superseded by the accepted D12 `FDissipationCorrected` correction (checked in `manifest/blockers.json` vs the D12 entropy-variation card). |

**No blocker is closed; `blockers_closed = []` is correct.**

## 5. Downstream-use replay (consumer counts)

Reviewer environment-level counts (own implementation) vs the L5 card; **all match**:

| declaration | L5 card | reviewer |
|---|---:|---:|
| `doubleBallHomeoSphere` | 1 | 1 |
| `sphereConnectSum_homeo_sphere` | 1 | 1 |
| `iteratedSphereSum_homeo_sphere` | 0 | 0 |
| `mkV2` | 1 | 1 |
| `finiteFreeOrbit_isQuotientCoveringMap` | 2 | 2 |
| `deckTrivial_of_simplyConnected_quotient` | 2 | 2 |
| `stage6Target_of_v2decomposition` → `_v2hypotheses` → `_v3hypotheses` | 1 → 1 → 0 | 1 → 1 → 0 |
| `stage6Target_of_certificates` | 2 | 2 |
| `diskGlueQuotHomeoSphere` | 6 | 6 |
| `alexanderHomeo` | 12 | 12 |
| `sphereOfTwoDisks` | 1 | 1 |
| `realLineProcedureChain_simplyConnected` | 0 | 0 |
| `stage6Target_of_sphereRecognition` / `_compactThreeManifold` | 0 / 0 | 0 / 0 |
| `HeatMeshConvergence` | 9 | 9 |
| I6 interfaces: 58 / 7 / 11 / 4 / 84 / 34 | as listed | 58 / 7 / 11 / 4 / 84 / 34 |
| `AntipodalGroup` | 46 | 46 |

**Import-closure defect — confirmed independently:** `.ilean` scan of 462 modules finds
**58** duplicate declaration names in exactly **3** module pairs
(`D7.Bochner.Basic`↔`D7.Monotonicity.BochnerCertificate` 20; `D7.Bochner.GradientEstimate`↔
`D7.Monotonicity.BochnerGradientEstimate` 10; `D7.ConjugateHeat.Basic`↔
`D7.Monotonicity.ConjugateHeatCertificate` 28), with 25 modules on side A, 14 on side B and 423
neutral; the reviewer's own split is A=448, B=437, union=**462/462**. No single Lean environment
can import every module.

**Audit-list drift — confirmed independently:** `Poincare.D12.SurgeryRecognition.*` contains
**172** module constants vs the D12 card's 171-entry audit list (`AntipodalGroup` absent from the
card, 0 occurrences); `Poincare.D10.TriangulationLowDim.*` contains **96** vs the D10 card's 71;
`Poincare.D12.TriangulationTopology.*` contains **350** = 348 audited + the 2 negative-control
declarations, as the card says.

## 6. No-promotion verification

- The parent card/JSON state `poincare_proved: false`, `promotions: []`,
  `verdict_scope: "…; NO mathematical blocker closed; Poincare not proved"`, and §0 explicitly
  classifies `stage6Target_of_v3hypotheses` as a conditional implication, "not the Poincaré
  conjecture". **Confirmed by the replayed types**: every Stage6-target-producing theorem takes
  `ExtinctionCertificate` + `CanonicalNeighborhoodInput` (+ `SphericalPieceRecognition` or
  `RemainingRecognitionHypothesesV3`) as explicit hypotheses; the only hypothesis-free routes
  are the two conclusion-equivalent wrappers, which are `P → P`.
- Downstream artifacts checked: `manifest/blockers.json` (I6/I7/A3 open, M8 absent),
  `results/D3-kappa-ledger.md` (lists the bridge as a statement, §5 "exact missing theorems"),
  `results/D12-semantic-ledger.md` ("conditional assembly, not a sphere-recognition theorem";
  D2/D3 counterexample audits absent), `manifest/verified-declarations.json` (per-declaration
  cones only), `release/ReleaseClaims.lean` (only `#check` probes). **No artifact promotes a
  conditional, model or statement-only claim to a proved one.**

## 7. Source hashes and artifact preservation

- 464/464 release `.lean` files recomputed: **0** mismatches against
  `audit-evidence/source-hashes.txt`; **0** differences between that list and the pre-audit
  baseline `audit-evidence/union-release-hashes.txt`; the reviewer added no file.
  Release tree digest over `(path, sha256)` pairs:
  `d3954cf9830a96d7dd87d16414d63dc6214348013655c129d17c601efbac30f2`.
- 462/464 files have a compiled `.olean`; the 2 without are exactly `ReleaseClaims.lean` and
  `D6LedgerProbe.lean` (not in `defaultTargets`, not imported anywhere, verified by grep) —
  the L5 "outside `lake build`" finding is correct. **0 oleans are older than their source**
  (freshness check), and the reviewer re-elaborated **all 464 sources with 0 failures** in 151 s
  (L5: 464, 0 failures, 156.5 s).
- Parent-artifact preservation: card, JSON, checkpoint, research brief, `audit-summary.json`,
  `collisions.json`, `forbidden-scan.json`, `perfile-check.json` re-hashed after the review —
  **all byte-identical**.

## 8. Findings and corrections to the parent card

**C1 (substantive wording; I7 status unchanged).** L5 §8 (and the research brief table) states
*"No inhabitant of any of the three exists"* for `FiniteMeshConvergence`,
`FiniteRepresentsContinuousPerelman`, `PerelmanEvolutionBoundary`, and calls
`ContinuousPerelmanFMonotonicity` statement-only with no inhabitant. This is **false as written**
for two of the three (and for `ContinuousPerelmanFMonotonicity`):
- `D4Audit.finiteMeshConvergence_nonvacuous : FiniteMeshConvergence (fun n ↦ 1/(n+1)) (fun _ _ ↦ 0) (fun _ ↦ 0)`
  is a kernel-checked inhabitant at those parameters (and `Poincare.D7.Limit.finiteMeshConvergence_of_stability`
  proves it from explicit stability hypotheses).
- `(D4Audit.perelmanApproximation_nonvacuous F hc ev).some.identification` is a kernel-checked
  inhabitant of `FiniteRepresentsContinuousPerelman` at the D4 parameters; the release's own
  docstring notes this witness "carries no continuous content".
- `D4Audit.transfer_nonvacuous` is a kernel-checked inhabitant of `ContinuousPerelmanFMonotonicity`
  at the D4 toy parameters.
Reviewer witnesses: `review/probes/SemRevInhabitants.lean` (compiles, exit 0;
`review/logs/SemRevInhabitants.log`). The **correct** statement is: the *general* I7 interfaces
are not discharged — no unconditional `FiniteMeshConvergence`/`FiniteRepresentsContinuousPerelman`
for a Perelman mesh, and `PerelmanEvolutionBoundary` has no construction — so **I7 stays OPEN**.
The L5 card's own §8 status line ("only the 1-D heat-mesh model is conditionally proved") is
accurate; only the blanket "no inhabitant" sentence is wrong.

**C2 (evidence-scope error; M8 status unchanged).** L5 §10 says M8's "only occurrence in the
project is `docs/orchestration_reuse.md` §4". M8 also occurs in the control plane:
`longrun/leader-registry.json` and `longrun/longrun/leader-registry.json` (`named_blockers` of
L5-topology-audit), `longrun/prompts/L5-topology-audit.md:19`, `longrun/state/L5-topology-audit/prompt.md:19`,
`longrun/longrun/prompts/L5-topology-audit.md:19`, plus L5's own card/checkpoint/child task.
None of these *defines* M8, so **UNBOUND is correct**, but the occurrence claim should be
restricted to "the only non-control-plane occurrence" or corrected outright.

**C3 (finding scope; the two flagged bridges are real).** L5 §9 reports the conclusion-equivalence
scan without stating that the detector annotated only the topology lane (3 220 declarations).
The reviewer's whole-package rerun finds **9** hits: the same 3 in the lane
(`stage6Target_of_sphereRecognition`, `stage6Target_of_compactThreeManifold`,
`realLineProcedureChain_simplyConnected`) plus 6 outside it — `D9.DeTurck` toy theorems ×3,
`D7.Compactness.cheegerGromov_of_ghSubsequence` (hypothesis is literally the unfolded conclusion,
two hypotheses unused), `D10.MaximumPrincipleRN.weak_maximum_principle_const` (`hcM : c ≤ M` is
the conclusion after beta), `D11.MaximumPrincipleTensor.PositivityPreserving.id` (identity
instance). Verified in `review/logs/SemRevEquivDebug.log`. The two Poincaré wrappers remain the
important instance; the defect class is larger than the card's scope suggests.

**N2 (metric definition; no error).** L5's forbidden scan reports `sorryAx` ×1 (it matches the
double-backtick name literal); the reviewer's lexer finds 14 textual `sorryAx` name-literal
occurrences (all audit tooling, none a proof). Both are correct under their token definitions.

**N3 (confirmed but worth stating).** The "proved" layer is small and genuinely consumed:
ball-gluing/Alexander/two-disks lemmas (1–12 consumers, including non-degeneracy and
non-vacuity instances) and the covering/monodromy deck-triviality theorems (2 consumers each).
The named theorem `iteratedSphereSum_homeo_sphere` really is bypassed by `mkV2` (source-checked),
and SR-4 van Kampen really is unwired (the only importer of `Poincare.VKPort` is
`Poincare.D13.IntegratedAudit.SnapshotRoot`).

## 9. Exact remaining blockers (what a builder must supply)

- **I6(a) neck analysis.** A geometric construction that turns canonical-neighbourhood data
  into a separating certified neck and an admissible cut-and-cap realizing the D3 datum
  (`missingFullNeckAnalysis`, `NeckAnalysisHypotheses`), with the opaque Prop fields discharged.
- **I6(b) extinction.** Finite-time extinction from a strictly decreasing `ℕ`-complexity with
  finitely many surgeries, plus the terminal-3-sphere identification (`missingExtinctionTheorem`,
  `Longrun.Surgery.ExtinctionTheorem`, `MissingInputs`).
- **I7(a) mesh limit.** A general vanishing-error/stability input discharging
  `FiniteMeshConvergence` for the Perelman mesh, and a non-degenerate inhabitant (or proof) of
  `FiniteRepresentsContinuousPerelman` for the continuous entropy family.
- **I7(b) Perelman boundary.** A construction of `PerelmanEvolutionBoundary` (needs the D2
  tensor realization and the D3 Bochner/IBP/regularity bridge), replacing the superseded
  `FDissipation = 0` wording with `FDissipationCorrected`.
- **A3.** Counterexample searches over D2 (`Poincare.Longrun.CurvatureODE.*`) and D3
  (`Entropy.*`, `PDE.*`); the mechanical screen is not a counterexample search.
- **M8.** A canonical control-plane binding of the identifier M8 (or removal/renaming), which is
  an integration action, not mathematics.
- **SR-4 / Moise / recognition.** van Kampen wiring for connected sums; the spherical space-form
  theorem (`spaceForm` is the last hypothesis of the V3 bridge); Moise triangulation
  (`MoiseTriangulationTheorem` has no inhabitant). Poincaré remains unproved.

## 10. Evidence index and reproduction

Evidence (all under `review/`): `logs/SemRevTypes.log`, `logs/SemRevShapes.log`,
`logs/SemRevAxioms.log`, `logs/PassA.log`, `logs/PassB.log`, `logs/SemRevNegControl.log`,
`logs/SemRevInhabitants.log`, `logs/SemRevEquivDebug.log`, `logs/perfile-replay.json`,
`logs/forbidden-replay.log`, `logs/L5A3Screen-replay.log`;
`evidence/cited-declarations.json`, `evidence/semantic-class-table.{json,md}`,
`evidence/collisions-replay.json`, `evidence/consumers-replay.json`, `evidence/passes.json`,
`evidence/hash-replay.json`, `evidence/forbidden-scan-replay.json`; tools in `review/tools/`.
Checkpoint with per-file sha256 of every evidence artifact: `checkpoint.json` (worktree root).

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
LEANBIN=$ELAN_HOME/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean
export LEAN_PATH="$(cat review/evidence/leanpath.txt)"     # parent release oleans + shared mathlib
$LEANBIN -R review review/probes/SemRevTypes.lean          # 51 exact types
$LEANBIN -R review review/probes/SemRevAxioms.lean         # fail-closed cited-declaration audit
$LEANBIN -R review review/probes/PassA.lean                # whole-release pass A (own detector)
$LEANBIN -R review review/probes/PassB.lean                # whole-release pass B
$LEANBIN -R review review/probes/SemRevInhabitants.lean    # C1 witnesses (exit 0 proves the claim)
python3 review/tools/perfile_replay.py                     # 464-file independent elaboration
python3 review/tools/ilean_scan.py                         # collisions + consumer replay
python3 review/tools/forbidden_scan.py                     # own forbidden-token lexer
python3 review/tools/hash_replay.py                        # source/baseline hash replay
python3 review/tools/build_table.py                        # semantic-class table
```

## 11. Verdict summary

| reviewed claim | verdict |
|---|---|
| cited declaration types/domains/kinds | **MATCH** (51/51) |
| fail-closed axiom cleanliness (only propext, Classical.choice, Quot.sound) | **MATCH** (cited + whole release + negative controls) |
| no `sorry`/`axiom`/`admit`/`unsafe`/`native_decide`/`proof_wanted` in proofs | **CONFIRMED** (3 axiom + 10 `.«unsafe»` pattern-match + 14 `sorryAx` name literals, all accounted for; 22 partials harmless) |
| downstream-use counts | **MATCH** (every cited number) |
| import-closure defect (58/3) | **CONFIRMED** |
| audit-list drift (172/171, 96/71) | **CONFIRMED** |
| blocker ledger M8/A3/I6/I7 | **CONFIRMED with corrections C1 (I7 wording), C2 (M8 evidence scope)** |
| adversarial conclusion-equivalence finding | **CONFIRMED in lane; extended package-wide (C3)** |
| source hashes / build / per-file | **CONFIRMED** (464/464, 0 failures, oleans fresh) |
| no promotion of conditional/model/statement-only claims | **CONFIRMED** |
| any mathematical blocker closed | **NONE** — M8 UNBOUND, A3/I6/I7 OPEN, Poincaré not proved |

## 12. Repair attempt 1 — gate transport incident, re-verification, remaining cache blocker

**Incident (infrastructure, not authored source).** The dispatcher compile gate for this card
(`state/SEMREV-L5-topology-audit/gate.json`, `checked_at 2026-09-12T00:31:12+0800`,
`ok:false`, `build_exit:1`) failed inside `lake build` before any per-file check: this worktree's
`.lake/packages` was not populated with the pinned packages (round 1 reviewed through a read-only
`LEAN_PATH`), so Lake fetched them from the network and the git transport died on the pinned
`plausible` package — `RPC failed; curl 56 GnuTLS recv error (-54) … fatal: early EOF`
(`gate-build.log`). No authored source was involved, and no release byte changed. The failed
record is preserved verbatim at `review/evidence/gate-transport-failure.json`
(sha256 `9831146e…`) and `…-build.log` (sha256 `df481e64…`).

**Repair and re-verification (release package, not worktree root).**

1. `release/.lake/packages` now resolves to the shared prebuilt package store; the pinned
   `lake-manifest.json` revisions are unchanged.
2. `timeout 3600 lake build` in `release/` (pinned toolchain v4.34.0-rc2) →
   **EXIT 0**, “Build completed successfully (8946 jobs)”, completed 2026-09-12T00:49:05+08:00,
   log `review/logs/repair-lake-build.log`. This (re)generated the 61 default-target oleans.
3. The gate's per-file stage replicated exactly (`lake env lean <rel>` for every authored
   `.lean` file, 4 workers, `review/tools/gate_replay.py`, same walk as
   `dispatch_loop.source_hash`) → **63/63 exit 0** in 63.1 s, including the two files outside
   `defaultTargets` (`ReleaseClaims.lean`, `D6LedgerProbe.lean`);
   `review/logs/gate-replication.json`.
4. Round-1 reviewer evidence re-run in this invocation is **byte-identical** to the recorded
   hashes: the fail-closed cited-declaration audit (51 cited / 0 missing / 0 unsafe / 0 `sorryAx`
   / 0 unapproved cones / 5 registered negative controls with their forbidden cones /
   `SEMREVVERDICT PASS`), the exact-type replay, the inhabitant witnesses, the forbidden-token
   scan, and the fail-closed negative control (fresh `axiom`/`sorry`/`native_decide` outside the
   release → detector exits 1, naming all four forbidden cones); `hash_replay.py` reproduces the
   release tree digest `d3954cf9…` and every parent-artifact hash; and the independent
   **464-file per-file elaboration replay** of the parent union release reruns with **0 failures**
   in 139.1 s (round 1: 151.0 s; round-1 logs preserved as `review/logs/round1-perfile-replay.*`).
   Reproduction:
   `cd release && lake build` (ELAN_HOME + PATH as in §10);
   `python3 review/tools/gate_replay.py`;
   `$LEANBIN -R review review/probes/SemRevAxioms.lean` under
   `LEAN_PATH=$(cat review/evidence/leanpath.txt)`;
   `LEAN_PATH=review/negcontrol $LEANBIN review/probes/SemRevNegControlAudit.lean` (expect exit 1);
   `python3 review/tools/perfile_replay.py`.
5. Scope fact recorded for transparency: the worktree's provisioned `release/` package contains
   **63** `.lean` files (byte-identical to the corresponding files of the audited union release:
   0 mismatches against the parent `audit-evidence/source-hashes.txt`), and its gate fingerprint
   is exactly `75e8231d…` — the `source_sha256` of the failed gate. The audited L5 union release
   has **464** `.lean` files and lives in the parent artifact; the 464-file replay and all
   `#print axioms` evidence in §1–§7 were produced against the parent's oleans. The dispatcher
   gate for this worktree compiles and checks the 63-file package.

**Remaining infrastructure blocker (bookkeeping only; no mathematical content).** The dispatcher
caches failures: `dispatch_loop.compile_gate` returns `gate.json` unchanged whenever `version`
and `source_sha256` match, regardless of `ok` (`bin/dispatch_loop.py:147–150`). Because this
review intentionally leaves the audited release unmodified, the fingerprint is stable, so the
dispatcher would return the stale 00:31 transport failure without re-running `lake build`. This
worker cannot invalidate the entry: the `mv` of `state/…/gate.json` returned `Permission denied`
(path outside the sandbox workspace), and the wider-access retry failed closed
(“no approval channel is available”). **Operator action (one line):**
`rm state/SEMREV-L5-topology-audit/gate.json` (or rename it) — the next dispatcher tick then
runs the gate unchanged and it passes on §12.2–12.4. This is the only remaining obstacle between
this card and a green dispatcher gate. Deliberately **not** done: editing the audited release
(e.g. adding the missing union files to this worktree's 63-file package) purely to change the
fingerprint — that would alter the artifact under review to force a cache miss, so the only
sanctioned fix is clearing the stale entry. **(Resolved in §13: the entry was cleared by operator
action at `2026-09-12T01:07:52+0800`; the gate now re-runs from scratch and passes on the
attempt-2 evidence.)**

This addendum changes nothing in §0–§11: **M8 UNBOUND, A3/I6/I7 OPEN, no promotion,
Poincaré not proved**, review verdict unchanged.

## 13. Repair attempt 2 — cache entry cleared; fresh compile-checked re-verification

**Status change (bookkeeping).** At `2026-09-12T01:07:52+0800` the stale dispatcher cache entry
`longrun/state/SEMREV-L5-topology-audit/gate.json` was removed from the state directory by
operator action and preserved as `gate.transport-failure-preserved-20260912010752.json`
(sha256 `9831146e…`, byte-identical to the record preserved in §12). No `gate.json` remains, so
`dispatch_loop.compile_gate` (`bin/dispatch_loop.py:146–150`) has no matching cache entry and the
next dispatcher tick that finds `state/DONE` re-runs `lake build` plus the 63-file `lake env lean`
stage from scratch. This worker's own attempt to clear the entry was sandbox-denied exactly as
recorded in §12 (`touch` probe → `Permission denied`; wider-access retry → “requires approval, but
no approval channel is available”), so the clearing was external; **the worker modified no
dispatcher file and no release byte**.

**Fresh re-verification in this invocation (release package, not worktree root).**

1. `timeout 3600 lake build` in `release/` → **EXIT 0**, “Build completed successfully
   (8946 jobs)”, with the D6 audit reporting
   `D6AUDIT VERDICT PASS — no sorryAx, no project axiom, no unsafe, no native_decide, no
   unapproved axiom, no proof_wanted`; `review/logs/repair2-lake-build.log`
   (sha256 `6c01b4be…`).
2. Gate per-file stage replicated (`lake env lean <rel>` for all 63 authored `.lean` files, 4
   workers, exact `dispatch_loop` walk/cwd) → **63/63 exit 0** in 62.4 s, per-file results
   identical to attempt 1; `review/logs/gate-replication.json` (sha256 `37fa73fb…`). The source
   fingerprint recomputed before and after the stage is `75e8231d…` (unchanged, 63 files), so the
   **predicted dispatcher gate outcome is `ok:true`**.
3. Every round-1 probe re-run is **byte-identical** to its recorded log: fail-closed cited
   declaration audit (`SEMREVVERDICT PASS`: 51 cited / 19 theorems / 22 defs / 0 missing /
   0 unsafe / 0 `sorryAx` / 0 unapproved axiom cones / 5 registered negative controls with their
   forbidden cones), exact types, printed shapes, inhabitant witnesses, whole-release passes A+B,
   forbidden-token scan, and source/baseline hash replay. The fail-closed negative control (fresh
   `axiom`/`sorry`/`native_decide` outside the release) still exits **1**, naming all four
   forbidden cones.
4. The A3 defect screen was replayed from the parent probe; its 337 `L5A3*` content lines are
   byte-identical to the parent's own `L5A3Screen.log` (round 1 additionally captured a `time`
   footer), verdict still `SCREEN_COMPLETE — no counterexample search; A3 remains open`.
5. Independent 464-file elaboration replay of the parent union release → **464/464, 0 failures**
   in 156.6 s; the file list and all exit codes are identical to round 1 modulo per-file timings
   (`review/logs/perfile-replay.json`, `perfile-replay.full.txt`).
6. Artifact preservation re-checked: parent L5 card/JSON/checkpoint hashes unchanged
   (`bab8e022…` / `bd9d9759…` / `f863293d…`), release tree digest `d3954cf9…`, **0** source-hash
   mismatches, **0** diffs against the pre-audit baseline, 464/464 files.
7. Attempt-2 evidence record: `review/evidence/gate-cache-cleared-repair2.json`; attempt-1 logs
   preserved as `review/logs/*-repair1.*`, round-1 logs as `review/logs/round1-*`.

**No mathematical change.** `M8` UNBOUND, `A3`/`I6`/`I7` OPEN, no promotion,
`poincare_proved = false`; no theorem, definition, test or negative control was edited in any
attempt. The review verdict remains `TASK_DONE` for the semantic review itself.

This review is independent, reproducible from the reviewer's own tools, and preserves the parent
artifact byte-for-byte. It is a semantic review of an audit, not a Poincaré proof.

TASK_DONE
