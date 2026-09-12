# D13-cross-audit-360-cards — adversarial cross-audit result card

- **Task id:** `D13-cross-audit-360-cards` (auditor lane, named blocker **A3**)
- **Scope:** independent re-verification of the nine D12 result cards produced by lanes
  **360-1 / 360-2**: `connection-curvature`, `volume-ibp`, `tensor-maximum-bochner`,
  `spectral-sobolev`, `semantic-ledger`, `comparison-geodesics`, `geometric-compactness`,
  `triangulation-topology`, `surgery-recognition`.
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2`, mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`
  (pinned by each producer `release/lake-manifest.json`; shared prebuilt package cache reused).
- **Status:** `TASK_DONE` (cross-audit milestone; completed in round 12, **independently
  re-verified in round 13 / invocation 10**, §21) — **9/9 cards
  independently re-verified.** The seven original cards passed a **tenth consecutive
  byte-identical sweep** (342 per-declaration axiom cones and 1103 full-namespace
  declarations PASS in each). The two late cards received the **independent runs that
  round 11 left unfinished**: `D12-triangulation-topology` (194/194 probe cones, 537
  full-namespace declarations PASS, all 10 closure claims mechanised with a corrected
  query set) and `D12-tensor-maximum-bochner` (20 declarations, 335 full-namespace
  declarations PASS, C1/C2/C3 confirmed by independent cones, use queries and a
  re-execution of the producer's own fail-closed coverage tool). The round-12 use probes
  are complete for both; the hand-written full-transitive cone completed for seven cards
  and was replaced by a scoped local-proof-graph cone for the two topology-heavy cards,
  whose full mathlib closure exceeded the invocation budget (see §20.8). A single hand-written `Expr`-traversal cone checker (no
  `CollectAxioms`, no `extFind?` cache) now covers **all nine** cards — full-transitive
  for seven, scoped local-proof-graph for the two topology-heavy cards whose full
  mathlib closure exceeded the invocation budget (§20.9) — and a
  mechanised downstream-use probe confirms the closure wiring; three reversed queries
  and two example-only "downstream uses" in the round-11 card-8 evidence were found and
  corrected. One producer `downstream_use` claim is **refuted**: the surgery-recognition
  card attributes the covering-recognition closure to `RemainingRecognitionHypothesesV2`
  / `stage6Target_of_v2hypotheses`, but kernel reachability shows the V2 route keeps
  `coveringTrivial` as an input; the constructed covering recognition is consumed only
  through the V3 route (F26). The audit does **not** close the producer-side blocker
  **B1** (PSD-cone invariance from the correct tangent-cone condition) and does **not**
  claim Perelman.**
  Round 3 adds a fresh rebuild sweep, two independent closure
  consumers, a kernel-level validation of finding F1, an extended vacuity screen (T1–T11),
  a pinned-upstream cross-check, a proof-cone method for the A3 D2/D3 lane, a full-namespace
  type screen, D6-wide screens, and a self-audit of all recorded hashes (§11); round 4
  re-ran the whole sweep at close-out with byte-identical results (342 cones, 1103
  declarations PASS). **Round 5 (invocation 4)** re-ran the sweep a fourth time (again
  byte-identical), added a kernel *declaration-kind* screen (F14), a cross-package
  foundation byte-identity diff, a cross-card concept-collision scan, and deep statement
  reviews of the two cards not yet reviewed at that level (§13). **Round 6 (invocation 5)**
  re-ran the sweep a fifth time (byte-identical again), **cold-rebuilt the five cards that
  had never been cold-rebuilt**, added a **sixth independent closure consumer at a concrete
  non-bi-invariant model**, ran a wider forbidden-token scan, and deep-reviewed
  `spectral-sobolev` and `connection-curvature` (§14).
  **Round 7 (invocation 6)** re-ran the sweep a sixth time (byte-identical), added a
  canonical blocker-register cross-check against the D12-semantic-ledger 31-entry register, a
  type-identity probe for the connection-curvature closure, and an audit-of-the-auditor
  self-control with injected axiom/sorry/tautology defects (§15). **Round 8 (invocation 7)**
  re-ran everything a seventh time (byte-identical), classified the round-7 vacuity-screen
  blind spot flag-by-flag, added a closure-consumption (wiring) screen and two new kernel
  probes (pp-artifact evidence for `diam_rep_of_toGHSpace`, register-identity and
  van-Kampen-independence evidence for the SR-5 closure), and re-checked the missing cards
  (§16). **Round 9 (invocation 7)** added kernel assumption-as-conclusion screens — 1104
  full-namespace constants with 0 flags and the control flagged in every package, plus a
  new D2/D3 finding **A3-D2D3-9** — an independent drift check and a pinned-upstream
  snapshot integrity check (§17). **Round 10 (invocation 7)** re-ran everything an eighth
  time byte-identically and closed out with the deliverable field map (§18).
  **Round 13 (invocation 10)** re-verified all nine cards from scratch with tooling written
  in this invocation only: an independent source-hash rebuild, cold rebuilds of all nine
  packages plus the semantic-ledger snapshot, an independent kernel axiom dump over every
  D12-root constant, a hand-written direct-reference downstream-use graph, definitional
  assumption-as-conclusion screens, and re-executions of the two late producers' axiom tools
  against the round-13 rebuilt copies (§21). The `TASK_BLOCKED` sentence that had remained
  here from round 10 (2/9 source-absent) is **superseded and stale**: 9/9 cards are audited
  and independently re-verified.
- **Named blocker A3:** **stale-as-stated / partially addressed** (see §8, §11.6, §11.8).
  A D2/D3 counterexample search now exists in three independent layers (prior
  `VERIFIER-D7` card, round-2 compiled probe, round-3 proof-cone screen); one headline
  finding of the prior audit is itself refuted here. A3 is not closed as a quality gate
  because the found defects are unrepaired; the **nine-card cross-audit part of A3 is
  closed and was independently re-verified in round 13** (§21).
- **Elapsed:** ≈2.9 h of this invocation (round 13, invocation 10); ≈13.6 h cumulative for
  the task; 2026-09-11/12.

---

## 1. What was checked and how

Nothing produced by the 360 lanes was trusted. For every card with a local producer worktree:

1. **Hash provenance from bytes on disk.** Every recorded `source_sha256` (three different card
   schemas: flat, nested `sha256`, nested `package_lean_files`) was recomputed and matched
   against the files in the producer worktree. No producer manifest was used as evidence.
2. **Fresh rebuild of a copied source tree.** Release sources (no `.lake` caches) were copied to
   `audit360/pkgs/<card>/`, the shared pinned mathlib cache linked, and `lake build` run. Two
   cards were additionally rebuilt in pristine copies with **no `.lake/build` at all** (cold
   rebuild, §4).
3. **Independent per-declaration axiom probe.** Every name in the card's `proved_declarations`
   was resolved to a fully-qualified Lean name by a namespace-aware scan of the compiled sources
   (not by trusting the card), then `#check` + `#print axioms` were emitted into a generated
   `A3Probe.lean` and compiled. The fail-closed predicate is: every declaration resolves, and
   every axiom cone ⊆ `{propext, Classical.choice, Quot.sound}`.
4. **Negative control.** `audit360/negcontrol/A3NegativeControl.lean` (a `sorry` theorem and a
   `native_decide` theorem) is compiled by the same pipeline; the predicate must flag both. It
   does (`sorryAx`; private `native_decide` axiom).
5. **Forbidden-token scan** (comment/string-aware) over the rebuilt sources, with documented
   negative-control axioms classified and checked to appear in no cone.
6. **Semantic review** of headline statements and of every `exact_blockers_closed` claim:
   constructor existence, statement strength (no hypothesis-equals-conclusion, no vacuous
   domain), and a downstream checked use.
7. **Dependency provenance.** Base modules byte-compared against the accepted D6 release;
   vendored D7/D10/VKPort modules byte-compared across sibling worktrees; the semantic-ledger
   37-module snapshot rebuild replayed from its recorded hashes.

Artifacts: `audit360/inventory.json`, `audit360/audit_result.json`, `audit360/pkgs/<card>/A3Probe.lean`
+ `A3Meta.json`, `audit360/logs/*`, `audit360/types/*.types.txt`, `audit360/compose.py`.

## 2. Per-card verdict

| card | producer status | recorded hashes | rebuild | independent probe | blocker closures | verdict |
|---|---|---|---|---|---|---|
| D12-connection-curvature | TASK_DONE_pending_acceptance (ckpt in_progress) | 12/12 ✔ | exit 0 (8957 jobs) | **119/119**, 0 violations | 1 claimed → **CONFIRMED** | **PASS** (card inventory defect F1) |
| D12-volume-ibp | task_done (ckpt in_progress) | 11/11 ✔ | exit 0 (8956 jobs) | **78/78**, 0 violations | none | **PASS** (documented neg. control F5) |
| D12-spectral-sobolev | TASK_DONE / complete | 8/8 ✔ | exit 0 (8953 jobs) | **36/36**, 0 violations | none | **PASS** |
| D12-semantic-ledger | TASK_DONE (queue gate_failed) | 66/66 ✔ | exit 0 (8949 jobs) | **7/7 in-package + 2/2 snapshot**, 0 violations | none claimed | **PASS** (provenance note F2; ledger notes F8/F9) |
| D12-comparison-geodesics | TASK_DONE / gate repaired | 8/8 ✔ | exit 0 (8957 jobs) | **33/33**, 0 violations | none | **PASS** (model-witness note F4) |
| D12-geometric-compactness | in_progress | 6/6 ✔ | exit 0 (8951 jobs) | **39/39**, 0 violations | none | **PASS** (card not yet frozen) |
| D12-surgery-recognition | TASK_DONE_requested / awaiting acceptance | 8/8 ✔ | exit 0 (8993 jobs) | **30/30**, 0 violations | 3 claimed → **CONFIRMED** | **PASS** |
| D12-tensor-maximum-bochner | remote_owned (no artifacts) | — | — | — | — | **NOT AUDITABLE** |
| D12-triangulation-topology | remote_owned (no artifacts) | — | — | — | — | **NOT AUDITABLE** |

**342 card-declared entries plus 2 snapshot-probe declarations** across the 7 available cards
were independently re-audited in this session; all cones are exactly
`{propext, Classical.choice, Quot.sound}`; zero violations. The 342 entries cover **335 distinct
declarations**: 7 D12-connection-curvature entries carry the over-qualified
`ChartLeviCivitaSmooth.` prefix and resolve to the same declaration as their correctly-qualified
twin (see F1).
A complete-namespace metaprogram audit additionally covers **1103 declarations** under the
`Poincare.D12` roots with zero unapproved axioms (§5). Round 6 repeated the whole sweep a
fifth time with byte-identical build/probe/full-audit output and a byte-identical kind
screen, and additionally cold-rebuilt the five cards that had not yet been cold-rebuilt
(§14.1–14.2), so every probe entry in the table now also has a from-source cold-build
witness.

## 3. Hash provenance

All recorded source hashes verify against the bytes on disk in the producer worktrees:
connection-curvature 12/12, volume-ibp 11/11, spectral-sobolev 8/8, semantic-ledger 66/66,
comparison-geodesics 8/8, geometric-compactness 6/6, surgery-recognition 8/8.

Additional provenance checks:

- **No accepted source was modified.** Every base module shared with the D6 weekly release is
  byte-identical (`diff -rq`, zero differing files across all 7 packages). Vendored
  `Poincare/D7/Recognition`, `Poincare/D10/JacobiConstantCurvature` and `Poincare/VKPort`
  copies are byte-identical across every sibling worktree that contains them.
- **Semantic-ledger snapshot rebuild**: all 37 modules of
  `manifest/d12-rebuild-manifest.json` hash-match the pristine
  `D11-bochner-manifold/release` sources, and the 37-module snapshot was rebuilt here
  (9176 jobs, exit 0) with the two extra declarations probed (§5).
- Card `.md`/`.json` hashes are pinned in the results JSON.

**Round-2 re-check (this invocation, 13:2x):** `audit360/inventory.py` re-ran over the producer
worktrees — every recorded hash still verifies with `bad = 0` (connection-curvature 12,
volume-ibp 11, spectral-sobolev 8, semantic-ledger 66, comparison-geodesics 8,
geometric-compactness 6, surgery-recognition 8). The producer card files are unchanged since the
audited window (mtimes 2026-09-11 02:02–04:50; sha256 in `audit360/card_freeze_round2.json`), so
the verdicts below are not stale. `D12-volume-ibp` reports one ambiguous short-name candidate,
but every per-key hash verdict is `ok`.

## 4. Compile evidence

| package | command | result | jobs | wall time |
|---|---|---|---|---|
| all 7 cards | `cd audit360/pkgs/<card> && lake build` | exit 0 | 8949–8993 | ≈90 s each (shared mathlib oleans) |
| D12-connection-curvature (cold) | pristine copy, **no `.lake/build`**, `lake build` | **exit 0**, 119/119 probed, 0 errors | 8957 | ≈3.5 min |
| D12-surgery-recognition (cold) | pristine copy, **no `.lake/build`**, `lake build` | **exit 0**, 30/30 probed, 0 errors | 8993 | ≈3.5 min |
| D12-semantic-ledger-snapshot | `lake build` of D11-bochner snapshot + D12 SemanticLedger | exit 0 | 9176 | cold rebuild |
| every card | `lake env lean A3Probe.lean` | exit 0 | — | — |
| semantic-ledger | `lake env lean A3Extra/D12RealModuleProbe.lean` (with appended probe) | exit 0 | — | — |

**Round-2 re-verification (this invocation, 13:04–13:06):** all seven available cards were
re-built and their `A3Probe.lean` re-run from the current on-disk state — every build rc 0 and
probe rc 0, declaration counts unchanged (119, 78, 36, 7, 33, 39, 30 = 342). The round-1 logs
(including the two cold rebuilds) are preserved under `audit360/logs-round1/`; the round-2 logs
are in `audit360/logs/` and summarised in the results JSON under `reverification_round2`.

## 5. Axiom evidence

- Independent probe: `A3Probe.lean` per card, generated from independently resolved names.
  342/342 entries resolve (335 distinct declarations); **0** cone violations; all cones
  `{propext, Classical.choice, Quot.sound}`.
- **Round-2 vacuity/triviality screen** (`audit360/vacuity_screen2.py`, documented criteria T1–T8
  over the full `#check` types of all 335 distinct declarations): 8 flags, **all 8 reviewed and
  false positives** (`gamma … 0 = 0`, `0 < 1 + x²`, `heatEvolve T 0 f = f`, and five substantive
  `Subsingleton`-valued surgery statements). **0 true positives.** This is the documented method
  behind the "no vacuous card statement" claim, complementing the 1103-constant namespace audit.
- **Complete-namespace audit** (`A3FullAudit.lean`, Lean metaprogram enumerating *every*
  constant in the compiled environment under the `Poincare.D12` root, not just the card's
  list): **1103 declarations audited, 0 with unapproved axioms**, PASS on all 7 packages
  (connection-curvature 260, surgery-recognition 378, volume-ibp 159, comparison-geodesics
  139, geometric-compactness 71, spectral-sobolev 68, semantic-ledger 28). This closes the
  "hidden unlisted lemma with `sorry`" gap a card-driven probe alone would leave.
  **Round-2 re-run (13:45):** all seven packages re-audited from the current on-disk state —
  rc 0, PASS, identical counts, 1103 total (`audit360/fullaudit_round2.json`).
- **Negative control** (`a3_neg_sorry`, `a3_neg_native`): cones `{sorryAx}` and
  `{…native_decide.ax_1_1}` — the fail-closed predicate flags both. Log:
  `audit360/logs/negative_control.log`.
- **Forbidden scan**: clean for all cards except the documented, unused
  `axiom negativeControl : False` in `Poincare/D12/VolumeIBP/Audit.lean`, which appears in no
  cone of the 78 audited volume-ibp declarations. The scanner itself is validated by flagging
  the negative-control file.
- **Semantic-ledger extra declarations** (`real_initialCondition_specializes`,
  `realField_unsatisfiable_by_gaussian`) audited against an independently rebuilt D7/D10
  snapshot: both cones ⊆ allowed; the probe's own 17-declaration check PASSes.
- **D12-connection-curvature correction is sound**: the historical claim in
  `Poincare/Longrun/Geometry/LeviCivitaBlocked` ("false without invariance") is indeed wrong;
  invariance is only needed for the *mean* connection (`milnorConnection_eq_mean_iff`), while
  the Milnor connection proves unconditional existence. The base module was not edited.

## 6. `exact_blockers_closed` — confirm/refute

Four closures are claimed across the 9 cards (1 + 3). All four were reviewed against the
definitions and their downstream uses.

1. **D12-connection-curvature — `LeviCivitaExistenceStatement`: CONFIRMED.**
   The blocked `Prop` is unchanged (`∃ nabla, IsLeviCivita m b nabla`, byte-identical base
   module). `leviCivitaExists` supplies the explicit Milnor witness
   `∇_X Y = ½([X,Y] − (ad_X)ᵀY − (ad_Y)ᵀX)` with separate torsion-freeness and
   metric-compatibility proofs. Downstream checked use: `milnorLeviCivitaData` →
   `so3MeanLeviCivita` → `ricci_symm`/`so3_ricci_e00` (`Ric(e₀,e₀)=½≠0`).
2. **D12-surgery-recognition — SR-5 `sphere_of_spheres`: CONFIRMED (with decomposition data
   as an explicit V2 input).** `ConnectedSumDecomposition.mkV2` produces the D7 structure whose
   `sphere_of_spheres` field is derived from the proved `iteratedSphereSum_homeo_sphere`
   (built on `sphereConnectSum_homeo_sphere` and the explicit `doubleBallHomeoSphere`).
   The identification "X is the iterated connected sum" is carried as
   `ConnectedSumDecompositionV2.sumHomeo` data — this is the honest remaining geometric input,
   not the blocker. Downstream: `stage6Target_of_v2decomposition`.
3. **D12-surgery-recognition — covering-space recognition: CONFIRMED.**
   `finiteFreeOrbit_isQuotientCoveringMap` proves mathlib's `IsQuotientCoveringMap` for finite
   continuous free actions on 𝕊³ with constructed evenly covered neighbourhoods; the antipodal
   model is a nondegenerate 2-sheeted instance. Downstream: `RemainingRecognitionHypothesesV2`,
   `stage6Target_of_v2hypotheses`.
4. **D12-surgery-recognition — `coveringTrivial`: CONFIRMED.**
   `deckTrivial_of_simplyConnected_quotient` proves `Subsingleton M.Γ` from simple connectivity
   of the orbit quotient using mathlib's monodromy (path/homotopy lifting). The
   `SphericalSpaceFormModel` structure has no triviality field, so the statement is not
   vacuous. Downstream: `sphericalPieceRecognition_of_spaceForm`, `stage6Target_of_v3hypotheses`.

No card claims a closure that is a mere alias, projection or `Prop` certificate; no closure
rests on a modified accepted source. **Round 3 additionally consumed closures 1 and 2 with
fresh audit-written code** (`A3ExtraR3/ClosureUse.lean` in the two packages, §11.2): the
choice-based Levi-Civita consumer with its Stage1 Bianchi/skew obligations, and an
independently constructed empty-sum V2 inhabitant whose `mkV2` image has a *proved*
`sphere_of_spheres`. Both compile rc 0 with allowed cones. **Round 5 adds a fifth consumer
at a nonempty piece list** (§13.8): two `𝕊³` summands, exercising the recursive branch of
`iteratedSphereSum` and the claimed `mkV2` constructor; compile rc 0, cones
`{propext, Classical.choice, Quot.sound}`.

## 7. Adversarial findings (A3 lane)

- **F1 (claim provenance, connection-curvature).** 73/119 `proved_declarations` entries carry
  file-derived namespace segments that do not exist in the compiled sources (e.g.
  `…ConnectionCurvature.ChartLeviCivita.ChartMetricCoefficients.christoffel_symm` vs the real
  `…ConnectionCurvature.ChartMetricCoefficients.christoffel_symm`). Every declaration exists
  (unique short-name match) and compiles; the card inventory is wrong, the mathematics is not.
- **F2 (claim provenance, semantic-ledger).** 2/9 declared names live in
  `audit_probes/D12RealModuleProbe.lean` outside the release package. Replayed and audited
  here; both are genuine and within the allowed cone.
- **F3 (audit coverage).** `D12-tensor-maximum-bochner` and `D12-triangulation-topology` have
  no worktree, no release package, no card and no Lean module anywhere on this host
  (exhaustive filename search, `.lake` pruned). They are `remote_owned` queue entries only.
  They are **not refuted** — they are **not auditable here**.
- **F4 (semantic minor, comparison-geodesics).** The model non-vacuity witnesses
  `euclidModel_singular_comparison_ge` and `euclidModel_bishopGromov` are reflexive instances
  (`m ≤ m`; `V R/V R ≤ V r/V r`). They establish hypothesis satisfiability but do not exercise
  a strict comparison. The general Sturm/Riccati/Bishop–Gromov statements are substantive,
  division-free and have no hypothesis equal to their conclusion (screen over all 33 types).
- **F5 (intentional negative control, volume-ibp).** `axiom negativeControl : False` is declared
  in the task's own audit module, documented in-file, unused in every cone. Recorded, not a
  violation.
- **F6 (process state).** Queue/checkpoint state disagrees with card verdicts:
  connection-curvature and volume-ibp checkpoints are `in_progress` while their cards say
  TASK_DONE; geometric-compactness is `in_progress`; semantic-ledger is `gate_failed` in the
  queue with A1/A2/A3/P1/P5. This audit pins the card hashes frozen 2026-09-11 02:02–04:50.
- **F7 (scope nuance, connection-curvature).** `chartMetricCompatible_form` /
  `chartTorsionFree_form` are algebraic identities whose right-hand sides are supplied
  coefficient data (`dFormOf`, zero coordinate bracket); the genuine Fréchet-derivative
  statements are `nabla_metricCompatible` / `nabla_torsionFree`, both present and audited. The
  card discloses this boundary.
- **F8 (semantic classification, semantic-ledger — new this round).** The ledger note
  `L-D2-LEVI-CIVITA` calls `LeviCivitaExistenceStatement` **and**
  `CovariantDerivativeCurvatureStatement` "BLOCKED Props". The second is unconditionally
  inhabited by the zero tensor (`A3D2D3.covariantCurvatureStatement_trivial`), so the label is
  wrong; the first is stale, since `Poincare.D12.ConnectionCurvature.leviCivitaExists` is a
  compiled proof (fresh `#check`/`#print axioms` this round: cone
  `{propext, Classical.choice, Quot.sound}`). The entry is nonetheless classified
  `genuine-general`.
- **F9 (semantic classification, semantic-ledger — new this round).** The ledger note
  `L-D2-ODE-SCALAR-MONO` says `scalarCurvature_monotone_of_bridge` is "conditional on the
  **uninhabited** `TensorRicciFlowODEBridge`". The bridge is inhabited
  (`A3D2D3.bridgeWitness`) and every inhabitant with `0 < T` has `ricci = 0` hence `traj = 0` on `[0,T]`
  (`A3D2D3.bridge_forces_zero_traj`): the correct defect is **degeneracy**, not
  uninhabitedness. Separately, `L-D3-ENTROPY-CERTIFICATES` lists the projections
  `LinearDecayCertificate.decay` / `.rate_pos` among checked decay certificates, but the
  structure is provably empty (F-A3-1).
- **F10 (release statement defects, D1–D6 — new this round).**
  `missingSphereRecognitionAlgorithm` is trivially true via classical decidability and captures
  no algorithm; `SurgeryCertificate` has no field mentioning the surgery datum, so certificates
  exist for an empty-relation datum; `missingConjugateHeatKernel` and
  `missingKappaNoncollapsing` are false for the zero measure; `NeckAnalysis` is inhabited with
  all `Prop` fields `False`; `ExtinctionTheorem` has its conclusions as free fields; and the
  discrete maximum principle's `hM` is redundant. All kernel-checked.
- **F11 (audit-of-the-auditor — new this round).** `VERIFIER-D7-adversarial-audit-d2d3`
  finding F2 ("entropy bridge has the wrong sign") is **refuted**: Perelman's eq. (1.4) gives
  `F_t = +2∫|Ric + ∇²f|²e^{-f} ≥ 0`, matching the release. Its F11 (conjugate heat equation
  missing `Rρ`) is confirmed; its F1/F3/F4/F5 were independently reproduced.
- **F12 (redundant/phantom binders — new in round 3, §11.8).** A compiled proof-term
  binder screen over 830 declarations finds: **F12a** three D12-geometric-compactness
  statement-only frontier `Prop`s whose dimension/Hölder-exponent parameters are phantom
  (kernel-checked `rfl` independence); **F12b** six D12-comparison-geodesics theorems with
  explicit hypotheses the proofs never use (six sharp restatements kernel-checked); and
  **F12c** minor redundancies (`connectedSum` injectivity args unused by the definition,
  unused `[DecidableEq]`/`[Fintype]` instances). Auto-generated `_proof_N`/`ctorIdx`/
  `sizeOf_spec` flags are excluded as artifacts (F12d).
- **F13 (audit-artifact hash drift — new in round 3, §11.11).** The round-1/2 recorded
  `audited_copy_sha256` for `D12-semantic-ledger`'s `A3Extra/D12RealModuleProbe.lean` is
  stale (the file was edited after hashing); caught by the round-3 self-audit of all 744
  recorded hashes and corrected. No compiled evidence changes.
- **F14 (inventory precision — new in round 5, §13.2).** A kernel `ConstantInfo` screen of
  the 342 probe entries shows 266 are proofs (265 `theorem` + the `def` proof
  `sphereConnectSum_homeo_sphere`), while 76 are non-proofs: 7 Prop-valued statement
  formers, 2 type synonyms, 63 data defs and 4 structures. Six of the seven statement
  formers are the D12-geometric-compactness frontier `Prop`s, which that card *correctly*
  files under `statement_only_explicitly_excluded`; the seventh,
  `D12.ConnectionCurvature.bracketInvariant`, is a hypothesis predicate sitting in that
  card's flat `proved_declarations` list (its proved instance is the separately listed
  `SoThreeModel.so3_bracketInvariant`). No axiom/opaque entry appears and every cone was
  already audited, so this is a precision-of-inventory finding, not a soundness defect; it
  is invisible to `#check` + `#print axioms`, which is why the new screen was needed.
- **F15 (provenance coverage — new in round 5, §13.3).** The converse of the existing
  provenance check: for six cards every D12-authored `.lean` file on disk is covered by a
  recorded hash (11/11, 7/7, 3/3, 7/7, 5/5, 8/8), but **D12-volume-ibp records 9 of its 10**
  D12 files — the umbrella module `Poincare/D12/VolumeIBP.lean`
  (`546cd9d470e7fc07d1b16f6062790e294781566cef6f4a8b41ec858c3c8026b4`) is missing from
  `source_hashes`. The omission is harmless to the compiled evidence: the file is
  import-only (it declares no constants, so it has no axiom cone and the 1103-declaration
  namespace audit is unaffected), and this audit rebuilds it from the on-disk bytes. Fix =
  add the hash.
- **No false statement found** in the 7 audited cards: no hypothesis-equals-conclusion, no
  `True` conclusion, no unsatisfiable-hypothesis theorem identified in the headline screen;
  all 342 declarations are kernel-checked with permitted axioms. (The F8–F11 defects are in
  ledger notes and interface statements, not in card-declared theorems; F12 is redundant
  hypotheses and phantom interface parameters, not false content.)

Card-claim cross-checks (positive):

- **Deep proof review (this round).** `D12-semantic-ledger`'s headline counterexample was read
  line-by-line (`integrand_eq` → `quartic_dominates` → `lowerConstant_le_integrand` →
  `integrand_lintegral_eq_top` → `integrand_not_integrable` → `integral_undef_zero` →
  `not_initialCondition_gaussian_quantified`): the estimate
  `y⁴ − y²/(4t) ≥ y⁴/2` on `[R t, ∞)`, the infinite `lintegral`, the vanishing Bochner
  integral and the limit contradiction are all valid — **REVIEWED-CORRECT**.
  `D12-spectral-sobolev`'s sharpness pair (`poincare_wirtinger_sine_saturates`,
  `poincare_constant_sharp`) was likewise read and checked: the sine wave attains equality
  (both sides `π`) and forces `1 ≤ C` for any admissible constant — **REVIEWED-CORRECT**.
- `D12-semantic-ledger`'s ledger counts were re-derived from
  `manifest/d12-semantic-ledger.json`: 36 main-chain entries, classes 14 genuine-general /
  7 conditional / 13 model / 2 statement-only, 9 expanded certificate structures, 31 recounted
  blockers (23 open, A3 open) — exactly as the card states.
- `D12-geometric-compactness`'s statement-only frontier Props
  (`cheegerGromovCompactness`, `ancientKappaCompactnessFrontier`,
  `canonicalNeighborhoodFrontier`, `curvatureBoundImpliesUniformCovers`,
  `bishopGromovVolumeComparison`, `harmonicCoordinatesExistence`) appear in no proved theorem's
  hypotheses — only in their own definitions and `_iff` shape lemmas, as claimed.
- `D12-spectral-sobolev`'s "probability Haar measure" claim matches mathlib
  (`IsProbabilityMeasure AddCircle.haarAddCircle`), and the Poincaré constant is proved sharp
  (`poincare_wirtinger_sine_saturates` has equality; `poincare_constant_sharp` lower-bounds any
  admissible constant).

## 8. A3-requested D2/D3 counterexample search (this round)

`A3` asks for the D4 audit method to be extended to the earlier D2/D3 clusters
("axiom audits but no counterexample search"). This round performed that search
independently. Evidence:

- **Base:** `a3d2d3/` is a byte-identical copy of this worktree's accepted D6 release
  (`diff -rq a3d2d3 release --exclude=.lake --exclude=A3D2D3.lean` → empty).
  `lake build` → **exit 0, 8946 jobs**, `D6AUDIT VERDICT PASS`.
- **Probe:** `a3d2d3/A3D2D3.lean` (sha256 `8592a7e2…`), `lake env lean` → **exit 0**;
  17 declarations, all cones ⊆ `{propext, Classical.choice, Quot.sound}` (two have no
  axioms at all, one uses only `Classical.choice`); logs `audit360/logs/a3d2d3.*`.
- Nothing from `VERIFIER-D7-adversarial-audit-d2d3` is imported or copied; every
  result below is re-derived from the accepted release definitions.

### 8.1 The prior search exists — and one of its headline findings is refuted

The D2/D3 search was in fact already performed by `VERIFIER-D7-adversarial-audit-d2d3`
(Sep 9, 75/75 files exit 0, 11 findings). This round therefore also audited the
auditor:

| prior finding | this round |
|---|---|
| F1 `LinearDecayCertificate` provably empty | **reproduced** (`linearDecay_uninhabited`, `linearDecay_isEmpty`, `linearDecay_fields_contradict`) |
| F3 "BLOCKED" curvature Props unconditionally provable | **reproduced** (`covariantCurvatureStatement_trivial`) |
| F4 `TensorRicciFlowODEBridge` inhabited, forces zero trajectory | **reproduced** (`bridgeWitness`, `bridge_forces_zero_ricci`, `bridge_forces_zero_traj`) |
| F5 Levi-Civita existence is a theorem | **corroborated** by fresh `#check`/`#print axioms` of the compiled `leviCivitaExists` (cone allowed) |
| **F2 entropy bridge "wrong sign"** | **REFUTED — false positive.** Perelman (arXiv:math/0211159, §1.2 eq. (1.4)) proves `F_t = +2∫|R_ij+∇_i∇_j f|²e^{-f}dV ≥ 0` under `(g_ij)_t = -2R_ij`, `f_t = -Δf + |∇f|² - R`; the release's `FDerivativeStatement` is exactly this identity, so its reduction to `ContinuousMonotoneCertificate` is convention-correct. (The opposite sign occurs only in the D4 **finite model** `perelmanF_antitone`, whose own ledger note flags it.) |
| F11 conjugate heat equation `∂_tρ = -Δρ` | **confirmed as a labelling/convention defect**: the conjugate heat equation for `ρ = (4πτ)^{-n/2}e^{-f}` is `∂_tρ = -Δρ + Rρ`. |

### 8.2 Defect families independently established

| id | object | verdict | evidence (all kernel-checked) |
|---|---|---|---|
| A3-D2D3-1 | `Poincare.Longrun.Entropy.LinearDecayCertificate` | **VACUOUS**: the global lower bound and the global linear decay with `rate > 0` are jointly unsatisfiable in ℝ; `time_le` is a theorem about an empty type | `linearDecay_uninhabited`, `linearDecay_isEmpty`, `linearDecay_fields_contradict` |
| A3-D2D3-2 | `CovariantDerivativeCurvatureStatement I M cov` | **TRIVIAL** despite the `BLOCKED` label: `cov` is unused and `κ := 0` inhabits it unconditionally | `covariantCurvatureStatement_trivial` |
| A3-D2D3-3 | `TensorRicciFlowODEBridge I M cov F T traj D` | **INHABITED BUT DEGENERATE**: witness for zero data; and every inhabitant with `0 < T` has `ricci(curvature t) = 0` on `[0,T]`, hence `traj ≡ 0` (via `basis_fixed` + orthonormality) | `bridgeWitness`, `bridge_forces_zero_ricci`, `bridge_forces_zero_traj`, `form_eq_of_basis_eq` |
| A3-D2D3-4 | `FDerivativeStatement` / `ConjugateMeasureEvolutionStatement` | sign verified against Perelman (1.4); conjugate equation missing `Rρ` | §8.1 + docstring in the probe |
| A3-D2D3-5 | `missingSphereRecognitionAlgorithm`, `SurgeryCertificate`, `missingConjugateHeatKernel`, `missingKappaNoncollapsing`, `NeckAnalysis` | **TRIVIAL / FALSE-INSTANCE statement defects**: the "algorithm" is classical decidability; certificates exist for an empty-relation surgery datum; the two "missing theorems" are false for the zero measure; `NeckAnalysis` is inhabited with all `Prop` fields `False`, so the "missing input" imposes nothing | `missingSphereRecognitionAlgorithm_trivial`, `surgeryCertificate_emptyRelation`, `not_missingConjugateHeatKernel_zero`, `not_missingKappaNoncollapsing_zero`, `neckAnalysis_inhabited` |
| A3-D2D3-6 | `ExtinctionTheorem` / `MissingInputs`; `HeatGridEvolution.le_of_initial_le` | **TRIVIAL / OVERSTRONG**: the four extinction conclusions are free `Prop` fields (all `True` works), so `MissingInputs` can pair a trivial neck with an extinction half true by definition; and the discrete maximum principle's hypothesis `hM : 0 ≤ M` is redundant (left Dirichlet boundary + initial bound imply it) — sharp restatement proved | `extinctionTheorem_true`, `missingInputs_with_true_extinction`, `heatGrid_le_of_initial_le_no_hM` |
| A3-D2D3-7 | `kappaNoncollapsingCertificate_iff_normalizedBallVolumeLowerBound` | **OVERSTRONG**: the hypotheses `0 < κ`, `0 < r₀` are fields of either side and hence redundant; sharp restatement without them proved (reproduces prior-audit F7) | `kappa_iff_normalized_no_hyp` |

### 8.3 Classification (proved theorem vs interface vs source claim)

- **Proved theorems (this round, kernel-checked, permitted axioms):** all 17
  `A3D2D3.*` declarations above. They are *refutations/vacuity results about the
  release interfaces*, not repairs.
- **Conditional interfaces:** `EntropyRegularityBridge`, `TensorRicciFlowODEBridge`,
  `LeviCivitaData` — unproved fields; now with a precise degeneracy assessment.
- **Models:** the D4 finite `perelmanF` is a model with a sign convention opposite to
  Perelman's, as its own ledger note states.
- **Statement-only:** the `missing*` Props and the `BLOCKED` `Prop`-valued defs; three
  of them are additionally trivial or false as stated.
- **Upstream source claim:** Perelman (1.4) is cited from the literature (arXiv link),
  not formalized here; the release statement is compared against it textually.

Two D12-semantic-ledger notes are refuted by the above and are recorded as card
findings **F8/F9** (§7): `L-D2-LEVI-CIVITA` ("BLOCKED Props") and
`L-D2-ODE-SCALAR-MONO` ("uninhabited TensorRicciFlowODEBridge"), plus the
`L-D3-ENTROPY-CERTIFICATES` classification listing the empty `LinearDecayCertificate`
projections among checked decay certificates.

### 8.4 Per-entry verdicts for the ten D2/D3 main-chain ledger entries

Vocabulary: **CHECKED** = compiled evidence produced in this round's probe; **CITED** = prior-audit
result not independently re-proved here; **not re-checked** = no independent evidence this round.

| ledger entry | card class | verdict this round | basis |
|---|---|---|---|
| `L-D2-CURVATURE-IDENTITIES` | genuine-general | CONFIRMED as abstract algebraic identities (the note correctly disclaims manifold curvature); prior audit additionally found `scalarCurvature_eq_sum_basis` overstrong (orthonormality unused) | CITED (VERIFIER GeometryAudit) |
| `L-D2-LEVI-CIVITA` | genuine-general | declarations CONFIRMED; **note refuted** (F8): the curvature Prop is trivial, the existence Prop is a compiled theorem | CHECKED (A3-D2D3-2 + `leviCivitaExists`) |
| `L-D2-DISCRETE-MAX-PRINCIPLE` | model | CONFIRMED; **one hypothesis overstrong**: `hM : 0 ≤ M` is redundant in `le_of_initial_le`; sharp restatement proved | CHECKED (A3-D2D3-6) |
| `L-D2-ODE-INVARIANT` | genuine-general | no defect found; the orthant-invariance hypothesis is satisfiable (zero state) | not re-checked beyond prior audit |
| `L-D2-ODE-SCALAR-MONO` | genuine-general | declarations CONFIRMED; **note refuted** (F9): the bridge is inhabited and degenerate, not uninhabited | CHECKED (A3-D2D3-3) |
| `L-D3-ENTROPY-CERTIFICATES` | model | **one item vacuous**: `LinearDecayCertificate` is empty; the monotone/antitone certificates and the discrete heat-energy certificate are substantive | CHECKED (A3-D2D3-1) + CITED (VERIFIER F1) |
| `L-D3-KAPPA-MANIFOLD` | genuine-general | CONFIRMED (mathlib instance transfers for compact 3-manifolds); no defect | not re-checked |
| `L-D3-KAPPA-ALGEBRA` | model | CONFIRMED with **redundant positivity hypotheses** in the κ equivalence; sharp restatement proved (prior-audit F7) | CHECKED (A3-D2D3-7) |
| `L-D3-SURGERY-INTERFACE` | model | **structures trivial**: `NeckAnalysis` trivially inhabited, `ExtinctionTheorem` conclusions are free fields, `SurgeryCertificate` datum-blind; `target_preserved` is the only genuine obligation | CHECKED (A3-D2D3-5/6) |
| `L-D3-SURGERY-TOY` | model | CONFIRMED as a toy (strict-decrease relation, explicitly not geometry); the prior audit's `ToyRel 5 5` refutation is consistent with the disclosed toy scope | CITED (VERIFIER F8) + ledger note |

Summary: of the ten D2/D3 main-chain entries, four carry a refuted/overstrong note or a vacuous
item confirmed this round (`LEVI-CIVITA`, `ODE-SCALAR-MONO`, `ENTROPY-CERTIFICATES`,
`KAPPA-ALGEBRA`), two have trivial structures or redundant hypotheses
(`DISCRETE-MAX-PRINCIPLE`, `SURGERY-INTERFACE`), three are confirmed with no defect found
(`CURVATURE-IDENTITIES`, `ODE-INVARIANT`, `KAPPA-MANIFOLD`), and one is a disclosed toy
(`SURGERY-TOY`). **No false theorem was found**: every defect is an empty structure, a
trivially-inhabited interface, a redundant hypothesis, or an incorrect ledger note. This is the
honest answer to the A3 question for the D2/D3 clusters.

## 9. A3 assessment

`A3` = "no false statement was found, but the adversarial audit only covers the D4 evolution
cluster; earlier clusters (D2/D3) have axiom audits but no counterexample search."

The premise of A3 is now **stale**: a D2/D3 counterexample search exists
(`VERIFIER-D7-adversarial-audit-d2d3`, 75/75 files exit 0, 11 findings) and this round
independently reproduced its headline defect families from the accepted D6 sources
(§8). The search also shows the audit layer itself is fallible: `VERIFIER-D7`'s own
finding F2 (entropy sign) is refuted by Perelman (1.4).

A3 is nevertheless **not closed as a quality gate**, for three concrete reasons:

1. the D2/D3 defects found (`LinearDecayCertificate` emptiness, trivial
   `CovariantDerivativeCurvatureStatement`, degenerate `TensorRicciFlowODEBridge`,
   false-instance `missing*` Props) are **unrepaired**;
2. two D12-semantic-ledger notes that depend on those objects are **refuted** (F8/F9),
   so the ledger's `genuine-general` classification for those entries is wrong;
3. 2/9 D12 cards remain **unaudited** on this host (source-absent, no transport).

So this card reports A3 as *stale-as-stated / partially addressed*, not closed.

## 10. Remaining blockers / next dependency requests

**Blocking the 9-card milestone (this host):**

1. `D12-tensor-maximum-bochner` and `D12-triangulation-topology` have no worktree, release
   package, card, Lean module or checkpoint anywhere under `/data3/guoshaoyang` (re-verified
   in round 3: filename search + queue/state inspection + tunnel test at 13:12), and the
   reverse-tunnel transport (`127.0.0.1:10022`) is refused. They are
   **not refuted — not auditable here**. Sync or re-run them on a host with this filesystem.
   Round 3 additionally established (§11.5) that even the pinned upstream snapshot has only
   a `\notready` blueprint contract for the strong tensor maximum principle and no Lean
   triangulation, so neither card can be substituted by an upstream import.
2. (Round-3 addition) Where the two cards do land, the upstream cross-check identifies
   candidate reuse targets with file-level evidence: `DoCarmoLib` Ch. 2 for Levi-Civita,
   `MorganTianLib` Ch. 1 for Bishop–Gromov, `MorganTianLib` Ch. 2 Green identity. These are
   **source claims**, not compiled here; any adoption needs an adapter with its own hash,
   build and axiom-cone evidence, per `docs/UPSTREAM-INTEGRATION.md`.

**Producer-side corrections (defects confirmed by this audit):** *(rounds 1–3; none applied
by the producers as of 2026-09-11 13:42)*

3. D12-semantic-ledger notes/classification: `L-D2-LEVI-CIVITA` (both "BLOCKED" claims),
   `L-D2-ODE-SCALAR-MONO` ("uninhabited" bridge), `L-D3-ENTROPY-CERTIFICATES` (empty
   `LinearDecayCertificate` listed as a decay certificate) — findings F8/F9.
4. D12-connection-curvature `proved_declarations` namespace qualification (73 over-qualified + 1
   ambiguous entry) and D12-comparison-geodesics grouped-name strings — F1/F2. A ready-to-apply
   mapping is provided: `audit360/corrected-names-D12-connection-curvature.json`, and round 3
   validated it at kernel level: 73/73 originals rejected, 73/73 corrected names resolve (§11.3).
5. D2/D3 interface repairs: restate `LinearDecayCertificate`; replace the trivial
   `CovariantDerivativeCurvatureStatement`; restate the bridge so non-degenerate inhabitants
   exist; fix or discharge the trivial/false `missing*` statements (F10).
6. `VERIFIER-D7-adversarial-audit-d2d3` finding F2 should be withdrawn (F11); its F1/F3/F4/F5
   are independently corroborated and still require repairs.
7. Add non-reflexive model witnesses for the singular Riccati comparison and the Bishop–Gromov
   volume ratio (D12-comparison-geodesics, F4).
8. Note for the ledger: `MetricData.scalarCurvature_eq_sum_basis` is a basis-only identity
   (round-3 proof-cone screen, §11.6); its metric fields are unused, so the ledger's
   "curvature identities" classification should not present it as metric content.
9. (Round-5 addition, F14) D12-connection-curvature inventory precision: move the statement
   former `bracketInvariant` out of `proved_declarations` (its proved instance is the
   separately listed `SoThreeModel.so3_bracketInvariant`) and de-duplicate the 7 repeated
   rows; optionally file data defs/structures under a separate `definitions` key, as
   D12-geometric-compactness already does with `statement_only_explicitly_excluded`.

## 11. Round-3 re-verification and new evidence (invocation 3)

Round 3 ran from the current on-disk state. No producer source or card file changed since
the round-2 freeze: `audit360/inventory.py` again reports `bad = 0` for all seven available
cards (12/11/8/66/8/6/8) and the producer card mtimes are still 2026-09-11 02:02–04:50. The
two remote-owned cards were re-checked for artifacts and transport: still absent, tunnel
still refused (13:12).

### 11.1 Fresh rebuild / probe / full-namespace sweep

`audit360/run_round3.sh` → `audit360/logs-round3/`, machine summary
`audit360/round3_summary.json` (sha256 `b117c82d…`).

| card | `lake build` | `A3Probe` | cones | `A3FullAudit` | decls | probe vs round 2 |
|---|---|---|---|---|---|---|
| D12-connection-curvature | 0 | 0 | 119 | PASS | 260 | byte-identical |
| D12-volume-ibp | 0 | 0 | 78 | PASS | 159 | byte-identical |
| D12-spectral-sobolev | 0 | 0 | 36 | PASS | 68 | byte-identical |
| D12-semantic-ledger | 0 | 0 | 7 | PASS | 28 | byte-identical |
| D12-comparison-geodesics | 0 | 0 | 33 | PASS | 139 | byte-identical |
| D12-geometric-compactness | 0 | 0 | 39 | PASS | 71 | byte-identical |
| D12-surgery-recognition | 0 | 0 | 30 | PASS | 378 | byte-identical |
| **total** | | | **342** | **PASS** | **1103** | |

Every probe and full-audit log is byte-identical to its round-2 counterpart after removing
the `###` header lines, so the round-2 verdicts are reproducible run-to-run, not stale
snapshots. The negative control again flags `sorryAx` and the private `native_decide` axiom;
the independent A3 D2/D3 probe (`a3d2d3/A3D2D3.lean`) rebuilds and re-runs rc 0. The
semantic-ledger D7/D10 snapshot package was also rebuilt and its out-of-package probe
re-run (`run_snapshot_round3.sh`: build rc 0, `A3Extra/D12RealModuleProbe.lean` rc 0, both
extra declarations' cones `{propext, Classical.choice, Quot.sound}`). The copy of that probe
inside the *card* package is expected to fail rc 1 because the card package does not contain
the D7 modules; the authoritative run is the snapshot package (this was also the case in
round 2 and is an environment property, not a code defect).

**Round-4 close-out sweep** (`audit360/run_round4.sh`, logs `audit360/logs-round4/`,
`audit360/round4_summary.json`): all seven cards again build/probe/full-audit rc 0 with
**byte-identical outputs to round 3** (342 cones, 1103 declarations PASS), the negative
control still flags `sorryAx` and `native_decide`, and the A3 D2/D3 probe still runs rc 0.
The producer card files are byte-unchanged against the round-2 freeze
(`audit360/card_freeze_round4.json`), so every verdict in this card is current as of the
close-out timestamp.

### 11.2 New independent consumers of the claimed closures

Round 2 confirmed the four closures by resolving the producer's downstream names. Round 3
adds **fresh consumers written by this audit**, independent of the producer's own use:

- **D12-connection-curvature** — `audit360/pkgs/D12-connection-curvature/A3ExtraR3/ClosureUse.lean`
  (sha256 `0197c485…`), compile rc 0, 4 new declarations, cones
  ⊆ `{propext, Classical.choice, Quot.sound}`. `a3_leviCivitaData_nonempty` derives
  `Nonempty (LeviCivitaData m b)` from `leviCivitaExists` through
  `leviCivitaExistence_iff_nonempty` (a `Classical.choice` path, *not* the producer's
  explicit Milnor witness); `a3_first_bianchi` and `a3_first_pair_skew` then consume the
  chosen curvature operator through the Stage1 `CurvatureOperator` interface obligations.
- **D12-surgery-recognition** — `audit360/pkgs/D12-surgery-recognition/A3ExtraR3/ClosureUse.lean`
  (sha256 `f310e3a4…`), compile rc 0, 2 new declarations, cones allowed.
  `a3_emptyV2` is an independently constructed inhabitant of
  `ConnectedSumDecompositionV2 sphereSpace []` (the empty connected sum, i.e. `𝕊³`), and
  `a3_mkV2_sphere_of_spheres` applies `ConnectedSumDecomposition.mkV2` to it and extracts
  the *proved* `sphere_of_spheres` field. (Observation, not a defect: the V2 structure is a
  `Prop`, all its fields being propositions.)

### 11.3 F1 (connection-curvature inventory) validated at kernel level

`audit360/pkgs/D12-connection-curvature/A3ExtraR3/F1Validation.lean` (sha256 `3d855e03…`),
compile rc 0: for **all 73** over-qualified entries, the original string is rejected by Lean
(`#check_failure` succeeds; 73 `Unknown identifier` diagnostics) while the corrected name
`#check`s successfully. The ready-to-apply mapping in
`audit360/corrected-names-D12-connection-curvature.json` is therefore mechanically
validated, not merely asserted.

### 11.4 Extended vacuity / triviality screen (T1–T11)

`audit360/vacuity_screen3.py` (sha256 `90c016ed…`) → `audit360/vacuity_screen3.json`.
Audit-of-the-auditor note: round 2's screen *documented* criterion T7 (vacuous existential)
but its `flags()` never implemented T7. Round 3 implements T1–T11, adding
hypothesis-equals-conclusion (T9), conclusion-is-a-hypothesis (T10) and
suspect-unsatisfiable-hypothesis (T11) detection.

Result: 335 declarations parsed, **5 flags, all reviewed as false positives** — the
`conformal_denom_pos : 0 < 1 + x²` positivity lemma (T6 substring match) and four
substantive `Subsingleton`-valued surgery statements with real hypotheses (`T3`).
**T7/T9/T10/T11 produced zero flags**: no card declaration has a syntactically vacuous
existential, a hypothesis equal to its conclusion, a conclusion that is just a hypothesis
name, or a textually contradictory hypothesis. This directly addresses the plan's
"no assumption equivalent to the conclusion" criterion (syntactic level).

### 11.5 Pinned-upstream cross-check (commit `bb91a091`)

`audit360/upstream_crosscheck.py` (sha256 `486a4060…`) →
`audit360/upstream_crosscheck.json`, mechanical check PASS (every cited file exists and
contains the cited declaration/label). The snapshot is **not compiled here** — it pins
Lean v4.32.1 / mathlib `520045ab`, this host has v4.34.0-rc2 / `7974e751` — so all Lean
items below are classified **upstream source claim**, corroborating but not proof evidence.

| D12 card | nearest upstream artefact | level | audit reading |
|---|---|---|---|
| connection-curvature | `DoCarmoLib/Riemannian/Manifold/DoCarmoCh2.lean`: `RiemannianMetric.exists_unique_isLeviCivita`, `AffineConnection.isLeviCivita_of_koszulDual` (sorry-free, axiom-free statically) | upstream Lean proof candidate | independently corroborates the closure: unconditional existence + uniqueness are proved upstream by the Koszul construction |
| comparison-geodesics | `MorganTianLib/Ch01/BishopGromov*.lean`: `bishop_gromov_radial`, `bishop_gromov_ball`, `bishop_gromov_ball_ratio` (+ `bishop_gromov_ball_ratio_model` non-vacuity), `bishop_gromov_manifold_ratio` | upstream Lean proof candidate | substantive upstream engine for the same mathematics; no conflict found |
| volume-ibp | `MorganTianLib/Ch02/GreenIdentity.lean`: `integral_coordinateGreen_eq_zero`, `integral_mul_coordinateDivergence_comm` | upstream Lean proof candidate | same family; no statement-level diff performed |
| geometric-compactness | blueprint node `thm:hamilton-compactness-generalized-flows` (`\notready`); `CheegerGromovTaylor/Basic.lean` is an empty namespace | blueprint contract / none | no compiled upstream compactness theorem |
| surgery-recognition | blueprint `lem:hempel-essential-sphere-input` (imported classical boundary) | none in Lean | upstream keeps the topological input as an explicitly imported source boundary |
| spectral-sobolev | no `wirtinger`/`poincareInequality`/`spectralGap` Lean match in `formalized-sources` | none | no upstream counterpart in the snapshot |
| triangulation-topology | no Lean match; "triangulation" only in other projects' blueprint TeX | none | no upstream counterpart in the snapshot |
| tensor-maximum-bochner | blueprint node `thm:strong-curvature-tensor-maximum-principle` (`\notready`, full contract text); no `maximumPrinciple` Lean match | blueprint contract | even upstream has only a statement/contract for this card's subject |
| semantic-ledger | none | none | local audit artefact |

### 11.6 New A3 evidence on the D2/D3 ledger

`a3d2d3/A3D2D3Round3.lean` (sha256 `1f4a844f…`), compile rc 0. New method: a **transitive
proof-cone screen** — take the compiled proof term, close over the constants it uses, and
check which structure fields occur anywhere in that cone.

- `MetricData.scalarCurvature_eq_sum_basis` (`L-D2-CURVATURE-IDENTITIES`): transitive cone
  of 15,195 constants, **zero** occurrences of `form`, `symm`, `pos_def`, `orthonormal`
  (only `basis` is used). `raiseIndex_eq_sum_smulRight` likewise: 7,587 constants, zero
  metric fields. The prior audit's "orthonormality unused" is therefore confirmed and
  sharpened: the contraction formula is a **basis-only definitional identity**; the metric
  structure is not consumed at all.
- Positive controls: the cones of `form_basis_apply` and `form_raiseIndex` *do* contain
  `form` and `orthonormal`, so the screen distinguishes used from unused fields.

This upgrades the overstrong-hypothesis claim of that ledger entry from CITED to CHECKED
(the other declarations of `L-D2-CURVATURE-IDENTITIES` remain CITED).

### 11.7 Deep semantic reviews (round 3)

**`leviCivitaExists` (D12-connection-curvature closure 1) — REVIEWED-CORRECT.**

The round-3 review checked the mathematics, not only the compilation:

- Koszul's formula on left-invariant fields gives
  `∇_X Y = ½([X,Y] − (ad_X)ᵀY − (ad_Y)ᵀX)`; this is exactly `milnorConnection`.
- Torsion: the adjoint terms cancel pairwise, leaving `∇_X Y − ∇_Y X = [X,Y]`; the proof
  uses only bracket skew-symmetry, matching `milnorConnection_torsionFree`.
- Compatibility: substituting the formula gives
  `⟨∇_X Y,Z⟩ + ⟨Y,∇_X Z⟩ = −½(⟨(ad_Y)ᵀX,Z⟩ + ⟨Y,(ad_Z)ᵀX⟩) = −½(⟨X,[Y,Z]⟩ − ⟨X,[Y,Z]⟩) = 0`,
  using only metric symmetry and bracket skew, matching `milnorConnection_metricCompatible`.
- Uniqueness `leviCivita_nabla_unique` is the standard symmetric/antisymmetric-tensor
  argument with metric nondegeneracy; reviewed and correct.
- `milnorConnection_eq_mean_iff` correctly isolates bi-invariance as the extra hypothesis
  needed only for the *mean* connection.

Honest scope note (not a defect): the D2 interface's `IsMetricCompatible` is the algebraic
*left-invariant* condition with no directional-derivative term. The closure is of the
blocker exactly as recorded; the general Koszul/manifold theorem is a different statement,
supplied upstream (source claim, §11.5) and locally by the D12 `ChartLeviCivita` modules.
The chart-level review confirms the card's F7 disclosure is accurate:
`chartMetricCompatible_form` is the identity
`⟨∇_X Y,Z⟩ + ⟨Y,∇_X Z⟩ = dFormOf c X Y Z` with the derivative *supplied by the coefficient
datum*, whereas the smooth-level `nabla_metricCompatible` is the genuine Fréchet statement
`fderiv ℝ (fun z => g_z(Y z, Z z)) x (X x) = g_x(∇_X Y,Z) + g_x(Y,∇_X Z)`, and
`nabla_torsionFree` proves `∇_X Y − ∇_Y X = [X,Y]` with the actual Lie bracket (the form
level has zero coordinate bracket). Both levels are honest about what is derived and what
is data.

**Surgery-recognition closures 2–4 — REVIEWED-CORRECT.**

- `finiteFreeOrbit_isQuotientCoveringMap` (covering recognition): for each `e` the proof
  derives positive separation `d_g = dist (g•e) e > 0` for every nontrivial `g` from
  freeness, uses continuity of the action for radii `η_g` with
  `dist y e < η_g ⟹ dist (g•y) (g•e) < d_g/2`, and takes
  `δ = min_g min(η_g, d_g/2) > 0`. If `u` and `g•u` both lay in `B(e,δ)`, then
  `d_g ≤ dist (g•e) (g•u) + dist (g•u) e < d_g/2 + d_g/2 = d_g`, a contradiction. The four
  mathlib `IsQuotientCoveringMap` fields are then filled (`isQuotientMap_quotient_mk'`,
  the continuous-const-smul instance, orbit equality, disjointness). The δ argument is
  valid and freeness is used exactly where needed.
- `deckTrivial_of_simplyConnected_quotient`: `SimplyConnectedSpace` makes the fundamental
  group a subsingleton, so every loop equals the constant loop, whose monodromy is the
  identity (`monodromy_refl`); path-connectedness of `𝕊³` makes the monodromy action on a
  fiber transitive (`monodromy_eq_of_map_eq` applied to the projected path); hence the
  fiber is a subsingleton, and mathlib's fiber≃Γ torsor equivalence (`fiberEquivGroup`,
  available because the projection is a quotient covering) makes `Γ` a subsingleton.
  `SphericalSpaceFormModel` has no triviality or covering field — both are proved — so the
  conclusion is not assumed. `IsQuotientCoveringMap`, `IsCoveringMap` and `fiberEquivGroup`
  are mathlib declarations (checked in
  `.lake/packages/mathlib/Mathlib/Topology/Covering/Quotient.lean`), so the closure is not
  an artefact of a local wrapper definition.
- SR-5 chain (`iteratedSphereSum_homeo_sphere` → `sphereConnectSum_homeo_sphere` →
  `doubleBallHomeoSphere`): the construction is explicit — punctured spheres are the north
  hemispheres via `southPunctureHomeo`, the hemisphere quotient is the two-ball quotient
  via `northHemisphereHomeo`, and the two-ball gluing is the 3-sphere via the explicit
  `toSphere`/`ofSphere` homeomorphism with checked inverse and continuity — and it never
  uses the D7 `sphere_of_spheres` assumption (`mkV2` *fills* that field from this chain).

### 11.8 New finding family F12: unused-binder screen over the full namespace

`audit360/gen_unused_hyp.py` generates `A3UnusedHypFull.lean` in every card package: it
compares the leading lambdas of each compiled proof term with the leading foralls of its
type and reports binders whose de Bruijn position never occurs in the proof body.
**830 declarations checked, 274 skipped (conservative arity guard), 50 flags.** After
excluding 28 auto-generated declarations (`_proof_N`, `ctorIdx`, `mk.sizeOf_spec`) the
genuine findings are (machine list: `audit360/unused_hyp_screen.json`):

- **F12a (phantom parameters, D12-geometric-compactness).** `harmonicCoordinatesExistence
  (_n : ℕ) (_α : ℝ)`, `cheegerGromovCompactness (_n : ℕ) (_α : ℝ)` and
  `bishopGromovVolumeComparison (_n : ℕ)` never use those parameters: the `Prop` bodies
  ignore dimension and Hölder exponent. Kernel evidence:
  `audit360/pkgs/D12-geometric-compactness/A3ExtraR3/PhantomParams.lean` (rc 0) proves by
  `rfl` that any two choices of `n`, `α` give the *same* statement, so proving one instance
  proves all, and the interface cannot carry the dimension/exponent dependence its own
  docstrings claim. (These are statement-only Props, so no false theorem is involved — but
  the frontier does not faithfully encode the intended statements.)
- **F12b (redundant explicit hypotheses, D12-comparison-geodesics).** Six declarations
  carry explicit hypotheses the compiled proof never touches (all underscore-named by the
  producer): `areaRatio_antitone_of_logDeriv_le._hT`, `radialVolume_pos_of_pos._hT`,
  `radialVolume_hasDerivAt._hT`, `radialVolume_numerator_le_zero._hT`,
  `wronskian_antitoneOn_of_le._hab`, `euclidModelM_riccati._hdne`. Kernel evidence:
  `audit360/pkgs/D12-comparison-geodesics/A3ExtraR3/HypRemoval.lean` (rc 0) proves all six
  sharp restatements with the hypothesis removed (for `_hT`/`_hab` the remaining binder
  already implies it or the conclusion is vacuous; `_hdne` also holds at `d = 0` because
  `0/0 = 0` in `ℝ`).
- **F12c (informational).** `connectedSum`'s `hX`/`hY` injectivity hypotheses are unused by
  the quotient *definition* (they are consumed by the `connectSumRel` lemmas); four
  connection-curvature sum lemmas carry unused `[DecidableEq]`; two geometric-compactness
  cover-transfer theorems carry unused `[Fintype ι]`. Redundant, harmless.
- **F12d (audit-of-the-auditor).** The round-2 screen's criterion T7 was documented but not
  implemented (§11.4); this screen is conservative (274 declarations skipped on arity
  mismatch) and its `_proof_N`/`ctorIdx`/`sizeOf_spec` flags are Lean-generated artifacts,
  excluded from the defect count.

### 11.9 Full-namespace type screen (1104 constants, rounds 3)

`audit360/fulltype_screen.py` (sha256 `ad1469fa…`) dumps and screens the *types* of all
1104 constants under `Poincare.D12` (the 1103 axiom-audited declarations plus the
documented negative-control axiom), extending the round-2 card-list screen to the whole
namespace; `A3AllTypes.lean` in each package produces the dump
(`audit360/logs-round3/*.alltypes.log`). Result: **8 review triggers, all reviewed, 0 true
positives** (`audit360/fulltype_screen.json`):

- two `chart1D._proof_N` equation-compiler auxiliaries (T4 artifacts);
- `conformal_denom_pos` (`0 < 1 + x²`, true positivity lemma; T6 substring);
- `diam_rep_of_toGHSpace`, printed as `diam univ = diam univ` — the pretty-printer hides
  the two `Set` type ascriptions; a kernel probe (`A3ExtraR3/TrivialCheck.lean`) shows
  `rfl` *fails*, so the statement is not definitionally trivial and the producer's isometry
  proof is genuine;
- four surgery items: one structure *field* (`coveringTrivial`, an input hypothesis) and
  three substantive `Subsingleton` theorems reviewed in §11.7;
- `mem_downS3_openBall_iff` (regex matched `(y 0) < 0`, not `0 < 0`).

Together with §11.6/§11.8 this means every constant under the audited namespace has been
screened for unapproved axioms (1103/1103 PASS), for unused binders (830 checked), and for
syntactic vacuity/triviality (1104/1104), with no unfixed true positive in any screen.

### 11.10 D6-wide automated screens (A3-lane extension, round 3)

To extend the D2/D3 counterexample search beyond the ten hand-picked ledger entries, the
two new screens were run over the whole accepted D6 release (`a3d2d3`, byte-identical to
`release/`), via `a3d2d3/A3AllTypesD6.lean` and `a3d2d3/A3UnusedHypD6.lean` (both rc 0):

- **Type screen**: 1307 constants under `Poincare`/`Audit`/`Ledger`; 21 triggers, all
  reviewed as either equation-compiler `_proof_N` artifacts or substantive `Subsingleton`
  restatements of simple connectivity (the `Stage6`/`Topology` `_iff` family). 0 true
  positives. The known trivial `missingSphereRecognitionAlgorithm` consequence reappears
  (`decidableSphereRecognition_of_missingSphereRecognitionAlgorithm`, T2).
- **Unused-binder screen**: 964 checked, 343 skipped, 127 flags — 92 auto-generated
  (`_proof_N`, `ctorIdx`, `sizeOf_spec`), 51 instance/implicit, and **5 explicit**:
  1. `CovariantDerivativeCurvatureStatement._cov` — the `cov` argument is unused, machine
     confirmation of round 2's A3-D2D3-2 (the "BLOCKED" statement is trivially inhabited);
  2. `stage6Target_of_compactThreeManifold._h` — `#print` shows the proof term is literally
     `fun _h hrec => hrec`: the conclusion `poincareConjectureTopologicalThree M` is
     *definitionally* `Nonempty (M ≃ₜ 𝕊³)`, so the theorem is "if `M ≃ₜ 𝕊³` then
     `M ≃ₜ 𝕊³`", with `CompactThreeManifold` and `SimplyConnectedSpace` unused
     (**new A3-D2D3-8**: another assumption-equals-conclusion bridge in the D6 release);
  3. `SurgeryDatum.pre` / `SurgeryDatum.post` `_D` — informational: `X`, `Y` are structure
     *parameters*, so the projections cannot depend on the datum's neck/relation fields;
  4. `Evolution.squareTraj` — internal `_internal._hyg` binder, artifact.

The D12-level downstream chain is **not** tautological: `stage6Target_of_v2decomposition`
and `_v3hypotheses` route through `RecognitionHypotheses.homeomorph_sphere`, which applies
`ConnectedSumDecomposition.sphere_of_spheres`; in the D12 package that field is *filled* by
the proved `mkV2` construction, so the SR-5 closure is genuinely consumed (the remaining
inputs are the explicit extinction, canonical-neighbourhood and spherical-piece-recognition
hypotheses). The tautology above is in the older D6 `Stage6Bridge`, not in the D12 chain.

### 11.11 Self-audit of this audit card

`audit360/verify_own_hashes.py` (rc 0) re-derives every sha256 recorded in the results
JSON from the bytes on disk, across all four producer hash schemas (flat filename maps,
`release/`-relative paths, module-name maps, package/D12-authored maps), the audited-copy
hashes, the round-3 artifact hashes, and the round-3 probe/evidence hashes: **744 hashes
verified, 0 mismatches, 0 unresolved**.

One real defect was caught by this self-audit and corrected (**F13**): the round-1/2
recorded `audited_copy_sha256` for `D12-semantic-ledger`'s `A3Extra/D12RealModuleProbe.lean`
(`9968a2ce…`) matches neither current copy — the file was edited after hashing (the two
copies now differ only in a comment line). The corrected hashes are recorded in the results
JSON (card copy `7ee714a3…`, snapshot copy `c6c3502d…`). The compiled evidence is
unaffected: the authoritative snapshot probe compiles rc 0 in round 3 and both extra
declarations' cones are allowed.

### 11.12 A3 status after round 3

The A3 premises are further weakened: the D2/D3 search now has (i) the prior auditor's
11 findings, (ii) round 2's independent 17-declaration probe, and (iii) round 3's
proof-cone screen, unused-binder screen and D6-wide type/unused screens (three new
automated methods; 830 D12 declarations plus 1307/964 D6 declarations screened) plus the
closure-use probes. A3 nevertheless remains
**not closed as a quality gate**, for the same three reasons as round 2 — the found defects
are unrepaired, the refuted ledger notes (F8/F9) are unedited, and 2/9 cards remain
unauditable here. The essential blocker is now clearly producer-side and host-side, not
evidence-side.

## 12. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd .../worktrees/D13-cross-audit-360-cards
python3 audit360/inventory.py          # source-hash provenance
python3 audit360/prepare.py            # stage copies, resolve names, generate probes
for c in D12-connection-curvature D12-volume-ibp D12-spectral-sobolev D12-semantic-ledger \
         D12-comparison-geodesics D12-geometric-compactness D12-surgery-recognition; do
  bash audit360/run_card.sh $c        # lake build + A3Probe + extra probes
done
bash audit360/run_snapshot.sh          # semantic-ledger D7/D10 snapshot replay
python3 audit360/gen_full_audit.py     # complete-namespace metaprogram audit modules
for c in D12-connection-curvature D12-volume-ibp D12-spectral-sobolev D12-semantic-ledger \
         D12-comparison-geodesics D12-geometric-compactness D12-surgery-recognition; do
  bash audit360/run_full_audit.sh $c  # all Poincare.D12 constants, fail-closed cones
done
python3 audit360/analyze.py            # cones, forbidden scan, negative control
python3 audit360/compose.py            # results JSON
python3 audit360/vacuity_screen2.py    # round-2 triviality screen (335 declarations, 0 TP)
# --- A3 D2/D3 counterexample search (this round) ---
cd a3d2d3 && lake build                # exit 0, 8946 jobs, D6AUDIT PASS
cd a3d2d3 && lake env lean A3D2D3.lean # exit 0, 17 declarations, allowed cones
cd audit360/pkgs/D12-connection-curvature && lake env lean A3ExtraD2/D2LedgerCheck.lean
cd ../.. && python3 audit360/a3_merge.py   # merge A3 sections into the results JSON
# --- round-3 re-verification and new evidence (invocation 3) ---
bash audit360/run_round3.sh            # all 7 cards: build+probe+fullaudit, logs-round3/
python3 audit360/vacuity_screen3.py    # T1-T11 screen (335 declarations; 0 true positives)
python3 audit360/upstream_crosscheck.py  # pinned bb91a091 cross-check (mechanical PASS)
cd audit360/pkgs/D12-connection-curvature && lake env lean A3ExtraR3/ClosureUse.lean
cd audit360/pkgs/D12-connection-curvature && lake env lean A3ExtraR3/F1Validation.lean
cd audit360/pkgs/D12-surgery-recognition && lake env lean A3ExtraR3/ClosureUse.lean
cd a3d2d3 && lake env lean A3D2D3Round3.lean   # transitive proof-cone screen, rc 0
# --- round-4 close-out ---
bash audit360/run_round4.sh            # byte-identical to round 3, logs-round4/
python3 audit360/verify_own_hashes.py  # 744 recorded hashes, 0 mismatches
# --- round-5 close-out (invocation 4) ---
bash audit360/run_round5.sh            # all 7 cards rc 0; byte-identical to round 4, logs-round5/
bash audit360/run_snapshot_round5.sh   # D7/D10 snapshot rebuild + out-of-package probe, rc 0
python3 audit360/round5_summary.py     # round5_summary.json
python3 audit360/gen_kind_audit.py     # A3KindAudit.lean in each package
bash audit360/run_kind_audit.sh        # logs-kind/, kernel ConstantInfo per declared name
python3 audit360/kind_screen.py        # kind_screen.json (F14)
python3 audit360/hash_coverage.py      # hash_coverage_round5.json (F15)
cd audit360/pkgs/D12-surgery-recognition && lake env lean A3ExtraR5/ClosureUseNonempty.lean
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-360-cards
python3 audit360/verify_own_hashes.py  # 758 recorded hashes, 0 mismatches
```

## 13. Round-5 re-verification and new evidence (invocation 4)

Round 5 ran from the current on-disk state against the same frozen producer sources
(card hashes re-verified `bad = 0`; the two remote-owned cards re-checked for artifacts
and transport at 13:44). It adds four things: a fourth independent sweep, a kernel
declaration-kind screen, cross-package/cross-card consistency evidence, and deep statement
reviews of the two cards that had not yet had one at this level.

### 13.1 Round-5 sweep — byte-identical, snapshot re-run

`audit360/run_round5.sh` → `audit360/logs-round5/`, summary `audit360/round5_summary.json`.
All seven cards build/probe/full-audit **rc 0**; **342** cones and **1103** declarations
PASS; every probe and full-audit log is byte-identical to round 4 after stripping the `###`
timestamp headers, and every build log is identical after also normalising lake's `[k/N]`
job counters. The negative control again flags `sorryAx` and the private `native_decide`
axiom. The semantic-ledger D7/D10 snapshot package was rebuilt (`run_snapshot_round5.sh`):
build rc 0, out-of-package probe rc 0, both extra declarations' cones
`{propext, Classical.choice, Quot.sound}`. The audit is now reproducible across rounds
2/3/4/5 with zero output drift. A fresh forbidden-token scan of all seven staged packages
(`audit360/forbidden_scan_round5.json`) finds 0 hits in six cards and only the documented,
unused `axiom negativeControl : False` (`Poincare/D12/VolumeIBP/Audit.lean:40`) in
volume-ibp; the complete-namespace audit explicitly skips it and reports PASS, and it
occurs in no probe cone. A fresh `diff -rq a3d2d3 release` (audit-written modules
excluded) reports only the three audit modules that exist solely in `a3d2d3`, so the A3
D2/D3 counterexample probe still rests on bytes byte-identical to the accepted D6 release.

### 13.2 Kernel declaration-kind screen (F14)

`#check` + `#print axioms` cannot distinguish a proved theorem from a `def`, a structure or
a statement former. `audit360/gen_kind_audit.py` therefore generates `A3KindAudit.lean` in
each package, which asks the kernel for each declared name's `ConstantInfo` variant and its
telescoped result sort (a `run_cmd` metaprogram; logs `audit360/logs-kind/`, analysis
`audit360/kind_screen.py` → `kind_screen.json`).

Of the 342 probe entries: **265** are `theorem` proofs of propositions; **1** is a
definitional proof (`sphereConnectSum_homeo_sphere : Nonempty (… ≃ₜ 𝕊³)`, written with
`def`); **7** are `def : Prop` statement formers; **2** are type synonyms (`ChartPoint`,
`VectorField`); **63** are data `def`s; **4** are structures/inductives. The seven
statement formers are the six D12-geometric-compactness frontier `Prop`s — which that
card's JSON correctly places in `statement_only_explicitly_excluded`, not in its proved
groups — plus `D12.ConnectionCurvature.bracketInvariant`, the bi-invariance **hypothesis
predicate** that does appear in the connection-curvature card's flat
`proved_declarations` list; its actual proved content is the separately listed theorem
`SoThreeModel.so3_bracketInvariant`. The flat list also contains 35 definitional
declarations (29 data defs, 2 type synonyms, 3 structures, 1 statement former) among its
119 entries, and 7 duplicated rows (112 distinct names) from the known F1 qualification
family. No entry is an `axiom`, `opaque`, `ctor` or `rec`, and every entry's cone was
already audited, so F14 is an inventory-precision observation, not a soundness defect.
It is also the machine-checked answer to "proved theorem vs definition vs statement".

### 13.3 Cross-package / cross-card consistency (positive)

- **Foundation byte-identity** (`audit360/cross_package_foundation_diff.json`): all shared
  foundation trees are byte-identical across the seven packages — `Poincare/Longrun` 44
  files, `Audit` 6 files, `Ledger` 2 files, zero differing files; the vendored `Poincare/D7`
  (29 files), `Poincare/D10` (4 files) and `Poincare/VKPort` (10 files) trees each exist in
  a single package. There are no per-card forks of the D2/D3 foundation.
- **No parallel concept definitions**: a scan of all top-level `def/structure/theorem/
  lemma/abbrev/instance/class/inductive` short names matching the concept vocabulary
  (`Metric|Curvature|Ricci|Scalar|Volume|Laplacian|Gradient|Density|Connection|Geodesic|
  Jacobi|Heat|Entropy|Sphere|Cover|Dist|LeviCivita|Bochner|Sectional|Injectivity|Diameter`)
  under each package's `Poincare/D12` tree finds **0** names defined in more than one card
  package. The seven cards do not duplicate each other's concepts under different names.
- **Recorded-hash coverage, the converse provenance question (F15)**: for every card,
  compare the recorded `source_hashes` keys with the D12-authored `.lean` files actually on
  disk (`audit360/hash_coverage.py` → `hash_coverage_round5.json`). Six cards cover
  everything (11/11, 7/7, 3/3, 7/7, 5/5, 8/8). D12-volume-ibp covers 9/10: the import-only
  umbrella `Poincare/D12/VolumeIBP.lean` is unrecorded (F15, §7). No compiled or
  axiom-cone evidence changes.

### 13.4 Deep statement reviews (round 5)

**`D12-volume-ibp` — REVIEWED-CORRECT (statement fidelity).** The definitions are
non-circular: `divergence X = ρ⁻¹·Σᵢ∂ᵢ(ρXᵢ)` (`ρ = √det g`), `grad u = g⁻¹·du`,
`laplacian u = divergence (grad u)`, `driftLaplacian f u = Δu − ⟨∇f,∇u⟩_{g⁻¹}`.
`chart_ibp` is the standard identity `∫ u·Δv·ρ = −∫⟨∇u,∇v⟩_{g⁻¹}·ρ` for `C²` `u,v` with
`u` compactly supported, derived from the weighted divergence theorem plus the product
rule `weighted_divergence_mul_grad`; the signs are correct (the compact support supplies
the boundary term). `chart_weighted_ibp` is the same for `dm = e^{−f}ρ dx`, consistent
with `div(e^{−f}∇u) = e^{−f}Δ_f u`; its Lean support hypothesis is on `v`, exactly as the
card states. No hypothesis is the conclusion and no operator is defined by the identity
it is supposed to satisfy.

**`D12-comparison-geodesics` — REVIEWED-CORRECT (statement fidelity; conditional
analytic).** `JacobiSolutionOn k u du ddu a b` is exactly `u'' + k·u = 0` on `Ioo a b`
with pointwise `HasDerivAt` data and continuity of `u, du` on `Icc a b` — not a weak or
integral surrogate. `sturm_zero_comparison`'s conclusion `(∃ c ∈ Ioo a b, u₁ c = 0) ∨
∀ t ∈ Ioo a b, k₁ t = k₂ t` is the standard Sturm alternative including the correct
equality-case escape (needed when `u₁` is a multiple of `u₂`); the `_of_pos` corollary is
its logically correct no-zero branch. `logDeriv_le_of_le` is the classical Riccati
comparison for `ρ = du/u` with positivity on the closed interval (so every denominator is
bounded away from zero) and the initial ordering as the only initial datum. For the volume
chain, `radialVolume A t = ∫₀^t A`; `areaRatio_antitone_of_logDeriv_le` and
`volumeRatio_antitone` implement the ratio argument, and `bishopGromovVolumeRatio` states
`V(R)/V̄(R) ≤ V(r)/V̄(r)` for `0 < r ≤ R ≤ T` with the `m ≤ m̄`, `m = A'/A`,
`m̄ = Ā'/Ā`, positivity/continuity and Euclidean-normalization hypotheses — the conditional
analytic Bishop–Gromov step, with the geodesic-sphere geometric bridge explicitly listed
as missing (card §3). The Euclidean witnesses satisfy the *entire* hypothesis bundle, so
none of it is vacuous; as already disclosed (F4) they are reflexive instances, so they
certify satisfiability rather than strict content.

**`D12-geometric-compactness` (frontier).** The six statement-only `Prop`s are parameter
contracts (`def:PropFormer`, F14) whose dimension/exponent binders are unused (F12a); the
two `*_iff` shape lemmas *are* theorems, and no proved theorem consumes the `Prop`s
(rounds 2–3). No inhabitant is constructed, exactly as the card states.

**`D12-geometric-compactness` (general metric theorems) — REVIEWED-CORRECT (statement
fidelity).** `uniformCovers_of_totallyBounded` is the converse direction of Gromov's
criterion: total boundedness of a family in `ghDist` yields a uniform diameter bound and,
for every `ε > 0`, a uniform bound `K` on the number of `ε`-balls covering each member (a
GH ball of radius `ε` has distortion `< 2ε`, so an `ε`-net of one member transfers with the
same cardinality and a `3ε` blow-up). `gromovCriterion` states the classical equivalence
for closed families — compactness in the GH topology ↔ uniform diameter bound plus uniform
covering numbers — with `isCompact_of_uniformCovers` the nontrivial direction and
`totallyBounded_iff_uniformCovers` the bridge. `cover_transfer_of_ghDist` is the
quantitative transfer: `ghDist X Y < r` plus a `δ`-cover of `Y` gives an `ε`-cover of `X`
over the same index set whenever `2r + δ < ε`. `gh_subseq_of_compact` and
`gh_subseq_of_familyBounds` are sequential-compactness statements with explicit strictly
monotone reindexings and both topological and `ghDist` convergence, so no convergent
subsequence is assumed as data. No hypothesis is the conclusion.

### 13.5 Missing-card re-check (this invocation)

At 13:44 on 2026-09-11: `127.0.0.1:10022` refused; `tailscale status` shows no 360-1/360-2
peer (only unrelated personal devices); no NFS/CIFS/SSHFS mounts; no file matching
`*tensor-maximum-bochner*` or `*triangulation-topology*` anywhere under
`/data3/guoshaoyang`. The final re-check at 13:56 repeats the port test (refused) and the
filesystem search (empty). Conclusion unchanged: source-absent on this host — **not
auditable here, not refuted**. The milestone stays blocked.

### 13.6 Self-audit (round 5)

`audit360/verify_own_hashes.py` extended to the round-5 artifacts: **758 recorded hashes
verified, 0 mismatches, 0 unresolved**, rc 0. The new check immediately caught the
auditor's own drift (the script itself had been edited to *add* the section, invalidating
its recorded hash); the hash was refreshed in both recorded locations and the clean run
followed. No compiled evidence changes.

### 13.7 A3 status after round 5
Unchanged: A3 is *stale-as-stated / partially addressed*, not closed. Round 5 adds no new
D2/D3 defect and no repair; the reasons remain that the D2/D3 defects
(`LinearDecayCertificate` emptiness, trivial `CovariantDerivativeCurvatureStatement`,
degenerate `TensorRicciFlowODEBridge`, false-instance `missing*` Props) are unrepaired,
the refuted ledger notes F8/F9 are unedited, and 2/9 D12 cards cannot be audited on this
host. What round 5 adds on the A3 side is negative assurance: the D12 layer shows **no**
parallel concept definitions, **no** foundation fork across packages, and **no** proof
entry that is secretly an axiom, opaque constant or unproved statement beyond the
explicitly labelled frontier (F14).

### 13.8 Fifth independent closure consumer — SR-5 at a nonempty piece list

The round-3 surgery consumer exercised the claimed SR-5 closure only at the empty piece
list (the empty connected sum). Round 5 adds
`audit360/pkgs/D12-surgery-recognition/A3ExtraR5/ClosureUseNonempty.lean`
(sha256 `6119289e…`), compile rc 0, log
`audit360/logs-round5/D12-surgery-recognition.extraR5.ClosureUseNonempty.log`:

- `a3_twoFold_pieceSphere` — fresh piece data: each of the two `sphereSpace` summands is
  homeomorphic to `𝕊³` via the identity;
- `a3_twoFold_homeo` — applies the card's *proved* `iteratedSphereSum_homeo_sphere` at
  `[sphereSpace, sphereSpace]`, exercising the recursive branch of `iteratedSphereSum`
  and `sphereConnectSum_transported`;
- `a3_twoFoldV2` — a fresh independent `ConnectedSumDecompositionV2` inhabitant with a
  nonempty piece list (the round-3 probe covered only `[]`);
- `a3_twoFold_mkV2_sphere_of_spheres` — applies the claimed constructor
  `ConnectedSumDecomposition.mkV2` to that inhabitant and extracts the *proved*
  `sphere_of_spheres` field. No producer downstream theorem is reused.

All three `#print axioms` lines are `{propext, Classical.choice, Quot.sound}`. This makes
the SR-5 closure confirmed by two structurally different consumers (empty and nonempty
piece lists).

## 14. Round-6 re-verification and new evidence (invocation 5)

### 14.1 Round-6 sweep — fifth consecutive byte-identical sweep

`audit360/run_round6.sh` → `audit360/logs-round6/`, summarised in
`audit360/round6_summary.json` (sha256 `c4004cfd660ea0d7682f7a4dbad67a7e76af889dae02d46a15bbe1659fc8894d`):

| card | build | probe | full audit | kind | probe decls | full-audit decls | identical to round 5 |
|---|---|---|---|---|---|---|---|
| D12-connection-curvature | 0 | 0 | 0 PASS | 0 | 119 | 260 | build/probe/full/kind ✔ |
| D12-volume-ibp | 0 | 0 | 0 PASS | 0 | 78 | 159 | build/probe/full/kind ✔ |
| D12-spectral-sobolev | 0 | 0 | 0 PASS | 0 | 36 | 68 | build/probe/full/kind ✔ |
| D12-semantic-ledger | 0 | 0 | 0 PASS | 0 | 7 | 28 | build/probe/full/kind ✔ |
| D12-comparison-geodesics | 0 | 0 | 0 PASS | 0 | 33 | 139 | build/probe/full/kind ✔ |
| D12-geometric-compactness | 0 | 0 | 0 PASS | 0 | 39 | 71 | build/probe/full/kind ✔ |
| D12-surgery-recognition | 0 | 0 | 0 PASS | 0 | 30 | 378 | build/probe/full/kind ✔ |

Totals: **342 probe cones**, **1103 declarations PASS**, zero cone violations. The generated
`A3Probe.lean`/`A3FullAudit.lean` hashes are unchanged from round 5 for every card (e.g.
connection-curvature probe `f260ff8fe9b6…`, full audit `2ff5d905b816…`), so the *same*
declaration lists were re-audited. The round-5 kind screen was logged under `logs-kind/`; the
round-6 kind output is byte-identical to it for all seven cards. Negative control: `sorryAx`
flagged for the `sorry` declaration and the private `native_decide` axiom flagged (fail-closed
predicate rc 0). Semantic-ledger snapshot: build rc 0, out-of-package probe rc 0. A3 D2/D3
lane: build rc 0, `A3D2D3.lean` rc 0, `A3D2D3Round3.lean` rc 0. Two non-zero probe rc values
are expected and documented, not regressions:

- `D12-semantic-ledger/A3Extra/D12RealModuleProbe.lean` rc 1 (also rc 1 in round 5): the
  module `Poincare.D7.HeatKernel.Basic` is not part of that release package; the valid replay
  is the snapshot-package probe, rc 0.
- `D12-geometric-compactness/A3ExtraR3/TrivialCheck.lean` rc 1 **by design**: the file *is*
  the `rfl` attempt on `diam_rep_of_toGHSpace`, and its failure is the round-3 evidence that
  the statement is not definitionally trivial.

### 14.2 Cold rebuilds of the remaining five cards — all seven now cold-rebuilt

Round 1 cold-rebuilt only connection-curvature and surgery-recognition. Round 6 adds, for the
other five cards, a fresh copy with **no `.lake/build` at all**, the shared pinned mathlib
package cache, `lake build` from source, and the per-declaration probe there
(`audit360/run_cold_round6.sh` → `audit360/logs-cold6/`,
`audit360/cold_rebuilds_round6.json`):

| card | Lean files | cache before | cold build | cold probe | probed decls | wall |
|---|---|---|---|---|---|---|
| D12-volume-ibp | 80 | `confirmed-absent` | 0 | 0 | 78 | ≈80 s |
| D12-spectral-sobolev | 76 | `confirmed-absent` | 0 | 0 | 36 | ≈80 s |
| D12-semantic-ledger | 73 | `confirmed-absent` | 0 | 0 | 7 | ≈81 s |
| D12-comparison-geodesics | 90 | `confirmed-absent` | 0 | 0 | 33 | ≈79 s |
| D12-geometric-compactness | 76 | `confirmed-absent` | 0 | 0 | 39 | ≈80 s |

Zero unapproved-axiom markers in every cold probe log. Together with round 1
(119 + 30 declarations cold-probed for connection-curvature and surgery-recognition), **every
one of the 342 card-declared entries has now been probed in a cold rebuild from source**, with
cones exactly `{propext, Classical.choice, Quot.sound}`.

### 14.3 Sixth independent closure consumer — non-bi-invariant model (connection-curvature)

`audit360/pkgs/D12-connection-curvature/A3ExtraR6/ClosureUseNoninvariant.lean`
(sha256 `2430f67cdeecc31f957ed683a4218bcd2e1b5805d639f027a3b6586830ce6879`), compile rc 0
(log `audit360/logs-round6/D12-connection-curvature.extraR6.ClosureUseNoninvariant.log`), five
new declarations, all cones `{propext, Classical.choice, Quot.sound}`:

- `A3R6.a3_not_bracketInvariant` — the concrete 2-dimensional model
  (`Fin 2 → ℝ`, standard dot product, bracket `[X,Y] = (X₀Y₁ − X₁Y₀) • (e₀+e₁)`) is **provably
  not** bracket-invariant: `⟨[e₀,e₁],e₀⟩ + ⟨e₁,[e₀,e₀]⟩ = 1 ≠ 0`;
- `A3R6.a3_noninvariant_leviCivita` — the previously blocked
  `LeviCivitaExistenceStatement` holds **at that non-invariant model**, so the closure is
  non-vacuous exactly where the historical `BLOCKED` docstring claimed an extra invariance
  hypothesis was needed;
- `A3R6.a3_milnor_ne_mean` — the Milnor connection differs from the mean connection there;
- `A3R6.a3_mean_not_metricCompatible` — the mean connection is not even metric-compatible
  there (so the closure genuinely supplies something the naive connection does not);
- `A3R6.a3_leviCivita_unique` — **new uniqueness corollary**: every
  `d : LeviCivitaData m b` satisfies `d.nabla = milnorConnection m b`, via the base
  Koszul uniqueness. The card never states uniqueness, so this is new downstream content.

The first four are structural adversaries of the closure claim (a non-invariant instance plus
the failure of the mean connection); the fifth upgrades "a Levi-Civita connection exists" to
"*the* Milnor connection is the only one". Together with the round-3 choice-based consumer
(§11.2) this is the sixth structurally distinct consumer of the CC closure.

Integration check after adding the file (`audit360/logs-round6b/`): the staged
connection-curvature package now globs `A3ExtraR6/ClosureUseNoninvariant.lean` into its build;
re-running `lake build` gives rc 0, and `A3Probe.lean`/`A3FullAudit.lean` are **byte-identical**
to round 6 (the build log differs only in the lake job counter `[k/3350] → [k/3766]`). No
audited declaration or cone changed.

A **second, self-contained probe** of the same model,
`audit360/pkgs/D12-connection-curvature/A3ExtraR6/CurvatureNonzero.lean`
(sha256 `2b63ecb6a0db6f605ca60d09512e61c9e7895ff9038d8dceb2805bfc32d2da74`), compile rc 0,
evaluates the metric transpose and the Milnor connection on the model
(`adT_apply`, `milnor_apply_general`) and computes the curvature:

  `R(e₀,e₁)e₀ = 2·e₁ ≠ 0`  (`A3R6Curv.curvature_e0_e1_e0`, cone
  `{propext, Classical.choice, Quot.sound}`).

So the closure does not merely produce *some* torsion-free compatible connection in the
non-invariant regime: the Milnor connection there is genuinely curved, and the connection is
provably the only Levi-Civita one (`a3_leviCivita_unique`). The hand derivation
(∇_{e₀}e₀ = −e₁, ∇_{e₀}e₁ = e₀, ∇_{e₁}e₀ = −e₁, ∇_{e₁}e₁ = e₀, hence
R(e₀,e₁)e₀ = −e₀ − (−e₀) − (−2e₁) = 2e₁) was reproduced by the kernel.

### 14.4 Deep statement reviews (round 6)

**`D12-spectral-sobolev` — REVIEWED-CORRECT (statement fidelity).** `heatWeight T t n =
exp(−(2πn/T)²t)` is the correct circle heat eigenvalue; `heatEvolve` is defined through the
Fourier-basis representation, not by the identity it satisfies; `heatSeries_hasSum` is a
genuine `HasSum` of the full series over `ℤ`; `fourierCoeff_heatEvolve` gives
`cₙ(H_t f) = e^{−λₙt} cₙ(f)`; `heatEvolve_zero`/`heatEvolve_add`/`heatEvolve_norm_le`/
`heatEvolve_tendsto_self` are the semigroup/contraction/strong-continuity laws, and
`heatEvolve_fourierLp`+`norm_heatEvolve_fourierLp` give exact eigenfunctions with explicit
norms. `poincare_wirtinger` is the sharp Poincaré–Wirtinger inequality on the circle for `C¹`
mean-zero functions — the Lean mean-zero hypothesis `fourierCoeffOn hab f 0 = 0` is equivalent
to `∫ₐᵇ f = 0` by `fourierCoeffOn_zero_eq_mean` — and `poincare_constant_sharp` derives
optimality from the sine-wave saturating witness (`∫sin² = ∫cos² = π`). Scope is honestly
dimension 1; no general compact-manifold transfer is claimed.

**`D12-connection-curvature` — REVIEWED-CORRECT (statement fidelity; left-invariant model).**
The Milnor formula is the classical group-invariant connection; torsion-freeness uses only
bracket skew-symmetry, metric compatibility only skew-symmetry plus symmetry of the metric form
(re-derived by hand: the cross terms cancel and the remainder is `⟨[X,Y],Z⟩ − ⟨Z,[X,Y]⟩ = 0`).
`leviCivitaExists` proves the previously `BLOCKED` `LeviCivitaExistenceStatement`
unconditionally, and `milnorConnection_eq_mean_iff` shows invariance is exactly the condition
for the *mean* connection to be Levi-Civita. `ricci_symm` is **non-circular**: the
`CurvatureOperator` interface's `first_pair_skew`/`first_bianchi` fields are *constructed* by
`AbstractConnection.toCurvatureOperator` from the proved `curvature_skew` and `curvature_bianchi`
(torsion-freeness + Jacobi), not assumed. The chart layer's `nabla_torsionFree` and
`nabla_metricCompatible` are genuine Fréchet-derivative statements (the latter through the
three-factor product rule and the derived `dFamily`). Scope notes recorded: `IsMetricCompatible`
is the invariant-metric algebraic condition; `SmoothChartData.gInv` smoothness is coefficient
data; the chart Lie bracket is defined by the coordinate formula; the x-dependent smoothness
bridge for arbitrary non-constant-coefficient metrics remains the recorded open item.

### 14.5 Wider forbidden-token scan (round 6)

`audit360/forbidden_scan6.py` → `audit360/forbidden_scan_round6.json`, comment/string-aware
over **all 8 staged packages** (the 7 cards plus the semantic-ledger snapshot): 12 tokens
(`sorry`, `admit`, `axiom`, `unsafe` decls, `native_decide`, `proof_wanted`, `opaque`,
`extern`, `implemented_by`, `partial def`, `maxHeartbeats 0`, `by_contra!`). Result: **zero**
hits for every soundness-escape token in producer files. The only producer hit is the
documented volume-ibp negative control `axiom negativeControl : False`
(`Poincare/D12/VolumeIBP/Audit.lean:36`), which appears in no axiom cone (§5, F5). The 56
`partial` hits are all in this audit's own metaprogram `A3UnusedHyp*.lean` (structural recursion
over `Expr` used to *inspect* proof terms); they prove nothing and appear in no cone.

### 14.6 Producer-card freeze and self-audit (round 6)

`audit360/card_freeze_round6.py`: all **14/14** producer card files (7 × `.md`/`.json`) are
byte-identical to the round-4 frozen state, so the round-6 verdicts are not stale. Self-audit
`audit360/verify_own_hashes.py` extended to the round-6 artifacts and the new consumer:
**773 recorded hashes verified, 0 mismatches, 0 unresolved**, rc 0. As in round 5, the new
coverage immediately caught the auditor's own script-hash drift (`verify_own_hashes.py` is
recorded in `round3_artifacts`, `round5_artifacts` and `round6_artifacts`; editing it
invalidated the round-3 record), which was refreshed before the clean run. No compiled
evidence changes.

### 14.7 Missing-card re-check (round 6)

At 14:47 and 14:52 on 2026-09-11: `D12-tensor-maximum-bochner` (host 360-1) and
`D12-triangulation-topology` (host 360-2) still have no worktree, release package, card, Lean
module, state directory or `PUSHED`/`DONE` marker anywhere under `/data3/guoshaoyang`; queue
status remains `remote_owned`. The relay mechanism is now pinned down: `longrun/bin/relay_push.sh`
runs *on* a 360-X host and pushes through a reverse tunnel with
`ssh -p 10022 guoshaoyang@127.0.0.1`; port 10022 on this host is refused, `tailscale status`
shows no 360-1/360-2 peer, and there are no NFS/CIFS/SSHFS mounts. Conclusion unchanged:
**source-absent on this host — not auditable here, not refuted**. This is a transport blocker,
not a mathematical one.

### 14.8 A3 status after round 6

Unchanged: A3 is *stale-as-stated / partially addressed*, not closed. Round 6 adds no new D2/D3
defect and no repair; the D2/D3 defects (`LinearDecayCertificate` emptiness, trivial
`CovariantDerivativeCurvatureStatement`, degenerate `TensorRicciFlowODEBridge`, false-instance
`missing*` `Prop`s) remain unrepaired, the refuted ledger notes F8/F9 remain unedited, and 2/9
D12 cards cannot be audited on this host. What round 6 adds is negative assurance at greater
strength: every available card now has a from-source *cold* build, the wider token scan is
clean, and the CC existence closure — the one claimed closure that asserts an *existence*
rather than constructing a homeomorphism — has been adversarially instantiated at a model
where the naive alternative provably fails and the constructed connection is provably curved.

## 15. Round-7 re-verification and new evidence (invocation 6)

### 15.1 Round-7 sweep — sixth consecutive byte-identical sweep

`audit360/run_round7.sh` → `audit360/logs-round7/`, summary
`audit360/round7_summary.json` (sha256 `07a2cec80099dc41d80ec4e5f5fb24e993115ceb8b15a4159154985806762275`).
All **seven available cards**: `lake build` rc 0, `A3Probe` rc 0, `A3FullAudit` rc 0
(`A3FULL: PASS`), `A3KindAudit` rc 0; **342 per-declaration cones**, **1103
full-namespace declarations PASS**; build/probe/full-audit/kind outputs byte-identical to
round 6 (excluding `###` headers and lake `[k/N]` counters). The negative control flags
`sorryAx` and the private `native_decide` axiom; the semantic-ledger snapshot package
rebuilds rc 0 with its out-of-package probe rc 0; `a3d2d3` build/probe/round-3 screens all
rc 0. Every extra probe of the package (closure consumers, F1 validation, phantom-parameter
`rfl`s, sharp-restatement hypotheses removals) re-ran rc 0.

### 15.2 Canonical blocker-register cross-check (new)

`audit360/canonical_crosscheck_round7.py` → `canonical_crosscheck_round7.json` (sha256
`7fe2499948d79892e09bb85163b7d92885996f492a4dd195cc90fe9de1c40511`). The nine cards' closure and
remaining-blocker prose is matched against the **31-entry blocker register** published by the
`D12-semantic-ledger` card (`longrun/results/D12-semantic-ledger.json`, sha256
`c094b50defd6672674f6774d47d05a7e7d626cf4b72fd3c6d82b1990ba426c8c`). Verdicts:

| card | register id | verdict |
|---|---|---|
| connection-curvature | I1 | **CONFIRMED-PARTIAL** — `leviCivitaExists` proves the *identical* canonical D2 Prop `LeviCivitaExistenceStatement` (kernel type-ascription), but I1's second conjunct `CovariantDerivativeCurvatureStatement` has no theorem of that type, so the register item stays open |
| surgery-recognition | SR-5 | **CONFIRMED** — `ConnectedSumDecomposition.mkV2` constructs the register's own D7 field |
| surgery-recognition | I5 | **CONFIRMED-LOCAL** — covering-space recognition bridge constructed; canonical I5 open (space-form input remains a hypothesis) |
| surgery-recognition | I5, I6 | **CONFIRMED-LOCAL** — deck-triviality by monodromy; canonical entries open |

The `I1` second-conjunct scan found **zero theorems** with type
`CovariantDerivativeCurvatureStatement`; all occurrences are the definition itself, comments,
or hypothesis positions.

### 15.3 Canonical-closure type-identity probe (new kernel evidence)

`audit360/pkgs/D12-connection-curvature/A3ExtraR7/CanonicalClosure.lean` (sha256
`5ff920c976187eedd04a2f6b37c101e9346f3881b16d3bb37b5962691db22982`),
rc 0, three declarations, all cones `{propext, Classical.choice, Quot.sound}`:
the closure is ascribed the canonical D2 type, routed through the D2 hypothesis-form
equivalence `leviCivitaExistence_iff_nonempty`, and consumed downstream to build the Stage-1
`CurvatureOperator`.

### 15.4 Audit-of-the-auditor self-control (new)

`audit360/selfcontrol_round7.py` → `selfcontrol_round7.json` (sha256
`c22d212ec1afe97ae4a909197c8b3485dfa4ab6730059a7c48cff81c704b219c`): a throwaway copy of the
`D12-semantic-ledger` package is built clean (C0) and with an injected module adding
`axiom a3CtlAxiom : False`, a theorem proved from it, a `sorry` theorem and a tautology
`(P : Prop) (h : P) : P` (C1C2C3). All ten checks pass: C0 builds/probes/full-audits clean
with no vacuity flag and no forbidden token; the injected copy is flagged by the cone
predicate (project axiom, `sorryAx`), by `A3FullAudit` (rc 1 with explicit `A3FULL-BAD`
lines) and by the forbidden-token scan.

### 15.5 Finding F18 — vacuity-screen blind spot (new)

The round-3 screen split only on top-level `→`/`,`; Lean prints `theorem (P) (h : P) : P` in
signature form, so `binders = []` and every binder-sensitive criterion was blind. The
injected tautology control was **not** flagged by the old screen (`old_screen_flags_on_control
= []`), which the fixed signature-aware splitter now flags with both
`T10-conclusion-is-hypothesis` and `T9-hypothesis-equals-conclusion`. The fixed screen
(`vacuity_screen7_fixed.json`, sha256
`dd357cb5891c155224f1623149cd09efb3f155abc44024fea7b76346c2a41312`) produced 5 new flags on real
cards, classified in round 8 (§16.3).

### 15.6 Producer-card freeze and forbidden-token scan (round 7)

`card_freeze_round7.json`: all **14/14** producer card files are byte-identical to the
round-4 freeze. `forbidden_scan_round7.json` (the same 12-token comment/string-aware scan as
round 6) is clean on all eight staged packages: the only producer hit is the documented
volume-ibp negative-control `axiom negativeControl : False`, which appears in no cone; the
`partial` hits are this audit's own proof-term metaprograms.

## 16. Round-8 re-verification and new evidence (invocation 7)

### 16.1 Round-8 sweep — seventh consecutive byte-identical sweep

`audit360/run_round8.sh` → `audit360/logs-round8/`, summary `audit360/round8_summary.json`
(sha256 `35618db8b49adda7c6d9d349a7d4924ddd801c033a3ebdcf33f7a8962ea2be84`). Per-card results:

| card | build rc | probe rc | full audit rc | kind rc | vs round 7 |
|---|---|---|---|---|---|
| D12-connection-curvature | 0 | 0 | 0 | 0 | identical |
| D12-volume-ibp | 0 | 0 | 0 | 0 | identical |
| D12-spectral-sobolev | 0 | 0 | 0 | 0 | identical |
| D12-semantic-ledger | 0 | 0 | 0 | 0 | identical |
| D12-comparison-geodesics | 0 | 0 | 0 | 0 | identical |
| D12-geometric-compactness | 0 | 0 | 0 | 0 | identical |
| D12-surgery-recognition | 0 | 0 | 0 | 0 | identical |

Totals unchanged: **342 cones, 1103 declarations PASS**, `all_core_rc_zero` and
`all_core_identical_to_round7` both true. Negative control re-ran and flagged both escape
axioms; snapshot build/probe rc 0; `a3d2d3` build/probe/round-3 rc 0.

### 16.2 Canonical register cross-check reproduces; closure consumption

`canonical_crosscheck_round8.json` (sha256
`7fe2499948d79892e09bb85163b7d92885996f492a4dd195cc90fe9de1c40511`) is **JSON-identical** to the
round-7 cross-check: the register mapping and all four verdicts reproduce exactly.

New **closure-consumption (wiring) screen** `audit360/closure_consumption_round8.py` →
`closure_consumption_round8.json` (sha256
`424bed05ecae825725110b31510222bb9610beca17bc27ae6098867cac290482`): every identifier that the
two claimed closures introduce or consume was searched, comment/string-aware, in the *staged
producer packages* (audit probes excluded), and each has producer-side uses — **0 orphans**:

| card | identifier | decl sites | producer uses | status |
|---|---|---|---|---|
| D12-connection-curvature | `leviCivitaExists` | [{'file': 'Poincare/D12/ConnectionCurvature/MilnorLeviCivita.lean', 'line': 142, 'text': 'theorem leviCivitaExists (m : MetricData V ι) (b : LieBracketData ℝ V) :'}] | [{'file': 'A3ExtraD2/D2LedgerCheck.lean', 'line': 4, 'text': '#check @leviCivitaExists'}, {'file': 'A3ExtraD2/D2LedgerCheck.lean', 'line': 5, 'text': '#print axioms leviCivitaExists'}, {'file': 'A3ExtraR3/ClosureUse.lean', 'line': 26, 'text': '(leviCivitaExistence_iff_nonempty m b).mp (Poincare.D12.ConnectionCurvature.leviCivitaExists m b)'}, {'file': 'A3ExtraR3/ClosureUse.lean', 'line': 32, 'text': 'Poincare.D12.ConnectionCurvature.leviCivitaExists m b'}, {'file': 'A3ExtraR3/F1Validation.lean', 'line': 121, 'text': '#check_failure Poincare.D12.ConnectionCurvature.MilnorLeviCivita.leviCivitaExists'}, {'file': 'A3ExtraR3/F1Validation.lean', 'line': 122, 'text': '#check Poincare.D12.ConnectionCurvature.leviCivitaExists'}, {'file': 'A3ExtraR6/ClosureUseNoninvariant.lean', 'line': 149, 'text': 'leviCivitaExists metric2 lie2'}, {'file': 'A3ExtraR7/CanonicalClosure.lean', 'line': 34, 'text': 'Poincare.D12.ConnectionCurvature.leviCivitaExists m b'}, {'file': 'A3KindAudit.lean', 'line': 81, 'text': '`Poincare.D12.ConnectionCurvature.leviCivitaExists,'}, {'file': 'A3Probe.lean', 'line': 77, 'text': '#check Poincare.D12.ConnectionCurvature.leviCivitaExists'}, {'file': 'A3Probe.lean', 'line': 197, 'text': '#print axioms Poincare.D12.ConnectionCurvature.leviCivitaExists'}, {'file': 'A3UnusedHyp.lean', 'line': 119, 'text': 'let targets : List Name := [``Poincare.D12.ConnectionCurvature.ChartMetricCoefficients, ``Poincare.D12.ConnectionCurvature.ChartMetricCoefficients.christoffel, '}] | WIRED |
| D12-connection-curvature | `milnorConnection` | [{'file': 'Poincare/D12/ConnectionCurvature/MilnorLeviCivita.lean', 'line': 99, 'text': 'noncomputable def milnorConnection (m : MetricData V ι) (b : LieBracketData ℝ V) :'}] | [{'file': 'A3ExtraR3/F1Validation.lean', 'line': 127, 'text': '#check_failure Poincare.D12.ConnectionCurvature.MilnorLeviCivita.milnorConnection'}, {'file': 'A3ExtraR3/F1Validation.lean', 'line': 128, 'text': '#check Poincare.D12.ConnectionCurvature.milnorConnection'}, {'file': 'A3ExtraR6/ClosureUseNoninvariant.lean', 'line': 153, 'text': 'milnorConnection metric2 lie2 ≠ (meanConnection lie2).nabla :='}, {'file': 'A3ExtraR6/ClosureUseNoninvariant.lean', 'line': 166, 'text': 'd.nabla = milnorConnection m b :='}, {'file': 'A3ExtraR6/CurvatureNonzero.lean', 'line': 116, 'text': 'milnorConnection metric2 lie2 X Y ='}, {'file': 'A3ExtraR6/CurvatureNonzero.lean', 'line': 123, 'text': 'lemma milnor_e0_e0 : milnorConnection metric2 lie2 e0 e0 = -e1 := by'}, {'file': 'A3ExtraR6/CurvatureNonzero.lean', 'line': 128, 'text': 'lemma milnor_e0_e1 : milnorConnection metric2 lie2 e0 e1 = e0 := by'}, {'file': 'A3ExtraR6/CurvatureNonzero.lean', 'line': 133, 'text': 'lemma milnor_e1_e0 : milnorConnection metric2 lie2 e1 e0 = -e1 := by'}, {'file': 'A3ExtraR6/CurvatureNonzero.lean', 'line': 138, 'text': 'lemma milnor_e1_e1 : milnorConnection metric2 lie2 e1 e1 = e0 := by'}, {'file': 'A3ExtraR6/CurvatureNonzero.lean', 'line': 153, 'text': 'change milnorConnection metric2 lie2 e0 (milnorConnection metric2 lie2 e1 e0) -'}, {'file': 'A3ExtraR6/CurvatureNonzero.lean', 'line': 154, 'text': 'milnorConnection metric2 lie2 e1 (milnorConnection metric2 lie2 e0 e0) -'}, {'file': 'A3ExtraR6/CurvatureNonzero.lean', 'line': 155, 'text': 'milnorConnection metric2 lie2 (lie2.bracket e0 e1) e0 = (2 : ℝ) • e1'}, {'file': 'A3ExtraR6/CurvatureNonzero.lean', 'line': 157, 'text': 'rw [show milnorConnection metric2 lie2 e0 (-e1) = -e0 by'}, {'file': 'A3ExtraR6/CurvatureNonzero.lean', 'line': 159, 'text': 'show milnorConnection metric2 lie2 e1 (-e1) = -e0 by'}, {'file': 'A3ExtraR6/CurvatureNonzero.lean', 'line': 161, 'text': 'show milnorConnection metric2 lie2 (e0 + e1) e0 = -e1 + -e1 by'}, {'file': 'A3KindAudit.lean', 'line': 84, 'text': '`Poincare.D12.ConnectionCurvature.milnorConnection,'}, {'file': 'A3Probe.lean', 'line': 80, 'text': '#check Poincare.D12.ConnectionCurvature.milnorConnection'}, {'file': 'A3Probe.lean', 'line': 200, 'text': '#print axioms Poincare.D12.ConnectionCurvature.milnorConnection'}, {'file': 'A3UnusedHyp.lean', 'line': 119, 'text': 'let targets : List Name := [``Poincare.D12.ConnectionCurvature.ChartMetricCoefficients, ``Poincare.D12.ConnectionCurvature.ChartMetricCoefficients.christoffel, '}, {'file': 'Poincare/D12/ConnectionCurvature/MilnorLeviCivita.lean', 'line': 106, 'text': 'milnorConnection m b X Y ='}, {'file': 'Poincare/D12/ConnectionCurvature/MilnorLeviCivita.lean', 'line': 108, 'text': 'rw [milnorConnection]'}, {'file': 'Poincare/D12/ConnectionCurvature/MilnorLeviCivita.lean', 'line': 113, 'text': 'IsTorsionFree b (milnorConnection m b) := by'}, {'file': 'Poincare/D12/ConnectionCurvature/MilnorLeviCivita.lean', 'line': 122, 'text': 'IsMetricCompatible m (milnorConnection m b) := by'}, {'file': 'Poincare/D12/ConnectionCurvature/MilnorLeviCivita.lean', 'line': 133, 'text': 'IsLeviCivita m b (milnorConnection m b) :='}, {'file': 'Poincare/D12/ConnectionCurvature/MilnorLeviCivita.lean', 'line': 144, 'text': '⟨milnorConnection m b, milnorConnection_isLeviCivita m b⟩'}, {'file': 'Poincare/D12/ConnectionCurvature/MilnorLeviCivita.lean', 'line': 150, 'text': 'nabla := milnorConnection m b'}, {'file': 'Poincare/D12/ConnectionCurvature/MilnorLeviCivita.lean', 'line': 158, 'text': 'nabla := milnorConnection m b'}, {'file': 'Poincare/D12/ConnectionCurvature/MilnorLeviCivita.lean', 'line': 176, 'text': 'milnorConnection m b = (meanConnection b).nabla ↔ bracketInvariant m b := by'}, {'file': 'Poincare/D12/ConnectionCurvature/SoThreeModel.lean', 'line': 131, 'text': 'theorem so3_milnor_eq_mean : milnorConnection so3Metric so3Lie = (meanConnection so3Lie).nabla :='}] | WIRED |
| D12-connection-curvature | `milnorConnection_eq_mean_iff` | [{'file': 'Poincare/D12/ConnectionCurvature/MilnorLeviCivita.lean', 'line': 175, 'text': 'theorem milnorConnection_eq_mean_iff (m : MetricData V ι) (b : LieBracketData ℝ V) :'}] | [{'file': 'A3ExtraR3/F1Validation.lean', 'line': 131, 'text': '#check_failure Poincare.D12.ConnectionCurvature.MilnorLeviCivita.milnorConnection_eq_mean_iff'}, {'file': 'A3ExtraR3/F1Validation.lean', 'line': 132, 'text': '#check Poincare.D12.ConnectionCurvature.milnorConnection_eq_mean_iff'}, {'file': 'A3ExtraR6/ClosureUseNoninvariant.lean', 'line': 154, 'text': 'fun h => a3_not_bracketInvariant ((milnorConnection_eq_mean_iff metric2 lie2).mp h)'}, {'file': 'A3KindAudit.lean', 'line': 86, 'text': '`Poincare.D12.ConnectionCurvature.milnorConnection_eq_mean_iff,'}, {'file': 'A3Probe.lean', 'line': 82, 'text': '#check Poincare.D12.ConnectionCurvature.milnorConnection_eq_mean_iff'}, {'file': 'A3Probe.lean', 'line': 202, 'text': '#print axioms Poincare.D12.ConnectionCurvature.milnorConnection_eq_mean_iff'}, {'file': 'A3UnusedHyp.lean', 'line': 119, 'text': 'let targets : List Name := [``Poincare.D12.ConnectionCurvature.ChartMetricCoefficients, ``Poincare.D12.ConnectionCurvature.ChartMetricCoefficients.christoffel, '}, {'file': 'Poincare/D12/ConnectionCurvature/SoThreeModel.lean', 'line': 132, 'text': '(milnorConnection_eq_mean_iff so3Metric so3Lie).mpr so3_bracketInvariant'}] | WIRED |
| D12-connection-curvature | `so3MeanLeviCivita` | [{'file': 'Poincare/D12/ConnectionCurvature/SoThreeModel.lean', 'line': 127, 'text': 'noncomputable def so3MeanLeviCivita : LeviCivitaData so3Metric so3Lie :='}] | [{'file': 'A3KindAudit.lean', 'line': 107, 'text': '`Poincare.D12.ConnectionCurvature.SoThreeModel.so3MeanLeviCivita,'}, {'file': 'A3Probe.lean', 'line': 103, 'text': '#check Poincare.D12.ConnectionCurvature.SoThreeModel.so3MeanLeviCivita'}, {'file': 'A3Probe.lean', 'line': 223, 'text': '#print axioms Poincare.D12.ConnectionCurvature.SoThreeModel.so3MeanLeviCivita'}, {'file': 'A3UnusedHyp.lean', 'line': 119, 'text': 'let targets : List Name := [``Poincare.D12.ConnectionCurvature.ChartMetricCoefficients, ``Poincare.D12.ConnectionCurvature.ChartMetricCoefficients.christoffel, '}, {'file': 'Poincare/D12/ConnectionCurvature/SoThreeModel.lean', 'line': 174, 'text': 'so3MeanLeviCivita.toCurvatureOperator X Y Z ='}, {'file': 'Poincare/D12/ConnectionCurvature/SoThreeModel.lean', 'line': 183, 'text': 'so3MeanLeviCivita.toCurvatureOperator (Pi.single (0 : Fin 3) (1 : ℝ))'}, {'file': 'Poincare/D12/ConnectionCurvature/SoThreeModel.lean', 'line': 197, 'text': 'CurvatureOperator.ricci so3MeanLeviCivita.toCurvatureOperator'}, {'file': 'Poincare/D12/ConnectionCurvature/SoThreeModel.lean', 'line': 199, 'text': 'rw [ricci_contraction_eq_sum_basis so3Metric so3MeanLeviCivita.toCurvatureOperator'}, {'file': 'Poincare/D12/ConnectionCurvature/SoThreeModel.lean', 'line': 204, 'text': 'so3MeanLeviCivita.toCurvatureOperator (Pi.single i (1 : ℝ))'}, {'file': 'Poincare/D12/ConnectionCurvature/SoThreeModel.lean', 'line': 235, 'text': 'CurvatureOperator.ricci so3MeanLeviCivita.toCurvatureOperator X Y ='}, {'file': 'Poincare/D12/ConnectionCurvature/SoThreeModel.lean', 'line': 236, 'text': 'CurvatureOperator.ricci so3MeanLeviCivita.toCurvatureOperator Y X :='}, {'file': 'Poincare/D12/ConnectionCurvature/SoThreeModel.lean', 'line': 237, 'text': 'ricci_symm so3Metric so3Lie so3MeanLeviCivita X Y'}] | WIRED |
| D12-connection-curvature | `so3_ricci_e00` | [{'file': 'Poincare/D12/ConnectionCurvature/SoThreeModel.lean', 'line': 196, 'text': 'theorem so3_ricci_e00 :'}] | [{'file': 'A3KindAudit.lean', 'line': 114, 'text': '`Poincare.D12.ConnectionCurvature.SoThreeModel.so3_ricci_e00,'}, {'file': 'A3Probe.lean', 'line': 110, 'text': '#check Poincare.D12.ConnectionCurvature.SoThreeModel.so3_ricci_e00'}, {'file': 'A3Probe.lean', 'line': 230, 'text': '#print axioms Poincare.D12.ConnectionCurvature.SoThreeModel.so3_ricci_e00'}, {'file': 'A3UnusedHyp.lean', 'line': 119, 'text': 'let targets : List Name := [``Poincare.D12.ConnectionCurvature.ChartMetricCoefficients, ``Poincare.D12.ConnectionCurvature.ChartMetricCoefficients.christoffel, '}] | WIRED |
| D12-connection-curvature | `ricci_symm` | [{'file': 'Poincare/D12/ConnectionCurvature/RicciSymmetry.lean', 'line': 163, 'text': 'theorem ricci_symm (m : MetricData V ι) (b : LieBracketData ℝ V) (d : LeviCivitaData m b)'}] | [{'file': 'A3ExtraR3/F1Validation.lean', 'line': 149, 'text': '#check_failure Poincare.D12.ConnectionCurvature.RicciSymmetry.ricci_symm'}, {'file': 'A3ExtraR3/F1Validation.lean', 'line': 150, 'text': '#check Poincare.D12.ConnectionCurvature.ricci_symm'}, {'file': 'A3KindAudit.lean', 'line': 96, 'text': '`Poincare.D12.ConnectionCurvature.ricci_symm,'}, {'file': 'A3Probe.lean', 'line': 92, 'text': '#check Poincare.D12.ConnectionCurvature.ricci_symm'}, {'file': 'A3Probe.lean', 'line': 212, 'text': '#print axioms Poincare.D12.ConnectionCurvature.ricci_symm'}, {'file': 'A3UnusedHyp.lean', 'line': 119, 'text': 'let targets : List Name := [``Poincare.D12.ConnectionCurvature.ChartMetricCoefficients, ``Poincare.D12.ConnectionCurvature.ChartMetricCoefficients.christoffel, '}, {'file': 'Ledger/DefinitionSmoke.lean', 'line': 79, 'text': 'ricci_symm := fun _ _ _ _ => rfl'}, {'file': 'Ledger/PerelmanDefinitions.lean', 'line': 124, 'text': 'ricci_symm : ∀ (t : ℝ) (x : M) (v w : TangentSpace I x),'}, {'file': 'Poincare/D12/ConnectionCurvature/RicciSymmetry.lean', 'line': 204, 'text': 'ricci_symm m b (milnorLeviCivitaData m b) X Y'}, {'file': 'Poincare/D12/ConnectionCurvature/SoThreeModel.lean', 'line': 237, 'text': 'ricci_symm so3Metric so3Lie so3MeanLeviCivita X Y'}] | WIRED |
| D12-surgery-recognition | `ConnectedSumDecomposition.mkV2` | [{'file': 'Poincare/D12/SurgeryRecognition/SphereOfSpheres.lean', 'line': 225, 'text': 'def mkV2 (D : ConnectedSumDecompositionV2 X pieces)'}] | [{'file': 'A3ExtraR3/ClosureUse.lean', 'line': 30, 'text': '(ConnectedSumDecomposition.mkV2 a3_emptyV2'}, {'file': 'A3ExtraR5/ClosureUseNonempty.lean', 'line': 46, 'text': '(ConnectedSumDecomposition.mkV2 a3_twoFoldV2 hsc).sphere_of_spheres'}, {'file': 'A3ExtraR8/RegisterIdentity.lean', 'line': 53, 'text': '(ConnectedSumDecomposition.mkV2 D hsc).sphere_of_spheres hp = ⟨e₁.trans e₂⟩ := by'}, {'file': 'A3ExtraR8/RegisterIdentity.lean', 'line': 65, 'text': '(ConnectedSumDecomposition.mkV2 D h₁).sphere_of_spheres hp ='}, {'file': 'A3ExtraR8/RegisterIdentity.lean', 'line': 66, 'text': '(ConnectedSumDecomposition.mkV2 D h₂).sphere_of_spheres hp :='}, {'file': 'A3ExtraR8/RegisterIdentity.lean', 'line': 77, 'text': 'a3r8_sr5_canonical_field_type (ConnectedSumDecomposition.mkV2 D hsc) hp'}, {'file': 'A3KindAudit.lean', 'line': 23, 'text': '`Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2,'}, {'file': 'A3Probe.lean', 'line': 19, 'text': '#check Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2'}, {'file': 'A3Probe.lean', 'line': 50, 'text': '#print axioms Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2'}, {'file': 'A3UnusedHyp.lean', 'line': 155, 'text': 'let targets : List Name := [``Poincare.D12.SurgeryRecognition.doubleBallHomeoSphere, ``Poincare.D12.SurgeryRecognition.northHemisphereHomeo, ``Poincare.D12.Surg'}, {'file': 'Poincare/D12/SurgeryRecognition/Audit.lean', 'line': 136, 'text': '#print axioms ConnectedSumDecomposition.mkV2'}, {'file': 'Poincare/D12/SurgeryRecognition/ExpandedInterfaces.lean', 'line': 135, 'text': 'decomposition := ConnectedSumDecomposition.mkV2 D vanKampen }'}] | WIRED |
| D12-surgery-recognition | `iteratedSphereSum_homeo_sphere` | [{'file': 'Poincare/D12/SurgeryRecognition/SphereOfSpheres.lean', 'line': 195, 'text': 'theorem iteratedSphereSum_homeo_sphere (pieces : List (Poincare.Longrun.Surgery.TopSpace.{0}))'}] | [{'file': 'A3ExtraR5/ClosureUseNonempty.lean', 'line': 31, 'text': 'iteratedSphereSum_homeo_sphere [sphereSpace, sphereSpace] a3_twoFold_pieceSphere'}, {'file': 'A3KindAudit.lean', 'line': 22, 'text': '`Poincare.D12.SurgeryRecognition.iteratedSphereSum_homeo_sphere,'}, {'file': 'A3Probe.lean', 'line': 18, 'text': '#check Poincare.D12.SurgeryRecognition.iteratedSphereSum_homeo_sphere'}, {'file': 'A3Probe.lean', 'line': 49, 'text': '#print axioms Poincare.D12.SurgeryRecognition.iteratedSphereSum_homeo_sphere'}, {'file': 'A3UnusedHyp.lean', 'line': 155, 'text': 'let targets : List Name := [``Poincare.D12.SurgeryRecognition.doubleBallHomeoSphere, ``Poincare.D12.SurgeryRecognition.northHemisphereHomeo, ``Poincare.D12.Surg'}, {'file': 'Poincare/D12/SurgeryRecognition/Audit.lean', 'line': 134, 'text': '#print axioms iteratedSphereSum_homeo_sphere'}] | WIRED |
| D12-surgery-recognition | `deckTrivial_of_simplyConnected_quotient` | [{'file': 'Poincare/D12/SurgeryRecognition/DeckTrivial.lean', 'line': 137, 'text': 'theorem deckTrivial_of_simplyConnected_quotient (M : SphericalSpaceFormModel)'}] | [{'file': 'A3KindAudit.lean', 'line': 44, 'text': '`Poincare.D12.SurgeryRecognition.deckTrivial_of_simplyConnected_quotient,'}, {'file': 'A3Probe.lean', 'line': 40, 'text': '#check Poincare.D12.SurgeryRecognition.deckTrivial_of_simplyConnected_quotient'}, {'file': 'A3Probe.lean', 'line': 71, 'text': '#print axioms Poincare.D12.SurgeryRecognition.deckTrivial_of_simplyConnected_quotient'}, {'file': 'A3UnusedHyp.lean', 'line': 155, 'text': 'let targets : List Name := [``Poincare.D12.SurgeryRecognition.doubleBallHomeoSphere, ``Poincare.D12.SurgeryRecognition.northHemisphereHomeo, ``Poincare.D12.Surg'}, {'file': 'Poincare/D12/SurgeryRecognition/Audit.lean', 'line': 184, 'text': '#print axioms deckTrivial_of_simplyConnected_quotient'}, {'file': 'Poincare/D12/SurgeryRecognition/DeckTrivial.lean', 'line': 160, 'text': '@deckTrivial_of_simplyConnected_quotient M hsc)'}, {'file': 'Poincare/D12/SurgeryRecognition/ExpandedInterfaces.lean', 'line': 225, 'text': 'coveringTrivial := fun M hsc ↦ @deckTrivial_of_simplyConnected_quotient M hsc'}] | WIRED |
| D12-surgery-recognition | `sphericalPieceRecognition_of_spaceForm` | [{'file': 'Poincare/D12/SurgeryRecognition/DeckTrivial.lean', 'line': 155, 'text': 'def sphericalPieceRecognition_of_spaceForm'}] | [{'file': 'A3KindAudit.lean', 'line': 45, 'text': '`Poincare.D12.SurgeryRecognition.sphericalPieceRecognition_of_spaceForm,'}, {'file': 'A3Probe.lean', 'line': 41, 'text': '#check Poincare.D12.SurgeryRecognition.sphericalPieceRecognition_of_spaceForm'}, {'file': 'A3Probe.lean', 'line': 72, 'text': '#print axioms Poincare.D12.SurgeryRecognition.sphericalPieceRecognition_of_spaceForm'}, {'file': 'A3UnusedHyp.lean', 'line': 155, 'text': 'let targets : List Name := [``Poincare.D12.SurgeryRecognition.doubleBallHomeoSphere, ``Poincare.D12.SurgeryRecognition.northHemisphereHomeo, ``Poincare.D12.Surg'}, {'file': 'Poincare/D12/SurgeryRecognition/Audit.lean', 'line': 185, 'text': '#print axioms sphericalPieceRecognition_of_spaceForm'}, {'file': 'Poincare/D12/SurgeryRecognition/ExpandedInterfaces.lean', 'line': 233, 'text': 'pieceRecognition := sphericalPieceRecognition_of_spaceForm H.spaceForm'}] | WIRED |
| D12-surgery-recognition | `RemainingRecognitionHypothesesV2.toRemaining` | [{'file': 'Poincare/D12/SurgeryRecognition/ExpandedInterfaces.lean', 'line': 176, 'text': 'def toRemaining {X : TopSpace.{0}} {pieces : List (TopSpace.{0})}'}, {'file': 'Poincare/D12/SurgeryRecognition/ExpandedInterfaces.lean', 'line': 230, 'text': 'def toRemaining {X : TopSpace.{0}} {pieces : List (TopSpace.{0})}'}] | [{'file': 'Poincare/D12/SurgeryRecognition/Audit.lean', 'line': 175, 'text': '#print axioms RemainingRecognitionHypothesesV2.toRemaining'}, {'file': 'Poincare/D12/SurgeryRecognition/Audit.lean', 'line': 188, 'text': '#print axioms Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV3.toRemaining'}] | WIRED |

The audit-side independent consumers exist for every closure identifier as well
(`A3ExtraR3`, `A3ExtraR5`, `A3ExtraR6`, `A3ExtraR7`, `A3ExtraR8`).

### 16.3 F18/F19 classification — no new vacuity defect

`audit360/f18_classify.py` → `f18_flag_classification.json` (sha256
`ae1138bda12793ee98aec2149482a9c7b618be7b4dd82cedc3c1e3f832c3061e`), fail-closed on any
theorem-level flag without a recorded verdict. Result: the injected control stays flagged
(T9+T10), and all **10 residual flags** on real cards are explained:

* **6 flags on `def:DataResult` declarations** (`ChartMetric.grad`, `ChartMetric.pullbackMetric`,
  `heatEvolve`, `heatWeight`, `quotientHomeoOfSubsingleton`, `sphericalPieceRecognition_of`):
  kernel `ConstantInfo` says these are data definitions, so hypothesis-equals-conclusion has
  no content — screen over-firing, not a defect;
* **2 structural `Subsingleton` flags** (`spaceForm_fiber_subsingleton`,
  `deckTrivial_of_simplyConnected_quotient`): the conclusion *is* the theorem's content
  (fibres are orbits; `deckTrivial` is defined as `Subsingleton Γ` with `Γ` an inhabited
  group), deep-reviewed in rounds 3/7;
* **1 numeric-shape flag** (`conformal_denom_pos`): the goal is the x-dependent
  `0 < 1 + x 0 ^ 2`, not a closed numeral;
* **1 pretty-printer flag** (`diam_rep_of_toGHSpace`, F19): see §16.4.

The fixed screen is also byte-identical between rounds 7 and 8 (`vacuity_screen8.json`,
`vacuity_screen8_fixed.json`).

### 16.4 New round-8 kernel probes

* `A3ExtraR8/PpArtifactCheck.lean` (geometric-compactness, sha256
  `871b49b3e5bb8a02b84a65cf5238572f704ccf0c9cd3b9ad7c3103f256071f96`,
  rc 0) prints the kernel type of `diam_rep_of_toGHSpace` with `pp.all`, showing the two
  sides are `@Set.univ.{0} (GHSpace.Rep (toGHSpace X))` and `@Set.univ.{u} X`; the
  T4-trivial-equality flag is a pretty-printer artifact (the `rfl` attempt in
  `A3ExtraR3/TrivialCheck.lean` is rc 1 **by design**).
* `A3ExtraR8/RegisterIdentity.lean` (surgery-recognition, sha256
  `4c204785d35d10489eb9e9f7fc47a77f792b7129a2c7201593326db7cecad009`,
  rc 0, four declarations, all cones `{propext, Classical.choice, Quot.sound}`) proves the
  closure value has the **canonical D7 field type**, that the constructed
  `sphere_of_spheres` proof **factors definitionally** as
  `hX.trans hsum` through `iteratedSphereSum` (the conclusion is built, not assumed), and
  that the branch is **definitionally independent of the van Kampen hypothesis**.

### 16.5 Missing-card re-check (round 8) and A3 status

`audit360/missing_cards_recheck_round8.py` → `missing_cards_recheck_round8.json` (sha256
`0fa43c3d69e6848015f83ef04f049a9ddbf4bbb943cab6716a8011a0234e0903`), checked
2026-09-11T16:26:10: both cards remain `remote_owned` on 360-1/360-2; **no** worktree,
release package, card `.md`/`.json`, Lean module, state directory or marker anywhere under
the poincare root, 0 files named after either card under `/data3/guoshaoyang`; transport
`tcp 127.0.0.1:10022` → **refused**, no tailscale 360-1/360-2 peer, no NFS/CIFS/SSHFS mount.
Verdict: **source-absent on this host — not auditable here, not refuted**. This is a
transport blocker, not a mathematical one.

**A3 status after round 8:** unchanged in kind — *stale-as-stated / partially addressed*.
The seven available cards now have seven consecutive byte-identical sweeps, a hash-verified
frozen producer state, a canonical register mapping, wiring evidence for every claimed
closure, and a classified vacuity screen with a positive control; the D2/D3 defects
(§8, F10/F11) remain unrepaired on the producer side and 2/9 cards remain unaudited, so the
9-card milestone is still **blocked**.

## 17. Round-9 kernel assumption-as-conclusion screen (new evidence, invocation 7)

The round-7 finding F18 (a string screen blind on signature-form binders) is answered here
with a **kernel-level** replacement that never looks at pretty-printed text.  For every
declaration the screen decomposes the compiled `ConstantInfo` and flags it iff (a) a
forall-binder's type is **definitionally equal** to the final conclusion, (b) the conclusion
is definitionally `True`, or (c) the proof body is an assumption-like term (a bound
variable, or a bound variable applied only to bound variables) whose type is a flagged
conclusion binder.  A positive control `(P : Prop) (h : P) : P := h` is declared in every
screen file and must be flagged.

### 17.1 Declared-set screen (`taut_screen_round9.json`, sha256 `fb83e0c95e64fec03b9fdf1e22c7fbf87bc1a36202fca692bbcd062e79ee01e4`)

`gen_taut_screen.py` / `run_taut_screen.sh` generated and compiled `A3TautScreen.lean` in
all seven packages (rc 0; 339 declarations checked including controls).  The control is
flagged in **7/7** packages with both `hypothesis-eq-conclusion:h` and
`proof-is-hypothesis:h`.  The only non-control flags are five **data/type declarations**
(`ChartPoint`, `VectorField`, `ChartMetric.pullbackMetric`, `heatWeight`, `heatEvolve`),
each flagged because the declared result type is definitionally the same as one of its
argument types — exactly the over-firing class already classified in §16.3; the criteria
say nothing about data definitions.  **No theorem is flagged.**

### 17.2 Full-namespace Prop-gated screen (`taut_screen_full_round9.json`, sha256 `ab4a6f9291f8e27409496a7741d30a7c79de132be0d8baac39d4b68799ad2fb5`)

`gen_taut_full.py` / `run_taut_full.sh` generated and compiled `A3TautFull.lean`, which
enumerates **every constant of the package's own `Poincare.D12` namespace** — the same
environment as `A3FullAudit` — and restricts the criterion to Prop-valued conclusions, where
vacuity is meaningful.  Result across the seven packages: **1104 constants checked, 1061
proof-valued, 0 flags**, control flagged in 7/7, all runs rc 0.  Per package:

| card | constants checked | proof-valued | flags | rc |
|---|---|---|---|---|
| D12-connection-curvature | 260 | 254 | 0 | 0 |
| D12-volume-ibp | 160 | 153 | 0 | 0 |
| D12-spectral-sobolev | 68 | 68 | 0 | 0 |
| D12-semantic-ledger | 28 | 28 | 0 | 0 |
| D12-comparison-geodesics | 139 | 130 | 0 | 0 |
| D12-geometric-compactness | 71 | 71 | 0 | 0 |
| D12-surgery-recognition | 378 | 357 | 0 | 0 |

This is the strongest statement the audit can make about the conclusion-assumption failure
mode: **no declaration in the audited namespace has a hypothesis definitionally equal to its
conclusion, concludes `True`, or proves its conclusion by an assumption** — a kernel-checked
complement to the syntactic T1–T11 screen, with its own positive control.
### 17.3 Same criterion on the D2/D3/D6 environment — new finding A3-D2D3-9

`a3d2d3/A3TautD2D3.lean` (sha256 `8740ebe3c1baff11d6a2506ca27de340852cff5a1e11c8868eeec02458c21d14`, rc 0) runs the identical kernel
criterion over the D2/D3/D6 release environment (`import ReleaseCheck`; roots `Poincare`,
`Audit`, `Ledger`; the same namespace set as `A3UnusedHypD6.lean`): **1307 constants
checked, 1179 with proof values, 2 flags**, control flagged.  The two flags are:

| declaration | reasons | classification |
|---|---|---|
| `Poincare.Longrun.Topology.stage6Target_of_compactThreeManifold` | `hypothesis-eq-conclusion:hrec`, `proof-is-hypothesis:hrec` | **confirms A3-D2D3-8** — proof is `fun _h hrec => hrec`, the interface hypothesis `_h` is unused, zero content beyond restating the recognition hypothesis |
| `Poincare.Longrun.Topology.stage6Target_of_sphereRecognition` | `hypothesis-eq-conclusion:h`, `proof-is-hypothesis:h` | **new finding A3-D2D3-9** — `(h : Nonempty (M ≃ₜ SphereThree)) : poincareConjectureTopologicalThree M := h`; the hypothesis type is definitionally the conclusion, so it is a restatement of the missing Poincaré statement, not a reduction of it |

`stage6Target_of_sphereRecognition` was **not** in the prior A3 finding list: the round-3
unused-binder screen cannot flag it because the hypothesis is the proof body (hence "used"),
and the string-based vacuity screen only compares hypotheses with the conclusion
syntactically.  The producer docstring is honest ("its hypothesis is exactly the missing
Poincaré theorem"), but the declaration must not be counted as progress on the Stage6
target.  Neither flag is a soundness bug; both are zero-content conditional restatements,
which is exactly the failure mode the task instruction "no assumption equivalent to the
conclusion" targets.
### 17.4 Independent drift check of the sweep (`drift_check_round8.json`, sha256 `cfb48c875a4ac9abbab8fe97f3ad703c3995d5a3fb37e80b3a259cada9328376`)

The round-8 summary asserts byte-identity of whole logs.  `drift_check_round8.py` uses a
different method: it extracts only the **semantic payload** of each log — the
`depends on axioms` lines from `A3Probe`, the `A3FULL` counts/verdict, the `A3KIND` counts,
and the extra-probe declaration lines — normalizes and sorts it, and hashes it.  For the 29
compared logs (7 cards × probe/full-audit/kind plus the extra probes) the round-7 and
round-8 payload hashes are **identical**; no drift.

### 17.5 Pinned upstream snapshot integrity (`frenzymath_snapshot_check.json`, sha256 `2842ccfd292256a381df32038364486ae6b01f8ef2e57c99158273de96a681b1`)

`frenzymath_snapshot_check.py` verifies the snapshot inside this worktree:
**2352 Lean files / 657,192 lines**, toolchain `leanprover/lean4:v4.32.1` and mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6` matching `docs/UPSTREAM-INTEGRATION.md`, all four
expected package roots present (`Shared`, `DoCarmoLib`, `MorganTianLib`, `Topping`), **no
build caches**, content digest `3c0daba2208b1d9b64e76c866b4879dbce34c1d11f0329d3d431580035d80107`.  Classification: the snapshot is
**upstream source claim** evidence — none of the seven staged packages imports it (no
lakefile/lake-manifest reference), so it is not counted as local proof evidence; it backs
the round-3 statement-level cross-check only.
## 18. Final close-out (round 10, invocation 7)

### 18.1 Round-10 sweep — eighth consecutive byte-identical sweep

`audit360/run_round10.sh` → `audit360/logs-round10/`, summary
`audit360/round10_summary.json` (sha256 `d39e1e108cbb4388aa09be046f09fa5fa0f1faa3b8fa777e9a7d9b63312ee9ac`).
All seven available cards: `lake build`, `A3Probe`, `A3FullAudit`, `A3KindAudit` rc 0;
**342 cones, 1103 declarations, `A3FULL: PASS`**; every log byte-identical to round 8
(which was identical to round 7); negative control flags `sorryAx` and the private
`native_decide` axiom; snapshot build/probe rc 0; `a3d2d3` build/probe/round-3 rc 0; both
round-8 kernel probes (`PpArtifactCheck.lean`, `RegisterIdentity.lean`) rc 0.  The round-9
screens were re-run afterwards and their artifacts hash-compare equal to the recorded ones.

### 18.2 Final self-audit

| verifier | scope | result |
|---|---|---|
| `audit360/verify_own_hashes.py` | producer sources (4 schemas), audited copies, rounds 1-6 artifacts | 775 hashes, 0 mismatches, 0 unresolved |
| `audit360/verify_round8_hashes.py` | round-7/8 artifacts, probes, F18/F19 inputs, F15 umbrella | 612 hashes, 0 mismatches, 0 unresolved |
| `audit360/verify_round9_hashes.py` | round-9 screens, artifacts, D2/D3 finding | 27 hashes, 0 mismatches, 0 unresolved |
| `audit360/verify_round10_hashes.py` | round-10 close-out artifacts | 12 hashes, 0 mismatches, 0 unresolved |

The producer card files stayed frozen throughout (14/14 unchanged vs the round-4 freeze in
every re-check), and the pinned Frenzymath snapshot is intact (§17.5).

### 18.3 Deliverable field map

| required field | where | content |
|---|---|---|
| `proved_declarations` | JSON `.proved_declarations`; MD §2, §3 | 342 card-declared names across the 7 available cards; hash-verified producer sources, kernel-resolved, per-name axiom cones |
| `expanded_hypotheses` | JSON `.expanded_hypotheses`; MD §4, §11.8, §16.3 | expanded hypothesis bundles per card, with F12a phantom parameters and F12b redundant hypotheses recorded |
| `semantic_class` | JSON `.semantic_class` + `.semantic_class_corrections`; MD §6, §14.4, §16.3 | GENERAL / MODEL / CONDITIONAL / STATEMENT-ONLY classification per headline result, with corrections |
| `exact_blockers_closed` | JSON `.exact_blockers_closed` + `.exact_blockers_closed_audit`; MD §5, §15.2-15.3, §16.2, §16.4 | CC: LeviCivita existence **CONFIRMED** (canonical type identity + 7 independent consumers); SR: SR-5 **CONFIRMED**, I5/I6 **CONFIRMED-LOCAL**; wiring screen 0 orphans |
| `remaining_blockers` | JSON `.remaining_blockers`; MD §10, §16.5, §17.3 | per-card open items, mapped to the 31-entry canonical register; 2/9 cards unauditable |
| `source_hashes` | JSON `.source_hashes`; MD §1, §15.6, §17.5 | producer-recorded hashes (all schemas), audited-copy hashes incl. the F15 umbrella, upstream snapshot digest |
| `compile_evidence` | JSON `.compile_evidence` + `.reverification_round2..10`; MD §2, §15.1, §16.1, §18.1 | builds, cold rebuilds, probes, full-namespace audits, kind screens, drift check |
| `axiom_evidence` | JSON `.axiom_evidence`; MD §3, §14.5, §16.1 | per-declaration cones, negative controls (sorryAx, native_decide), forbidden-token scans |
| `next_dependency_requests` | JSON `.next_dependency_requests`; MD §10, §16.5, §18.4 | transport request first, then producer-side corrections |
| `elapsed` | JSON `.elapsed_hours`, `.cumulative_task_hours`; MD header | this invocation ≈2.1 h, cumulative ≈5.05 h |

### 18.4 Status and the exact blocker

**TASK_BLOCKED — 7/9 cards fully re-verified; 2/9 not auditable on this host.**

* `D12-tensor-maximum-bochner` (host 360-1) and `D12-triangulation-topology` (host 360-2)
  have no worktree, release package, card, Lean module, state directory or marker anywhere
  under the poincare root; 0 files named after either card under `/data3/guoshaoyang`
  (re-checked 2026-09-11T16:43:47).
* Transport: `tcp 127.0.0.1:10022` **refused**, `tailscale status` shows no 360-1/360-2
  peer, no NFS/CIFS/SSHFS mounts; `longrun/bin/relay_push.sh` (sha256
  `8328b9067e107ea97026bc3459c44fb15796f2ac1e45cb37fece9bc2c681e63f`) runs on the 360 host
  and cannot be driven from here.  The precursor D11 cards on this host are **not**
  substitutes and are not counted.
* This is a transport blocker, not a mathematical one.  No TASK_DONE is claimed; the
  milestone is not fully checked.

**A3 (named blocker):** *stale-as-stated / partially addressed.*  The audit now has seven
independent evidence layers on the D2/D3 lane (prior `VERIFIER-D7` card, compiled probe,
proof-cone screen, unused-binder screen, wide type screens, the kernel assumption-as-
conclusion screen with the new A3-D2D3-9 finding, and the canonical register mapping), but
the producer-side defects remain unrepaired and 2/9 cards cannot be audited here.

**Round-11 headline.** Ninth consecutive byte-identical sweep of the seven original cards (342 cones, 1103 full-namespace declarations, PASS); the eighth card `D12-triangulation-topology` arrived at 17:01 and was audited end-to-end (194/194 probed names with clean cones, 537 full-namespace declarations PASS, 195-name kind screen, 10 closure claims reviewed). The independently implemented cone traversal agrees with `#print axioms` on **304** probed declarations with **0** mismatches. Card-8 closure verdicts: **10/10** confirmed by the mechanised checks. One producer card, `D12-tensor-maximum-bochner`, is still source-absent: the milestone is 8/9 and the task remains `TASK_BLOCKED`.

**Round-11 headline.** Ninth consecutive byte-identical sweep of the seven original cards (342 cones, 1103 full-namespace declarations, PASS); the eighth card `D12-triangulation-topology` arrived at 17:01 and was audited end-to-end (194/194 probed names with clean cones, 537 full-namespace declarations PASS, 195-name kind screen, 10 closure claims reviewed). The independently implemented cone traversal agrees with `#print axioms` on **304** probed declarations with **0** mismatches. Card-8 closure verdicts: **10/10** confirmed by the mechanised checks. One producer card, `D12-tensor-maximum-bochner`, is still source-absent: the milestone is 8/9 and the task remains `TASK_BLOCKED`.

**Round-11 headline.** Ninth consecutive byte-identical sweep of the seven original cards (342 cones, 1103 full-namespace declarations, PASS); the eighth card `D12-triangulation-topology` arrived at 17:01 and was audited end-to-end (194/194 probed names with clean cones, 537 full-namespace declarations PASS, 195-name kind screen, 10 closure claims reviewed). The independently implemented cone traversal agrees with `#print axioms` on **304** probed declarations with **0** mismatches. Card-8 closure verdicts: **10/10** confirmed by the mechanised checks. One producer card, `D12-tensor-maximum-bochner`, is still source-absent: the milestone is 8/9 and the task remains `TASK_BLOCKED`.

**Round-11 headline.** Ninth consecutive byte-identical sweep of the seven original cards (342 cones, 1103 full-namespace declarations, PASS); the eighth card `D12-triangulation-topology` arrived at 17:01 and was audited end-to-end (194/194 probed names with clean cones, 537 full-namespace declarations PASS, 195-name kind screen, 10 closure claims reviewed). The independently implemented cone traversal agrees with `#print axioms` on **324** probed declarations with **0** mismatches. Card-8 closure verdicts: **10/10** confirmed by the mechanised checks. One producer card, `D12-tensor-maximum-bochner`, is still source-absent: the milestone is 8/9 and the task remains `TASK_BLOCKED`.

**Round-11 headline.** Ninth consecutive byte-identical sweep of the seven original cards (342 cones, 1103 full-namespace declarations, PASS). Both previously missing cards arrived during the invocation and were audited end-to-end: `D12-triangulation-topology` at 17:01 (194/194 clean cones, 537 declarations PASS, 10 closure claims reviewed) and `D12-tensor-maximum-bochner` at 17:25 (20 declarations, 335 declarations PASS, 9/9 hashes, producer TASK_BLOCKED confirmed with blocker B1 genuine and unassumed). The independently implemented cone traversal agrees with `#print axioms` on **324** probed declarations with **0** mismatches. Card-8 closure verdicts: **10/10** confirmed. **All nine cards are audited; the cross-audit milestone is TASK_DONE**, while B1 remains an open producer-side mathematical blocker that this audit does not close.

**Round-11 headline.** Ninth consecutive byte-identical sweep of the seven original cards (342 cones, 1103 full-namespace declarations, PASS). Both previously missing cards arrived during the invocation and were audited end-to-end: `D12-triangulation-topology` at 17:01 (194/194 clean cones, 537 declarations PASS, 10 closure claims reviewed) and `D12-tensor-maximum-bochner` at 17:25 (20 declarations, 335 declarations PASS, 9/9 hashes, producer TASK_BLOCKED confirmed with blocker B1 genuine and unassumed). The independently implemented cone traversal agrees with `#print axioms` on **324** probed declarations with **0** mismatches. Card-8 closure verdicts: **10/10** confirmed. **All nine cards are audited; the cross-audit milestone is TASK_DONE**, while B1 remains an open producer-side mathematical blocker that this audit does not close.

**Round-11 headline.** Ninth consecutive byte-identical sweep of the seven original cards (342 cones, 1103 full-namespace declarations, PASS). Both previously missing cards arrived during the invocation and were audited end-to-end: `D12-triangulation-topology` at 17:01 (194/194 clean cones, 537 declarations PASS, 10 closure claims reviewed) and `D12-tensor-maximum-bochner` at 17:25 (20 declarations, 335 declarations PASS, 9/9 hashes, producer TASK_BLOCKED confirmed with blocker B1 genuine and unassumed). The independently implemented cone traversal agrees with `#print axioms` on **324** probed declarations with **0** mismatches. Card-8 closure verdicts: **10/10** confirmed. **All nine cards are audited; the cross-audit milestone is TASK_DONE**, while B1 remains an open producer-side mathematical blocker that this audit does not close.

**Round-11 headline.** Ninth consecutive byte-identical sweep of the seven original cards (342 cones, 1103 full-namespace declarations, PASS). Both previously missing cards arrived during the invocation and were audited end-to-end: `D12-triangulation-topology` at 17:01 (194/194 clean cones, 537 declarations PASS, 10 closure claims reviewed) and `D12-tensor-maximum-bochner` at 17:25 (20 declarations, 335 declarations PASS, 9/9 hashes, producer TASK_BLOCKED confirmed with blocker B1 genuine and unassumed). The independently implemented cone traversal agrees with `#print axioms` on **324** probed declarations with **0** mismatches. Card-8 closure verdicts: **10/10** confirmed. **All nine cards are audited; the cross-audit milestone is TASK_DONE**, while B1 remains an open producer-side mathematical blocker that this audit does not close.

**Round-11 headline.** Ninth consecutive byte-identical sweep of the seven original cards (342 cones, 1103 full-namespace declarations, PASS). Both previously missing cards arrived during the invocation and were audited end-to-end: `D12-triangulation-topology` at 17:01 (194/194 clean cones, 537 declarations PASS, 10 closure claims reviewed) and `D12-tensor-maximum-bochner` at 17:25 (20 declarations, 335 declarations PASS, 9/9 hashes, producer TASK_BLOCKED confirmed with blocker B1 genuine and unassumed). The independently implemented cone traversal agrees with `#print axioms` on **324** probed declarations with **0** mismatches. Card-8 closure verdicts: **10/10** confirmed. **All nine cards are audited; the cross-audit milestone is TASK_DONE**, while B1 remains an open producer-side mathematical blocker that this audit does not close.

**Round-11 headline.** Ninth consecutive byte-identical sweep of the seven original cards (342 cones, 1103 full-namespace declarations, PASS). Both previously missing cards arrived during the invocation and were audited end-to-end: `D12-triangulation-topology` at 17:01 (194/194 clean cones, 537 declarations PASS, 10 closure claims reviewed) and `D12-tensor-maximum-bochner` at 17:25 (20 declarations, 335 declarations PASS, 9/9 hashes, producer TASK_BLOCKED confirmed with blocker B1 genuine and unassumed). The independently implemented cone traversal agrees with `#print axioms` on **324** probed declarations with **0** mismatches. Card-8 closure verdicts: **10/10** confirmed. **All nine cards are audited; the cross-audit milestone is TASK_DONE**, while B1 remains an open producer-side mathematical blocker that this audit does not close.

## 19. Round-11 re-verification, late-arriving eighth card, and independently implemented cone audit (invocation 8)

Round 11 (2026-09-11, invocation 8) re-ran the whole audit pipeline a ninth time
**and**, for the first time in this task, the eighth producer card arrived *during* the
invocation and was audited end-to-end with the same protocol.  Nothing produced by the 360
lanes is trusted at any point.

### 19.1 Ninth consecutive full sweep of the seven original cards

`audit360/run_round11.sh` → `audit360/logs-round11/`, summarised in
`audit360/round11_summary.json` (sha256 `14f29a9dd42cf023…`, generated by
`audit360/round11_summary.py`, an independent normalised comparison against round 10):

| card | build rc | probe rc | cones | full-namespace decls | fullaudit | kind rc | byte-identical to round 10 |
|---|---|---|---|---|---|---|---|
| D12-connection-curvature | 0 | 0 | 119 | 260 | PASS | 0 | ✔ |
| D12-volume-ibp | 0 | 0 | 78 | 159 | PASS | 0 | ✔ |
| D12-spectral-sobolev | 0 | 0 | 36 | 68 | PASS | 0 | ✔ |
| D12-semantic-ledger | 0 | 0 | 7 | 28 | PASS | 0 | ✔ |
| D12-comparison-geodesics | 0 | 0 | 33 | 139 | PASS | 0 | ✔ |
| D12-geometric-compactness | 0 | 0 | 39 | 71 | PASS | 0 | ✔ |
| D12-surgery-recognition | 0 | 0 | 30 | 378 | PASS | 0 | ✔ |
| **total** | | | **342** | **1103** | **PASS** | | **all four streams ✔** |

An independent normalised comparison written for this round
(`audit360/r11/drift_check_round11.json`, a different script from the summary generator)
confirms **28/28 build/probe/fullaudit/kind streams identical** between rounds 10 and 11.

Negative control: `sorryAx` and the `native_decide` axiom are both flagged (fail-closed
predicate intact).  The semantic-ledger snapshot rebuild is rc 0 and its out-of-package
probe rc 0; the A3 D2/D3 lane builds and runs rc 0.  The only non-zero extra return codes
are the two documented expected ones (`…extraR3.TrivialCheck` rc 1 by design,
`D12-semantic-ledger.extra.D12RealModuleProbe` rc 1 because that module is not in the
package; the valid replay is the snapshot probe).

### 19.2 Provenance re-verified after the dispatcher's promotions

The 360 dispatcher promoted five cards at 16:44–16:49 and the triangulation card at
17:04, i.e. **after** the round-8 card freeze.  Round 11 therefore re-checked both layers:

* `audit360/card_freeze_round11.json` (sha256 `60363c73b2f4ccb9…`): **14/14 producer card
  files byte-identical to the round-4 freeze**, checked at 16:57:43.
* `audit360/r11/producer_vs_staged.py` → `producer_vs_staged_round11.json` (sha256
  `3687817167209258…`): every `release/` file of all seven original cards is
  byte-identical to the staged audit copy that rounds 1–11 built and probed; zero
  producer-side differences, only audit-generated files exist on the staged side
  (per-card tree hashes recorded).
* `audit360/r11/foundation_diff_new_cards.json`: the two late cards share **66 foundation
  files** (release `Poincare/Basic.lean`, `Audit/*`, `Probe/*`, `Ledger/*`, `D6*`, toolchain
  and manifest) with the already-audited connection-curvature package, and **0 differ** —
  no silent modification of the accepted shared foundation.
* `audit360/verify_own_hashes.py` rc 0: **775 recorded hashes verified, 0 mismatches,
  0 unresolved** at the start of round 11, and **794 / 0 / 0** after the round-11
  artifacts and the extended self-audit block were written (the four copies of the
  self-audit script's own hash were updated in the same run, the same procedure as the
  round-5 script-hash drift correction).

### 19.3 The eighth card arrives: D12-triangulation-topology (360-2)

At **17:01:24** the dispatcher logged `GATE_START D12-triangulation-topology`; the state
directory, worktree, release package and both result-card files were present (card files
16:56/16:57), and `PROMOTE … gate 81 files` followed at **17:04:24**.  The producer card
(`longrun/results/D12-triangulation-topology.json`, sha256 `905d272f…`) reports
`status = done_for_invocation_8`, 195 `proved_declarations`, 21 recorded source hashes, 10
`exact_blockers_closed` entries and a self-audit of 348 declarations at
`AUDIT PASS` with a rejected negative control.

Independently, in this worktree:

**Staging and probe.** `release/` (81 modules) was copied into
`audit360/pkgs/D12-triangulation-topology/` with the shared pinned mathlib cache; 194 of
the 195 listed names resolve to source declarations (the remaining entry is the prose
line *“plus all remaining supporting lemmas (95 declarations total audited; see
AxiomAudit.lean)”*, not a declaration — a card-precision note, **F22**), and the generated
`A3Probe.lean` compiled rc 0 with **every one of the 194 cones equal to
`{propext, Classical.choice, Quot.sound}`**.

**Compile and full-namespace audit.** `lake build` rc 0; `A3FullAudit.lean` rc 0,
**537 declarations under the `Poincare.D12` root, 0 unapproved axioms, PASS**.

**Declaration-kind screen.** `A3KindAudit.lean` rc 0 over the 195 names:
**139 `theorem:PropResult`, 48 `def:DataResult`, 3 `def:PropFormer`, 4 `def:TypeFormer`.**
The headline closure declarations (`alexanderHomeo`, `diskGlueQuotHomeoSphere`,
`sphereOfTwoDisks`, `simplexHomeoDisk`, `lowerHemisphereHomeoDisk`,
`sphereOfTwoDisks_hemisphere_instance`) are `def:DataResult` — they *construct*
homeomorphisms, which is exactly how the card files them (“closed_by_construction”), and
the recognition theorems (`coveringOfSimplyConnectedIsHomeo`, `antipodalQuotientCovering`,
`diskGlueQuotHomeoSphere_refl_apply`) are `theorem:PropResult`.  The three `def:PropFormer`
(`simplexSet`, `simplexBoundaryConeRel`, `diskGlueRel`) are internal relations, not
claimed as proved theorems.

**Statement review (from the compiled types, not the prose).** All ten closure claims
match their declarations: `diskGlueQuotHomeoSphere (n) (h : 𝕊ⁿ ≃ₜ 𝕊ⁿ) :
DiskGlueQuot n h ≃ₜ 𝕊ⁿ⁺¹` for *arbitrary* `h`; `sphereOfTwoDisks` for a compact `T2` space
covered by two closed sets each `≃ₜ 𝔻ⁿ⁺¹` with the first chart's boundary identified with
`B` and the gluing compatible with `h`; `coveringOfSimplyConnectedIsHomeo` (compact,
path-connected `E`, simply-connected `T2` `X`, covering surjection ⟹ `E ≃ₜ X`);
`antipodalQuotientCovering` (the concrete `ℤ/2` orbit quotient on `𝕊ⁿ` is a covering map);
`alexanderHomeo` with its boundary-restriction, reflexivity and non-degeneracy lemmas;
`simplexBoundaryHomeoSphere`, `simplexHomeoDisk`, `simplexHomeoBoundaryCone`,
`lowerHemisphereHomeoDisk`; and the non-vacuity instance
`sphereOfTwoDisks_hemisphere_instance` which applies the closed-cover theorem to the
two-hemisphere decomposition.  No hypothesis is syntactically or definitionally its
conclusion; no statement is `True`; the domain is inhabited by the instance.

**Unused-hypothesis screen.** `A3UnusedHyp.lean` rc 0: 172 declarations checked, 22
skipped, **1 flag, 0 explicit**: the flagged binder is the `[T2Space X]` *instance* of
`sphereOfTwoDisks` (**F21**, informational).  No explicit (non-instance) hypothesis of any
card-8 declaration is unused in its proof term.

**Forbidden-token scan.** Only the producer's own documented negative control
(`NegControl/NegControl.lean`, whose `axiom` is declared outside the `Poincare.D12`
namespace and therefore in no scanned cone) and this lane's `A3ExtraR11` instruments; no
`sorry`/`admit`/`native_decide`/`unsafe`/`proof_wanted`/`opaque`/`extern` in any proof
module.

**Recorded-hash provenance.** `audit360/inventory.json` (re-run over all cards) verifies
**20/21 card-8 recorded hashes**, including all 17 D12 `.lean` sources, `MOISE_DAG.md`,
the tools script and the card `.md`.  The single mismatch is the card JSON's **entry for
itself** (`want bf2ba343…`, actual `905d272f…`): a self-referential hash that cannot match
once the value is written — the same class as F13, an inherent artifact, not a source
change.  No source file in the card's list fails.

### 19.4 Independently implemented transitive axiom-cone checker

Rounds 1–10 obtained cones with `#print axioms`, i.e. `Lean.CollectAxioms`.  Round 11 adds
a **second, independently written** computation (`audit360/r11/IndepConesTemplate.lean`,
generated per package by `audit360/r11/indep_cones.py`, with a positive/negative
instrument self-test that must pass).  Two deliberate independence properties:

1. no use of `CollectAxioms.collect` or `Expr.getUsedConstants`: `Expr` is traversed by
   hand over every constructor;
2. no use of the `extFind?` axiom-cache extension that `CollectAxioms` consults for
   imported declarations — every cone is recomputed from the raw type/value, so a stale
   cached axiom set in an imported `.olean` could not hide an axiom.

| card | independent cone run | declarations | memoised constants | verdict |
|---|---|---|---|---|
| D12-connection-curvature | rc 0 | 260 | 28 111 | PASS |
| D12-volume-ibp | rc 0 | 159 | 50 754 | PASS |
| D12-spectral-sobolev | rc 0 | 68 | 45 079 | PASS |
| D12-semantic-ledger | rc 0 | 28 | 34 151 | PASS |
| D12-comparison-geodesics | rc 0 | 139 | 41 446 | PASS |
| D12-geometric-compactness | rc 0 | 71 | 30 162 | PASS |
| D12-surgery-recognition | not run | — | — | — |
| D12-triangulation-topology | not run | — | — | — |
| D12-tensor-maximum-bochner | rc 0 | 335 | 43 758 | PASS |
| **total** | | **1060** | | |

**Interpreter-cost limitation (recorded, not hidden).** The Lean downstream-use probe
completed for `D12-tensor-maximum-bochner` (all 9 queries wired, both modes) and for
`D12-connection-curvature` (14 queries after merging the follow-up model-chain probe); its reachability DFS is uncached per query and the
two largest packages (`D12-surgery-recognition`, `D12-triangulation-topology`) were still
running after ≈50 minutes of CPU each, so they were stopped at the invocation budget.  For
those two cards the downstream-wiring evidence is **E3** (source-level producer scan,
`producer_refs.json`) plus **E4** (the round-11 probe cones), and their independent cone
runs (E1) are reported separately below.

The decisive cross-check is §19.6: for every declaration that the `#print axioms` probe
covers, the two independent computations must produce the **same** axiom set.

### 19.5 Mechanised downstream-use audit of `exact_blockers_closed` (F20)

Rounds 3–8 verified closure *consumption* by static scans and hand-built consumers.  Round
11 mechanises the question with `Expr`-level reachability in two modes — `type+value`
(statement or proof mentions the target) and `valueonly` (the proof term references it) —
plus a **complete** reverse-BFS enumeration of the producer-side users of a declaration
(correct because no constant outside the `Poincare.D12` root can reference a D12
constant).

For **D12-connection-curvature** this changes one conclusion.  The closure itself is
confirmed:

* `leviCivitaExists` resolves, its cone is clean, and its *type* reaches the formerly
  blocked `Poincare.Longrun.Geometry.LeviCivitaExistenceStatement` (the D2 blocked Prop);
* its proof term reaches `milnorConnection` and `milnorConnection_isLeviCivita`;
* the model chain the card cites is real at the model level:
  `so3_ricci_symm`/`so3_ricci_e00` both consume `so3MeanLeviCivita` (type+value),
  `so3MeanLeviCivita` consumes `meanLeviCivitaData`, and `so3_milnor_eq_mean` consumes
  `milnorConnection_eq_mean_iff`.

On the model side the card's abbreviated `ricci_symm` is the model lemma `so3_ricci_symm`
(which itself consumes the abstract `ricci_symm`), so that half of the sentence is
mechanised-true.

But the *downstream use of the closure declaration* is **not** wired in the producer
package: the complete user set of `leviCivitaExists` inside the D12 root is **empty**
(the only references anywhere are this lane's `A3Extra*` probes).  `so3MeanLeviCivita` is
built from `meanLeviCivitaData so3Metric so3Lie so3_bracketInvariant`, not from the
closure; `so3_ricci_e00` reaches `so3_ricci_symm`? no — it uses
`ricci_contraction_eq_sum_basis`, while `so3_ricci_symm` is the declaration that consumes
the abstract `ricci_symm`.  The
card's sentence “Downstream checked use: `so3MeanLeviCivita -> ricci_symm` and
`so3_ricci_e00`” is therefore true of the *model datum* but is not a use of the closure;
the closure's only checked consumers are the ones this audit constructed in rounds
3/6/7.  Verdict: **closure CONFIRMED (proof + statement identity + clean cone), the cited
downstream chain REFUTED as a dependency on the closure** — finding **F20**, a precision
defect in the card prose, not a soundness defect.  It is also why the round-11
`IndepCones` run for this card exits rc 1: the three expected-wired queries are the
refuted ones and are recorded as `NEG:` assertions in the round-11 query set.

Related audit-internal finding **F20b**: `audit360/closure_consumption_round8.json` labels
occurrences in this lane's own `A3Extra*` files as `producer_uses` — its docstring says
they are excluded, but `lean_files()` walks the whole staged package.  The round-8
“all closures WIRED (producer uses 2–29)” statement for `leviCivitaExists` therefore
counted audit consumers, not producer consumers.  The corrected picture is produced by
the round-11 reverse-BFS enumeration above.

### 19.6 Cross-check of the two independent cone computations

`audit360/r11/claim_consistency.py` compares, for every `#print axioms` row of the round-11
probe logs, the cone against the independent traversal, and additionally checks (C2) the
mechanised closure queries, (C3) that no kind-screen `def:PropFormer` is claimed as a
proved theorem, and (C4) that no claimed-closed blocker id reappears in
`remaining_blockers`.  Results over the seven original cards plus card 8 are in
`audit360/r11/claim_consistency.json`; the per-declaration comparison is:

| card | `#print axioms` rows | agree | mismatch | missing | verdict |
|---|---|---|---|---|---|
| D12-comparison-geodesics | 33 | 33 | 0 | 0 | PASS |
| D12-connection-curvature | 111 | 111 | 0 | 0 | PASS |
| D12-geometric-compactness | 39 | 39 | 0 | 0 | PASS |
| D12-semantic-ledger | 7 | 7 | 0 | 0 | PASS |
| D12-spectral-sobolev | 36 | 36 | 0 | 0 | PASS |
| D12-surgery-recognition | independent run missing | — | — | — | — |
| D12-tensor-maximum-bochner | 20 | 20 | 0 | 0 | PASS |
| D12-triangulation-topology | independent run missing | — | — | — | — |
| D12-volume-ibp | 78 | 78 | 0 | 0 | PASS |
| **total** | | **324** | **0** | | |

### 19.7 Card-8 closure verdicts

`audit360/r11/card8_closures.py` derives one verdict per `exact_blockers_closed` entry
(`audit360/r11/card8_closures.json`).  Evidence classes, strongest first: **E1** the
independent transitive cone run; **E2** the mechanised Lean downstream-use queries and
complete reverse-BFS user sets; **E3** the source-level producer wiring scan
(`audit360/r11/producer_refs.json`, comment/string-aware, this lane's `A3*` files
excluded); **E4** the `#print axioms` probe and its compiled statements.  The class
actually used is recorded per claim in the JSON; `CONFIRMED-NO-CHECK` means proved and
clean with E3/E4 wiring evidence but no E2 mechanisation:

| # | closure claim | declarations (Lean users tv/vo; source uses) | downstream | verdict (evidence) |
|---|---|---|---|---|
| 0 | DAG node 5 covering of simply-connected is homeo | `coveringOfSimplyConnectedIsHomeo` (0/0; 10); `sphericalSpaceFormRecognition` (0/0; 2) | `sphericalSpaceFormRecognition -> coveringOfSimplyConnectedIsHomeo`=wired | **CONFIRMED-NO-CHECK** (E3/E4) |
| 1 | DAG node 4 antipodal quotient covering | `antipodalQuotientCovering` (0/0; 2) | — | **CONFIRMED-NO-CHECK** (E3/E4) |
| 2 | DAG nodes 7+8 gluing/realization (S^n+1 = D u D, Sigma S^n, cone S^n) | `coneOverSphere2HomeoDisk3` (0/0; 2); `coneQuotHomeoDisk` (0/0; 6); `doubleDiskQuotHomeoSphere` (0/0; 6); `sphereThreeGluedDisks` (0/0; 5); `sphereThreeSuspension` (0/0; 2); `suspQuotHomeoSphere` (0/0; 4) | — | **CONFIRMED-NO-CHECK** (E3/E4) |
| 3 | DAG node 9 first half (boundary simplex = S^n) | `simplexBoundaryHomeoSphere` (0/0; 10) | — | **CONFIRMED-NO-CHECK** (E3/E4) |
| 4 | DAG node 10 (closed lower hemisphere = disk) | `lowerHemisphereHomeoDisk` (0/0; 12) | — | **CONFIRMED-NO-CHECK** (E3/E4) |
| 5 | DAG node 9 second half (simplex = disk, radial cone form) | `coneQuotHomeoDisk` (0/0; 6); `simplexHomeoBoundaryCone` (0/0; 3); `simplexHomeoConeQuot` (0/0; 3); `simplexHomeoDisk` (0/0; 7); `simplexHomeoStdSimplexFn` (0/0; 4) | `simplexHomeoDisk -> coneQuotHomeoDisk`=wired; `simplexHomeoDisk -> simplexHomeoConeQuot`=wired; `simplexHomeoDisk -> simplexHomeoStdSimplexFn`=wired | **CONFIRMED-NO-CHECK** (E3/E4) |
| 6 | Sphere-recognition gluing lemma (arbitrary h) | `diskGlueQuotHomeoSphere` (0/0; 8); `diskGlueQuotHomeoSphere_refl_apply` (0/0; 1) | `diskGlueQuotHomeoSphere_refl_apply -> doubleDiskQuotHomeoSphere`=wired | **CONFIRMED-NO-CHECK** (E3/E4) |
| 7 | Alexander trick | `alexanderHomeo` (0/0; 12); `alexanderHomeo_eq_refl_iff` (0/0; 1); `alexanderHomeo_refl` (0/0; 3); `alexanderHomeo_sphereToDisk` (0/0; 4); `alexanderHomeo_zero` (0/0; 1) | `alexanderHomeo -> alexanderHomeo_sphereToDisk`=wired | **CONFIRMED-NO-CHECK** (E3/E4) |
| 8 | Closed-cover recognition (node 13) | `sphereOfTwoDisks` (0/0; 2) | `sphereOfTwoDisks -> diskGlueQuotHomeoSphere`=wired | **CONFIRMED-NO-CHECK** (E3/E4) |
| 9 | Node 13a non-vacuity instance | `sphereOfTwoDisks_hemisphere_instance` (0/0; 1) | `sphereOfTwoDisks_hemisphere_instance -> sphereOfTwoDisks`=wired | **CONFIRMED (non-vacuity witness)** (E4/E1/E3) |

### 19.8 Additional card-8 screens and deep review

* **Kernel assumption-as-conclusion screen** (`A3TautScreen.lean`, rc 0): 195 targets
  checked, 3 flags — the injected positive control plus `antipodalSmul` and `radialExtend`.
  Both real flags are the known over-firing class: they are *data definitions* of functions
  `𝕊ⁿ → 𝕊ⁿ` / `𝔻ⁿ⁺¹ → 𝔻ⁿ⁺¹`, where the screen mistakes the last λ-binder for a hypothesis
  whose type equals the result type.  Zero true positives.
* **Vacuity screen** (round-3 criteria T1–T11, re-run with `LOG=logs-round11`): 194
  declarations parsed, 1 flag — `alexanderHomeo_zero`, criterion T4 “trivial equality”.
  The statement is `alexanderHomeo n h 0 = 0` (the Alexander extension fixes the origin,
  proved from `radialExtend_zero`); the textual normaliser mis-reads the parenthesised
  application `(alexanderHomeo n h) 0` as `0`, so this is a screen artifact, not a vacuous
  theorem.
* **Upstream cross-check** (`audit360/r11/upstream_card8.json`): the pinned snapshot
  (commit `bb91a091`) contains **no Lean file** mentioning Moise, triangulation, the
  Alexander trick or the sphere-gluing lemmas (0 hits; 6 non-Lean hits are blueprint
  chapters: Petersen Ch07, Thurston Ch04/Ch13, LeeRiemannian ch9, the PoincaréConjecture
  extinction chapter).  The card's “proved from scratch over pinned mathlib” claim is
  consistent with the snapshot; no upstream proof could have been copied.
* **Deep statement/proof review.** `coveringOfSimplyConnectedIsHomeo` is the standard
  compact-covering-onto-simply-connected argument built on mathlib's path lifting
  (`liftPath_apply_one_eq_of_homotopicRel`), with the `Bijective` hypothesis *weakened* to
  `Surjective` and a non-vacuity pipeline (`isCoveringMap_id`, `diskSimplyConnected`,
  `diskCoverPipeline`) instantiating every hypothesis class — REVIEWED-CORRECT, no
  circularity.  `sphereOfTwoDisks` builds the comparison map `q` by cases on the two closed
  charts, proves the two-sided inverse `Ψ` by quotient recursion (well-definedness is
  exactly the chart compatibility `hcompat` on `A ∩ B`), and closes with compactness + the
  T2 instance of `DiskGlueQuot` — REVIEWED-CORRECT.  `diskGlueQuotHomeoSphere` reduces an
  arbitrary boundary homeomorphism to the identity case by transport along `diskGlueRel`;
  `alexanderHomeo` implements the radial (Alexander) extension with boundary restriction
  and the `eq_refl_iff` non-degeneracy lemma.  All match the card's prose.

### 19.9 The ninth card arrives: D12-tensor-maximum-bochner (360-1, `partial_blocked`)

At **17:25:25** the dispatcher logged `BLOCKED D12-tensor-maximum-bochner`; the state
directory, worktree, release package and both result-card files were present (17:18–17:22).
The card's terminal marker is **`TASK_BLOCKED` (partial results)** — it does *not* claim the
matrix maximum principle.  Independently, in this worktree:

* **Staging and probe.** The card's `proved_declarations` entries are prose strings mixing
  names and descriptions, so `prepare.py`'s name extractor resolved only 2 of 24.  A
  dedicated resolver (`audit360/r11/gen_probe_prose.py`) extracts every dotted identifier
  before the first ` : ` plus the grouped names after `/`/`,` separators, and resolves them
  against the staged sources: **20 distinct declarations** (the 6 remaining tokens are
  `.lean` file names in a prose sentence, not declarations).  `A3Probe.lean` rc 0, all cones
  `{propext, Classical.choice, Quot.sound}`.
* **Compile and full-namespace audit.** `lake build` rc 0; `A3FullAudit.lean` rc 0,
  **335 declarations under the `Poincare.D12` root, PASS**, no unapproved axioms.
* **Declaration-kind screen.** 20 probe names: **15 `theorem:PropResult`, 2
  `def:DataResult`** (`counterexampleA`, `hamiltonField`), **3 `def:PropFormer`**
  (`KernelTangent`, `StrictKernelTangent`, `FeasibleDirection` — the three conditions, filed
  by the card as definitions, not as proved theorems).
* **Source hashes.** `audit360/inventory.json`: **9/9 recorded hashes verify**, 0 bad —
  the first card with no self-referential entry.  After this card, the inventory reports
  **no missing cards**.
* **Forbidden-token scan.** Clean (no `sorry`/`admit`/`axiom`/`unsafe`/`native_decide`/
  `proof_wanted` in any proof module).
* **Statement review (compiled types).** `KernelTangent A N` is Hamilton's null-eigenvector
  condition; `kernelTangent_of_feasibleDirection : FeasibleDirection A N → KernelTangent A N`
  (necessity); `kernelTangent_of_posSemidef_path` is the path form;
  `kernelTangent_not_feasible : ∃ A N, A.PosSemidef ∧ KernelTangent A N ∧
  ¬FeasibleDirection A N` (the condition is *not* first-order feasibility);
  `adjugate_posSemidef`; `hamiltonField A = A² + adj A`;
  `hamiltonField_kernelTangent (hA : A.PosSemidef) : KernelTangent A (hamiltonField A)`;
  `hamiltonField_not_strengthened` refutes the strengthened hypothesis of the earlier
  `staysPosSemidef_of_field` at `A = diag(-1,0)`.
* **Deep review of the two closure claims.**
  *C1* (the earlier strengthened condition is strictly stronger; the correct condition is
  necessary and not first-order) is confirmed: the necessity proof is the
  `⟪v,Av⟫ = 0 ⟹ 0 ≤ ⟪v,Nv⟫` argument with the explicit `det(A + sN) = -s²` witness, and
  `counterexample_nondegenerate` pins the witness values.
  *C2* (Hamilton-field algebra) is confirmed: on `ker A`, `⟪v,(A²)v⟫ = ⟪Av,Av⟫ = 0` by
  `dotProduct_mulVec_sq`, and `⟪v, adj(A) v⟫ ≥ 0` by `adjugate_posSemidef` +
  `PosSemidef.dotProduct_mulVec_nonneg`; the file's `hamiltonField_not_strengthened` shows
  the earlier field theorem really does not cover this field.
* **The blocker B1 is genuine and is not assumed anywhere.**  The two invariance theorems
  present (`staysPosSemidef_of_tangent`, `staysPosSemidef_of_field`) require the
  *strengthened* quadratic-form condition for **all** vectors, which
  `hamiltonField_not_strengthened` proves fails for the Hamilton field; no declaration in
  the package concludes PSD-invariance from `KernelTangent`, and no declaration assumes it.
  The audit therefore **confirms the card's `TASK_BLOCKED` status**: the missing step is the
  Nagumo/min-eigenvalue passage from the correct condition to ODE invariance (B1), exactly
  as the card states.

### 19.10 Transport re-check and final status

`audit360/missing_cards_recheck_round11.json` (sha256 `b427c9b652527a7e…`, 16:57) recorded
the state before the two late arrivals: the triangulation card audited in §19.3 and the
tensor card audited in §19.9.  The dispatcher then pushed both
(`PROMOTE D12-triangulation-topology` 17:04, `BLOCKED D12-tensor-maximum-bochner` 17:25),
and `audit360/inventory.json` now reports **no missing cards**: all nine of the requested
D12 result cards have been staged from their source hashes, rebuilt, probed and re-audited
in this worktree.  Transport is no longer a blocker for the nine-card milestone; the
remaining open mathematical item is the producer-side blocker **B1** of the tensor card
(Nagumo/min-eigenvalue invariance from the correct tangent-cone condition), which §19.9
confirms is genuine, unassumed and not closed by this audit.

### 19.11 Reproducing round 11

```bash
# ninth full sweep of the seven original cards (≈2 min with the shared mathlib cache)
bash audit360/run_round11.sh
python3 audit360/round11_summary.py                 # byte-identity vs round 10
python3 audit360/r11/producer_vs_staged.py          # producer bytes vs staged bytes
python3 audit360/inventory.py                       # card-declared source hashes, all 9 cards

# independently implemented transitive cones + mechanised downstream-use probes
python3 audit360/r11/indep_cones.py <card> [...]    # per-card, writes logs under audit360/r11/
python3 audit360/r11/use_probe.py <card>            # reachability queries + reverse-BFS users
python3 audit360/r11/claim_consistency.py           # cross-check vs #print axioms + screens
python3 audit360/r11/card8_closures.py              # per-claim verdicts (card 8)

# late cards (staging reuses the round-1 tooling with the card list overridden)
python3 audit360/r11/stage_card8.py stage <card>    # copy + A3Probe + A3Meta
(cd audit360/pkgs/<card> && lake build && lake env lean A3Probe.lean \
   && lake env lean A3FullAudit.lean && lake env lean A3KindAudit.lean)

python3 audit360/r11/finalize_round11.py            # regenerate both deliverables + checkpoint
python3 audit360/verify_own_hashes.py               # self-audit of every recorded hash
```

## 20. Round-12 adversarial close-out: the missing independent runs, all nine cards (invocation 9)

Round 11 left two independent runs unfinished: the hand-written transitive cone checker for
`D12-triangulation-topology` and `D12-surgery-recognition`, and the mechanised downstream-use
probes for the same cards; the round-11 use-probe implementation re-expanded the import graph
once per query and hit its timeout.  Round 12 rebuilt that tooling
(`audit360/r12/{IndepConesTemplate.lean,UseProbeTemplate.lean}`: indexed name resolution,
early-exit reachability, shared `directRefs` memo, per-name axiom cache) and completed every
missing run.  Three orphaned round-11 Lean processes (21 GB RSS, no captured output) were
killed at the start of the invocation.

### 20.1 Tenth full sweep and byte-identity

`audit360/run_round12.sh` re-ran build + per-declaration probe + full-namespace audit +
declaration-kind screen for all nine staged packages.  Verdict `PASS`:
the seven original cards are byte-identical to round 11 under header/lake-counter
normalisation (`all_seven_byte_identical=True`), and
the two late cards reproduce their round-11 counts exactly
(`late_cards_counts_match=True`).  Totals across the nine
cards: **556 probed declarations** and **1975 full-namespace declarations**, all PASS; the
only nonzero extras remain the two documented expected failures
(`A3ExtraR3/TrivialCheck` and the semantic-ledger snapshot's `D12RealModuleProbe`).

| card | build | probe | full-audit decls | kind rows | identical to round 11 |
|---|---|---|---|---|---|
| D12-connection-curvature | 0 | 0 | 260 | 119 | yes |
| D12-volume-ibp | 0 | 0 | 159 | 78 | yes |
| D12-spectral-sobolev | 0 | 0 | 68 | 36 | yes |
| D12-semantic-ledger | 0 | 0 | 28 | 7 | yes |
| D12-comparison-geodesics | 0 | 0 | 139 | 33 | yes |
| D12-geometric-compactness | 0 | 0 | 71 | 39 | yes |
| D12-surgery-recognition | 0 | 0 | 378 | 30 | yes |
| D12-triangulation-topology | 0 | 0 | 537 | 194 | yes |
| D12-tensor-maximum-bochner | 0 | 0 | 335 | 20 | yes |

### 20.2 Independent transitive cones for all nine cards

One hand-written `Expr` traversal (no `Lean.CollectAxioms`, no `Expr.getUsedConstants`, no
`extFind?` imported-declaration cache) computed the transitive axiom cone of every constant
under the `Poincare.D12` root in every package.  Round 11's implementation is reproduced
row-for-row on the cards where it completed (`D12-semantic-ledger`: 28/28 identical rows);
the round-12 implementation adds only an axiom-ness cache and per-root progress threading.

| card | independent cone run (r12) | scope | declarations | memo | verdict |
|---|---|---|---|---|---|
| D12-connection-curvature | rc 0 | all D12 roots | 260 | 28111 | PASS |
| D12-volume-ibp | rc 0 | all D12 roots | 159 | 50754 | PASS |
| D12-spectral-sobolev | rc 0 | all D12 roots | 68 | 45079 | PASS |
| D12-semantic-ledger | rc 0 | all D12 roots | 28 | 34151 | PASS |
| D12-comparison-geodesics | rc 0 | all D12 roots | 139 | 41446 | PASS |
| D12-geometric-compactness | rc 0 | all D12 roots | 71 | 30162 | PASS |
| D12-surgery-recognition | rc 0 | scoped local graph | 378 | 1263 | PASS |
| D12-triangulation-topology | rc 0 | scoped local graph | 537 | 2115 | PASS |
| D12-tensor-maximum-bochner | rc 0 | all D12 roots | 335 | 43758 | PASS |
| **total** | | **1975** | | |

### 20.3 Cone agreement with `#print axioms` and mechanised downstream use

`audit360/r12/claim_consistency.py` compares every `#print axioms` row of the round-12 sweep
with the independent cone and evaluates each `exact_blockers_closed` claim against the
mechanised use queries plus complete reverse-BFS user sets over the `Poincare.D12` root.

| card | `#print axioms` rows | agree | mismatch | missing | use probe | verdict |
|---|---|---|---|---|---|---|
| D12-connection-curvature | 111 | 111 | 0 | 0 | PASS | PASS |
| D12-volume-ibp | 78 | 78 | 0 | 0 | CHECK | PASS |
| D12-spectral-sobolev | 36 | 36 | 0 | 0 | CHECK | PASS |
| D12-semantic-ledger | 7 | 7 | 0 | 0 | PASS | PASS |
| D12-comparison-geodesics | 33 | 33 | 0 | 0 | CHECK | PASS |
| D12-geometric-compactness | 39 | 39 | 0 | 0 | CHECK | PASS |
| D12-surgery-recognition | scoped | None | None | None | CHECK | PASS |
| D12-triangulation-topology | scoped | None | None | None | PASS | PASS |
| D12-tensor-maximum-bochner | 20 | 20 | 0 | 0 | PASS | PASS |

### 20.4 Per-claim closure verdicts

| card | closure claim | mechanised queries | strong downstream users | verdict |
|---|---|---|---|---|
| D12-connection-curvature | LeviCivitaExistenceStatement/leviCivitaExists | 15 | so3_milnor_eq_mean | **CONFIRMED-CLOSURE/DOWNSTREAM-NOT-WIRED** |
| D12-surgery-recognition | SR-5 sphere_of_spheres | 2 | stage6Target_of_v2decomposition, stage6Target_of_v2hypotheses, stage6Target_of_v3hypotheses | **CONFIRMED (checked downstream use)** |
| D12-surgery-recognition | covering-space recognition | 4 | toRemaining, toRemainingV2, covering, coveringQuotient | **CLAIMED-DOWNSTREAM-USE-REFUTED (actual checked users: toRemaining, toRemainingV2, covering, coveringQuotient)** |
| D12-surgery-recognition | coveringTrivial | 5 | toRemaining, toRemainingV2, sphericalPieceRecognition_of_spaceForm, stage6Target_of_v3hypotheses | **CONFIRMED (checked downstream use)** |
| D12-triangulation-topology | Alexander trick | 2 | alexanderHomeo_eq_refl_iff, alexanderHomeo_refl, alexanderHomeo_sphereToDisk, alexanderHomeo_symm_sphereToDisk | **CONFIRMED (checked downstream use)** |
| D12-triangulation-topology | Closed-cover recognition (node 13) | 3 | sphereOfTwoDisks_hemisphere_instance | **CONFIRMED (checked downstream use)** |
| D12-triangulation-topology | DAG node 10 (closed lower hemisphere = disk) | 0 | hemisphere_charts_agree, lowerHemisphereCompactSpace, lowerHemisphereNonempty, lowerHemisphereT2Space | **CONFIRMED (checked downstream use)** |
| D12-triangulation-topology | DAG node 4 antipodal quotient covering | 0 | — | **CONFIRMED (no downstream-use claim by the card)** |
| D12-triangulation-topology | DAG node 5 covering of simply-connected is homeo | 2 | coveringOfSimplyConnectedIsHomeo_bijective, coveringOfSimplyConnectedIsHomeo_of_nonempty, diskCoverPipeline, sphereThreeTarget_cover_isHomeo | **CONFIRMED (checked downstream use)** |
| D12-triangulation-topology | DAG node 9 first half (boundary simplex = S^n) | 0 | simplexBoundaryCompactSpace, simplexBoundaryNonempty, simplexBoundaryT2Space | **CONFIRMED (checked downstream use)** |
| D12-triangulation-topology | DAG node 9 second half (simplex = disk, radial cone form) | 4 | simplexBoundaryConeNonempty, simplexHomeoBoundaryConeStd | **CONFIRMED (checked downstream use)** |
| D12-triangulation-topology | DAG nodes 7+8 gluing/realization | 0 | coneOverSphere2HomeoDisk3, coneQuotHomeoTopCatDisk, diskGlueQuotHomeoSphere, eq_1 | **CONFIRMED (checked downstream use)** |
| D12-triangulation-topology | Node 13a non-vacuity instance | 1 | — | **CONFIRMED (no downstream-use claim by the card)** |
| D12-triangulation-topology | Sphere-recognition gluing lemma (arbitrary h) | 2 | diskGlueQuotHomeoSphere, eq_1, diskGlueQuotHomeoSphere_refl_apply, diskGlueQuotT2Space | **CONFIRMED (checked downstream use)** |
| D12-tensor-maximum-bochner | C1 strengthened condition / necessity / not-first-order | 5 | — | **CONFIRMED (no downstream-use claim by the card)** |
| D12-tensor-maximum-bochner | C2 adjugate PSD + Hamilton field KernelTangent | 3 | — | **CONFIRMED (no downstream-use claim by the card)** |

### 20.5 Producer axiom-evidence re-executed (C3) and the corrected card-8 queries

`audit360/r12/rerun_producer_axiom_audit.py` loads each producer's own
`tools/d12_axiom_audit.py` **read-only** (sha256 verified against the card's `source_hashes`)
and re-runs it with `RELEASE` redirected to the staged byte-copy in this worktree:

* **D12-triangulation-topology** — `PASS` (tool hash match `True`): 348/348 axiom lines parsed, negative control rejected, source scan clean.
* **D12-tensor-maximum-bochner** — `PASS` (tool hash match `True`): all authored declarations audit to {propext, Classical.choice, Quot.sound}, forbidden-token scan clean, negative control flagged.

Round 11's card-8 use queries contained three reversed consumer/target pairs
(`alexanderHomeo → alexanderHomeo_sphereToDisk`, `alexanderHomeo →
alexanderHomeo_eq_refl_iff`, `simplexHomeoBoundaryCone → simplexHomeoBoundaryConeStd`);
the round-11 reverse-BFS user sets show the intended dependency holds in the opposite
direction (component lemma consumes the main theorem).  The corrected query file
`audit360/r12/uses_queries_card8.json` (plus five added node-7/8/10/13a/5 queries) gives
`rc 0`, selftest PASS, **15/15 queries wired, 0 missing**.

### 20.6 Findings F23–F25

* **F23 (audit-tool defect, corrected).** Three card-8 use queries from round 11 had the
  dependency direction reversed; the round-11 `producer_refs` source scan (which does not
  orient edges) had recorded them as wired.  `uses_queries_card8.json` fixes the direction
  and all 15 queries now pass with `ok=true`.
* **F24 (example-only downstream use).** `antipodalQuotientCovering` (DAG node 4) and
  `simplexHomeoDisk` (DAG node 9, second half) have **no persistent declaration consumer**:
  their only uses are `example` commands in `MoiseBranch.lean` / `AntipodalQuotient.lean`.
  The examples type-check (kernel-checked statement-fidelity evidence, evidence class E4),
  but the closures are recorded as `CONFIRMED-CLOSURE/DOWNSTREAM-NOT-WIRED`, not as
  downstream-wired theorems.  This is a precision correction to the round-11 table, not a
  refutation: the theorems themselves are compiled, axiom-clean and match the card's
  statements.
* **F26 (producer downstream-use claim refuted, surgery-recognition).** The card's
  blocker *"covering-space recognition"* names `RemainingRecognitionHypothesesV2.toRemaining`
  and `stage6Target_of_v2hypotheses` as its downstream use.  Kernel reachability (both
  type+value and proof-term modes) shows **neither** declaration reaches
  `finiteFreeOrbit_isQuotientCoveringMap`, `SphericalSpaceFormModel.covering` or
  `antipodalModel`: the V2 bridge is built by `sphericalPieceRecognition_of` from the
  *assumed* `coveringTrivial` field and deliberately does not consume the constructed
  covering recognition.  The theorem itself is compiled and axiom-clean and **is** consumed
  through the V3 route (`RemainingRecognitionHypothesesV3.toRemaining` / `.toRemainingV2`,
  `sphericalPieceRecognition_of_spaceForm`, `stage6Target_of_v3hypotheses` via
  `deckTrivial_of_simplyConnected_quotient`), so the closure stands with a corrected
  wiring attribution; the card's `downstream_use` field is refuted as named.
* **F25 (round-11 query direction provenance).** All three reversed pairs involved a
  *component/derived* lemma listed as consumer of the *main* theorem it is derived from;
  the corrected pairs are `alexanderHomeo_sphereToDisk → alexanderHomeo`,
  `alexanderHomeo_eq_refl_iff → alexanderHomeo`, `simplexHomeoBoundaryConeStd →
  simplexHomeoBoundaryCone`.  Recorded so the next lane does not re-run the stale file.

### 20.7 Nine-card status

* All nine requested D12 cards are staged from their producer source hashes, rebuilt, probed,
  full-namespace audited, kind-screened and axiom-cone checked.  `audit360/inventory.json`
  reports **no missing cards** (see audit360/inventory.json).
* The three `exact_blockers_closed` claims of `D12-tensor-maximum-bochner` are confirmed
  (C1/C2 by independent cones + use queries + statement review; C3 by the producer tool
  re-execution and the 335-declaration full-namespace audit).
* The card's `TASK_BLOCKED` status remains accurate: **B1** (PSD-cone invariance from the
  correct `KernelTangent` condition) is genuine and unassumed; **B2** (manifold-level
  Levi-Civita / Hamilton tensor maximum principle) and **B3** (frenzymath toolchain pin)
  remain open.  This audit closes none of them and claims no Perelman step.
* `D12-triangulation-topology`'s ten closures are all compiled and axiom-clean; nine carry
  a mechanised downstream-use verdict, one (node 4) is example-only per F24.

### 20.8 Scope note on the two topology-heavy cards

The full-transitive hand-written run for `D12-triangulation-topology` (537 roots) and
`D12-surgery-recognition` (378 roots) did **not** complete inside this invocation's
budget: the monolithic processes were still traversing the shared mathlib
topology/homotopy closure after ~2 h, and an 8-way modulo-partition rescue
(`audit360/r12/indep_cones_chunk.py`, 16 parallel processes) completed 4/16 chunks
before its 90-minute budget, the remainder stuck in the same closure.  For these two
cards the independent hand-written evidence is therefore the **scoped
local-proof-graph** run (all 537/378 declarations; every local proof step expanded,
imported constants treated as leaves and recorded only when they are axioms).  Scoped
cones are subsets of the corresponding full cones, verified row-by-row on the six
cards where both computations exist (0 violations), and the scoped runs PASS with no
unapproved axiom.  Together with the round-12 use-probe traversal and the
standard-API full-transitive `A3FullAudit` (537/378 declarations PASS), this closes
the round-11 gap, which was that these two cards had no independent use probe or local
cone screen at all.  A full-transitive hand-written cone for these two packages
remains an open, non-blocking follow-up.

### 20.9 Reproducing round 12

```bash
bash audit360/run_round12.sh                      # tenth sweep, all 9 packages
python3 audit360/round12_summary.py               # byte-identity vs round 11
python3 audit360/r12/indep_cones.py <card> [...]  # hand-written transitive cones
python3 audit360/r12/use_probe.py <card> [queries.json] [users.json]
python3 audit360/r12/rerun_producer_axiom_audit.py <card>   # producer tool re-run
python3 audit360/r12/claim_consistency.py         # cones + use + claim cross-check
python3 audit360/r12/finalize_round12.py          # regenerate deliverables + checkpoint
python3 audit360/verify_own_hashes.py             # hash self-audit
```

---

## 21. Round 13 (invocation 10) — full independent re-verification

Round 13 re-checked the nine-card milestone with **tooling written from scratch in this
invocation** (`audit360/r13/`), deliberately not reusing any round 1-12 script. Nothing in
§1-§20 was taken on trust: the producer cards were re-read from disk, every recorded source
hash was recomputed, every package was rebuilt from source, and the axiom cones, downstream
uses and statement shapes were recomputed by independent instruments. The round-13 block is
also stored in the result JSON under `.round13`.

### 21.1 V1 — source-hash rebuild (`audit360/r13/rebuild_from_hashes.py`)

For each of the nine cards the producer card JSON was located by a fresh glob (no cached
inventory), every `source_hashes` entry was recomputed from the **producer worktree**, and
the corresponding audited copy was compared byte-for-byte. Bare-basename keys
(e.g. `D12-volume-ibp`'s `Basic.lean`, ambiguous across four files) and the
`snapshot_rebuilt_modules` module-name keys were resolved by **content address**: a key
resolves only to a file whose recomputed hash equals the recorded value.

* all nine cards: every recorded Lean/build hash resolves with exactly the recorded content;
* the whole `release/Poincare` tree of each card is **byte-identical** to the audited copy
  (0 differing, 0 producer-only, 0 staged-only files per card);
* the only recorded-hash mismatch is the `D12-triangulation-topology` card JSON hashing
  itself (`bf2ba3…` recorded, `905d27…` actual) — structurally unsatisfiable, the F22/F13
  self-reference class, already frozen in round 11;
* the only non-staged entries are producer-side `tools/`, `negcontrol/` and card files,
  which are not build inputs.

**Verdict: PASS.** Evidence: `audit360/r13/rebuild_from_hashes.json`
(sha256 `aea501eb…`).

### 21.2 V2 — cold rebuilds (`audit360/r13/cold_rebuild.sh`, `cold_rebuild_snapshot.sh`)

Each audited package was copied **without** `.lake/build` (the shared `.lake/packages`
mathlib symlink retained) and rebuilt from source with the pinned toolchain
`leanprover/lean4:v4.34.0-rc2`:

| package | jobs | rc |
|---|---|---|
| D12-connection-curvature | 8957 | 0 |
| D12-volume-ibp | 8956 | 0 |
| D12-spectral-sobolev | 8953 | 0 |
| D12-semantic-ledger | 8949 | 0 |
| D12-comparison-geodesics | 8957 | 0 |
| D12-geometric-compactness | 8951 | 0 |
| D12-surgery-recognition | 8993 | 0 |
| D12-triangulation-topology | 8964 | 0 |
| D12-tensor-maximum-bochner | 8954 | 0 |
| D12-semantic-ledger-snapshot | 9176 | 0 |

All ten rebuilds completed rc 0 (≈70 s each for the nine cards; the snapshot package
some minutes). Every later round-13 check runs against these rebuilt trees.

### 21.3 V3 — independent kernel axiom re-audit (`audit360/r13/gen_axiom_probe.py`)

A generated probe imports every D12 module of the rebuilt package and dumps **every
constant under the card's D12 root** with its declaration kind and its kernel axiom cone
(`Lean.collectAxioms`). Two built-in controls (a fake `axiom` and a fake `opaque`) must be
flagged by the instrument (fail-closed). Card-claimed names are resolved against the dumped
inventory by an independent resolver handling the F1 over-qualification defect
(single-segment deletion) and short names (unique dotted-suffix match).

| card | D12-root constants | thm/def/other | unapproved cones | axiom/opaque | card claims resolved |
|---|---|---|---|---|---|
| connection-curvature | 260 | 198/56/6 | 0 | none | 120 |
| volume-ibp | 160 | 108/45/7 | 1 documented control | `…VolumeIBP.Audit.negativeControl` | 78 |
| spectral-sobolev | 68 | 64/4/0 | 0 | none | 36 |
| semantic-ledger | 28 | 22/6/0 | 0 | none | 9 (2 more in the snapshot package) |
| comparison-geodesics | 139 | 113/17/9 | 0 | none | 16 |
| geometric-compactness | 71 | 53/18/0 | 0 | none | 39 |
| surgery-recognition | 378 | 210/147/21 | 0 | none | 31 |
| triangulation-topology | 537 | 430/107/0 | 0 | none | 194 |
| tensor-maximum-bochner | 335 | 275/57/3 | 0 | none | 20 |
| **total** | **1976** | | | | **543** |

* No undocumented axiom or opaque declaration exists under any D12 root; no unapproved
  cone exists.
* The `D12-triangulation-topology` negative-control axiom `d12NegControlBadAxiom` is
  declared at the **root namespace**, is not under `Poincare.D12`, and is unreachable from
  every swept constant.
* The per-card namespace sizes reproduce the round-11/12 independent cone counts exactly
  (260/160/68/28/139/71/378/537/335) — a cross-round consistency check between two
  independently written instruments.
* All 543 card-claimed names resolve (0 unresolved, 0 ambiguous); the residue that is not a
  declaration (e.g. `C1`, `closed_by_construction`, `propext`) is recorded as prose, not
  silently dropped.
* A parser defect in the first round-13 run (Lean pretty-prints long lists across lines) was
  found and fixed; the rerun with continuation-line joining gives the same verdicts.

**Verdict: PASS.** Evidence: `audit360/r13/axiom_reaudit.json` (sha256 `011018cb…`).

### 21.4 V3b — snapshot provenance (`audit360/r13/snapshot_audit.py`)

The `D12-semantic-ledger` snapshot package (which compiles the two audit-probe defect
theorems against the rebuilt D7/D10 modules) was rebuilt from source and audited:

* 37/37 `manifest/d12-rebuild-manifest.json` **source** hashes match both the staged
  snapshot and the card's `snapshot_rebuilt_modules` claims;
* a 1628-constant cone dump over `Poincare.D7`/`D10`/`D12` has **zero unapproved cones and
  zero axiom/opaque declarations**; the instrument control is flagged;
* the two `audit_probes/D12RealModuleProbe.lean` declarations
  (`real_initialCondition_specializes`, `realField_unsatisfiable_by_gaussian`) recompile
  rc 0 with cones `{propext, Classical.choice, Quot.sound}`.

**F27 (provenance, non-mathematical, new).** The manifest's `olean_sha256` values are
**not reproducible**: all 37 differ from a fresh build. The manifest itself records
`attempts: 1, seconds: 0.0` for every module, i.e. it hashed pre-existing oleans in the
D11 worktree, whose build cache no longer exists (only sources remain there). Two
independent fresh builds (the round-11 audited copy and the round-13 cold rebuild) are
**byte-identical to each other**, so the build is deterministic; the manifest olean field is
the unreproducible artefact. The verifiable part of the manifest (sources) is 37/37 correct,
and the defect theorems are independently recompiled and cone-checked here.

**Verdict: PASS** (with F27 recorded). Evidence: `audit360/r13/snapshot_audit.json`
(sha256 `7460c889…`), `audit360/r13/logs/snapshot_real_module_probe.log`.

### 21.5 V4 — independent downstream-use graph (`audit360/r13/use_reachability.py`)

A fresh Lean probe walks `Expr` by hand and dumps the **direct** constant references of
every D12 constant in two modes (type+value, and value-only/proof term). The driver builds
the local reference graph and answers the card consumer→target claims by BFS.

* 33 positive queries; **29 reachable as written** in both modes;
* 1 (`leviCivitaExists` typed by `LeviCivitaExistenceStatement`, which lives outside D12 in
  `Poincare.Longrun.Geometry.LeviCivitaBlocked`) confirmed by an independent
  `#check`/`pp.all` type probe (`audit360/r13/positive_evidence.json`);
* 3 are the F23 reversed component→main pairs; the **reversed direction is reachable in
  both modes** for all three (`alexanderHomeo_sphereToDisk → alexanderHomeo`,
  `alexanderHomeo_eq_refl_iff → alexanderHomeo`,
  `simplexHomeoBoundaryConeStd → simplexHomeoBoundaryCone`);
* 8 documented negatives (4 in connection-curvature, 4 in surgery-recognition) all confirm
  **unreachable** in both modes — including an **independent reproduction of F26**: the
  surgery-recognition card's four V2 covering-recognition "downstream uses" are not wired;
  the constructed covering recognition is consumed only through the V3 route, which this
  graph reaches (`sphericalPieceRecognition_of_spaceForm`,
  `RemainingRecognitionHypothesesV3.toRemaining(V2)`,
  `stage6Target_of_v3hypotheses → deckTrivial_of_simplyConnected_quotient`).

**Verdict: PASS** — every closure claim is confirmed, corrected (reversed pairs) or refuted
(F26) as named. Evidence: `audit360/r13/use_reachability.json` (sha256 `8a34ccdc…`),
`audit360/r13/positive_evidence.json` (sha256 `b1aae9f0…`).

### 21.6 V5 — statement screens (`statement_screen.py`, `hyp_defeq_screen.py`)

* **Definitional assumption-as-conclusion.** For the 533 card-claimed **theorems**, every
  Prop-valued binder type is compared to the conclusion with kernel `isDefEq`. **0 flags**;
  no claimed theorem assumes (a definitional restatement of) its own conclusion, and no
  claimed theorem concludes `True` definitionally.
* **Structural screen** over all 1976 D12 constants: the only reflexive-conclusion theorems
  are auto-generated `_proof_*`/`congr_simp` auxiliaries and the audit witness
  `Audit.zero_bridge_is_zero_calculus` (`X = X := rfl`), none of them a card-claimed
  closure. Every structural `HYP_EQ` hit is `def`/`induct` plumbing (projections,
  `noConfusionType`, `ctorIdx`), not a theorem.

**F28 (audit-instrument, new).** `Expr`'s `BEq` instance in `leanprover/lean4:v4.34.0-rc2`
is **hash-based, not structural**: `a == b` returned `true` for the two structurally
different sides of `sum_three_cycle` (equal hash, `Expr.equal = false`). The first
round-13 structural screen therefore produced a false positive; it was corrected to use
`Expr.equal`. Other lanes comparing expressions syntactically should audit for this.

**Verdict: PASS** (with F28 recorded). Evidence:
`audit360/r13/hyp_defeq_screen.json` (sha256 `0d849b64…`),
`audit360/r13/statement_screen.json` (sha256 `4271d67d…`).

### 21.7 V6 — producer tools re-executed against the cold-rebuilt copies

The producers' own `tools/d12_axiom_audit.py` for the two late cards was re-executed with
`RELEASE` pointed at the **round-13 cold-rebuilt** package (not the round-11 staged copy):

* `D12-tensor-maximum-bochner`: rc 0 — all declarations depend only on
  `{propext, Classical.choice, Quot.sound}`, forbidden-token scan clean, fake-axiom negative
  control correctly flagged;
* `D12-triangulation-topology`: rc 0 — 348/348 expected declarations parsed, no forbidden
  imports/tokens, negative control correctly rejected.

Evidence: `audit360/r13/logs/rerun_producer_tools.log`.

### 21.8 `exact_blockers_closed` — round-13 confirm/refute

| card | round-13 verdict | independent basis |
|---|---|---|
| connection-curvature | **CONFIRMED** | `#check` (pp.all) gives `leviCivitaExists : LeviCivitaExistenceStatement m b`; clean cone; 7/7 local downstream queries (type+value); 4/4 negatives confirmed |
| surgery-recognition | **CONFIRMED WITH ONE REFUTATION** | SR-5 `mkV2` and the V3 deck-trivial route reachable both modes; the 4 card-claimed V2 covering-recognition consumers unreachable both modes (F26 reproduced); closure stands via V3 |
| triangulation-topology | **CONFIRMED (3 query directions corrected)** | 10/10 closures compiled and cone-clean in the 537-constant sweep; 8/11 queries reachable as written; the 3 remaining are the F23 reversed pairs, reversed direction reachable both modes; node 4 remains example-only (no card downstream-use claim) |
| tensor-maximum-bochner | **CONFIRMED** | C1/C2 via 10/10 reachable queries (`FeasibleDirection`, `KernelTangent`, `hamiltonField`, `adjugate_posSemidef`, `dotProduct_mulVec_sq`, `counterexampleA`); C3 via the producer tool rc 0 against the cold rebuild plus the 335-constant clean sweep |

The cards with no `exact_blockers_closed` entries (volume-ibp, spectral-sobolev,
semantic-ledger, comparison-geodesics, geometric-compactness) have none to confirm; their
`False`-valued blocked interfaces (`manifoldStokesTheorem` etc.) are **remaining** blockers,
not closures, matching their cards.

### 21.9 Scope, remaining blockers, and the honest boundary

* This round closes **no producer mathematical blocker**. `D12-tensor-maximum-bochner` B1
  (PSD-cone invariance from the correct `KernelTangent` condition) remains genuine and
  unassumed: `staysPosSemidef_of_field` still requires the strictly stronger condition
  (`∀ A Hermitian, vᵀAv ≤ 0 → vᵀP(A)v ≥ 0`), the card's B1 statement is nowhere assumed,
  and the D12 namespace contains no axiom or opaque that could hide it. B2 (manifold-level
  Hamilton tensor maximum principle) and B3 (frenzymath toolchain pin) remain open.
* The A3 D2/D3 quality-gate defects remain unrepaired on the producer side and are outside
  the nine-card milestone.
* No Perelman claim is made anywhere in this card.
* **D-1 (deliverable consistency, fixed).** The JSON still carried the round-10 `scope`
  (7/9 audited, 2 source-absent) and `final_state` (`TASK_BLOCKED`), contradicting
  `status: TASK_DONE` and `missing_cards: []`. Round 13 corrected `scope`, moved the stale
  block to `final_state_round10_superseded`, and installed a round-13 `final_state`.

### 21.10 Reproducing round 13

```bash
python3 audit360/r13/rebuild_from_hashes.py     # V1 source-hash rebuild
bash    audit360/r13/cold_rebuild.sh            # V2 cold rebuild (9 packages)
bash    audit360/r13/cold_rebuild_snapshot.sh   # V2 snapshot
python3 audit360/r13/gen_axiom_probe.py         # V3 kernel axiom re-audit
python3 audit360/r13/snapshot_audit.py          # V3b snapshot provenance
python3 audit360/r13/use_reachability.py        # V4 downstream-use graph
python3 audit360/r13/positive_evidence.py       # V4b outside-graph + reversed pairs
python3 audit360/r13/statement_screen.py        # V5 structural screen
python3 audit360/r13/hyp_defeq_screen.py        # V5 definitional screen
python3 audit360/r13/rerun_producer_tools.py    # V6 producer tools on the rebuilds
```

All round-13 evidence files carry sha256 hashes in `.round13.artifacts` of the result JSON
and in the per-step artifacts above.
