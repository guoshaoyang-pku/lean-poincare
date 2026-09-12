# D5-clean-rebuild — result card

> **Delivery note (sandbox).** The canonical shared path
> `/data3/guoshaoyang/workdir/lean_poincare/longrun/results/D5-clean-rebuild.md` is outside
> this session's `workspace-write` sandbox (workspace =
> `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D5_clean_rebuild`). This card
> and its JSON twin are mirrored at `<worktree>/longrun/results/`.
> **Integrator action:** copy the two mirrored files to the shared `longrun/results/`
> directory (same delivery pattern as the accepted D2/D3/D4 cards). The promotion attempt
> made by this run: `{"D5-clean-rebuild.md": "denied: PermissionError: [Errno 13] Permission denied: '/data3/guoshaoyang/workdir/lean_poincare/longrun/results/D5-clean-rebuild.md'", "D5-clean-rebuild.json": "denied: PermissionError: [Errno 13] Permission denied: '/data3/guoshaoyang/workdir/lean_poincare/longrun/results/D5-clean-rebuild.json'"}`.
>
> Path note: the prompt names the worktree `.../worktrees/D5_rebuild`; the runtime workspace
> is `.../worktrees/D5_clean_rebuild` (the `D5_rebuild` name does not exist on disk). All work
> was done in `D5_clean_rebuild`.

- **Task id:** `D5-clean-rebuild`
- **Stage / lane:** D5 / verifier (`requires_lean: true`)
- **Model:** `deepseek-v4.1-flash-expires-on-0910`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D5_clean_rebuild`
- **Generated:** 2026-09-09T03:42:35.187485+00:00
- **Verdict:** **RELEASE GATE PASS** — all release gates pass; the kernel dependency audit found
  no `sorryAx`, no project axiom, no `unsafe`, no `native_decide`, and no `proof_wanted`.
  23 open blockers remain (20 mathematical/interface, 2 audit
  residual, 1 process; see §6); none is a release-hygiene failure.

## 1. Scope and acceptance rule

The clean-room package collects **only** D1–D4 deliverables that are (a) recorded by a
`DONE` state marker, (b) described by a machine-readable result card, (c) hash-identical to
the card's `sha256` claims, and (d) recompiled and audited here from a fresh build directory.
Source artifacts are copied, never modified: all 58 origin files were re-hashed after the
gate and **0 changed** (`manifest/source-integrity.json`; provenance and hashes in
`manifest/provenance.json`).

`longrun/queue.json` is the integrator's formal acceptance record, but it is **stale**: it was
last updated 2026-09-08T23:55 and still lists five later, completed tasks as
`running`/`queued` (see blocker **P1**). The D5 gate therefore treats *queue-verified* and
*D5-clean-room-verified* as two separate columns in §2 and supplies the missing independent
verification for the latter five.

## 2. Collected artifacts (only accepted D1–D4)

| stage | task | files | queue.json | result card | DONE | card sha256 | per-file lean | verdict |
|---|---|---|---|---|---|---|---|---|
| D1 | `D1-mathlib-geometry-map` | 1 | verified | no status field (checks exit 0) | yes | yes | yes | accepted (queue verified + clean-room verified) |
| D1 | `D1-pde-api-map` | 1 | verified | done | yes | yes | yes | accepted (queue verified + clean-room verified) |
| D1 | `D1-perelman-ledger` | 2 | verified | no status field (checks exit 0) | yes | yes | yes | accepted (queue verified + clean-room verified) |
| D2 | `D2-geometry-foundation` | 6 | running | completed_with_delivery_note | yes | yes | yes | accepted by D5 clean-room verification (queue.json not updated) |
| D2 | `D2-pde-foundation` | 5 | verified | done | yes | yes | yes | accepted (queue verified + clean-room verified) |
| D2 | `D2-ricci-ode-cluster` | 8 | queued | done | yes | yes | yes | accepted by D5 clean-room verification (queue.json not updated) |
| D3 | `D3-entropy-interface` | 7 | queued | done | yes | yes | yes | accepted by D5 clean-room verification (queue.json not updated) |
| D3 | `D3-kappa-ledger` | 7 | verified | CHECKED_INTERFACE_LAYER | yes | yes | yes | accepted (queue verified + clean-room verified) |
| D3 | `D3-surgery-ledger` | 6 | verified | complete-with-documented-missing-geometry | yes | yes | yes | accepted (queue verified + clean-room verified) |
| D4 | `D4-evolution-theorem` | 8 | queued | done | yes | yes | yes | accepted by D5 clean-room verification (queue.json not updated) |
| D4 | `D4-counterexample-audit` | 2 | queued | done | yes | yes | yes | accepted by D5 clean-room verification (queue.json not updated) |

- 11/11 D1–D4 tasks delivered; 53 promoted Lean files copied.
- Cross-worktree duplicate check: **0 conflicts** (every
  shared file that appears in several worktrees is byte-identical).
- Base skeleton dependencies (pre-existing, not D1–D4 artifacts):
  `Poincare/Basic.lean`, `Poincare/Stage1/CurvatureAlgebra.lean`, `Poincare/Stage1/RiemannAdapter.lean`, `Poincare/Stage6/TopologyBridge.lean`, `Poincare/Stage6/SphereSimplyConnected.lean`.

## 3. Fresh clean-room build

Environment (exact pins):

```text
lean-toolchain : leanprover/lean4:v4.34.0-rc2
lean           : Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release)
lake           : Lake version 5.0.0-src+6a10ac8 (Lean version 4.34.0-rc2)
mathlib rev    : 7974e751bece493b6ff508039423ca9fa2452fa8  (master-2026-09-04-26-g7974e751be)
mathlib status : clean (git status --porcelain empty, before and after the gate)
```

The project build directory was wiped and rebuilt from scratch in
`/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D5_clean_rebuild/release`; the pinned mathlib is a shared **prebuilt, read-only** package
cache (rebuilding 8.2 GB of mathlib from source is not the variable under test, and the D4
cards already record a full mathlib build).

| gate step | command | exit | seconds | notes |
|---|---|---|---|---|
| mathlib_precheck_head | `git rev-parse HEAD` | 0 | 0.0 |  |
| mathlib_precheck_status | `git status --porcelain` | 0 | 0.0 |  |
| wipe_project_build | `rm -rf .lake/build` | 0 | 0.1 |  |
| lake_build | `lake build` | 0 | 82.2 |  |
| release_check | `lake env lean ReleaseCheck.lean` | 0 | 5.0 |  |
| release_audit | `lake env lean ReleaseAudit.lean` | 0 | 7.7 |  |
| per_file_checks | `lake env lean <each release module>` | 0 | 237.0 | 58 release modules (53 promoted + 5 base), failures={} |
| source_scan | `python3 /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D5_clean_rebuild/tools/scan_forbidden.py /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D5_clean_rebuild/release` | 0 | 0.2 |  |
| mathlib_postcheck_head | `git rev-parse HEAD` | 0 | 0.0 |  |
| mathlib_postcheck_status | `git status --porcelain` | 0 | 0.0 |  |
| claim_resolution | `lake env lean ReleaseClaims.lean` | 0 | 6.5 |  |

Final re-verification of the delivered package after the manifest was written:
`lake build` exit 0, `lake env lean ReleaseCheck.lean` exit 0,
`lake env lean ReleaseAudit.lean` exit 0 (logs `10_final_*`).

`ReleaseCheck.lean` imports every promoted cluster and every audit driver:

```text
Probe.GeometryApi, Probe.PdeApi, Ledger.PerelmanDefinitions, Ledger.DefinitionSmoke,
Poincare.Longrun.Geometry, Poincare.Longrun.PDE.{HeatGrid,DiscreteMaximumPrinciple,Energy,
ContinuousInterface,AxiomAudit}, Poincare.Longrun.CurvatureODE, Poincare.Longrun.Entropy,
Poincare.Longrun.Entropy.AxiomAudit, Poincare.Longrun.Topology.{Basic,CompactThreeManifold,
Noncollapsing,NormalizedVolume,Stage6Bridge,MissingTheorems,AxiomAudit},
Poincare.Longrun.Surgery, Poincare.Longrun.Surgery.Axioms, Poincare.Longrun.Evolution,
Audit.{GeometryAudit,CurvatureODEAudit,EvolutionAudit,CounterexampleAudit,PromotedEvolutionAudit}
```

## 4. Forbidden-dependency gate (kernel level)

`ReleaseAudit.lean` walks every constant declared in a release module
(**1619 declarations**) and collects its full
transitive axiom cone with `Lean.collectAxioms`:

```text
project axiom declarations ................ 0
unsafe declarations ....................... 0
declarations depending on sorryAx ......... 0
declarations depending on native_decide ... 0
declarations with unapproved axioms ....... 0
proof_wanted-derived declarations ......... 0
distinct axiom cones ...................... 4
```

The only cones are subsets of the three standard Lean/mathlib axioms
(`propext`, `Classical.choice`, `Quot.sound`), plus the empty cone.

Gate definitions used by the audit: `sorryAx` = literal axiom name; *unapproved project axiom*
= any `axiom` declaration in a release module, and any axiom in a cone outside the three
standard axioms (this is also what catches `native_decide`, which in this toolchain emits a
private `..._native.native_decide.ax_*` axiom); `unsafe` = `DefinitionSafety.unsafe`
declaration; `proof_wanted` = literal source usage (comment-aware scan) or a release
declaration whose name contains `proof_wanted`. `partial` definitions are *not* on the
forbidden list and are reported separately (blocker H1).

- **Comment/string-aware source scan** (`tools/scan_forbidden.py`, 61 files):
  **0 hard matches** for `sorry`, `axiom`, `unsafe`, `native_decide`,
  `proof_wanted`, `sorryAx`, `admit`; 0 soft matches for
  `implemented_by`/`extern`.
- **Negative control** (`negcontrol/NegativeControl.lean`): proves the audit predicate really
  fails on forbidden input — `sorry` yields cone `[sorryAx]`, `native_decide` yields an
  unapproved private axiom (in Lean 4.34.0-rc2 `native_decide` emits
  `<decl>._native.native_decide.ax_*`, not `ofReduceBool`). Log: `logs/09_negative_control.log`.
- **`Mathlib.Wanted`**: the pinned mathlib has no such module (D3-kappa probe exit 1); no
  release module imports it.

## 5. Result-card claim resolution (informational, non-gating)

All 193 fully-qualified declaration names named by the D1–D4 result cards
were `#check`ed in the clean package (`release/ReleaseClaims.lean`).

| unresolved claim | error |
|---|---|
| (none) | all claimed declaration names resolve |

## 6. Complete unresolved-blocker list

| id | class | status | blocker |
|---|---|---|---|
| U1 | upstream-mathlib-gap | open | Pinned mathlib has no Riemann curvature tensor; curvature-based evolution equations cannot use a mathlib object. |
| U2 | upstream-mathlib-gap | open | Pinned mathlib has no Ricci tensor or scalar curvature. |
| U3 | upstream-mathlib-gap | open | No geodesics, exponential map, or parallel transport in pinned mathlib. |
| U4 | upstream-mathlib-gap | open | Levi-Civita connection smoothness (C^k) is not proved upstream; it must be a hypothesis. |
| U5 | upstream-mathlib-gap | open | Covariant derivative is known to depend only on the germ, not the 1-jet, of a section; tensorial identities may need germ-level arguments. |
| U6 | upstream-mathlib-gap | open | No heat-equation theory, heat kernel, or parabolic PDE layer; the continuous parabolic maximum principle cannot be proved and is a statement-only interface. |
| U7 | upstream-mathlib-gap | open | No Riemannian volume form, divergence theorem, integration by parts, or Bochner formula in the pinned mathlib. |
| U8 | upstream-mathlib-gap | open | No smooth manifold of Riemannian metrics and no Hamilton short-time existence theorem for Ricci flow. |
| U9 | upstream-mathlib-gap | open | No reduced length/reduced volume, no pointed Gromov-Hausdorff compactness, no canonical-neighborhood theorem, no surgery machinery; Perelman steps P-REDUCED-VOL, P-HARNACK, P-KAPPA-SOL, P-CANON, P-LONG, P-SURG, P-EXT remain planned/blocked. |
| U10 | upstream-mathlib-gap | open | No tensor Laplacian: the spatial Laplacian of the curvature evolution is not modeled; exposed as the explicit DiffusionVanishes hypothesis. |
| U11 | upstream-mathlib-gap | open | Pinned mathlib has no manifold orientability: `Orientable` is a parameter of the surgery LedgerPredicates, not a definition; a future contribution should define it and instantiate canonicalLedger. |
| U12 | upstream-mathlib-gap | open | The four blocked Perelman steps P-F-MONO, P-W-MONO, P-MU-MONO and P-NLC are recorded as hypothesis structures only: no backward/conjugate heat equation, no integration by parts, no integrability/finiteness of the F/W integrals, no attainment of the infimum defining mu, no reduced length/volume or ball-volume comparison geometry. |
| I1 | explicit-unproved-interface | open | LeviCivitaExistenceStatement and CovariantDerivativeCurvatureStatement are explicit BLOCKED Props with no proof. |
| I2 | explicit-unproved-interface | open | ContinuousHeatMaximumPrincipleInterface is statement-only; no discrete-to-continuous limit is proved. |
| I3 | explicit-unproved-interface | open | TensorRicciFlowODEBridge / ManifoldCurvatureRealization have no inhabitant; the ODE-to-tensor-Ricci-flow bridge is an explicit interface, never an axiom. |
| I4 | explicit-unproved-interface | open | FDerivativeStatement, WeightedIBPStatement, BochnerStatement, ConjugateMeasureEvolutionStatement, EntropyFunctionalRegularityStatement are unproved Props; one-sided bounds are hypotheses; WeightedCalculus is abstract data. |
| I5 | explicit-unproved-interface | open | kappa-noncollapsing K1-K7 and sphere-recognition S1-S5 are statement-only; nine foundational gaps listed (curvature, volume form, IBP, short-time existence, heat kernel, reduced length, Cheeger-Gromov, Brendle-Schoen). |
| I6 | explicit-unproved-interface | open | NeckAnalysis, ExtinctionTheorem and MissingInputs are statement-only; no geometric neck analysis or extinction theorem is proved. |
| I7 | explicit-unproved-interface | open | FiniteMeshConvergence, PerelmanEvolutionBoundary and FiniteRepresentsContinuousPerelman are statement-only; FDissipation = 0 (no spatial Laplacian/Bochner content). |
| I8 | explicit-unproved-interface | open | The transfer theorems perelmanF_monotone_of_tensorBridge / continuousPerelmanFMonotone_of_approximation are conditional on interfaces with no inhabitant; only a trivial finite identification inhabits PerelmanApproximation. |
| A1 | audit-residual-finding | open | Overstrong hypotheses (not falsity) in three promoted theorems: perelmanF_step_lt and gibbsTerm_strictAnti/gibbsTerm_step_lt assume 1 < c where 1 ≤ c suffices. Corrected theorems are proved in D4Audit; upstream restatement recommended. |
| A2 | audit-residual-finding | documented | Sign convention: the released functional is nonincreasing, opposite to Perelman's F-monotonicity; the cluster explicitly disclaims Perelman's theorem. |
| A3 | audit-residual-finding | open | No false statement was found, but the adversarial audit only covers the D4 evolution cluster; earlier clusters (D2/D3) have axiom audits but no counterexample search. |
| P1 | process-delivery | open | queue.json is stale (last update 2026-09-08T23:55, before 5 later tasks finished): D2-geometry-foundation is recorded as running; D2-ricci-ode-cluster, D3-entropy-interface, D4-evolution-theorem and D4-counterexample-audit are recorded as queued. D5 clean-room verification supplies the missing independent acceptance evidence. |
| P2 | process-delivery | known-environment-limit | Shared longrun/results/ path is outside the worker workspace-write sandbox; every card was mirrored inside its worktree and promoted later. D5 uses the same delivery pattern. |
| P3 | process-delivery | known-environment-limit | Prompt worktree names do not match the runtime worktree names (D5_rebuild vs D5_clean_rebuild; D2_geometry vs D2_geometry_foundation; D2_ode vs D2_ricci_ode_cluster; D3_topology vs D3_kappa_ledger; D4_audit vs D4_counterexample_audit). |
| H1 | hygiene-note | informational | Two compiler-generated partial-safety helpers exist for safe structural recursions: D4Audit.sqTraj._unsafe_rec and Poincare.Longrun.Surgery.SurgeryChain.append._unsafe_rec. They are DefinitionSafety.partial, not unsafe declarations, introduce no axioms, and are not in the forbidden list; reported for awareness. |
| H2 | hygiene-note | informational | Batteries.Util.ProofWanted is imported transitively (it defines the proof_wanted command); no project source uses proof_wanted (comment-aware scan clean) and no proof_wanted-derived project declaration exists. |
| H3 | hygiene-note | informational | In Lean 4.34.0-rc2 native_decide no longer routes through ofReduceBool; it emits a private axiom <decl>._native.native_decide.ax_*. The audit catches it through the unapproved-axiom rule; the negative control confirms detection. |

Counts: 23 open, 1 documented,
2 environment limits,
3 informational — 29 total.
The complete per-card blocker text is in `manifest/card-blockers.json`.

## 7. What is explicitly NOT claimed

This release does **not** claim the Poincaré conjecture, Ricci-flow existence or uniqueness,
Perelman F/W/µ monotonicity, κ-noncollapsing, canonical neighbourhoods, surgery, extinction,
or sphere recognition. Every such item is a statement-only interface or an explicit hypothesis
structure (blockers I1–I8, U1–U12). The only genuinely checked content is the finite-dimensional
/ algebraic / discrete cluster listed in §2 and the adversarial audit of the D4 evolution
cluster, whose sharp-hypothesis corrections are recorded in `D4Audit`.

## 8. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D5_clean_rebuild
python3 tools/collect_release.py          # copy + hash-verify artifacts (read-only on sources)
python3 tools/gen_claims.py               # result-card claim probe
python3 tools/scan_forbidden.py release   # source scan
python3 tools/run_gates.py                # fresh build + ReleaseCheck + ReleaseAudit + per-file
python3 tools/finalize_manifest.py        # merge manifest/build-manifest.json
```

## 9. Files produced (all under the D5 worktree)

- `release/` — fresh Lake package (60 modules: 53 promoted + 5 base + `ReleaseCheck`/`ReleaseAudit`)
- `release/ReleaseCheck.lean` — imports every promoted cluster
- `release/ReleaseAudit.lean` — kernel-level forbidden-dependency audit
- `release/ReleaseClaims.lean` — result-card claim probe
- `manifest/build-manifest.json` — clean Lean build manifest (pins, hashes, gates, blockers)
- `manifest/provenance.json`, `manifest/gate-results.json`, `manifest/forbidden-scan.json`,
  `manifest/claims.json`, `manifest/card-blockers.json`
- `tools/*.py` — reproducible collector, scanner, gate runner, manifest/result-card generators
- `negcontrol/NegativeControl.lean` — audit negative control
- `logs/` — every command's full log
- `longrun/results/D5-clean-rebuild.md`, `.json` — this card (mirror)
