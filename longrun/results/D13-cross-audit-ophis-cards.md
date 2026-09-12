# D13-cross-audit-ophis-cards — independent cross-audit of all ophis-gpu D13 cards

- **Task id:** `D13-cross-audit-ophis-cards`
- **Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-ophis-cards`
- **Audit host:** 360-1 (`gpu01`); **source host:** ophis-gpu (`zp-nc71`) via the reverse tunnel `127.0.0.1:10022`
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2`; mathlib `7974e751bece493b6ff508039423ca9fa2452fa8` (identical pin in every card's `lake-manifest.json`; shared prebuild staged inside this worktree at `audit/share/packages`)
- **Generated (local):** 2026-09-11T23:40 (+08:00)
- **Verdict:** `TASK_DONE` for the cross-audit milestone. **TASK_DONE on any audited card is not a Poincaré proof**, and no card is accepted as proving one. Of the nine cards that ship Lean modules, eight delivered trees cold-build and pass an independently written fail-closed axiom-cone detector; the ninth (`D13-heatkernel-bridge-d10-d7`) **fails to cold-build** in a module that is absent from its own card (the tenth, `D13-cross-audit-360-cards`, ships no Lean module). Four closure records satisfy the constructor + downstream checked use + independent rebuild rule, each with an explicit scope; two claimed ledger discharges do **not** satisfy it. 17 findings recorded.

---

## 0. Scope, transport and independence

The ophis-gpu queue (fetched 2026-09-11T23:11) lists eleven D13 tasks; ten are ophis-gpu cards and one
is this audit. The ten audited cards, with their ophis worktrees and result files, are:

| # | card | lane | ophis queue status |
| --- | --- | --- | --- |
| 1 | `D13-integrated-kernel-audit` | auditor | verified |
| 2 | `D13-critical-path-review` | auditor | verified (repair 1) |
| 3 | `D13-upstream-adapter-audit` | auditor | verified |
| 4 | `D13-morgan-tian-adapter-plan` | integrator | verified |
| 5 | `D13-topping-ricci-adapter-plan` | integrator | verified |
| 6 | `D13-manifold-ibp-volume-form` | integrator | verified |
| 7 | `D13-deturck-shorttime-producer` | researcher | verified |
| 8 | `D13-vankampen-recognition` | researcher | verified |
| 9 | `D13-heatkernel-bridge-d10-d7` | integrator | **running (no gate)** |
| 10 | `D13-cross-audit-360-cards` | auditor | paused |

Transport (all read-only from ophis-gpu): result `.md`/`.json`, `checkpoint.json`, `manifest/`,
`tools/`, `negcontrol/`, `docs/`, `audit-evidence/` and `release/**` **sources only**
(`.lake`, `third_party`, `tmp` excluded). Everything is under `audit/ophis/<task>/`. The transport is
hash-verifiable: the recomputed sha256 of every transported `release/` file is recorded in
`audit/evidence/<task>/release-hashes.txt`.

Independence measures actually taken:

1. **Source-hash replay** — recomputed from the transported bytes (never from a card's own tool).
2. **Cold rebuild** — fresh `audit/build/<task>/release` with an empty `.lake/build`; only the pinned
   mathlib/dependency prebuild is linked in (`audit/share/packages`, a copy made inside this
   worktree; the cards' own oleans are never reused).
3. **Independent detector** — `audit/probes/<task>/CleanProbe.lean`, written for this audit only,
   enumerates every declaration owned by every non-baseline module reachable in the rebuilt
   environment and computes its axiom cone with `Lean.collectAxioms`; it aborts on any project axiom,
   any `unsafe` declaration, any `sorryAx`/`native_decide`/unapproved axiom in a cone, any
   `proof_wanted`, or any harness exception. The approved cone is exactly
   `{propext, Classical.choice, Quot.sound}`.
4. **Negative controls** — the cards' documented `axiom … : False` modules are excluded from the
   clean pass and fed to the same detector separately, which must fail.
5. **Downstream-use pair probes** — `audit/probes/<task>/UseProbe.lean` checks, in the rebuilt
   olean environment, that every claimed constructor and downstream declaration exists and whether
   the constructor occurs in the downstream's **type** and in its **value** (proof term, unsealed
   with `value? true`), plus a direct reverse-use census.
6. **Semantic review** — four independent read-only source reviews (full reports in
   `audit/subreports/`): `adapter-plans.md`, `audit-and-review-cards.md`, `heatkernel-bridge.md`,
   `ibp-deturck.md`; the load-bearing findings were re-verified by me against the sources and logs.
7. **Per-file compile gates** — `lake env lean` on every `.lean` file under `release/`, 64-way
   parallel (`audit/tools/perfilesweep.sh`), mirroring the dispatcher's compile-gate semantics.

Per-file gate results (every `.lean` file under `release/`, `lake env lean`, exit-0 required):

| task | files | nonzero |
| --- | --- | --- |
| D13-integrated-kernel-audit | 456 | 0 |
| D13-critical-path-review | 454 | 0 |
| D13-upstream-adapter-audit | 315 | 0 |
| D13-morgan-tian-adapter-plan | 322 | 0 |
| D13-topping-ricci-adapter-plan | 322 | 0 |
| D13-manifold-ibp-volume-form | 121 | 0 |
| D13-deturck-shorttime-producer | 339 | 0 |
| D13-vankampen-recognition | 116 | 0 |
| D13-heatkernel-bridge-d10-d7 | 320 | **1** (`Poincare/D13/HeatKernelBridge/ConjugateScalarCurvature.lean`) |

Raw results are in `audit/logs/perfile_all.status`, `audit/logs/perfile_all2.status` and
`audit/logs/<task>-perfile-gate/results.txt`. The heat-kernel failure is isolated to exactly the
module that is absent from its card (F13).

No audited file was modified. This audit introduces no `sorry`, `axiom`, `admit`, `unsafe`,
`native_decide` or `proof_wanted`; its only axioms in any environment are the cards' own documented
negative controls.

---

## 1. Results at a glance

| card | hash replay | cold build | independent probe | worst finding |
| --- | --- | --- | --- | --- |
| D13-integrated-kernel-audit | 462/462 MATCH | exit 0 (9339 jobs); per-file 456/456 | 237 modules / 8161 decls PASS; new layer 4343 / 3196 theorems PASS; statement-shape scan 3196 theorems 0/0/0; negative control FAILs as required | F1 coverage over-claim, F2 in-package constant collision |
| D13-critical-path-review | 460/460 MATCH | exit 0 (9337 jobs) | 2073 decls PASS; **per-file gate 454/454 exit 0** | F12 minor (self-attested counts) |
| D13-upstream-adapter-audit | no card manifest; 20 listed hashes match | exit 0 | 839 decls PASS | F9 unbacked mapping row |
| D13-morgan-tian-adapter-plan | no card manifest; 7/7 module hashes match | exit 0 | 1743 decls PASS | F10a section reference |
| D13-topping-ricci-adapter-plan | no card manifest; listed hashes match | exit 0 | 1552 decls PASS | F10b/c/d mapping + missing logs |
| D13-manifold-ibp-volume-form | no card manifest; 5 listed hashes match | exit 0 (9003 jobs) | 971 decls / 49 modules PASS | F3/F4 scope + accounting |
| D13-deturck-shorttime-producer | no card manifest; 6 listed hashes match | exit 0 | 1971 decls PASS | F5/F6 certificate disconnect + `(h:P):P` wording |
| D13-vankampen-recognition | 6/6 listed hashes match | exit 0 | 2099 decls PASS | SR-4/SR-5 verified (F14) |
| D13-heatkernel-bridge-d10-d7 | 26/26 listed hashes match (23 Lean + 3 root build config) | **exit 1 — build failed** | 1271 decls PASS for the 15 card-audited modules (broken 16th excluded) | F7/F13 delivered tree does not build; card stale |
| D13-cross-audit-360-cards | no own Lean modules | n/a | n/a (local 360-1 sources used for re-verification) | F11 card-internal contradictions |

Every clean probe's full cone census is in `audit/logs/<task>-clean-probe.log`; every exit code and
job count is in `audit/logs/<task>-cold-build.log` and `audit/logs/build_all.status`.

---

## 2. What the audited cards actually prove (semantic classification)

None of the ten cards claims the Poincaré conjecture, and no audited headline theorem is a
manifold-level Perelman theorem. The honest classification of the load-bearing content is:

* **Audit / infrastructure** — `D13-integrated-kernel-audit`, `D13-critical-path-review`,
  `D13-cross-audit-360-cards`. These produce ledgers, probes and verdicts, not mathematics.
* **Adapter plans (statement-mapping + small compatibility modules)** —
  `D13-upstream-adapter-audit` (36 declarations, A1/A2/A3/P1/P5 explicitly not closed),
  `D13-morgan-tian-adapter-plan` (50 declarations, U1–U5/U9 not closed; one **flat-model** closure),
  `D13-topping-ricci-adapter-plan` (50 declarations, U6/U7/U8/I2 not closed).
* **Model + conditional** — `D13-manifold-ibp-volume-form`: the volume measure is a glued sum of
  chart measures over an **abstract atlas** (`OverlapAtlas` with `M : Type* [MeasurableSpace M]`,
  `metric : ℕ → ChartMetric d`); the unconditional IBP is a **model** theorem on the explicit
  half-space atlas with an arbitrary per-chart `ChartMetric`; the general cover IBP is **conditional**
  on abstract `Du`/`Guv` plus explicit `hD`/`hG` identifications. No mathlib-manifold instantiation
  exists (`Riemannian/AtlasBridge.lean` lemmas are not wired into `OverlapAtlas`).
* **Conditional / model** — `D13-deturck-shorttime-producer`: the producer packages a D12 Duhamel
  setup plus a strict-parabolicity certificate; `MildClassicalOutput` is the named gauge/regularity
  bridge; no short-time existence theorem and no closure of U8.
* **General + conditional** — `D13-vankampen-recognition`: the stereographic homeomorphisms, the
  van Kampen computation and `SimplyConnectedSpace S3` are unconditional point-set/algebraic
  topology; the Stage6 assembly is conditional on `spaceForm` + the D7 certificates.
* **Statement-level refutation + conditional interface** — `D13-heatkernel-bridge-d10-d7`: the D7
  snapshot predicate is genuinely refuted (`¬ P`, hypotheses explicit); the v2/v3 repaired predicates
  are statement-only interfaces with model inhabitants; `D7-HEAT-KERNEL-EXISTENCE` remains open.

---

## 3. F-findings (all with reproducible evidence)

Full evidence lines are in `longrun/results/D13-cross-audit-ophis-cards.json` (`findings`). Summary:

**F1 — coverage over-claim (integrated audit).** The “full-package pass … every declaration of the
integrated package … excluding only the two negative-control modules” actually covers the import
closure of `SnapshotRoot + SelfAudit + ReleaseCheck + ReleaseAudit + D6AuditReport`: **237 of the 456
modules** in the released tree. 219 modules are outside it (D7:128, D9:24, D12:20, D10:12, D11:9,
D8:6, Longrun:9, D13 audit drivers:3, VKPort:1, base/driver files:7). I reproduced the 237/8161
numbers exactly with my own detector; an independent source scan finds no top-level axiom among the
219 other than the two documented negative controls, but the card does not establish their kernel
cleanliness.

**F2 — in-package constant collision (integrated audit).** `Poincare.D7.ConjugateHeat.ConjugateHeatData`
is declared twice in the same package (`D7/ConjugateHeat/Basic.lean:129`,
`D7/Monotonicity/ConjugateHeatCertificate.lean:140`). Importing both in one environment is rejected
by Lean; `lake build` does not catch it. The card's collision check covers only the 161 merged
modules, so “path-level collisions: 0” does not extend to the 456-module package.

**F3 — headline scope over-claim (manifold IBP).** “the named blockers I4 and U7 … are discharged”
over-scopes: the constructions are internal chart/atlas results, the D6 ledger `U7` entry still reads
`open` (“in the pinned mathlib”), and the queue still carries `["I4","U7"]` with
`compiled_only_until_independent_semantic_review`.

**F4 — accounting (manifold IBP).** Three section-5 “downstream checked use” cells name proof inputs
or terminal results rather than consumers: `halfSpaceAtlas_laplacianIntegralZero` has no consumer;
`halfSpaceAtlas_integrable_dirichlet` does not call `halfSpaceAtlas_weightedIBP_unconditional`
(my probe: `value=false`); the `W_gauss*` names do not consume the I4 bridge. The card also says
27 declarations for a file containing 29.

**F5 — internal coherence (DeTurck).** `RicciDeTurckPicardModel`’s `strictParabolic` certificate is
disconnected from its analytic data: `existsUnique_mildSolution_of_model` is
`P.duhamel.existsUnique_mildSolution` and `strictParabolic` has no consumer. `of_metric` takes
`S, F, u₀, DuhamelSetup` as inputs, so it produces a model + symbol certificate, not a solution.

**F6 — wording vs shape (DeTurck).** `MildClassicalOutput` is `DeTurckShortTimeExistence` unpacked and
`deTurckShortTimeExistence_of_classicalOutput` repackages it; the row “never the conclusion” is
inaccurate for that adapter. U8 itself is correctly not claimed closed.

**F7 + F13 — delivered tree vs card, and cold-build failure (heat-kernel bridge).**
`release/Poincare/D13/HeatKernelBridge/ConjugateScalarCurvature.lean` (33 top-level declarations,
mtime 23:13) is absent from the card, its hash manifest, its forbidden scan and its `AxiomAudit`.
My cold rebuild fails on exactly that module:

```text
error: Poincare/D13/HeatKernelBridge/ConjugateScalarCurvature.lean:497:8: invalid `▸` notation,
       expected result type of cast is Tendsto (fun t => ∑ x, finiteConjKernelWith G R t₀ x y t) (𝓝[<] t₀) (𝓝 1)
Some required targets logged failures:
- Poincare.D13.HeatKernelBridge.ConjugateScalarCurvature
error: build failed                       (COLD_BUILD_EXIT 1)
```

Reproduced by direct `lake env lean` on the module, and isolated by the per-file gate: of 320 `.lean`
files in the tree, exactly this one is nonzero. The card therefore cannot be replayed on the
delivered tree, and the 33–39 declarations of that module have no kernel-cone evidence. The ophis
queue still lists the task as **running**, consistent with a post-card invocation.

**F8 — unformalized claim (heat-kernel bridge).** The card attributes the falsity of both the
self-adjointness and the dissipativity Bochner forms to `LaplacianSymmetryRefutation.lean`; only
`not_forall_laplacian_symmetric_flatLine` is formalized.

**F9 — unbacked mapping row (upstream adapter).** The Gaussian-reduced-volume row records an
“rfl-transport” from the Evans integral to `gaussianReducedVolume_eq_one`; no D13 declaration performs
it (0 `gaussianReducedVolume` hits under `release/Poincare/D13`).

**F10 — mapping/evidence gaps (Topping adapter).** “10 transcribed Topping Core theorems” vs 9
upstream theorem declarations; the mapping table credits D12 modules absent from this release; no
build logs or negative-control artifacts were relayed, so the job-count and per-file claims are
undetermined from the snapshot.

**F11 — card-internal contradictions (360-cards audit).** Ten consecutive contradictory “Round-11
headline” paragraphs (some still `TASK_BLOCKED` / 8-9 cards / 304 cones, others `TASK_DONE` / 9-9 /
324 cones), duplicated `F27`/`F28` ids, and a stale `Audit.lean:36` citation. The substantive findings
(F1 name over-qualification, F2, F4, F5, F11, F26) were independently reproduced against the local
360-1 sources; the `audit360/`/`a3d2d3/` staging tree was not transported, so several further
findings remain undetermined.

**F12 — minor self-attestation defects (critical-path review).** The card says “two” in-glob `False`
axioms although its own release contains three (my token census lists the third,
`Poincare.D13.CriticalPathReview.NegControl`); it cites 9329 jobs where the repair log and my rebuild
show 9337; one `authored-hashes.txt` entry is stale.

**F14/F15/F16/F17 — verified positives and a downstream precision point.** SR-4/SR-5 (vankampen),
B1 dimension 1 (critical-path), and the flat-model KV-10/NCF-9 closure (Morgan–Tian) all pass the
triple rule (section 4). For the heat-kernel bridge, the named equivalence
`exists_v1_iff_exists_legacy` has 0 direct users; D7 consumption is real but flows through
`HeatKernelDataV1` (81 direct users, including D7 `finite_pinned_dataV1` and `v1_flat_inhabited`).

---

## 4. Blocker closures: accepted and not accepted

The acceptance rule applied here is the task's rule: **constructor + downstream checked use +
independent rebuild**, with the scope stated. Exactly four records pass; two claimed discharges do not.

| card | claim | constructor | downstream checked use | rebuild | scope | accepted |
| --- | --- | --- | --- | --- | --- | --- |
| vankampen-recognition | SR-4 | `simplyConnectedPieces_of_v2` | `mkV2Complete` (value=true), `toRemainingV3` | exit 0, 2099 decls PASS | unconditional about V2 data; Stage6 consumption conditional | **yes** |
| vankampen-recognition | SR-5 | `ConnectedSumDecomposition.mkV2` bundled in `mkV2Complete` | `stage6Target_of_v4hypotheses_from_certificates` (value=true) | exit 0, 2099 decls PASS | conditional Stage6 assembly | **yes** |
| critical-path-review | B1 | `b1_dimension_one` | `kernelTangent_scalarField_iff`, `scalar_forward_invariance` (value=true) | exit 0 (9337 jobs), 2073 decls PASS | **dimension 1 only; n ≥ 2 open** | **partial only** |
| morgan-tian-adapter-plan | KV-10/NCF-9 | `flatModel_ballVolumeComparison` | `flatModel_kappaNoncollapsingCertificate` (value=true) | exit 0, 1743 decls PASS | **flat ℝ³ model only** | **model level only** |
| manifold-ibp-volume-form | I4+U7 discharged | internal constructions exist and two have consumers | two of the claimed cells are not consumers (probe `value=false`); ledger `U7` still `open` | exit 0, 971 decls PASS | — | **no** |
| deturck-shorttime-producer | U8 antecedent | `of_metric` packages model+certificate; certificate has no consumer | `deTurckShortTimeExistence_of_classicalOutput` is `(h:P):P` | exit 0, 1971 decls PASS | U8 correctly not claimed | **no** |

`D13-integrated-kernel-audit`’s own nine blocker-verification records were re-checked with my pair
probe: all 30 constructor/downstream names exist, and my results agree with the card’s honest
caveats (e.g. `heatOperatorBCF_comp → heatOperator_gaussianKernel_L1_tendsto_seq` `value=false`,
matching its `partially_over_claimed` verdict; `leviCivitaExists` has 0 retained consumers, matching
its `verified_with_caveat`). The **direct-use** probe agrees with the card’s recorded pair evidence
on 25/30 pairs; the five differences are exactly the cases the card probed **transitively**, and my
own transitive proof-term closure probe confirms all five are true
(`audit/logs/D13-integrated-kernel-audit-transitive-use.log`), so all 30 records agree. No D13 card
closes a D12 named blocker outright.

The audited cards’ own self-critical findings were also independently reproduced where the artifacts
allow: the integrated card’s heat-semigroup over-claim (my direct probe `value=false`), its
zero-consumer constructors (`leviCivitaExists`, `fDerivativeStatement_of_corrected_of_idempotent`),
its `sturm_comparison` name mismatch (0 occurrences), the critical-path card’s
`iteratedSphereSum_homeo_sphere` zero-consumer finding, and the 360-card’s F26
(`finiteFreeOrbit_isQuotientCoveringMap` is used only in the V3/spaceForm route, not through
`mkV2`/`stage6Target_of_v2hypotheses`). Finally, my independent statement-shape scan over all 3196
new-layer theorems reproduces the integrated card’s 0/0/0 result (no hypothesis equal to the
conclusion, syntactically or definitionally; no conclusion inside a hypothesis).

---

## 5. Honest boundaries

* **`TASK_DONE` is not a Poincaré proof.** No audited card claims one, and this audit accepts none.
  The end-game theorems remain conditional on `spaceForm`, extinction, canonical-neighbourhood and
  surgery inputs; the analytic core (quasilinear Ricci–DeTurck existence, manifold heat kernel,
  Cheeger–Gromov compactness, Moise, extinction) remains open.
* **Conditional / model / statement-only results stay labelled.** In particular: the manifold-IBP
  measure is an abstract-atlas construction; the half-space IBP is a model theorem; the DeTurck
  producer is a conditional package; the heat-kernel repaired predicates are statement-only; the
  adapter modules map statements and prove flat-model instances.
* **Kernel-clean is not mathematically correct**, and a constructor-plus-consumer pair is not the
  general theorem. The independent probes certify cones and use, not meaning.
* **One delivered tree does not compile** (heat-kernel bridge) and is reported as such rather than
  being repaired here: the audit does not edit builder mathematics.
* **No sorry/axiom/admit/unsafe/native_decide/proof_wanted** is used by this audit. The only
  `False` axioms encountered are the cards’ own negative controls, and they fail the detector as
  required (`audit/logs/D13-integrated-kernel-audit-negcontrol-probe.log`).

---

## 6. Reproduction

```bash
export ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-ophis-cards

# 1. transport (tunnel to ophis-gpu)
bash audit/fetch_ophis.sh

# 2. source-hash replay per card
for t in D13-integrated-kernel-audit D13-critical-path-review ... ; do python3 audit/tools/replay_hashes.py $t; done

# 3. cold rebuilds (fresh .lake/build, shared pinned prebuild)
bash audit/tools/build_all.sh D13-vankampen-recognition D13-manifold-ibp-volume-form \
  D13-upstream-adapter-audit D13-morgan-tian-adapter-plan D13-topping-ricci-adapter-plan \
  D13-deturck-shorttime-producer D13-critical-path-review D13-heatkernel-bridge-d10-d7
bash audit/tools/cold_build.sh D13-integrated-kernel-audit

# 4. independent fail-closed axiom probes
python3 audit/tools/gen_probe.py <task>
bash audit/tools/run_cleanprobes.sh <task>
# integrated full closure + new layer + negative control
cd audit/build/D13-integrated-kernel-audit/release
lake env lean ../../../probes/D13-integrated-kernel-audit/FullClosureProbe.lean
lake env lean ../../../probes/D13-integrated-kernel-audit/NewModulesProbe.lean
lake env lean ../../../probes/D13-integrated-kernel-audit/NegControlProbe.lean   # exit 1 expected
lake env lean ../../../probes/D13-integrated-kernel-audit/CollisionProbe.lean    # exit 1 expected

# 5. downstream-use pair probes
python3 audit/tools/gen_useprobe.py audit/specs/<task>.json
bash audit/tools/run_useprobes2.sh <task>

# 6. evidence + result
python3 audit/tools/collect_probe.py <task>
python3 audit/tools/assemble_result.py
```

Key artifacts: `audit/logs/` (builds and probes), `audit/evidence/<task>/` (hashes and summaries),
`audit/probes/<task>/` (generated Lean detectors), `audit/subreports/` (four independent semantic
reviews), `checkpoint.json` (progress), `longrun/results/D13-cross-audit-ophis-cards.json`
(machine-readable twin of this card).

TASK_DONE
