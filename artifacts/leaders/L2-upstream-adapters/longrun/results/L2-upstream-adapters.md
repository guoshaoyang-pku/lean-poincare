# L2-upstream-adapters — result card

**Task id:** `L2-upstream-adapters` (lane: scout, milestone M2)
**Worktree:** `longrun/worktrees/leaders/L2-upstream-adapters`
**Generated (UTC):** 2026-09-11T17:25:30Z
**Round:** 5 (continues rounds 1–4 from `checkpoint.json`; no completed work restarted)
**Verdict:** **TASK_DONE** — the M2 upstream-adapter milestone is delivered and
independently checkable: the pinned Frenzymath snapshot was verified, twelve
upstream packages (the eight API-bearing ones plus the four remaining
inventoried PDE/Riemannian sources) and an isolated adapter package build in the
same workspace without flattening pins, APIs are inventoried against the local
U1–U12 blockers, imported claims are classified, and the fail-closed axiom audit
covers **124 declaration cones** with only `propext`, `Classical.choice`,
`Quot.sound`; the audit is **complete by construction** (every authored
declaration is discovered, audited and cross-checked against the log). Round 3
added real constructed-input consumers for **U1** and **U3**, including two
general (model-independent) pointwise curvature theorems; round 4 corrected an
inventory over-claim, exposed the upstream pointwise `(0,4)` symmetry surface
through aliases, and hardened the audit and novelty evidence. Round 5 adds the
requested **snapshot-wide `sorry` ledger** (274 real occurrences, all LeeSmooth,
all `statement-only`, machine-checked quarantine), **builds the integrator
`release/` at its own pin from a byte-identical mirror in this worktree**
(`lake build` exit 0, 9339 jobs, release self-audits green), adds four explicit
pointwise `(0,4)`-form symmetry consumers with weaker hypotheses, and
**corrects one overstated snapshot check from round 3**. This card requests
independent acceptance. **No named blocker is closed**
(`exact_blockers_closed = []`) and **no Poincaré theorem is claimed**.

---

## 0. What this card claims and does not claim

**Claims (each with recorded command, exit code and log):**

1. The pinned snapshot `frenzymath/Poincare-Conjecture@bb91a091` (Lean
   `v4.32.1`, mathlib `520045ab`) is intact: 2801 tracked files, 2352 Lean
   files, 657189 Lean lines, `source_tree_sha256 =
   9a2b660a8c9c3940cf076512d70d7ee04997efc53d3ecabd5d1a8a149e3684af`.
   Building in place added only ignored `.lake` artifacts
   (`sources_untouched: true`). **Round-5 correction:** the round-3/4 sentence
   that `verify_frenzymath_snapshot.py` still exited 0 after those builds was a
   piped-status artifact; that script is the *pristine-seed* check and its
   recorded pass is `evidence/snapshot-verify.json` (taken before the builds).
   The authoritative source-integrity check is `source-hashes.py`
   (`sources_untouched: true`, tree hash unchanged), and the pristine script now
   correctly reports the expected `.lake` artifacts and exits 1. See §11.1.
2. `Shared` and the seven selected upstream packages build with `lake build` at
   their own pin, all exit 0: `DoCarmoLib`, `MorganTianLib`, `Topping`,
   `PetersenLib`, `HatcherLib`, `KleinerLott`, `ChowKnopf` (round-2 logs; round 3
   rebuilt both adapter libraries against them, exit 0). Round 4 additionally
   compile-checked the four remaining inventoried packages in the same
   workspace: `LeeLib` (LeeRiemannian), `EvansLib`, `HanLinLectureNotes`,
   `GilbargTrudinger`, all exit 0 with zero `sorry` warnings
   (`evidence/logs/round4-new-packages-build-canonical.log`); they are required
   by the adapter lakefile but never imported by its modules, so the adapter's
   Lean environments and audit are unaffected.
3. An isolated adapter package `adapters/` (Lean `v4.32.1` + mathlib
   `520045ab`) consumes those packages **in place as Lake path requirements** —
   no source is copied and no pin is flattened — and builds its authored
   modules in two Lean libraries from 16 authored Lean files, exit 0; round 5
   re-ran a clean authored-layer rebuild after `rm -rf adapters/.lake/build`:
   3757 jobs, `SCRIPT_EXIT=0`, 37.9 s including the audits and the 124-cone
   check (`evidence/logs/round5-clean-rebuild.log`).
4. The adapter exposes 89 `alias` renamings of upstream declarations (exact
   type, exact proof term) plus **27 authored constructed-input consumers** and
   8 auxiliary constructions (89 aliases + 35 non-alias authored declarations =
   the 124 audited declarations). Round 5 expanded the alias surface by 30 names
   covering the remaining inventoried U2/U3/U4/U6/U7/U9/M4 entry points
   (`ricciForm`, `scalarCurvature`, `sectionalCurvature`, `ricciForm_symm`,
   `IsGeodesic`, `HasGeodesicEquationAt`, `parallelTransportTangentEquiv`,
   MorganTian's pointwise `ricciForm`/`scalarCurvature`/`ricci_curvature_comparison`,
   the Hamilton parallel-frame maximum principle, Topping's `divergence` family
   and the Laplace–Beltrami identity, `SmoothCompleteRicciFlowOn`/`RicciFlowData`,
   the universal-cover construction, and Petersen's
   `curvatureTensorTypes`/`expMap`/`RicciCurvature`/`IsJacobiField`/`leviCivita`/
   `koszul`/Myers bound surface). The consumers are: **4 general
   model-independent U1 operator theorems** (`curvatureOperatorAt_antisymm_left`,
   `…_bianchi`, `…_zero_first`, `…_zero_third`), **4 derived pointwise
   `(0,4)`-form lemmas** (`UpstreamAdapters/PointwiseSymmetries.lean`, round 5,
   explicitly *derived*, see §6), **12 Euclidean-model consumers** (9 in
   `DownstreamGeometry.lean` + 3 in the Petersen library) and **7 `DownstreamUse`
   consumers** (4 Riesz, 1 length-space, 2 topology). The 8 auxiliary items are
   the two `Plane` abbrevs, the defs `euclideanLine` and `stdFormR`, and the
   four facts `euclideanLine_zero`, `euclideanLine_contMDiff`, `stdFormR_apply`,
   `stdFormR_isPosDef`. Round 4 added four aliases for
   the upstream pointwise `(0,4)`-form symmetry surface
   (`MorganTian.curvatureFormAt_antisymm_left/_right`, `curvatureFormAt_bianchi`,
   `isAlgCurvatureForm_curvatureFormAt`).
5. The fail-closed axiom audit passes: **124 declaration cones**, all exactly
   within `{propext, Classical.choice, Quot.sound}`, zero `sorryAx`. The audit
   is generated from **every** declaration in the authored sources (100 in the
   main library, 24 in the Petersen library) and is checked for coverage:
   authored == audited == logged (124 == 124 == 124), so a declaration added
   without regenerating the audit, a stale/duplicate audit line, or a truncated
   log is a hard failure. Independently, the upstream packages' own 1111
   `#print axioms` self-audit records (round 2) also show only those three
   axioms.
6. Every static claim is classified as `proved`, `conditional`, `model`,
   `statement-only`, `upstream source claim`, or `definition`, with file/line
   provenance: **108 curated entries** (71 proved / 15 definitions / 14 model /
   8 conditional), of which 35 are adapter-authored — **every non-alias
   authored declaration** (the 59 aliases are exempt by construction) — and
   carry runtime-resolved provenance (`evidence/claim-classification.json`).
7. A novelty check (`evidence/check-novelty.py`) compares every non-alias
   authored declaration name against the upstream declaration index, fails on
   public duplicates, and records permitted private-name re-derivations. It
   passes with exactly one recorded case: the public re-derivation of the
   upstream `private` lemma `euclidean_curvatureFormAt_eq_zero`. Round 4 used
   this check to catch and withdraw four drafted form-symmetry theorems that
   duplicated public upstream pointwise lemmas — see §10.
8. Round-3 U1/U3 consumers are honestly graded by novelty (§6): four are new
   **general** theorems (no upstream pointwise operator form); the Euclidean-plane
   statements are marked `model`; several are upstream instantiations and are
   labelled as such, not passed off as new mathematics; the pointwise `(0,4)`
   form symmetries are upstream and are exposed as aliases, not re-proved. The
   four round-5 `PointwiseSymmetries` lemmas are labelled *derived consumers*
   (weaker hypotheses, no new mathematics).
9. **The integrator release builds in this worktree.** `release/` was seeded
   from the same D6 base as the peer leaders and then synced to the current L1
   integrator sources; the mirror is **byte-identical**: 462/462 files match
   the L1 `source-hash-drift.json` manifest (`evidence/release-mirror-hashes.json`).
   `lake build` at the release pin (`leanprover/lean4:v4.34.0-rc2`, mathlib
   `7974e751`) exits **0** (9339 jobs), with **0** `declaration uses 'sorry'`
   warnings and the release's own audits replaying green (`D5ReleaseAudit`,
   `D6AUDIT`, `D13VERDICT`, `D13SELFVERDICT`, `D13FULLVERDICT` all PASS;
   `evidence/logs/round5-release-build.log`). This is an independent rebuild of
   the integrator artifact from the L2 worktree; it neither edits L1 nor
   flattens a pin.
10. **The requested `sorry` ledger exists.** `evidence/sorry-ledger.py` scans
    the whole snapshot comment/string-aware and emits
    `evidence/sorry-ledger.json` + `.md`: **274 real `sorry` occurrences in 89
    files, every one in `LeeSmooth`, every one classified `statement-only`,
    every enclosing declaration resolved**, exactly matching the static
    inventory (`evidence/upstream-inventory-v2.json`) per package. `--check` is
    idempotent and `--quarantine` proves that no authored adapter file mentions
    the sorry-backed package (`evidence/logs/round5-final-verify.log`).

**Does not claim:**

- No Poincaré conjecture, geometrization, or Perelman theorem is proved or
  asserted. The snapshot's root `PoincareConjecture/` project is an empty stub
  (3 files, 37 lines, **0 declarations**).
- No named blocker is closed: **U1 and U3 remain open**. Constructed input and
  downstream consumers now exist at the upstream pin (2 of the 4 closure legs);
  the independent rebuild and the semantic review are delegated child tasks,
  and no release-pin consumer exists (cross-pin olean import is impossible).
- The upstream declarations are not re-verified against the books they
  formalize; the classification is a static + compiled audit of the snapshot,
  not a mathematical review of Morgan–Tian, do Carmo or Petersen.
- The release mirror is a *copy* of the L1 integrator sources, kept byte-identical
  and hash-checked; it is not a second authoring surface. Round 5 did not add
  release-side consumer theorems: the release-pin mathlib still has no
  connection/curvature/geodesic primitives, so a release-pin consumer would
  require re-developing the connection layer at the release pin, which is
  integrator/geometry-lane work (see §5 of `evidence/pin-gap-u1u3.md`).

---

## 1. Pins and why isolation is mandatory

| | snapshot (upstream) | local release (L1 worktree, read-only) |
|---|---|---|
| Lean | `leanprover/lean4:v4.32.1` | `leanprover/lean4:v4.34.0-rc2` |
| mathlib | `520045ab14e26149ee970e2e617ca04b09bde5d6` | `7974e751bece` |
| source | `frenzymath/Poincare-Conjecture@bb91a091` | local `release/` package |

Upstream oleans are not importable by `release/`, and flattening the pins is
forbidden (it would invalidate release evidence and create ambiguous module
ownership). The adapter package is therefore the sound reuse mechanism: it
adopts the upstream pins locally, keeps upstream trees authoritative, and gives
downstream lanes stable names plus machine-checked provenance.

**Compatibility findings.** (i) `Shared.Util.Attributes` and
`PetersenLib.Foundations.Attributes` both call
`register_simp_attr metric_simp`, so any module importing both fails with
"environment already contains `Parser.Attr.metric_simp`"; the adapter is
therefore split into `UpstreamAdapters` and `UpstreamAdaptersPetersen`, which
never share an environment. (ii) The upstream root modules `Topping.lean` and
`KleinerLott.lean` import only a subset of their own files (specific modules
must be imported explicitly). (iii)
`HatcherLib.fundamental_group_retract_map_injective` is `private` and therefore
not consumable.

**Read-only observation (round 3; extended in round 4).** The L1 `release/`
worktree contains an authored `Poincare/D7/Curvature` layer and
`Poincare/D7/Geodesic` files (456 Lean files). It has since been surveyed
read-only for the pins of §10.4; the measurements (no mathlib curvature /
geodesic / exponential / parallel-transport declarations; a
`Probe.CurvatureTensor` interface with field-supplied laws; the abstract
`RiemannCurvatureData` layer; the model-space `GeodesicData` and the unstatable
`GeodesicContext.accel_is_covariant_acceleration`) are recorded in
`evidence/pin-gap-u1u3.md`. This task neither built nor modified that worktree;
reconciling the release-side layer with this upstream manifold-level adapter is
the subject of the imported `M2-PIN-BRIDGE-DECISION` child task.

---

## 2. Build evidence (exact commands and exits)

| step | command (in the stated directory) | exit | log |
|---|---|---|---|
| mathlib cache | `MATHLIB_CACHE_DIR=evidence/mathlib-cache lake exe cache get` | 143 (killed after 99.8%, remaining modules compiled from source) | `evidence/logs/shared-cache2.log` |
| `Shared` | `lake build` in `third_party/.../shared` | **0** (2476 jobs) | `evidence/logs/shared-build2.log` |
| upstream libs | `lake build DoCarmoLib` … `lake build ChowKnopf` in `adapters/` | **0,0,0,0,0,0,0** | `evidence/logs/adapters-upstream-build.log` |
| adapter package (round 3) | `lake build` in `adapters/` (default target `UpstreamAdapters`) | **0** (9624 jobs) | `evidence/logs/axiom-audit-build.log` |
| Petersen library (round 3) | `lake build UpstreamAdaptersPetersen` | **0** | `evidence/logs/axiom-audit-build.log` |
| audit modules | `lake env lean UpstreamAdapters/Audit.lean` and `…Petersen/Audit.lean` | **0, 0** | `evidence/logs/axiom-audit.log` |
| hardened audit (round 4) | `bash evidence/run-axiom-audit.sh` — builds, audits, cone check **and** coverage check, exits non-zero on any failure | **0** (`SCRIPT_EXIT=0`) | `evidence/logs/round4-clean-rebuild.log` |
| clean rebuild (round 5) | `rm -rf adapters/.lake/build; bash evidence/run-axiom-audit.sh` (16 authored files, includes `PointwiseSymmetries`) | **0** (`CLEAN_REBUILD_EXIT=0`, 3757 jobs, 37.9 s, 124 cones) | `evidence/logs/round5-clean-rebuild.log` |
| release mirror build (round 5) | `lake build` in `release/` with `leanprover/lean4:v4.34.0-rc2` + mathlib `7974e751` | **0** (9339 jobs, 0 sorry warnings) | `evidence/logs/round5-release-build.log` |
| release mirror hash check | `python3 evidence/verify-release-mirror.py release <L1 manifest>` | **0** (462/462 byte-identical) | `evidence/release-mirror-hashes.json` |
| release forbidden-token classification | `python3 evidence/classify-release-forbidden-hits.py release` | **0** (10 hits, all classified) | `evidence/release-forbidden-classification.json` |
| `sorry` ledger | `python3 evidence/sorry-ledger.py <snapshot> …` + `--check` + `--quarantine` | **0, 0, 0** (274 occurrences, all classified) | `evidence/sorry-ledger.json` |
| forbidden tokens | `python3 evidence/check-authored-files.py .` | **0** (16 files, 0 forbidden tokens in code) | stdout |
| source integrity | `python3 evidence/source-hashes.py . evidence/source-hashes.json` | **0** (`sources_untouched: true`) | `evidence/source-hashes.json` |
| novelty | `python3 evidence/check-novelty.py .` | **0** (124 authored declarations, 1 recorded private-name re-derivation, 0 public duplicates) | stdout |
| four remaining packages (round 4) | `lake build GilbargTrudinger / HanLinLectureNotes / EvansLib / LeeLib` in `adapters/` | **0, 0, 0, 0** (8663 / 8691 / 3754 / 3685 jobs, 0 sorry warnings) | `evidence/logs/round4-new-packages-build-canonical.log` |

The `MATHLIB_CACHE_DIR` override was the only environmental blocker: mathlib's
cache tool defaults to `~/.cache/mathlib`, outside the workspace sandbox
(`mathlib/Cache/IO.lean:56` documents the override). The cache holds 8636
`.ltar` files (435 MB). The offline manifest is generated by
`evidence/make-adapter-manifest.py` and the dependency closure is seeded by
`evidence/seed-adapter-packages.sh` (`git clone --shared`), because `lake
update` cannot reach github.com from this sandbox.

**Round-3 reproducibility re-verification** (`evidence/logs/round3-reverify.log`):
from `adapters/`, `lake build DoCarmoLib MorganTianLib Topping HatcherLib
KleinerLott ChowKnopf` all exit 0 and `lake build Shared` exit 0 (no-op
re-checks against the built oleans);
`python3 evidence/inventory-v2.py …` is byte-deterministic
(inventory JSON sha256 `f8af49eb0104773d94fc297852e026cbd1ae8143fcdc2d5afde659aab73c9565`
before and after); `python3 evidence/qualified-names.py …` exit 0.
**Correction (round 5):** the `SNAPSHOT_EXIT=0` recorded in that log was the
exit status of a *piped* command, not of
`python3 evidence/verify_frenzymath_snapshot.py`, which is a pristine-seed check
and reports the expected `.lake` artifacts (exit 1) once the upstream packages
have been built in place. The pristine pass itself is preserved at seed time in
`evidence/snapshot-verify.json` (2801 files, `no_build_caches: true`); source
integrity is covered by `source-hashes.py` (`sources_untouched: true`). The
round-5 consolidated log records the true status
(`evidence/logs/round5-final-verify.log`, `SNAPSHOT_EXIT=1` with the artifact
list). See §11.1.

**Clean rebuild of the authored layer (rounds 4–5)**
(`evidence/logs/round4-clean-rebuild.log`, `evidence/logs/round5-clean-rebuild.log`,
internal logs `axiom-audit-build.log` / `axiom-audit.log`): after `rm -rf
adapters/.lake/build` (upstream oleans in `third_party/*/.lake` untouched), the
authored layer rebuilt and the hardened `run-axiom-audit.sh` passed with
`SCRIPT_EXIT=0`, 124 cones and coverage 124 == 124 == 124 in round 5 (90 cones in
round 4, 81 in round 3). This shows the authored modules are self-contained and
reproducible from a clean adapter build directory.

**Release mirror build (round 5).** `release/` was seeded exactly as the peer
leader worktrees were (`rsync` of the D6 base sources plus a `.lake/packages`
symlink to the shared `poincare-lab` store) and then re-synced from the L1
integrator worktree. `evidence/verify-release-mirror.py` proves the mirror is
byte-identical to the L1 manifest (462/462 files). With the release toolchain
(`leanprover/lean4:v4.34.0-rc2`, mathlib `7974e751`) `lake build` exits **0**
(9339 jobs) and the release's own audits replay green
(`evidence/logs/round5-release-build.log`). No file outside this worktree was
modified; no pin was flattened.

**Compile-checked axioms:** warnings in the upstream builds are
linter/deprecation notes; there are **zero** `declaration uses 'sorry'`
warnings in the built packages.

---

## 3. Fail-closed axiom audit

```
$ bash evidence/run-axiom-audit.sh
BUILD_EXIT=0
PETERSEN_BUILD_EXIT=0
AUDIT_LEAN_EXIT=0
PETERSEN_AUDIT_LEAN_EXIT=0
axiom audit: parsed 124 declaration cones (record starts in log: 124)
  cone contains Classical.choice: 124
  cone contains Quot.sound: 124
  cone contains propext: 124
AXIOM AUDIT PASSED: all cones within {propext, Classical.choice, Quot.sound}
CHECK_EXIT=0
coverage: 124 authored declarations, 124 audit lines, 124 log records
AUDIT-COVERAGE CHECK PASSED: authored == audited == logged
COVERAGE_EXIT=0
AXIOM AUDIT AND COVERAGE PASSED
SCRIPT_EXIT=0
```

`evidence/check-axioms.py` fails closed: any axiom outside the allowed set
(notably `sorryAx`, `Lean.trustCompiler`), any unparsed record start, or an
empty audit is a failure. Since round 4 the records are generated by
`evidence/make-audit-file.py` from **every declaration discovered in the
authored sources** (100 in the main library, 24 in the Petersen library as of
round 5; dotted
alias names supported; anonymous instances and `private` declarations are
refused), not from a curated list — so no alias, consumer, definition or
auxiliary construction can escape. `evidence/check-audit-coverage.py` then
asserts authored == audited == logged as sets *and* counts. The shell driver
runs both checkers and exits non-zero if any build step, audit run, cone check
or coverage check fails (round 3's driver only echoed exit codes). In addition,
MorganTianLib and Topping annotate their own
sources with `#print axioms`; Lake replays 1111 records into the build log and
**all** have cone exactly `{propext, Classical.choice, Quot.sound}`
(`evidence/logs/upstream-self-audit-axioms.txt`, extractor
`evidence/extract-upstream-self-audits.py`).

---

## 4. Inventory: snapshot content mapped to the local blockers

Static, comment/string-aware scan of the whole snapshot
(`evidence/upstream-inventory-v2.json`, `evidence/upstream-api-inventory.md`,
`evidence/upstream-qualified-names.json` with 5331 namespace-qualified names).

| package | files | lines | decls | real `sorry` | role |
|---|---:|---:|---:|---:|---|
| `shared` | 12 | 877 | 50 | 0 | book-agnostic infra: Riesz extraction, length spaces, fibre-bundle T2 |
| `DoCarmo` | 293 | 103342 | 2931 | 0 | Riemannian geometry: Levi-Civita, curvature, geodesics, parallel transport, sectional/Ricci |
| `MorganTian` | 573 | 140731 | 4655 | 0 | Ricci flow: pointwise Ricci/scalar, Hamilton maximum principles, curvature evolution, Bochner, divergence; 635 self-audited cones |
| `Petersen` | 419 | 144140 | 4617 | 0 | curvature tensor, exponential map, geodesics, comparison |
| `Topping` | 184 | 44610 | 1871 | 0 | weak maximum principles, divergence, volume evolution; 213 self-audited cones |
| `Hatcher` | 58 | 18778 | 1251 | 0 | fundamental group, covering spaces, homotopy equivalences |
| `LeeRiemannian` | 116 | 33374 | 1544 | 0 | Riemannian geometry — **compile-checked round 4** (`lake build LeeLib` exit 0, 3685 jobs, 0 sorry warnings) |
| `Evans` / `HanLin` / `GilbargTrudinger` | 65/37/9 | 22091/10059/1509 | 994/314/63 | 0 | PDE sources — **compile-checked round 4** (`EvansLib` 3754, `HanLinLectureNotes` 8691, `GilbargTrudinger` 8663 jobs, all exit 0, 0 sorry warnings) |
| `KleinerLott` | 11 | 1962 | 96 | 0 | κ-noncollapsing, point selection, smooth complete flow interface |
| `ChowKnopf` | 8 | 357 | 22 | 0 | small Ricci-flow development |
| `LeeSmooth` | 552 | 135191 | 5842 | **274** | smooth manifolds — **statement-only** |
| `PoincareConjecture`, `CaoZhu`, `CheegerGromovTaylor`, `ChowEtAl`, `Thurston` | 3 each | 25–37 | **0** | **stubs** |

Blocker → compiled, aliased candidate (all names `#check`ed; see
`evidence/logs/probe-check-output.txt`):

- **U1 curvature tensor:** `Riemannian.AffineConnection.curvature_zero_left/right`,
  `curvature_apply_congr`, `curvatureOperatorAt_add_left/smul_left`,
  `Riemannian.leviCivita_curvature_frame_expansion`,
  `leviCivita_curvature_chartFrame_expansion`,
  `PetersenLib.curvatureTensorTypes/_coordinates/_indexLowering/_derivation`,
  `contMDiff_curvatureTensorFour`.
- **U1 pointwise `(0,4)` symmetries (round-4 inventory correction):**
  `MorganTianLib.curvatureFormAt_antisymm_left`,
  `MorganTianLib.curvatureFormAt_antisymm_right`,
  `MorganTianLib.curvatureFormAt_bianchi`,
  `MorganTianLib.isAlgCurvatureForm_curvatureFormAt`
  (`MorganTianLib/Ch01/PointwiseCurvature.lean:314/322/332/364`). These already
  exist at the pointwise level; the adapter now exposes them as
  `UpstreamAdapters.Adapters.MorganTian.*` instead of re-proving them. The
  pointwise **operator**-level statements of §6 remain new (upstream has them
  only for vector fields, and only the form level is pointwise upstream).
- **U2 Ricci/scalar:** `MorganTianLib.ricciAt`, `scalarCurvatureAt`, `ricciForm`,
  `scalarCurvature`, `sum_metricInner_riemannCurvature_frame_eq_ricciAt`,
  `trace_frameCurvOp_eq_ricciAt`, `Riemannian.sectionalCurvature`,
  `ricciForm_self_eq_sum_sectionalCurvature`, `ricci_curvature_comparison`.
- **U3 geodesics/exp/parallel transport:**
  `Riemannian.Geodesic.hasGeodesicEquationAt_iff_covDerivAlong_velocity_eq_zero`,
  `isGeodesic_iff_covDerivAlong_velocity_eq_zero`,
  `continuous_and_isGeodesic_iff_leviCivita_covDerivAlong_velocity_eq_zero`,
  `Riemannian.parallelTransportTangentEquiv`,
  `metricInner_parallelTransportTangentEquiv`; `PetersenLib.expMap`,
  `expMap_zero/smul/localDiffeomorphism`, `isGeodesicOn_of_isChartGeodesicOn`,
  `segment_isGeodesic`, `energyLocalMinimum_isGeodesic`.
- **U4 Levi-Civita:** `Riemannian.RiemannianMetric.leviCivita_chartContraction_eq`,
  `leviCivita_covDerivAlong_eq`,
  `AffineConnection.preservesMetricUnderParallelTransport_iff_isMetricCompatible`.
- **U6 parabolic/max principle:**
  `MorganTianLib.hamilton_tensor_maximum_principle_compact/bounded/compact_support/of_parallel_frame`,
  `Topping.weak_maximum_principle(_of_pos)`.
- **U7/U10 divergence/Bochner:** `MorganTianLib.laplacianAt_eq_chart_divergence`,
  `chartVolumeDensity_mul_laplacianAt_eq_divergence`, `function_bochner_formula`,
  `Topping.divergence*`,
  `ParabolicPDE.metricLaplacianAt_eq_laplaceBeltramiChart_divergence`.
- **U8 Ricci flow:** `MorganTianLib.IsRicciFlowEquationOn`,
  `IsRicciFlowOn(.metricInner_hasDerivAt/.inner_hasDerivWithinAt)`,
  `Topping.hasVolumeDerivativeOn_riemannianMeasure_of_isRicciFlowOn`,
  `riemannianVolume_antitoneOn_of_isRicciFlowOn`.
- **U9 Perelman:** `KleinerLott.IsKappaNoncollapsedOnScale`,
  `IsHamiltonIveyPinched`, `exists_point_selection_of_bounded_moving_curvature`,
  `exists_point_of_bounded_curvature`, `SmoothCompleteRicciFlowOn`.
- **M4 topology:** `HatcherLib.simplyConnected_iff_unique_path_class`,
  `IsUniversalCoveringMap.simplyConnectedSpace`,
  `UniversalCoverConstruction.universalCover_simplyConnectedSpace`,
  `attachingSpace_homotopyEquiv`, `homotopyEquivPiOneMulEquiv`,
  `collapseMk_homotopyEquiv`, `simplyConnectedSpace_of_pathConnectedOpenCover`.

---

## 5. Semantic classification

Vocabulary: `proved` (compiled, cone within the allowed set, genuine
hypotheses) · `conditional` (compiled implication whose antecedent is an
unproved interface) · `model` (proved only for a toy/finite/Euclidean model of
the intended geometry) · `statement-only` (proof admitted) · `upstream source
claim` (asserted upstream but not kernel-checked) · `definition` (not a claim).

Counts over the **108 curated entries**: **71 proved, 15 definitions, 14 model,
8 conditional**. All **35 non-alias authored declarations** are entries (the 59
aliases are exempt by construction), each resolved to file:line at
classification time:

- `proved` (general, model-independent): `curvatureOperatorAt_antisymm_left`,
  `curvatureOperatorAt_bianchi`, `curvatureOperatorAt_zero_first`,
  `curvatureOperatorAt_zero_third`; the four round-5
  `PointwiseSymmetries` lemmas (explicitly labelled *derived*, see §6); plus the
  auxiliary `euclideanLine_zero`, `euclideanLine_contMDiff`.
- `model` (constructed Euclidean plane): pointwise curvature operator and
  `(0,4)`-form vanishing, the alias-routed zero-slot theorem, the geodesic /
  exponential / parallel-transport statements, and the three Petersen-family
  statements.
- Upstream-derived classification carries the round-2 entries plus the four
  round-4 MorganTian pointwise `(0,4)` entries: `conditional`
  covers `MorganTianLib.IsRicciFlowOn` and everything named
  `…_of_isRicciFlowOn` plus `KleinerLott.SmoothCompleteRicciFlowOn` (flow
  existence, U8, is not proved); `model` covers
  `Riemannian.sphere_sectionalCurvature_one` and
  `Hyperbolic.hyperbolicMetric_sectionalCurvature_eq_neg_one`; `statement-only`
  is all 274 real `sorry`s in `LeeSmooth`; `upstream source claim` is the
  snapshot's book-faithful developments (the root project has 0 declarations).

---

## 6. Downstream checked use (constructed input, rounds 3–4)

**General (model-independent) U1 consumers — new relative to upstream:**

- `curvatureOperatorAt_antisymm_left` — for **any** affine connection on
  **any** manifold, `R_p(u,v)w = -R_p(v,u)w`. Upstream has only the field-level
  `curvature_antisymm_left`; no pointwise **operator** form exists (grep: 0
  occurrences of the name; no `curvatureOperatorAt…= 0` lemma). The pointwise
  *form*-level symmetry does exist upstream (`MorganTianLib`, §4): the operator
  statement is the new one, and it needs no metric.
- `curvatureOperatorAt_bianchi` — for any **symmetric** connection,
  `R_p(u,v)w + R_p(v,w)u + R_p(w,u)v = 0`. Upstream has only the field-level
  `curvature_bianchi`.

Both are proved through the audited tensoriality bridge
`AffineConnection.curvatureOperatorAt_eq` and `extendField`. The novelty claim
is checked by grep (`evidence/logs/round4-novelty-greps.log`): the snapshot's
only occurrence of `curvatureOperatorAt` near `antisymm`/`bianchi`/`skew` is a
docstring in `JacobiSectionalCurvature.lean:159`; the field-level counterparts
are `DoCarmoCh4.lean:316/333` and the pointwise *form*-level ones are the
MorganTian lemmas aliased in §4.

- `curvatureOperatorAt_zero_first`, `curvatureOperatorAt_zero_third` — the
  pointwise operator vanishes when its first (resp. third) argument is zero,
  for **any** affine connection. These route through the **adapter alias**
  layer (`UpstreamAdapters.Adapters.DoCarmo.curvature_zero_left/right`), so the
  renamed upstream theorems are consumed at full generality.

**Derived pointwise `(0,4)`-form symmetry consumers (round 5,
`adapters/UpstreamAdapters/PointwiseSymmetries.lean`) — weaker hypotheses, *not*
new mathematics:**

- `curvatureFormAt_skew_fst` — the pointwise `(0,4)`-form of **any** affine
  connection is antisymmetric in its first pair. Upstream's pointwise route
  (`isAlgCurvatureForm_curvatureFormAt`) requires `IsLeviCivita`; the field-level
  `curvatureForm_antisymm_left` needs nothing.
- `curvatureFormAt_skew_snd_of_isMetricCompatible` — last-pair antisymmetry under
  metric compatibility alone (the upstream pointwise route bundles symmetry too).
- `curvatureFormAt_bianchi_of_isSymmetric` — pointwise first Bianchi identity
  under symmetry alone (no metric compatibility).
- `curvatureFormAt_pairSwap_of_isSymmetric_of_isMetricCompatible` — pointwise
  pair swap `R(x,y,z,t) = R(z,t,x,y)`, the pointwise form of the upstream
  field-level `curvatureForm_pairSwap`.

Each proof is a one-step consequence of the corresponding upstream field-level
lemma through the audited tensoriality bridge `curvatureFormAt_eq` (or
`curvatureOperatorAt_eq`); the classification notes explicitly say "derived
consumer, not new mathematics". They are still useful downstream because the
upstream *pointwise* surface is bundled behind `IsLeviCivita` and a local
`RiemannianBundle` instance. The genuinely new pointwise **operator** statements
remain the four in the previous subsection.

**Round-4 correction.** The novelty scan (§0.7) found that the corresponding
pointwise statements for the metric-lowered `(0,4)` form are **not** new:
`MorganTianLib.curvatureFormAt_antisymm_left/_right/_bianchi` and
`isAlgCurvatureForm_curvatureFormAt` already state them. Four drafted theorems
were therefore withdrawn and replaced by aliases
(`UpstreamAdapters.Adapters.MorganTian.*`); the aliases are compiled and in the
124-cone audit. The operator-level theorems above need no metric and have no
upstream pointwise counterpart, so they remain the genuine additions. Round 5
adds explicit pointwise form-level lemmas with weaker hypotheses (§6) but labels
them derived consumers, not new mathematics.

**Model-level U1/U3 consumers on the constructed Euclidean plane
`EuclideanSpace ℝ (Fin 2)` (DoCarmo family, `DownstreamGeometry.lean`):**

- `euclidean_curvatureOperatorAt_eq_zero`, `euclidean_curvatureFormAt_eq_zero`
  — the pointwise `(1,3)` operator and `(0,4)` form of the flat plane vanish.
  The pointwise operator statement is new; the `(0,4)` statement is a public
  re-derivation of an upstream **private** lemma of the same name
  (`MorganTianLib/Ch03/RicciFlow/EuclideanExample.lean:34`), whose public
  adapter-level version is consumable downstream.
- `euclidean_alias_curvature_zero_third` — routed through the adapter alias
  `UpstreamAdapters.Adapters.DoCarmo.curvature_zero_right`, showing the renamed
  layer is consumable.
- `euclideanLine_isGeodesic`, `euclideanLine_hasGeodesicEquationAt` — the
  constructed affine line `t ↦ p + t • v` is a geodesic; the moving-foot
  equation is the projection of the upstream predicate. These are **upstream
  instantiations** of the public `isGeodesic_euclideanGeodesic`, labelled as
  such, not new mathematics.
- `euclideanLine_expMapIntrinsic`, `_smul`, `_add` — `exp_p(v) = γ(1)`,
  `exp_p(tv) = γ(t)`, `exp_{γ(s)}(tv) = γ(s+t)`. The first two are
  consequences of the public `expMapIntrinsic_euclidean`; the basepoint flow
  identity is derived and not stated upstream.
- `euclideanLine_parallelTransport_preserves` — parallel transport along the
  line preserves the Euclidean metric, an instantiation of the public
  `metricInner_parallelTransportTangentEquiv`.

**Petersen-family consumers (`UpstreamAdaptersPetersen/DownstreamUse.lean`,
separate environment):** `euclidean_curvatureTensorAt_eq_zero` (new pointwise
form of the public field-level `euclideanSpace_curvature_eq_zero`),
`euclidean_expMap_zero`, `euclidean_expMap_zero_smul` (instantiations at the
concrete `euclideanMetric 2`).

**Classification of this use.** All 27 consumers are in the 124-cone audit with
allowed cones only. The general operator theorems and the four derived
pointwise-form lemmas are `proved`; the Euclidean-plane statements are `model`;
the instantiations are recorded as instantiations.
`TASK_DONE` here means "constructed input + downstream consumer exist and are
compiled"; it is **not** a claim that U1/U3 are closed.

---

## 7. Named blockers

| blocker | status | precise reason |
|---|---|---|
| **M2** (this milestone) | **delivered, requesting acceptance** | inspection, builds, adapter package, inventory, classification and fail-closed audit are complete and reproducible; acceptance of this card is requested |
| **U1** (no curvature tensor in pinned release mathlib) | **open** | upstream compiled candidate inputs exist and two general pointwise operator theorems, four derived pointwise-form lemmas and Euclidean-plane consumers were proved at the upstream pin; the integrator release now also builds in this worktree from a byte-identical mirror (exit 0, self-audits green), but it still has no connection/curvature construction, so a release-pin *consumer* needs a port; still missing: independent rebuild, semantic review (child tasks), and that release-pin consumer |
| **U3** (no geodesics/exp/parallel transport in pinned release mathlib) | **open** | upstream candidates exist and are consumed on the constructed Euclidean plane (geodesic predicate, exponential, parallel-transport isometry); closure requires the independent rebuild + semantic review and a release-side consumer (blocked by the same release-side primitive gap) |

`exact_blockers_closed = []`. The blocker boundary is recorded, not papered
over.

---

## 8. Child tasks and comms

Round 3 emitted two schema-valid child tasks, both imported by the
dispatcher (required fields: `id`,
`group_id`, `parent_node`, `deps`, `lane`, `acceptance`, `host_pool`,
`requires_lean`, `max_hours`, `objective`), each in its own worktree and
classified by expected evidence:

- `comms/outbox/L2-child-u1u3-independent-rebuild.imported` (imported by the
  dispatcher) — verifier lane:
  fresh-worktree rebuild of both adapter libraries, `run-axiom-audit.sh`
  (cone count at emission time 79; the round-5 artifact has **124** after two
  alias-routed general theorems, four aliases, four derived pointwise-form
  lemmas and the full-coverage audit regeneration — `run-axiom-audit.sh` and
  the fail-closed checkers are authoritative), authored-file check, source-hash
  check, novelty check.
- `comms/outbox/L2-child-u1u3-semantic-review.imported` (imported by the
  dispatcher) — reviewer lane: per-theorem
  novelty/classification review of the 27 consumers (23 round-3/4 consumers plus
  the four round-5 derived pointwise-form lemmas), conclusion-equivalence
  check, and a verdict on whether U1/U3 can be marked closed.

**Count-drift note.** Both child tasks were emitted before the final artifact
settled; the independent-rebuild task text cites "79 declaration cones" and the
semantic-review task text cites 24 consumers, while the round-5 artifact audits
**124 declaration cones** over **124 authored declarations** and has **27
consumers**. The commands (`evidence/run-axiom-audit.sh`,
`evidence/check-authored-files.py .`, `evidence/check-audit-coverage.py`,
`evidence/check-novelty.py`) are the source of truth; a child that observes
90/26 with `COVERAGE_EXIT=0` has found the expected final state. Round 4 also
changed the driver: `run-axiom-audit.sh` now exits non-zero on any failure
(it previously only echoed the exit codes), so a verifier should record
`SCRIPT_EXIT=0` in addition to the individual `*_EXIT=0` lines.

The four round-2 tasks (`M2-ADAPTER-U1-CURVATURE-CONSUMER`,
`M2-ADAPTER-U3-GEODESIC-CONSUMER`, `M2-LEESMOOTH-SORRY-LEDGER`,
`M2-PIN-BRIDGE-DECISION`) were imported by the dispatcher (files renamed
`.imported`). The round-2 index file `comms/outbox/M2-child-tasks.index.json`
was rejected as a non-task and is kept as
`comms/outbox/M2-child-tasks.index.rejected`.

---

## 9. Artifacts and reproduction

```
# full check (about 2 minutes when the mathlib cache is populated)
bash evidence/run-round5-checks.sh                              # consolidated round-5 chain; writes evidence/logs/round5-final-verify.log
python3 evidence/verify_frenzymath_snapshot.py                 # pristine-IMPORT check; reports the expected .lake artifacts once the packages are built in place (see §11.1)
python3 evidence/source-hashes.py . evidence/source-hashes.json  # tracked sources untouched (authoritative integrity check)
python3 evidence/inventory-v2.py third_party/frenzymath/Poincare-Conjecture \
        evidence/upstream-inventory-v2.json evidence/upstream-api-inventory.md
python3 evidence/qualified-names.py third_party/frenzymath/Poincare-Conjecture evidence/upstream-qualified-names.json
python3 evidence/sorry-ledger.py third_party/frenzymath/Poincare-Conjecture evidence/sorry-ledger.json evidence/sorry-ledger.md
python3 evidence/sorry-ledger.py --check third_party/frenzymath/Poincare-Conjecture evidence/sorry-ledger.json
python3 evidence/sorry-ledger.py --quarantine adapters evidence/sorry-ledger.json
python3 evidence/classify-claims.py .
python3 evidence/check-authored-files.py .                     # adapter contract: 0 forbidden tokens
python3 evidence/check-authored-files.py . release             # release mirror scan (10 classified hits, see below)
python3 evidence/classify-release-forbidden-hits.py release    # fail-closed classification of those hits
python3 evidence/verify-release-mirror.py release \
        ../L1-lean-baseline/baseline/reconcile/source-hash-drift.json evidence/release-mirror-hashes.json
python3 evidence/check-novelty.py .                            # authored names vs upstream (public duplicates fail)
python3 evidence/make-audit-file.py .                          # regenerate audit modules from ALL authored declarations (idempotent)
bash evidence/run-axiom-audit.sh                               # build + #print axioms + cone check + coverage check; non-zero on failure
```

Authored artifacts: `adapters/` (lakefile, manifest, toolchain,
`UpstreamAdapters.lean`, `UpstreamAdapters/{Probes/*,Adapters,DownstreamUse,
DownstreamGeometry,PointwiseSymmetries,Audit}.lean`,
`UpstreamAdaptersPetersen.lean`,
`UpstreamAdaptersPetersen/{Probes,Adapters,DownstreamUse,Audit}.lean`);
`release/` (byte-identical mirror of the L1 integrator sources at the release
pin, with `.lake/packages` symlinked to the shared package store); evidence
scripts listed in `L2-upstream-adapters.json` (round 5 adds
`sorry-ledger.py`, `verify-release-mirror.py`,
`classify-release-forbidden-hits.py`, `run-round5-checks.sh`,
`run-round5-mutation-tests.sh` and `VERIFY-round5.md`, and extends
`check-authored-files.py` with a `subdir` argument and correct `axiom`
line reporting); brief `research-brief-2026-09-11.md` (§6/§7 are the update);
checkpoint `checkpoint.json` (round 5).

**Limitations / residual risk.** (i) `LeeSmooth` was inventoried but
deliberately not built: it is statement-only by design (274 real `sorry`), and
no claim rests on it; round 5 delivers the full ledger and an executable
quarantine check. The four other formerly unbuilt packages
(`LeeRiemannian`, `Evans`, `HanLinLectureNotes`, `GilbargTrudinger`) are now
compile-checked (exit 0, 0 `sorry` warnings) but their declarations are not
imported into the adapter modules, so their individual claims remain statically
classified rather than audited. (ii) The proved-vs-conditional
classification is based on declaration statements and module structure, not on
a line-by-line review of every upstream proof. (iii) The mathlib cache fetch
was killed at 99.8%; the remaining modules were compiled from source, so no
artifact is missing, but a fully clean `cache get` should be repeated by the
independent verifier. (iv) The Euclidean-plane consumers are model-level; they
do not transfer to general manifolds. (v) The novelty check is name-based plus
the manual classification notes; it catches same-name duplication, not a
same-statement/different-name restatement (the round-4 withdrawal was found by
the name collision). (vi) Independent rebuild and semantic
review are pending — that is what "requests independent acceptance" means.
(vii) The release mirror is a copy of another lane's in-progress artifact: its
hash identity is recorded against the L1 manifest snapshot taken at
`2026-09-11T16:48:48Z`, and a later L1 change would make the mirror stale
until re-synced (the check fails closed on any difference).

---

## 10. Round-4 changelog (corrections and hardening)

1. **Withdrawn over-claim.** Four general pointwise `(0,4)`-form symmetry
   theorems were drafted and then removed: `MorganTianLib` already provides
   them at the pointwise level (`Ch01/PointwiseCurvature.lean:314/322/332` and
   the `isAlgCurvatureForm_curvatureFormAt` package at `:364`). They are now
   adapter **aliases**, and the round-3 sentence in §6 that claimed "no
   upstream pointwise form exists" is corrected there and in the classification
   notes.
2. **Audit coverage.** `make-audit-file.py` discovers every authored
   declaration (refusing anonymous instances/`private`), and
   `check-audit-coverage.py` enforces authored == audited == logged;
   `run-axiom-audit.sh` is fail-closed end to end.
3. **Novelty gate.** `check-novelty.py` fails on non-alias authored names that
   duplicate a public upstream declaration; the single private-name
   re-derivation is explicitly recorded.
4. **Pin-gap scout.** `evidence/pin-gap-u1u3.md` records what the release pin
   has (interfaces and abstract/model layers, no constructions) versus the
   adapter pin, as input to `M2-PIN-BRIDGE-DECISION`; it closes no blocker.
5. **Fresh evidence.** Authored-file check, source-hash check, classification
   (91 entries), hardened audit (90 cones, coverage pass) and a clean
   `adapters/.lake/build` rebuild were all re-run in this round. The final
   end-to-end chain is `evidence/logs/round4-final-verify.log`; the verifier
   checklist with the expected numbers is `evidence/VERIFY-round4.md`.
6. **Checker mutation tests** (`evidence/logs/round4-checker-mutation-tests.log`):
   an injected unaudited declaration makes the coverage checker exit 1; a
   truncated log makes it exit 1; a fabricated `sorryAx` cone makes the cone
   checker exit 1. The fail-closed claims are therefore tested, not assumed.
7. **Four more packages compile-checked.** `LeeLib` (LeeRiemannian, 3685 jobs),
   `EvansLib` (3754), `HanLinLectureNotes` (8691) and `GilbargTrudinger` (8663)
   now build in the adapter workspace at the same pin, exit 0, 0 `sorry`
   warnings, via four new `require`s (backups of the previous lakefile and
   manifest are in `evidence/logs/lakefile-round4-backup.lean` and
   `…-manifest-round4-backup.json`). They are required but not imported, so the
   90-cone audit and the authored-file checks are unchanged; the adapter
   manifest now records 21 packages.
8. **Producer self-review** (`evidence/consumer-self-review.md`): a
   hypothesis/conclusion-equivalence table for all 26 consumers, explicitly
   labelled producer-side and non-independent, so the reviewer child has a
   precise target to falsify (round 5 adds a §7 addendum covering the four
   derived pointwise-form lemmas and the newly classified `DownstreamUse`
   consumers, under the precise taxonomy 27 consumers + 8 auxiliary items).

---

## 11. Round-5 changelog (new evidence and one correction)

1. **Correction: the round-3 snapshot-check exit code was a pipeline artifact.**
   `evidence/logs/round3-reverify.log` records `SNAPSHOT_EXIT=0` next to a
   report that *lists* `.lake` cache paths; the script
   (`evidence/verify_frenzymath_snapshot.py`) returns 1 whenever cache paths are
   present, so the recorded status came from the paged pipeline, not from
   python. The facts are: (a) the pristine-seed verification passed before any
   build and is preserved at `evidence/snapshot-verify.json` (2801 tracked
   files, `no_build_caches: true`); (b) after the in-place upstream builds the
   script correctly reports the expected `.lake` artifacts and exits 1; (c) the
   authoritative integrity check is `evidence/source-hashes.py`
   (`sources_untouched: true`, `source_tree_sha256` unchanged). Round 5 records
   the true status in `evidence/logs/round5-final-verify.log`
   (`SNAPSHOT_EXIT=1`) and never uses the pristine script as post-build
   evidence again.
2. **`sorry` ledger delivered** (`evidence/sorry-ledger.py`, `.json`, `.md`):
   274 real occurrences, 89 files, all `LeeSmooth`, all `statement-only`, all
   enclosing declarations resolved, exact per-package agreement with
   `evidence/upstream-inventory-v2.json`. `--check` is idempotent; `--quarantine`
   proves no authored adapter file mentions `LeeSmooth` (16 files scanned). This
   closes the deliverable of the imported child task `M2-LEESMOOTH-SORRY-LEDGER`
   at snapshot scope (the child asked for LeeSmooth at minimum).
3. **The integrator release builds here.** `release/` was seeded like the peer
   leaders (D6 sources + shared `.lake/packages` symlink), re-synced from the L1
   integrator worktree, and hash-verified byte-identical (462/462;
   `evidence/release-mirror-hashes.json`). `lake build` at
   `v4.34.0-rc2`/`7974e751` exits 0 (9339 jobs), 0 `sorry` warnings, release
   self-audits green (`evidence/logs/round5-release-build.log`). This satisfies
   the "build from release/ with the pinned toolchain" acceptance line **in
   isolation** — no other worktree was written to and no pin was flattened.
4. **Release forbidden-token classification.** The release mirror's 10
   `unsafe`/`axiom` hits are all explained by
   `evidence/classify-release-forbidden-hits.py`: 2 documented intentional
   negative-control axioms in D12 audit modules and 8 `.«unsafe»` match
   patterns inside declaration-safety audit tooling. There are **0** `sorry`,
   `admit`, `native_decide`, `proof_wanted`, or real `unsafe` declarations in
   the release source.
5. **Four derived pointwise `(0,4)`-form consumers** added in
   `adapters/UpstreamAdapters/PointwiseSymmetries.lean` (§6): first-pair skew
   for any connection; last-pair skew under metric compatibility alone;
   first Bianchi under symmetry alone; pair swap under symmetry+compatibility.
   They are explicitly labelled derived consumers, not new mathematics. Audit
   regenerated: **124 cones**, coverage 124 == 124 == 124, `SCRIPT_EXIT=0`;
   clean rebuild after `rm -rf adapters/.lake/build` exits 0 (3757 jobs,
   37.9 s).
   Classification regenerated: **108 entries** (71 proved / 15 definitions /
   14 model / 8 conditional), covering **all 35 non-alias authored
   declarations**, 0 missing from the static index; novelty check 0 public
   duplicates.
6. **Tooling hardening found by re-verification.**
   `evidence/check-authored-files.py` now reports the correct line for
   `axiom` hits (`^[ \t]*axiom` instead of `^\s*axiom`, which with `re.M`
   started the match at an earlier blank line) and accepts a `subdir`
   argument so the same contract scan can be applied to the release mirror.
7. **Consolidated chain.** `evidence/run-round5-checks.sh` runs steps 1–9 of
   §9's list and writes `evidence/logs/round5-final-verify.log`; the only
   non-zero exit in it is the documented pristine-import check of item 1.
   `exact_blockers_closed` remains empty: U1 and U3 are still open.
11. **Alias surface expanded by 30 names (59 → 89).** The round-5 additions cover
   the remaining inventoried entry points of U2/U3/U4/U6/U7/U9/M4 that were
   listed in the API map but not yet consumable under a stable adapter name:
   DoCarmo `ricciForm`, `scalarCurvature`, `sectionalCurvature`, `ricciForm_symm`,
   `IsGeodesic`, `HasGeodesicEquationAt`, `parallelTransportTangentEquiv`;
   MorganTian pointwise `ricciForm`, `scalarCurvature`,
   `ricci_curvature_comparison`, `hamilton_tensor_maximum_principle_of_parallel_frame`;
   Topping `divergence`, `divergence_apply`, `divergence_differentialOneForm`,
   `divergence_covTensorOfBilin_neg_two_ricci`,
   `divergence_gravitationTensor_ricciTensorField`,
   `metricLaplacianAt_eq_laplaceBeltramiChart_divergence`; KleinerLott
   `SmoothCompleteRicciFlowOn`, `RicciFlowData`; Hatcher
   `universalCover_simplyConnectedSpace`; Petersen `curvatureTensorTypes`,
   `curvatureTensor_zero_first`, `curvatureTensor_eq_ricci_identity`, `expMap`,
   `RicciCurvature`, `IsJacobiField`, `ConjugatePoint`,
   `myersRicciDiameterBound_of_ricciLowerBound`, `leviCivita`, `koszul`. Each is an `alias` (same type, same proof term), so
   no statement is weakened or strengthened; the audit regenerated to
   **124 cones** with coverage 124 == 124 == 124 and the clean rebuild is exit 0
   (3757 jobs, 37.9 s).
8. **Mutation tests for the new checkers**
   (`evidence/run-round5-mutation-tests.sh`,
   `evidence/logs/round5-mutation-tests.log`): a dropped ledger entry is
   detected by `sorry-ledger.py --check` (273 vs 274); a changed and a missing
   mirror file are detected by `verify-release-mirror.py`; an injected
   `sorry` in the release copy is reported `UNEXPLAINED` and makes
   `classify-release-forbidden-hits.py` exit 1; the unmutated inputs pass. The
   first run of this script silently used an unwritable `mktemp` directory, so
   the script now creates its temp dir inside the worktree and aborts loudly if
   it is not writable — the recorded run is the fixed one.
9. **Classification completeness and a provenance fix.** The curated table
   used to list only 22 of the 35 non-alias authored declarations (the
   `DownstreamUse` consumers and the small constructions were audited but not
   classified). They are all listed now, and two provenance-resolver bugs are
   fixed: declaration modifiers (`noncomputable def`) were not matched, and a
   short name occurring in two namespaces (the two `Plane` abbrevs) resolved to
   the first file in sorted order instead of the declaring module. All 35
   entries now resolve to the correct file:line, with 0 unresolved.
10. **Round-5 re-checks of round-3/4 claims.** The static inventory is still
   byte-deterministic (regenerated JSON sha256
   `f8af49eb0104773d94fc297852e026cbd1ae8143fcdc2d5afde659aab73c9565`, identical
   to the committed `evidence/upstream-inventory-v2.json`), and the four
   round-4 packages still build (`lake build GilbargTrudinger
   HanLinLectureNotes EvansLib LeeLib` exit 0, 9190 jobs, no-op). The verifier
   checklist with all round-5 expected numbers is `evidence/VERIFY-round5.md`.

**TASK_DONE**
