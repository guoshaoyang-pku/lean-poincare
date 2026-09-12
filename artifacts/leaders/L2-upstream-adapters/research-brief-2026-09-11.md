# L2-upstream-adapters research brief — 2026-09-11

**Task:** M2 upstream adapters (lane: scout). **Named blockers in scope:** M2, U1, U3.
**Worktree:** `longrun/worktrees/leaders/L2-upstream-adapters` (isolated; no other
worktree or the main tree is written to). **Pins:** upstream
`bb91a091f0b968f8bbe8d861e025a88d82b161be` on `leanprover/lean4:v4.32.1` +
mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`.

## 1. Question

The local release package (blockers U1-U12) records that its pinned mathlib
(`7974e751bece`, Lean `v4.34.0-rc2`) has no Riemann curvature tensor (U1), no
Ricci/scalar curvature (U2), no geodesics/exponential map/parallel transport
(U3), no heat/parabolic layer (U6), no volume form/IBP/Bochner (U7), no Ricci
flow (U8), no Perelman machinery (U9). The Frenzymath snapshot was imported
under `third_party/` for exactly these gaps but had never been rebuilt or
inventoried (D12: "reference only, not rebuilt"). M2 asks: which of these gaps
does the snapshot actually fill, with what compiled evidence, and under what
semantic class?

## 2. Findings (compiled unless marked static)

1. **Pin divergence is structural, not incidental.** Upstream is Lean 4.32.1 +
   mathlib `520045ab`; the local release is Lean 4.34.0-rc2 + mathlib
   `7974e751`. Upstream oleans therefore cannot be imported by `release/`
   without a pin decision. Reuse must go through an isolated adapter package
   (built here) or through re-statement/porting; flattening the pins is
   forbidden and would invalidate release evidence.
2. **The root `PoincareConjecture` project is an empty stub** (3 files, 37
   lines, 0 declarations). The snapshot does **not** contain a formalized
   Poincaré conjecture; it contains source-faithful book projects. Any claim of
   the form "upstream proves Poincaré" is an upstream source claim, not a
   kernel-checked theorem.
3. **Real developments present** (file/line counts, static): DoCarmo 293 files /
   103k lines, MorganTian 573 / 141k, Petersen 419 / 144k, Topping 184 / 45k,
   Hatcher 58 / 19k, LeeRiemannian 116 / 33k, Evans 65 / 22k, LeeSmooth 552 /
   135k, KleinerLott 11 / 2k, ChowKnopf 8, GilbargTrudinger 9, HanLin 37.
4. **Static `sorry` map (comments stripped).** LeeSmooth: 274 real `sorry`s.
   DoCarmo, MorganTian, Petersen, Topping, Hatcher, Evans, KleinerLott,
   ChowKnopf, LeeRiemannian, HanLin, GilbargTrudinger: none. Pass-1 counts of
   `axiom`/`admit`/`proof_wanted`/`unsafe` in those packages were docstring
   false positives except one tooling `unsafe def main` in a DoCarmo review app.
5. **API coverage of the local blockers** (names are `#check`ed in
   `adapters/UpstreamAdapters/Probes/`):
   - U1 curvature: `Riemannian.AffineConnection.curvature_zero_left/right`,
     `curvatureOperatorAt_add/smul_*`, `Riemannian.leviCivita_curvature_frame_expansion`,
     `PetersenLib.curvatureTensorTypes/_coordinates/_indexLowering`.
   - U2 Ricci/scalar: `MorganTianLib.ricciAt`, `scalarCurvatureAt`,
     `ricciForm`, `scalarCurvature`,
     `Riemannian.sectionalCurvature`, `ricciForm_self_eq_sum_sectionalCurvature`.
   - U3 geodesics/exp/parallel: `Riemannian.Geodesic.isGeodesic_iff_covDerivAlong_velocity_eq_zero`,
     `Riemannian.parallelTransportTangentEquiv`,
     `metricInner_parallelTransportTangentEquiv`, `PetersenLib.expMap`,
     `expMap_localDiffeomorphism`, `segment_isGeodesic`.
   - U4 Levi-Civita: `Riemannian.RiemannianMetric.leviCivita_chartContraction_eq`,
     `leviCivita_covDerivAlong_eq`, `AffineConnection.preservesMetricUnderParallelTransport_iff_isMetricCompatible`.
   - U6 parabolic/max principle: `MorganTianLib.hamilton_tensor_maximum_principle_compact/bounded`,
     `Topping.weak_maximum_principle(_of_pos)`.
   - U7/U10 divergence/Bochner: `MorganTianLib.laplacianAt_eq_chart_divergence`,
     `chartVolumeDensity_mul_laplacianAt_eq_divergence`,
     `function_bochner_formula`, `Topping.divergence*`.
   - U8 Ricci flow: `MorganTianLib.IsRicciFlowOn` (hypothesis structure),
     `Topping.riemannianVolume_antitoneOn_of_isRicciFlowOn`,
     `hasVolumeDerivativeOn_riemannianMeasure_of_isRicciFlowOn`.
   - U9 Perelman: `KleinerLott.IsKappaNoncollapsedOnScale`,
     `exists_point_selection_of_bounded_moving_curvature`,
     `SmoothCompleteRicciFlowOn`, `IsHamiltonIveyPinched`.
   - M4 topology: `HatcherLib.simplyConnected_iff_unique_path_class`,
     `IsUniversalCoveringMap.simplyConnectedSpace`,
     `UniversalCoverConstruction.universalCover_simplyConnectedSpace`,
     `attachingSpace_homotopyEquiv`, `homotopyEquivPiOneMulEquiv`.
6. **Semantic classes are not uniform.** Declarations named
   `..._of_isRicciFlowOn` are conditional on an explicit Ricci-flow hypothesis
   structure (flow existence is U8 and is *not* proved); `..._of_bochner` names
   signal a Bochner-formula hypothesis. These are `conditional`, not `proved`.
   Pointwise curvature/geodesic identities of DoCarmo/Petersen are `proved`
   (subject to the fail-closed axiom audit). LeeSmooth's 274 `sorry`s are
   `statement-only`. The empty root stub and the κ-noncollapsing predicates are
   interfaces/definitions, not theorems. Nothing here closes U1/U3: the
   inventory supplies *candidate inputs*, and closure requires constructed
   input + downstream consumer + independent rebuild + semantic review.

## 3. Method / artifacts

- `evidence/mathlib-cache/` — mathlib `520045ab` cache (8636 ltars, 435 MB),
  fetched with `MATHLIB_CACHE_DIR` (the default `~/.cache/mathlib` is outside
  the sandbox; `mathlib/Cache/IO.lean:56` documents the override).
- `adapters/` — isolated Lake package. Upstream projects are consumed **in
  place** via `require … from "../third_party/…"`. `evidence/make-adapter-manifest.py`
  builds the manifest offline from upstream manifests; `evidence/seed-adapter-packages.sh`
  seeds the transitive mathlib closure with `git clone --shared`.
- `evidence/inventory-upstream.py` (pass 1) and `evidence/inventory-v2.py`
  (pass 2, comment/string aware) + `evidence/qualified-names.py` (namespace
  tracking) produce `evidence/upstream-inventory-v2.json`,
  `evidence/upstream-api-inventory.md`, `evidence/upstream-qualified-names.json`.
- `adapters/UpstreamAdapters/{Probes,Adapters,DownstreamUse,Audit}.lean` — the
  authored files: compile-time probes, `alias` adapters (exact-type renames, no
  copied proofs), constructed-input downstream uses, and the generated
  `#print axioms` audit; `evidence/check-axioms.py` fails closed outside
  `{propext, Classical.choice, Quot.sound}`.

## 4. Result

All eight selected packages built (exit 0), the isolated `adapters/` package
built (exit 0), the fail-closed axiom audit passed (63 cones, all within
`{propext, Classical.choice, Quot.sound}`, 0 `sorryAx`), and 1111 upstream
self-audit cones are also within the allowed set. The full evidence, the
semantic-classification table and the blocker status are in
`longrun/results/L2-upstream-adapters.md` / `.json` (verdict `TASK_DONE`,
requesting independent acceptance). Named blockers **U1/U3 remain open**: the
inventory supplies compiled candidate inputs, not closures. Four child tasks
were emitted to `comms/outbox/` and imported by the dispatcher.

## 5. Round 3 update (same session, continuation from `checkpoint.json`)

**New mathematical work: constructed-input consumers for U1/U3.**

- `adapters/UpstreamAdapters/DownstreamGeometry.lean` (DoCarmo family):
  - *general, model-independent* U1 consumers that do not exist upstream:
    `curvatureOperatorAt_antisymm_left` (pointwise first-pair antisymmetry of
    the curvature operator of an arbitrary affine connection) and
    `curvatureOperatorAt_bianchi` (pointwise first Bianchi identity for any
    symmetric affine connection), and the alias-routed
    `curvatureOperatorAt_zero_first` / `curvatureOperatorAt_zero_third`.
    Upstream has only the field-level `curvature_antisymm_left` /
    `curvature_bianchi` / `curvature_zero_left` / `curvature_zero_right`; the
    pointwise forms are obtained through the audited bridge
    `curvatureOperatorAt_eq`, and the zero-slot ones consume the adapter
    aliases directly.
  - *model-level* consumers on the constructed Euclidean plane
    `EuclideanSpace ℝ (Fin 2)`: pointwise curvature operator and `(0,4)`
    curvature form vanish, the affine line is a geodesic, the moving-foot
    geodesic equation holds at every time, `exp_p(v) = γ(1)`,
    `exp_p(tv) = γ(t)`, `exp_{γ(s)}(tv) = γ(s+t)`, and parallel transport
    along the line preserves the Euclidean metric.
  - the adapter **alias layer** is consumed downstream:
    `euclidean_alias_curvature_zero_third` routes through
    `UpstreamAdapters.Adapters.DoCarmo.curvature_zero_right`.
- `adapters/UpstreamAdaptersPetersen/DownstreamUse.lean` (Petersen family,
  separate environment because of the duplicate `metric_simp` attribute):
  pointwise `curvatureTensorAt` vanishing for the flat metric (via upstream
  `euclideanSpace_curvature_eq_zero`), `expMap_zero`, `expMap_zero_smul`.

**Evidence refresh (round 3).** Fail-closed audit now covers **81 declaration
cones** (45 DoCarmo-family aliases + 23 main-library authored consumers +
10 Petersen aliases + 3 Petersen consumers), all within
`{propext, Classical.choice, Quot.sound}`, 0 `sorryAx`.  Authored-file check:
15 Lean files, 0 forbidden tokens.  Sources untouched
(`source_tree_sha256 9a2b660a…84af`).  Classification extended to **87 curated
entries** (54 proved / 11 definitions / 14 model / 8 conditional); the 18
adapter-authored entries carry runtime-resolved file:line provenance.

**Blocker status.** U1 and U3 now have *constructed input + downstream
consumer* at the upstream pin (2 of the 4 closure legs).  The independent
rebuild and the semantic review are delegated to two new child tasks.  **No
blocker is closed**; the release-pin consumer does not exist, and cross-pin
olean import is impossible.

**Read-only observation on the release lane.** The L1 worktree's `release/`
(Lean `v4.34.0-rc2`) now contains an authored `Poincare/D7/Curvature` layer and
`Poincare/D7/Geodesic` files (456 Lean files in total).  This task did not
build or modify that worktree; reconciling the release-side layer with the
upstream manifold-level adapter is the subject of the imported
`M2-PIN-BRIDGE-DECISION` child task.

**Child tasks (round 3).** `L2-child-u1u3-independent-rebuild` and
`L2-child-u1u3-semantic-review`, both schema-valid (id, group_id, parent_node,
deps, lane, acceptance, host_pool, requires_lean, max_hours, objective).  The
round-2 `comms/outbox/M2-child-tasks.index.json` was rejected by the dispatcher
as a non-task index file; the four round-2 task files themselves were imported
(renamed `.imported`).

## 6. Round 4 update (2026-09-11T16:41Z, continuation from `checkpoint.json`)

**Inventory correction (found by the new novelty scan).** Round 3 claimed that
"no upstream pointwise form exists" for the curvature symmetries.  That is true
for the *operator* `curvatureOperatorAt`, but **false for the metric-lowered
form**: `MorganTianLib.curvatureFormAt_antisymm_left` /
`_antisymm_right` / `_bianchi` (`MorganTianLib/Ch01/PointwiseCurvature.lean:314`,
`:322`, `:332`) already state the pointwise `(0,4)` symmetries, and
`MorganTianLib.isAlgCurvatureForm_curvatureFormAt` (`:364`) packages them for a
Levi-Civita connection.  Four general form-symmetry theorems were drafted in
this round, then **withdrawn** rather than presented as new.  Instead the
upstream surface is now exposed through the adapter:
`UpstreamAdapters.Adapters.MorganTian.{curvatureFormAt_antisymm_left,
curvatureFormAt_antisymm_right, curvatureFormAt_bianchi,
isAlgCurvatureForm_curvatureFormAt}`.  The genuinely new general consumers
remain the **operator-level** ones from round 3 (no metric needed, no upstream
pointwise statement).

**Audit hardening (fail closed on coverage, not only on cones).**

- `evidence/make-audit-file.py` now **discovers every declaration** in the
  authored sources (namespace/section aware; refuses anonymous instances and
  `private` declarations; supports dotted alias names such as
  `IsRicciFlowOn.metricInner_hasDerivAt`) and generates `Audit.lean` for all of
  them: 76 declarations in the main library, 14 in the Petersen library.
- `evidence/check-audit-coverage.py` asserts the three sets are equal — authored
  declarations, `#print axioms` lines, and records actually printed in the audit
  log — and that no duplicates or truncation occurred.  A declaration added
  without regenerating the audit, a stale audit line, or a partially written log
  is a hard failure.
- `evidence/run-axiom-audit.sh` runs the cone checker **and** the coverage
  checker and exits non-zero if any build step, audit run, cone check or
  coverage check fails.  Hardened result: **90 declaration cones**, all within
  `{propext, Classical.choice, Quot.sound}`, 0 `sorryAx`; coverage 90 == 90 ==
  90; `SCRIPT_EXIT=0`.
- `evidence/check-novelty.py` compares every non-alias authored declaration name
  against the upstream declaration index, fails on public duplicates, and
  requires an explicit recorded justification for private-name re-derivations.
  It passes with exactly one recorded case
  (`euclidean_curvatureFormAt_eq_zero`, the documented public re-derivation of
  the upstream `private` lemma at `EuclideanExample.lean:34`).

**Pin-gap analysis** (`evidence/pin-gap-u1u3.md`): the release pin
(`v4.34.0-rc2`, mathlib `7974e751`) has no curvature, geodesic, exponential or
parallel-transport declarations in mathlib; it has the manifold-level
*interface* `Probe.CurvatureTensor` (fields, no construction), the abstract
`D7/Curvature/RiemannCurvatureData` layer, and the model-space
`D7/Geodesic/GeodesicData` plus the unstatable
`GeodesicContext.accel_is_covariant_acceleration`.  Because oleans do not cross
pins, a release-pin U1/U3 consumer requires a port (re-proof), not an import.
This is decision input for `M2-PIN-BRIDGE-DECISION`; no blocker is closed.

**Evidence refresh (round 4).** Authored-file check PASSED (15 files, 0
forbidden tokens); source-hash check PASSED (`sources_untouched: true`,
`source_tree_sha256 9a2b660a…84af`, 37 authored files hashed); classification
regenerated to **91 curated entries** (58 proved / 11 definitions / 14 model /
8 conditional), 0 missing from the static index.  After `rm -rf
adapters/.lake/build` the authored layer rebuilt and the hardened audit passed
again (`evidence/logs/round4-clean-rebuild.log`).

**Blocker status (round 4).** `exact_blockers_closed = []`: M2 remains
delivered-pending-acceptance; U1 and U3 still have only the constructed-input +
downstream-consumer legs at the upstream pin, with the independent rebuild and
semantic review queued and no release-pin consumer.  The count-drift note in the
result card now reads 90 audited cones / 26 consumers.
