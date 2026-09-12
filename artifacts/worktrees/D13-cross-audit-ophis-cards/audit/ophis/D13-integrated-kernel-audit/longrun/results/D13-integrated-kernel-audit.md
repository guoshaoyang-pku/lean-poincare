# D13-integrated-kernel-audit — result card

- **Task id:** `D13-integrated-kernel-audit`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-integrated-kernel-audit`
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (`release/lean-toolchain`, unchanged)
- **mathlib:** `leanprover-community/mathlib4` @ `7974e751bece493b6ff508039423ca9fa2452fa8`
  (`release/lake-manifest.json`, Apache-2.0, unmodified, shared prebuilt packages)
- **Generated (local):** 2026-09-11 18:10 (+08:00) · actual elapsed this invocation: **0.73 h** (single invocation, cap 4 h)
- **Verdict:** `TASK_DONE` — the independent integrated rebuild, collision check, per-declaration
  kernel audit, negative-control rejection, statement-shape scan and blocker-closure verification
  all hold, with the findings in §6. **No Perelman/Poincaré claim is made.**

---

## 0. What this task claims and does not claim

**Claims (all machine-checked in this worktree):**

1. An **integrated snapshot** was rebuilt from sources: the pre-existing `release/` package
   (286 files, byte-identical after integration), the six D11 preliminary packages (37 Lean files
   from the D11 sibling worktrees), the 13 verified + 1 blocked D12 terminal releases (116 Lean
   files + 2 non-Lean delivered assets), and a **relay-gap recovery** of the 10-file `VKPort`
   van Kampen port that the D12-surgery-recognition result card references but the terminal relay
   omitted. 176 files added, **0 pre-existing files changed**, all copies byte-verified against
   their sources (`audit-evidence/snapshot-provenance.json`, sha256 per file).
2. **Collision check:** all **161 clean modules** (151 D11/D12 + 10 VKPort) elaborate together in
   one Lean environment (`Poincare.D13.IntegratedAudit.SnapshotRoot`); Lean rejects duplicate
   constant names on import, so a successful build is the collision check. Path-level collisions:
   0. The two intentional negative-control declarations collide with nothing (§3).
3. **Fresh build:** `release/.lake/build` was deleted and rebuilt from scratch;
   `cd release && lake build` → **exit 0**, `Build completed successfully (9339 jobs)`,
   ~1.5 min wall (192-core host), zero `error:` lines.
4. **Kernel audit of every new declaration:** 4343 declarations (3196 theorems; 757 of them from
   the recovered VKPort) attributed to `Poincare.D11.*`, `Poincare.D12.*`, `Poincare.VKPort.*`.
   Every axiom cone is contained in `{propext, Classical.choice, Quot.sound}`; **0** project
   axioms, **0** `unsafe`, **0** `sorryAx`, **0** `native_decide`, **0** `proof_wanted`, **0**
   `collectAxioms` failures. 4192 public declarations additionally covered by literal
   `#print axioms` output that agrees with the programmatic cones; the 151 module-private
   declarations are covered programmatically only (private names cannot be referenced from
   another module).
5. **Intentional negative controls rejected:** the two modules that declare `axiom … : False`
   (`Poincare.D12.TriangulationTopology.NegControl.NegControl`,
   `Poincare.D12.VolumeIBP.Audit`) are excluded from the clean root and are fed to the *same*
   detector by `audit-evidence/negcontrol/NegativeControlIncluded.lean`, which **fails** the build
   (exit 1) and names exactly those two axioms and nothing else.
6. **Statement-shape scan:** all 3196 theorems were scanned; **0** hypotheses syntactically equal
   to the conclusion, **0** definitionally equal, **0** conclusions occurring inside a hypothesis
   (`StatementAudit.lean`).
7. **Blocker-closure verification:** for every `exact_blockers_closed` record of the D12 cards,
   the constructors exist and the downstream pair was evaluated by a transitive proof-term
   dependency probe; retained-consumer counts were computed by a reverse-use probe over the whole
   snapshot. Verdicts and over-claims: §5, §6.
8. **Full-package pass:** the same fail-closed detector was run over the *entire* rebuilt package
   (base D1–D10 + `Longrun` + `Stage*` + drivers + the new layer), excluding only the two
   negative-control modules: **8161 declarations in 237 modules, 0 violations** (`FullAudit.lean`).
   The whole snapshot — not only the new declarations — is kernel-clean.

**Not claimed:** no theorem of Riemannian geometry, Ricci flow, surgery, extinction or sphere
recognition is proved here; no D12 "blocked" input is closed by D13; the two negative-control
modules are *not* repairs of anything; the `axiom … : False` declarations remain in the package
inside the library glob (reported, not edited). "Proof irrelevance/packaging" findings are process
findings, not mathematics.

---

## 1. Integrated snapshot

### 1.1 Construction

| source | files | origin tag | verification |
| --- | --- | --- | --- |
| pre-existing `release/` (D6–D10 package, drivers, base libs) | 286 files | — | hashed before integration; 286/286 unchanged after |
| D11 preliminary packages (6 worktrees: BochnerManifold, ComparisonModels, HeatKernelBridge, MaximumPrincipleTensor, ReducedVolume, SpectralTorus) | 37 Lean | `D11:<worktree>` | byte-identical copy, sha256 recorded |
| D12 terminal releases (14 tasks, 13 verified + 1 blocked) | 116 Lean + `MOISE_DAG.md` + `VolumeIBP/audit.py` | `D12:<task>` | byte-identical copy, sha256 recorded |
| `VKPort` van Kampen port (relay-gap recovery, §6.4) | 10 Lean + README | `D12:D12-surgery-recognition/relay-gap:VKPort` | byte-identical copy, sha256 recorded |
| D13 audit modules (authored here) | 10 Lean | `D13` | this task |

No pre-existing file was overwritten (`integrate_snapshot.py` refuses to overwrite;
`integrate_vkport.py` refuses differing bytes). No builder mathematics was edited. The snapshot's
`lakefile.toml`, `lean-toolchain`, `lake-manifest.json` are the pre-existing ones, unchanged.

### 1.2 Collision check (path + name)

- Path collisions across the 21 source sets: **0**.
- Cross-set conflicts (same path, different bytes): **0**.
- Constant-name collisions: impossible among clean modules because the generated merged root
  imports all 161 clean modules into one environment; the build of that root succeeded. The two
  negative-control modules are compared separately against the 4343 clean declaration names:
  **0 collisions** (`d12NegControlBadAxiom`, `d12NegControlBadTheorem`,
  `Poincare.D12.VolumeIBP.Audit.negativeControl` are unique).
- **83 declarations attributed to D11/D12 modules carry names outside those namespaces** (mostly
  `_private.*` helpers and on-demand generated equation lemmas, e.g.
  `Poincare.D10.HeatKernelEuclidean.gaussianKernel.eq_1` is generated while compiling
  `Poincare.D11.HeatKernelBridge.ZeroDimension`). Benign here, but rebuild-order dependent; listed
  in `kernel-audit.json` under `checks.C2_kernel_cones.cross_namespace_declarations`.

### 1.3 Fresh build directory

`.lake/build` was **removed** before the definitive replay. Command, cwd and exit code are in
`audit-evidence/logs/transcript.txt`; the build log is `audit-evidence/logs/10-full-build.log`.

---

## 2. Kernel audit

Module `release/Poincare/D13/IntegratedAudit/AuditCore.lean` (`runNewModuleAudit`, fail-closed) +
root `KernelAudit.lean`. It emits `D13DECL`/`D13TYPE`/`D13AUDIT` lines and raises an elaboration
error unless every check passes; an exception while collecting a declaration's axioms is itself a
failure (never a skip). Results (`audit-evidence/logs/11-kernel-audit.log`):

| metric | value |
| --- | --- |
| expected clean modules / missing | 161 / **0** |
| duplicate module names | **0** |
| declarations audited | **4343** (theorems 3196, defs 1033, induct/ctor/rec 99, partial defs 15) |
| project axioms / unsafe / sorry / native_decide / proof_wanted | **0 / 0 / 0 / 0 / 0** |
| unapproved axioms in any cone / collect failures | **0 / 0** |
| cones | `{propext, Classical.choice, Quot.sound}` 3799 · `{propext}` 356 · `{propext, Quot.sound}` 87 · `{Quot.sound}` 11 · `{}` 90 |

Per subpackage declaration counts: D12 TriangulationTopology 543, SurgeryRecognition 383,
ParabolicLocal 351, TensorMaximumBochner 335, ConnectionCurvature 270, EntropyVariation 213,
VolumeIBP 159, ComparisonGeodesics 148, KappaVariational 125, HeatSemigroup 119,
ReducedVolume 113 (D11), BochnerManifold 109 (D11), HeatDomain 83, SpectralTorus 185 (D11),
SpectralSobolev 68, GeometricCompactness 71, HeatKernelBridge 130 (D11), MaximumPrincipleTensor 79
(D11), ComparisonModels 72 (D11), SemanticLedger 30, VKPort 757.

**Literal `#print axioms`:** four generated probes print the cone of every public audited
declaration (`audit-evidence/probes/PrintAxiomsAll{0..3}.lean`, logs `18-print-axioms-*.log`):
**4192/4192 public declarations covered, 0 violations, 0 mismatches** with the programmatic cones.
The 151 `_private.*` declarations cannot be named from another module; they are covered by
`Lean.collectAxioms` in the programmatic pass (clean). The probes exit 1 because Lean exits nonzero
on linter warnings about auto-generated auxiliary declarations; the driver asserts the *only*
errors are the 151 expected `_private` parse errors (one per private probe line) and that no other
error occurs.

**Partial definitions (residual trust note):** 15 `partial def` recursion helpers exist
(12 in VKPort, 3 in D12: `iteratedSphereSum._unsafe_rec`, `restrictionChain._unsafe_rec`,
`segChain._unsafe_rec`). Their safety is `.partial` (not `.unsafe`), their cones are clean, and
Lean requires a partial definition's return type to be nonempty — verified by a failing test:
`partial def badF : Nat → False := fun n => badF n` is rejected
("could not prove that the type … is nonempty"). A partial definition therefore cannot manufacture
a proof of an empty type; the three D12 helpers define path/chain *data*, not proofs.

**Self-audit of the auditor:** `SelfAudit.lean` runs the same checks over `Poincare.D13.*`
(51 declarations, 8 expected modules): **PASS**, 0 axioms/unsafe/sorry/unapproved.

**Full-package pass:** `FullAudit.lean` runs the same fail-closed checks over **every**
declaration of the integrated package (base D1–D10, `Longrun`, `Stage*`, drivers, D13), excluding
only the two negative-control modules: **237 modules, 8161 declarations, 0 project axioms,
0 unsafe, 0 sorryAx, 0 native_decide, 0 unapproved axioms, 0 collect failures — PASS**. The whole
rebuilt snapshot, not only the new layer, is kernel-clean with respect to the approved cone.

---

## 3. Intentional negative controls

The snapshot contains two modules whose stated purpose is to test the detector:

| module | forbidden declaration | consumers |
| --- | --- | --- |
| `Poincare.D12.TriangulationTopology.NegControl.NegControl` | `axiom d12NegControlBadAxiom : False` (+ `d12NegControlBadTheorem`) | none (verified) |
| `Poincare.D12.VolumeIBP.Audit` | `axiom negativeControl : False` | none (verified) |

They are excluded from the clean merged root and audited by
`audit-evidence/negcontrol/NegativeControlIncluded.lean`, an *intentional negative-control root*
that imports both modules and runs the same detector. Expected and observed result
(`audit-evidence/logs/17-negcontrol-included.log`):

```
D13FAIL  project_axiom       Poincare.D12.VolumeIBP.Audit.negativeControl
D13FAIL  project_axiom       d12NegControlBadAxiom
D13FAIL  unapproved_axiom    d12NegControlBadTheorem   d12NegControlBadAxiom
D13VERDICT FAIL      (lean exit 1)
```

No declaration of the snapshot depends on either axiom (the 4343 clean cones and the two
modules' isolation were both checked). **Finding (P-D13-1):** both modules live under the
`Poincare.+` library glob, so the *built package* contains an inconsistent environment reachable
by importing those two leaf modules. This is a packaging defect; per the hard rules D13 did not
edit or move them.

---

## 4. Statement-level audit and non-vacuity

### 4.1 Automated shape scan (`StatementAudit.lean`)

3196 theorems decomposed with `forallTelescopeReducing`; every propositional hypothesis compared
to the conclusion:

| pattern | count |
| --- | --- |
| hypothesis syntactically equal to the conclusion (`(h : P) → P`) | **0** |
| hypothesis definitionally equal to the conclusion | **0** |
| conclusion occurring as a subterm of a hypothesis | **0** |

This is the machine check behind "no hypotheses equivalent to the conclusion" and
"no fake propositions" at the level of statement shape. It does not certify that each statement
says what its name/docstring suggests; §4.2 samples that.

The scan cannot see the *indirect* form in which a hypothesis is a **record one of whose fields is
the conclusion** (e.g. a `SphericalPieceRecognition.recognize` field asserting sphere recognition
for a piece, fed into `stage6Target_of_certificates`). Such patterns are not treated as closures
anywhere in this audit: they are why the corresponding declarations are classified `conditional`
in §4.2 and why their record fields appear in the remaining-blocker ledger (§8). A `H → C` proof
with `C` packaged inside `H` establishes nothing about `C`.

### 4.2 Expanded hypotheses of the load-bearing statements

`expanded-hypotheses.json` carries 15 declarations with their **full types** (verbatim from the
fresh inventory) and an explicit hypothesis expansion/classification. Highlights:

- `Poincare.D12.HeatDomain.not_fullInitialCondition_flat_of_pos :
  ∀ n, 0 < n → ¬ (flatHeatKernelCore n).FullInitialCondition` — a genuine refutation of the
  unchanged legacy field in every positive dimension. D13 independently re-elaborates it at
  `n = 1` (`Nonvacuity.d13_consumer_notFullInitialCondition_one`).
- `Poincare.D12.SemanticLedger.not_initialCondition_gaussian` — a closed negation against the real
  D7 `D7InitialConditionAt` with the Gaussian kernel; D13 consumes it.
- `Poincare.D12.ConnectionCurvature.milnorConnection_isLeviCivita :
  ∀ (m : MetricData V ι) (b : LieBracketData ℝ V), IsLeviCivita m b (milnorConnection m b)` —
  the Koszul/Milnor construction for arbitrary metric data and any skew + Jacobi bracket. This is
  an abstract left-invariant model, **not** the manifold-chart Levi-Civita theorem.
- `Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere (n) (h : Sphere n ≃ₜ Sphere n) :
  DiskGlueQuot n h ≃ₜ Sphere (n+1)` — general topology, arbitrary gluing homeomorphism.
- `Poincare.D12.SpectralSobolev.poincare_wirtinger` — Poincaré–Wirtinger with the optimal
  constant `((b-a)/2π)²` on the interval/1-torus model.
- `Poincare.D12.ParabolicLocal.existsUnique_heatMildSolution` — Banach fixed point for the Duhamel
  map of a semilinear heat equation on BUC (condition `L*T < 1`), not quasilinear Ricci–DeTurck.
- `Poincare.D12.ComparisonGeodesics.bishopGromovVolumeRatio` — density-function Riccati comparison;
  becomes geometric Bishop–Gromov only when `A` is identified with geodesic-sphere volume, which is
  **not** constructed.
- `Poincare.D12.SurgeryRecognition.stage6Target_of_v3hypotheses` — a conditional implication whose
  geometric antecedents (extinction certificate, canonical neighbourhoods, V3 recognition
  hypotheses) are explicit unproved inputs; **not** a sphere-recognition theorem.

### 4.3 Zero-operator scan

A source-level scan of the new modules for definitions of geometrically named operators whose body
is literally `0` found exactly two hits, both legitimate and documented: the entropy datums in
`Poincare.D12.EntropyVariation.FFlowModel` and `GaussianShrinker` set the scalar-curvature field
`R := 0` of a **flat** Gaussian-shrinker model, with `|Ric + ∇²f|²` supplied by the explicit
nonzero formula `fflowRiccHess`. No Laplacian, Ricci, connection, volume, entropy or heat operator
in the snapshot is a zero placeholder.

### 4.4 Non-vacuity witnesses

`NonvacuityProbe.lean` supplies **independent, named, kernel-checked consumers** for the four
constructors that had no retained consumer in the snapshot (§6.3), plus concrete instances:
`d13_consumer_tetrahedron_homeo_ball` (Δ³ ≅ D³), `d13_consumer_flat_ccClass` /
`d13_consumer_flat_integrableClass` (the repaired interface is inhabited in every dimension),
`d13_consumer_notFullInitialCondition_one`, `d13_consumer_defect_gaussian`,
`d13_consumer_sphereOfTwoDisks_instance`. All compile with exit 0 and are audited clean.

---

## 5. Blocker-closure verification

Two machine probes back the acceptance rule "no claimed closure without a constructor plus a
downstream checked use":

* `UsageProbe.lean` builds the reverse direct-use graph over all snapshot-declared constants and
  reports transitive consumers of each named constructor (proof terms unsealed with `value? true`).
* `DependencyProbe.lean` walks the transitive proof-term closure of each claimed downstream and
  reports whether the constructor occurs in the **type** and in the **proof**.

| D12 task | claimed closure | constructor(s) | retained consumers | D13 verdict |
| --- | --- | --- | --- | --- |
| connection-curvature | Levi-Civita existence | `milnorConnection`, `leviCivitaExists` | 11 / 0 | **verified with caveat** — the witness is consumed; the existential corollary had no consumer (D13 supplies one) |
| entropy-variation | `B-D7-F-DERIVATIVE` | `hasDerivAt_F_of_pointwise`, `fflow_F_hasDerivAt`, `fDerivativeStatement_…` | 8 / 5 / 0 | **verified with caveat** — chain retained through `derivative_sign_distinction`; the literal-D7 bridge had no consumer (D13 supplies one) |
| heat-domain-repair | D11 domain defect | counterexample + interface inhabitant | 6 / 4 / 1 | **verified** — counterexample consumed by the refutation and by the upgraded datum |
| heat-semigroup | operator semigroup law | `heatOperator_comp_heatOperator(_of_bounded)`, `heatOperatorBCF_comp` | 7 / 3 / 1 | **partially over-claimed** (§6.2) |
| kappa-variational | RLV-10 / NCF-12 / RLV-1 (Gaussian model) | 3 constructors | 11 / 5 / 5 | **verified at model level** — consumed via `kappaVariationalClosures`, `rlv10Closure`, `ncf12ModelClosure` |
| parabolic-local | Gaussian smap, semigroup law, BUC strong continuity, derivative-loss barrier | 4 constructors | 19 / 23 / 21 / 1 | **verified** — all reach `existsUnique_heatMildSolution` / `derivativeLossBarrier_discharged` |
| surgery-recognition | SR-5, covering recognition, coveringTrivial | `mkV2`, `finiteFreeOrbit_…`, `deckTrivial_…` | 3 / 17 / 4 | **verified** — consumed by `stage6Target_of_v2/v3hypotheses` (which remains conditional) |
| triangulation-topology | DAG nodes 4/5/7/8/9/10/13 | 6 constructors | 8 / 0 / 13 / 5 / 0 / 1 | **verified with caveat** — two constructors had no retained consumer (D13 supplies both) |
| tensor-maximum-bochner | C1/C2/C3 partial (task blocked) | 3 matrix theorems | 1 / 1 / 3 | **partial only** — the task's own blocker B1 remains open |

`exact_blockers_closed` records with explicit pair evidence are in
`longrun/results/D13-integrated-kernel-audit.json`.

---

## 6. Findings

### 6.1 The D12-semantic-ledger "absent D11 HeatKernelBridge" finding is superseded
That report audited a snapshot in which the D11 bridge did not exist. In the integrated snapshot
the six D11 packages are present; `Poincare.D12.HeatDomain.FlatInstance` imports
`Poincare.D11.HeatKernelBridge.InitialCondition` and the whole set compiles in one environment.
The D7 field defect itself is confirmed unchanged and refuted in every positive dimension.

### 6.2 Over-claim: D12-heat-semigroup-analysis downstream use
The card states that `heatOperator_gaussianKernel_L1_tendsto_seq` uses `heatOperatorBCF_comp`.
The reverse-use probe and the pair probe agree that the only transitive consumer of
`heatOperatorBCF_comp` is `heatOperatorBCF_comp_swap`; the L1 theorem does not reference it.
The semigroup law closure itself is genuine (7/3 consumers). Reported as a card correction.

### 6.3 Constructors with no retained downstream consumer
`leviCivitaExists`, `fDerivativeStatement_of_corrected_of_idempotent`,
`antipodalQuotientCovering` (TriangulationTopology) and `simplexHomeoDisk` have 0 transitive
consumers **in the olean environment**: their uses are anonymous `example` commands, which Lean
checks during elaboration but does not store. This does not invalidate the constructions (the
examples were checked when their files compiled), but it means the relayed snapshot contains no
reusable consumer; D13 supplies four in `NonvacuityProbe.lean`.
`derivativeLossBarrier_discharged` is a terminal discharged statement with no consumer, which is
expected — its *constructor* `derivativeLossBarrier_holds` is consumed by it.

### 6.4 Relay gap: the VKPort van Kampen cluster
`D12-surgery-recognition`'s card reports the frenzymath Hatcher Ch1 van Kampen cluster "PORTED and
COMPILING in this worktree (`release/Poincare/VKPort`, 9 files, sorry-free, axioms clean)" and
lists the remaining SR-4 work relative to it. The terminal input snapshot relayed to D13 contains
only `Poincare/D12/SurgeryRecognition`. The 10 Lean files were recovered byte-identically from the
sibling worktree, copied with a distinct provenance tag, compiled against the pinned toolchain
(exit 0) and audited (757 declarations, all cones clean). Their README calls them
"EXPERIMENTAL, not part of the D12 audit deliverable"; they are therefore reported as a
**flagged relay-gap recovery**, not as terminal-release content. The D12-triangulation card also
describes van Kampen as a future port candidate — the two cards are inconsistent about its state.

### 6.5 Card name mismatch
The closure name `sturm_comparison` used in the comparison-geodesics material does not resolve to
any declaration; the actual comparison theorems are e.g.
`Poincare.D12.ComparisonGeodesics.areaRatio_antitone_of_logDeriv_le`,
`bishopGromov_volume_le`, `RiccatiLeOn`, `RiccatiEqOn`.

### 6.6 Packaging: negative controls inside the library glob (P-D13-1)
See §3. The package builds, but a consumer importing `Poincare.D12.VolumeIBP.Audit` or
`Poincare.D12.TriangulationTopology.NegControl.NegControl` obtains `False`.

---

## 7. Trust separation

| layer | status | evidence |
| --- | --- | --- |
| **kernel trust** | verified for all 4343 new declarations **and** for the full package (8161 declarations): only `propext`, `Classical.choice`, `Quot.sound`; no project axioms; negative controls rejected; auditor's own 51 declarations clean | `kernel-audit.json`, `11-kernel-audit.log`, `18-print-axioms-*.log`, `17-negcontrol-included.log`, `16-self-audit.log` |
| **compilation** | verified: fresh build directory, `lake build` exit 0 (9339 jobs), all audited files re-elaborated with recorded cwd/exit codes | `transcript.txt`, `10-full-build.log` |
| **statement correctness** | *partially* verified: automated hypothesis/conclusion scan over all 3196 theorems (0 flags); 15 load-bearing statements expanded and manually classified; non-vacuity witnesses for the repaired interface and the negative results | `12-statement-audit.log`, `expanded-hypotheses.json`, `NonvacuityProbe.lean` |
| **closure of a named blocker** | *evidence-based per claim*: 4 closures verified, 3 verified with caveat, 1 partially over-claimed, 1 partial-only (blocked task); **no D12 blocked input is closed by D13**, and no new axiom/assumption is introduced anywhere | §5, `blocker-verdicts.json` |

No layer claims more than its evidence. In particular, "kernel-clean" is not "mathematically
correct", and "constructor + consumer" is not "the general theorem".

---

## 8. Remaining blockers

* **Per D12 card** (23 entries in the D12-semantic-ledger recount, plus the task-specific lists):
  quasilinear Ricci–DeTurck short-time existence; manifold heat-kernel existence/parametrix;
  general L1 strong continuity (C_c density); Bochner identity on manifolds and weighted IBP with
  domination; reduced-length/reduced-volume general theory (KV-1…KV-13); Cheeger–Gromov
  compactness; harmonic coordinates; ancient-κ solutions; canonical neighbourhoods; extinction;
  surgery; Moise triangulation and PL→smooth; van Kampen wiring into `mkV2`; space-form
  recognition; manifold-level Levi-Civita/Riemannian framework; Bishop–Gromov geometric
  identification; tensor maximum principle PSD-cone invariance (B1: exact missing statement
  recorded by the blocked D12-tensor-maximum-bochner card).
* **Introduced/confirmed by D13**: the 7 entries in
  `remaining_blockers.introduced_or_confirmed_by_d13` (negative-control packaging; the
  heat-semigroup over-claim; four zero-consumer constructors; the VKPort relay gap; the
  `sturm_comparison` name mismatch; 83 cross-namespace generated declarations; the superseded
  "D11 absent" finding).

No blocker is reported closed by D13. The list is a ledger, not an estimate.

---

## 9. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd <worktree>/release
rm -rf .lake/build && lake build                       # exit 0, fresh build dir
lake env lean Poincare/D13/IntegratedAudit/KernelAudit.lean      # exit 0, D13VERDICT PASS
lake env lean Poincare/D13/IntegratedAudit/StatementAudit.lean   # exit 0, 0 suspects
lake env lean Poincare/D13/IntegratedAudit/UsageProbe.lean       # exit 0, D13USE lines
lake env lean Poincare/D13/IntegratedAudit/DependencyProbe.lean  # exit 0, D13DEP lines
lake env lean Poincare/D13/IntegratedAudit/NonvacuityProbe.lean  # exit 0, consumers
lake build Poincare.D13.IntegratedAudit.SelfAudit                # exit 0, D13SELFVERDICT PASS
lake env lean Poincare/D13/IntegratedAudit/FullAudit.lean        # exit 0, D13FULLVERDICT PASS (8161 decls)
lake env lean ../audit-evidence/negcontrol/NegativeControlIncluded.lean  # EXIT 1 (expected)
for i in 0 1 2 3; do lake env lean ../audit-evidence/probes/PrintAxiomsAll$i.lean; done
cd ..
python3 audit-evidence/tools/d13_audit_final.py        # all checks PASS
python3 audit-evidence/tools/assemble_result_json.py
```

`audit-evidence/tools/final_audit_replay.sh` runs exactly this sequence and writes
`audit-evidence/logs/transcript.txt` (command, cwd, exit code for each step).

**Source hashes.** `audit-evidence/final-release-hashes.txt`
(sha256 of all 462 files under `release/`, excluding `.lake`; manifest sha256 in the result JSON),
`audit-evidence/base-release-hashes-preintegration.txt` (286 pre-existing files; 0 changed),
`audit-evidence/snapshot-provenance.json` (per-file sha256 + origin for the 165 imported assets).

**Third-party reuse.** Only the VKPort recovery: frenzymath `Poincare-Conjecture`
(<https://github.com/frenzymath/Poincare-Conjecture>) at
`bb91a091f0b968f8bbe8d861e025a88d82b161be`, Apache-2.0, byte-identical copy, no modifications by
D13; the originating worktree documents its own port modifications in
`release/Poincare/VKPort/README.md`.

---

## 10. Dependency requests

1. D12 owners: move the two negative-control modules out of the `Poincare.+` library glob so the
   built package contains no `False` axiom.
2. D12 owners: correct the `D12-heat-semigroup-analysis` downstream-use record for
   `heatOperatorBCF_comp`.
3. D12/D14 cards: machine-readable closure records must carry fully qualified
   `(constructor, downstream)` names; the arrows in the prose could not be checked automatically
   and two of them do not hold.
4. Relay owners: include `release/Poincare/VKPort` in the D12-surgery-recognition terminal release
   (or state explicitly that it is excluded), and reconcile the triangulation card's
   "port candidate" statement with the surgery card's "ported and compiling" statement.
5. D14/successors: supply the manifold-level Riemannian/PDE framework named in §8 to convert the
   D12 model/ODE/conditional results into geometric theorems.

---

## 11. Artifacts

| artifact | path |
| --- | --- |
| machine-readable result | `longrun/results/D13-integrated-kernel-audit.json` |
| this card | `longrun/results/D13-integrated-kernel-audit.md` |
| consolidated audit evidence | `audit-evidence/kernel-audit.json` |
| declaration/type inventory + cones | `audit-evidence/logs/11-kernel-audit.log` |
| literal `#print axioms` | `audit-evidence/logs/18-print-axioms-*.log` |
| negative-control rejection | `audit-evidence/logs/17-negcontrol-included.log` |
| downstream-use + pair probes | `audit-evidence/logs/13-usage-probe.log`, `14-dependency-probe.log` |
| statement scan | `audit-evidence/logs/12-statement-audit.log` |
| self-audit | `audit-evidence/logs/16-self-audit.log` |
| full-package pass (8161 declarations) | `audit-evidence/logs/16b-full-audit.log` |
| command/cwd/exit transcript | `audit-evidence/logs/transcript.txt` |
| source hashes & provenance | `audit-evidence/final-release-hashes.txt`, `snapshot-provenance.json` |
| authored Lean modules | `release/Poincare/D13/IntegratedAudit/*.lean` |
| checkpoint | `checkpoint.json` |

TASK_DONE
