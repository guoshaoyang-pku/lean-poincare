# D7-sphere-recognition — end-game logical assembly

- **Task:** `D7-sphere-recognition`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-sphere-recognition`
- **Verdict:** `TASK_DONE`
- **Lean:** `4.34.0-rc2` (`leanprover/lean4:v4.34.0-rc2`)
- **mathlib:** `7974e751bece493b6ff508039423ca9fa2452fa8`
- **New Lean sources:** `release/Poincare/D7/Recognition/` (6 files, 1098 lines, 62 audited declarations)
- **Verification transcript:** `longrun/d7sr-logs/`

## 1. Summary

The task is the end-game logical assembly of the Poincaré programme.  The deliverable has four
layers, all built over the accepted D7 canonical-neighborhood interface
(`Poincare.D7.Canonical`, `CanonicalNeighborhoodCertificate`), the D3/D6 surgery and extinction
interface (`Poincare.Longrun.Surgery.ExtinctionTheorem`, `NeckAnalysis`, `ChainCertificate`) and
the shared Stage6 statement-only targets (`Poincare.Stage6.TopologyBridge`,
`Poincare.Stage6.SphereSimplyConnected`).

1. **Certificate vocabulary.**
   - `IsSurgeryAdmissible C` is the neck/cap dichotomy of a canonical-neighborhood certificate;
     `isSurgeryAdmissible_or_compactSpherical` is the checked classification
     (neck ∨ cap ∨ compact-spherical), and `not_isSurgeryAdmissible_of_compactSpherical`
     excludes the terminal alternative from the surgery step.
   - `SphericalPiece X` is a terminal piece carrying the compact-spherical alternative of a
     canonical-neighborhood certificate at a positive scale, together with a homeomorphism from
     the piece to the certified region.  `SphericalPiece.ofCertificate` is the checked
     constructor used by the assembly.
   - `ConnectedSumDecomposition X pieces` records that `X` is the connected sum of the terminal
     pieces, with two explicit named missing inputs: `simplyConnected_pieces` (van Kampen) and
     `sphere_of_spheres` (a connected sum of `𝕊³` summands is `𝕊³`).
   - `ExtinctionCertificate X` is the certificate supplied by the surgery / neck-extinction
     analysis: positive extinction time, the D3/D6 `ExtinctionTheorem` interface, strict
     complexity decrease, the nonempty terminal piece list and its connected-sum decomposition.
   - `ExtinctionConclusion X` is the interface-level conclusion (finite time, finitely many
     surgeries, extinction, terminal pieces, decomposition); `ExtinctionWithSphericalPieces X`
     bundles it with a `SphericalPiece` datum for every terminal piece.
   - `CanonicalNeighborhoodInput X E` records the flow's high-curvature regions and their
     certificates at one admissible scale, the checked classification of every certificate, and
     the fact that every terminal piece of `E` is homeomorphic to a compact-spherical certified
     region.
   - `SphericalPieceRecognition` is the named recognition bridge: a simply connected spherical
     piece is homeomorphic to `𝕊³`.
2. **Kernel-checked assembly.**
   - `ExtinctionCertificate.toConclusion` derives the interface-level conclusion, using the
     checked D3/D6 theorems `ExtinctionTheorem.finitelyMany_of_complexity` and
     `ExtinctionTheorem.extincts_of_complexity` for the finite-surgery and extinction fields.
   - `CanonicalNeighborhoodInput.only_spherical` turns the canonical-neighborhood classification
     of the terminal regions into `SphericalPiece` data.
   - The chain `RecognitionHypotheses.conclusion` → `onlySphericalPieces` →
     `pieces_simplyConnected` (van Kampen) → `pieces_homeomorph_sphere` (recognition) →
     `homeomorph_sphere` (connected sum) → `stage6Target` is proved in `Assembly.lean`.
   - `stage6Target_of_certificates` is the explicit conditional theorem: for a closed
     `ℝ³`-charted three-manifold `X`, simple connectivity plus an extinction certificate plus
     the canonical-neighborhood input plus the recognition bridge imply the shared Stage6
     statement-only target `Poincare.Stage6.poincareConjectureTopologicalThree X`.
     `extinctionWithSphericalPieces_of_certificates` is the same theorem for the bundled
     interface-level conclusion.
   - The D3/D6 surgery interface is re-exported (`surgeryCertificate_of_neckAnalysis`,
     `simplyConnected_preserved_of_chainCertificate`, `extincts_and_target_of_missingInputs`).
3. **Statement-only final homeomorphism construction.**  `missingFinalHomeomorphismConstruction`
   is the uniform statement that every simply connected closed `ℝ³`-charted three-manifold is
   homeomorphic to `𝕊³`; `missingMoiseSmoothingBridge` is the Moise/smoothing bridge from the
   topological to the smooth Stage6 target; `missingGeometrizationOutput Geometric` is the
   geometrization output parameterized by a geometric predicate.  The checked bridges
   `missingFinalHomeomorphismConstruction_iff_missingPoincareConjectureTopologicalThree`,
   `stage6Target_of_missingFinalHomeomorphismConstruction`,
   `smoothTarget_of_topologicalTarget_and_moise`,
   `sphericalPieces_of_geometrization` and
   `finalHomeomorphismConstruction_of_certificateFamily` connect them to the existing D3/Stage6
   statement-only targets and to the assembly.
4. **Named missing-input ledger.**  `finalHomeomorphismDependencies` names six inputs (SR-1
   Moise bridge, SR-2 geometrization output, SR-3 spherical space form theorem, SR-4 van Kampen
   for connected sums, SR-5 connected sum of spheres, SR-6 Ricci flow with surgery and
   extinction); `finalHomeomorphismBlockers` names four blockers.

No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs in any authored file
(comment/string-aware scan: 6 files, hard 0, soft 0).  All 62 audited declarations have standard
axiom cones (`{}` × 7, `{propext}` × 2, `{propext, Quot.sound}` × 2,
`{propext, Classical.choice, Quot.sound}` × 51); nonstandard 0.

## 2. Scaffold

The documented scaffold command `cp -al ../D7-surgery-neck-extinction/. .` was attempted at
worktree creation.  At that moment `../D7-surgery-neck-extinction` existed but contained only the
directory skeleton with **0 files**: its own `cp -al` had failed with
`EXDEV Invalid cross-device link` (cross-worktree hard links are rejected on this filesystem),
leaving empty directories, and the sibling task was still running.  The documented fallback
`../D6_weekly_release` contains the D6 base but not the D7 dependency layers that this task
imports, while the queue dependency of `D7-sphere-recognition` is `D7-canonical-neighborhood`
(the accepted aggregation of the D6 base plus the seven D7 dependency layers).

Effective scaffold: `../D7-canonical-neighborhood`, copied with `rsync -a` excluding `.lake`
(hard links are impossible across worktrees: `EXDEV`).  The Lake environment was reconstructed
from the same stable worktree: `release/.lake/build` and `release/.lake/config` copied,
`release/.lake/packages` symlinked read-only, and the root `.lake -> release/.lake` symlink
re-created.  The Lake package root is `release/`; new sources live in
`release/Poincare/D7/Recognition/`, and the gate command
`lake env lean release/Poincare/D7/Recognition/<File>.lean` resolves the imports.

Source-integrity check against `../D7-canonical-neighborhood` (excluding `.lake`, `longrun/` and
the new directory): **245 files checked, 0 changed, 0 removed, 0 added outside the new
directory** (`longrun/d7sr-logs/source-integrity.json`).

The concurrently running sibling task `D7-surgery-neck-extinction` authored
`release/Poincare/D7/SurgeryFlow/` (observed at the time of writing: `Basic`, `Extinction`,
`Statements`, `Times`, …).  It is **not** imported here: this worktree may add files only under
`Poincare/D7/Recognition/`, and the sibling was still running.  The extinction interface of this
task is therefore self-contained; an adapter from `SurgeryFlow.ExtinctionData` to
`Recognition.ExtinctionCertificate` is future work (see §7).

## 3. New files

| file | lines | decls | role |
|---|---:|---:|---|
| `Basic.lean` | 381 | 23 | surgery-admissible classification, `SphericalPiece`, `ConnectedSumDecomposition`, `ExtinctionCertificate`/`ExtinctionConclusion`/`ExtinctionWithSphericalPieces`, `CanonicalNeighborhoodInput`, `SphericalPieceRecognition` |
| `Assembly.lean` | 231 | 17 | `RecognitionHypotheses`, the checked chain conclusion → only-spherical → simply-connected pieces → `𝕊³` pieces → `X ≃ₜ 𝕊³` → Stage6 target, the explicit conditional theorem, D3/D6 re-exports |
| `Homeomorphism.lean` | 279 | 20 | statement-only `missingMoiseSmoothingBridge`, `missingGeometrizationOutput`, `missingFinalHomeomorphismConstruction`, checked bridges to the D3/Stage6 targets, six-entry dependency ledger and four blockers |
| `All.lean` | 18 | 0 | umbrella module |
| `Probe.lean` | 92 | 0 | 62 `#check` API probes |
| `Audit.lean` | 97 | 0 | 62 `#print axioms` commands (generated from the probe list) |

## 4. Main declarations

### 4.1 The surgery-admissible alternatives (`Basic.lean`)

```lean
def IsSurgeryAdmissible {ε κ r : ℝ} {X : PointedMetricSpace.{u}}
    (C : CanonicalNeighborhoodCertificate ε κ r X) : Prop :=
  C.kind = CanonicalKind.neck ∨ C.kind = CanonicalKind.cap

theorem isSurgeryAdmissible_or_compactSpherical (C : CanonicalNeighborhoodCertificate ε κ r X) :
    IsSurgeryAdmissible C ∨ C.kind = CanonicalKind.compactSpherical

theorem not_isSurgeryAdmissible_of_compactSpherical
    (h : C.kind = CanonicalKind.compactSpherical) : ¬ IsSurgeryAdmissible C
```

### 4.2 Spherical terminal pieces (`Basic.lean`)

```lean
structure SphericalPiece (X : TopSpace.{0}) : Type 1 where
  ε κ r : ℝ
  region : PointedMetricSpace.{0}
  certificate : CanonicalNeighborhoodCertificate ε κ r region
  kind_eq : certificate.kind = CanonicalKind.compactSpherical
  homeo : Nonempty (X.Carrier ≃ₜ region)

def IsSphericalPiece (X : TopSpace.{0}) : Prop := Nonempty (SphericalPiece X)
```

Checked API: `SphericalPiece.scale_pos`, `SphericalPiece.certificate_kind`,
`SphericalPiece.homeomorphic`, `SphericalPiece.ofCertificate`.

### 4.3 The connected-sum decomposition and its missing bridges (`Basic.lean`)

```lean
structure ConnectedSumDecomposition (X : TopSpace.{0}) (pieces : List (TopSpace.{0})) : Type 1 where
  relation : Prop
  relation_holds : relation
  simplyConnected_pieces : SimplyConnectedSpace X.Carrier →
    ∀ P ∈ pieces, SimplyConnectedSpace P.Carrier            -- van Kampen (missing)
  sphere_of_spheres : (∀ P ∈ pieces, Nonempty (P.Carrier ≃ₜ SphereThree)) →
    Nonempty (X.Carrier ≃ₜ SphereThree)                     -- connected sum of S³ (missing)
```

### 4.4 Extinction certificates and the interface-level conclusion (`Basic.lean`)

```lean
structure ExtinctionCertificate (X : TopSpace.{0}) : Type 1 where
  extinctionTime : ℝ
  extinctionTime_pos : 0 < extinctionTime
  extinction : ExtinctionTheorem extinctionLedger
  complexityDecreases : extinction.complexityDecreases
  pieces : List (TopSpace.{0})
  pieces_ne_nil : pieces ≠ []
  decomposition : ConnectedSumDecomposition X pieces

structure ExtinctionConclusion (X : TopSpace.{0}) : Type 1 where
  extinctionTime : ℝ
  extinctionTime_pos : 0 < extinctionTime
  finiteSurgeries : Prop
  finiteSurgeries_holds : finiteSurgeries
  extincts : Prop
  extincts_holds : extincts
  pieces : List (TopSpace.{0})
  pieces_ne_nil : pieces ≠ []
  decomposition : ConnectedSumDecomposition X pieces

structure ExtinctionWithSphericalPieces (X : TopSpace.{0}) : Type 1 where
  conclusion : ExtinctionConclusion X
  spherical : ∀ P ∈ conclusion.pieces, SphericalPiece P
```

`ExtinctionCertificate.toConclusion` fills `finiteSurgeries_holds` by
`ExtinctionTheorem.finitelyMany_of_complexity` and `extincts_holds` by
`ExtinctionTheorem.extincts_of_complexity` (both D3/D6 checked theorems), so the interface-level
conclusion is derived, not postulated.

### 4.5 The canonical-neighborhood input (`Basic.lean`)

```lean
structure CanonicalNeighborhoodInput (X : TopSpace.{0}) (E : ExtinctionCertificate X) : Type 1 where
  ε κ r : ℝ
  ε_pos : 0 < ε
  κ_pos : 0 < κ
  r_pos : 0 < r
  regions : List (PointedMetricSpace.{0})
  certificate : ∀ R ∈ regions, CanonicalNeighborhoodCertificate ε κ r R
  admissible_or_spherical : ∀ R hR,
    IsSurgeryAdmissible (certificate R hR) ∨
      (certificate R hR).kind = CanonicalKind.compactSpherical
  piece_region_homeo : ∀ P ∈ E.pieces,
    ∃ (R : PointedMetricSpace.{0}) (hR : R ∈ regions),
      (certificate R hR).kind = CanonicalKind.compactSpherical ∧
        Nonempty (P.Carrier ≃ₜ R)
```

`CanonicalNeighborhoodInput.sphericalPiece` constructs the `SphericalPiece` datum from the
compact-spherical certificate and the homeomorphism; `only_spherical` is its pointwise form.

### 4.6 The recognition bridge (`Basic.lean`)

```lean
structure SphericalPieceRecognition : Type 1 where
  recognize : ∀ {X : TopSpace.{0}}, SphericalPiece X → SimplyConnectedSpace X.Carrier →
    Nonempty (X.Carrier ≃ₜ SphereThree)
```

### 4.7 The end-game assembly (`Assembly.lean`)

```lean
structure RecognitionHypotheses (X : TopSpace.{0}) : Type 1 where
  compact : CompactSpace X.Carrier
  t2 : T2Space X.Carrier
  charted : ChartedSpace EuclideanThree X.Carrier
  simplyConnected : SimplyConnectedSpace X.Carrier
  extinction : ExtinctionCertificate X
  canonical : CanonicalNeighborhoodInput X extinction
  pieceRecognition : SphericalPieceRecognition

namespace RecognitionHypotheses

def conclusion : ExtinctionConclusion X := H.extinction.toConclusion
def extinctionWithSphericalPieces : ExtinctionWithSphericalPieces X
def onlySphericalPieces (P) (hP : P ∈ H.extinction.pieces) : SphericalPiece P
theorem pieces_simplyConnected : ∀ P ∈ H.extinction.pieces, SimplyConnectedSpace P.Carrier
theorem pieces_homeomorph_sphere : ∀ P ∈ H.extinction.pieces,
    Nonempty (P.Carrier ≃ₜ SphereThree)
theorem homeomorph_sphere (H) : Nonempty (X.Carrier ≃ₜ SphereThree)
theorem stage6Target (H) :
    @Poincare.Stage6.poincareConjectureTopologicalThree X.Carrier X.topology
      H.t2 H.charted H.simplyConnected H.compact
theorem all_pieces_spherical_and_sphere (H) :
    ∀ P ∈ H.extinction.pieces, IsSphericalPiece P ∧ Nonempty (P.Carrier ≃ₜ SphereThree)
```

### 4.8 The explicit conditional theorem (`Assembly.lean`)

```lean
theorem stage6Target_of_certificates {X : TopSpace.{0}}
    (compact : CompactSpace X.Carrier) (t2 : T2Space X.Carrier)
    (charted : ChartedSpace EuclideanThree X.Carrier)
    (simplyConnected : SimplyConnectedSpace X.Carrier)
    (extinction : ExtinctionCertificate X)
    (canonical : CanonicalNeighborhoodInput X extinction)
    (pieceRecognition : SphericalPieceRecognition) :
    @Poincare.Stage6.poincareConjectureTopologicalThree X.Carrier X.topology t2 charted
      simplyConnected compact

theorem extinctionWithSphericalPieces_of_certificates ... :
    ∃ W : ExtinctionWithSphericalPieces X,
      0 < W.conclusion.extinctionTime ∧ W.conclusion.extincts
```

Every hypothesis is an explicit argument.  The only opaque inputs are the named function fields
of `ConnectedSumDecomposition` and `SphericalPieceRecognition`; there are no hidden assumptions.

### 4.9 Statement-only final homeomorphism construction (`Homeomorphism.lean`)

```lean
def missingMoiseSmoothingBridge : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M]
    [IsManifold ThreeManifoldModel ∞ M] [SimplyConnectedSpace M] [CompactSpace M],
    Nonempty (M ≃ₜ SphereThree) → Poincare.Stage6.poincareConjectureSmoothThree M

def missingGeometrizationOutput (Geometric : TopSpace.{0} → Prop) : Prop :=
  ∀ (M : TopSpace.{0}), CompactSpace M.Carrier → T2Space M.Carrier →
    ∃ pieces : List (TopSpace.{0}), pieces ≠ [] ∧ ∀ P ∈ pieces, Geometric P

def missingFinalHomeomorphismConstruction : Prop :=
  ∀ (X : TopSpace.{0}), SimplyConnectedSpace X.Carrier → CompactSpace X.Carrier →
    T2Space X.Carrier → ChartedSpace EuclideanThree X.Carrier →
      Nonempty (X.Carrier ≃ₜ SphereThree)
```

Checked bridges:

| declaration | statement |
|---|---|
| `missingMoiseSmoothingBridge_iff` | shape lemma (definitional unfolding) |
| `missingGeometrizationOutput_iff` | shape lemma (definitional unfolding) |
| `missingFinalHomeomorphismConstruction_iff` | shape lemma (definitional unfolding) |
| `missingFinalHomeomorphismConstruction_iff_missingPoincareConjectureTopologicalThree` | the final construction is exactly the uniform D3 statement-only Poincaré target |
| `stage6Target_of_missingFinalHomeomorphismConstruction` | the final construction discharges the shared Stage6 target for every admissible `M` |
| `missingFinalHomeomorphismConstruction_of_missingPoincare` | the D3 uniform target implies the final construction |
| `smoothTarget_of_topologicalTarget_and_moise` | the Moise bridge upgrades a topological homeomorphism to the smooth Stage6 target |
| `sphericalPieces_of_geometrization` | the geometrization output instantiated at the spherical predicate |
| `finalHomeomorphismConstruction_of_certificateFamily` | a certificate family (one per admissible manifold) plus the recognition bridge implies the final construction through `stage6Target_of_certificates` |

## 5. Verification transcript

`bash longrun/d7sr-logs/run_verification.sh` (reproducible):

```
lake_build 0
Basic 0
Assembly 0
Homeomorphism 0
All 0
Probe 0
Audit 0
```

- **Package build:** `cd release && lake build` — exit 0, 9019 jobs
  (`longrun/d7sr-logs/lake_build.log`).
- **Per-file gate:** `lake env lean release/Poincare/D7/Recognition/<File>.lean` from the
  worktree root — all six files exit 0 (`exit_codes.txt`, per-file `.out`/`.err`).
- **Forbidden scan** (`input/d5-tools/scan_forbidden.py`, comment/string-aware): 6 Lean files
  scanned, **hard 0, soft 0** (`forbidden-scan.json`).
- **Axiom audit:** `#print axioms` on 62 declarations (`axioms-print.out`); cones `{}` × 7,
  `{propext}` × 2, `{propext, Quot.sound}` × 2,
  `{propext, Classical.choice, Quot.sound}` × 51; **nonstandard 0** (`axioms.json`).
- **Source integrity:** 245 files compared with `../D7-canonical-neighborhood`;
  **changed 0, removed 0, added outside the new directory 0** (`source-integrity.json`).

## 6. Missing inputs and blockers

`finalHomeomorphismDependencies` (length 6, all names/reasons nonempty):

| id | input |
|---|---|
| SR-1 | Moise smoothing bridge (topological `3`-manifolds smooth; homeomorphisms smoothable) |
| SR-2 | geometrization output (geometric decomposition of a closed `3`-manifold) |
| SR-3 | spherical space form theorem (a simply connected spherical space form is `𝕊³`) |
| SR-4 | van Kampen for connected sums (simple connectivity passes to summands) |
| SR-5 | connected sum of `𝕊³` summands is `𝕊³` |
| SR-6 | Ricci flow with surgery and finite-time extinction (the certificate family) |

`finalHomeomorphismBlockers` (length 4): `B-D7-SR-MOISE`, `B-D7-SR-GEOMETRIZATION`,
`B-D7-SR-SPHERICAL-FORM`, `B-D7-SR-EXTINCTION`.

## 7. Honest boundary

- No manifold-level Ricci flow, surgery construction, canonical-neighborhood theorem,
  κ-noncollapsing theorem or extinction theorem is proved or constructed.  The extinction
  certificate, the canonical-neighborhood input and the certificate family are explicit
  hypotheses.
- `SphericalPiece` records the compact-spherical alternative of the D7 canonical-neighborhood
  certificate (an algebraic curvature normalization plus a metric noncollapsing shadow); the
  smooth positive-curvature geometry is not formalized.
- The connected-sum relation is an opaque `Prop` field; van Kampen and the connected-sum
  computation are function fields, not theorems.
- `missingFinalHomeomorphismConstruction`, `missingMoiseSmoothingBridge` and
  `missingGeometrizationOutput` are statement-only `Prop`s, never asserted as theorems.
- `finalHomeomorphismConstruction_of_certificateFamily` is conditional on a certificate family
  for every admissible manifold; it does not prove the Poincaré conjecture.
- The sibling task `D7-surgery-neck-extinction` (`Poincare/D7/SurgeryFlow/`) was running
  concurrently and is not imported; an adapter from its `ExtinctionData` to
  `Recognition.ExtinctionCertificate` is future work.

## 8. Artifacts

| artifact | path |
|---|---|
| verification script | `longrun/d7sr-logs/run_verification.sh` |
| exit codes | `longrun/d7sr-logs/exit_codes.txt` |
| per-file logs | `longrun/d7sr-logs/lean_<File>.out` / `.err` |
| axiom print | `longrun/d7sr-logs/axioms-print.out` |
| axiom summary | `longrun/d7sr-logs/axioms.json` |
| axiom parser | `longrun/d7sr-logs/parse_axioms.py` |
| forbidden scan | `longrun/d7sr-logs/forbidden-scan.json` |
| source integrity | `longrun/d7sr-logs/source-integrity.json` |
| integrity checker | `longrun/d7sr-logs/source_integrity.py` |
| package build | `longrun/d7sr-logs/lake_build.log` |
| result card | `longrun/results/D7-sphere-recognition.md` / `.json` |

TASK_DONE — card: longrun/results/D7-sphere-recognition.md
