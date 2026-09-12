# D3-kappa-ledger — compact 3-manifold / non-collapsing / normalized-volume interface

**Task id:** `D3-kappa-ledger`
**Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D3_kappa_ledger`
**Prompt file:** `longrun/prompts/D3_topology.md`
**Started:** 2026-09-08T23:36+08:00
**Finished:** 2026-09-08T23:51+08:00
**Overall status:** `CHECKED INTERFACE LAYER` — 6 Lean modules + 1 audit module compile with
exit code 0; 70 of the 71 audited declarations depend only on `[propext, Classical.choice, Quot.sound]` and the remaining one on no axioms.
No missing theorem is claimed as proved. Nothing in the shared Stage6 files was modified.

**Worktree note.** The prompt template names the worktree `D3_topology`; the actual session
workspace (and the directory holding `state/D3_kappa_ledger`) is
`worktrees/D3_kappa_ledger`, which is where all deliverables live.

**Sandbox note.** The shared result directory
`/data/home/guoshaoyang/workdir/lean_poincare/longrun/results/` is outside the session
workspace (`.../worktrees/D3_kappa_ledger`); writes there are denied under `workspace-write`.
The result card is therefore stored inside the worktree at
`longrun/results/D3-kappa-ledger.{md,json}` (plus copies at the worktree root) for the
integrator to promote.

## 1. Files changed

| Path (worktree-relative) | Role |
| --- | --- |
| `lean-toolchain` | pins `leanprover/lean4:v4.34.0-rc2` |
| `lakefile.toml` | isolated `Poincare` package, library glob `Poincare.+`, mathlib `master` |
| `lake-manifest.json` | copied from `poincare-lab`; mathlib rev `7974e751bece493b6ff508039423ca9fa2452fa8` |
| `.lake/packages` | symlink to the prebuilt `poincare-lab/.lake/packages` (mathlib reused, never rebuilt) |
| `Poincare/Stage6` | **read-only symlink** to the shared Stage6 sources (not copied, not modified) |
| `Poincare/Longrun/Topology/Basic.lean` | model spaces `ℝ³`, `𝕊³`, `𝓡 3` |
| `Poincare/Longrun/Topology/CompactThreeManifold.lean` | `CompactThreeManifold` interface + consequences |
| `Poincare/Longrun/Topology/Noncollapsing.lean` | `CurvatureBoundedOn`, `KappaNoncollapsingCertificate` + consequences |
| `Poincare/Longrun/Topology/NormalizedVolume.lean` | two normalized-volume interfaces + equivalence with the κ-certificate |
| `Poincare/Longrun/Topology/Stage6Bridge.lean` | connection to the shared Stage6 statement-only targets |
| `Poincare/Longrun/Topology/MissingTheorems.lean` | statement-only ledger of the exact missing theorems |
| `Poincare/Longrun/Topology/AxiomAudit.lean` | `#print axioms` for all audited declarations |
| `Poincare/Longrun/Topology/README.md` | module-level documentation |
| `verification/00_clean_rebuild.log` … `05_shared_stage6_integrity.log` | captured command outputs and exit codes |

No file outside the worktree was written. The shared Stage6 sources keep their original
mtime and sha256 (see §6.5).

## 2. Interfaces (all explicit, no postulates)

### 2.1 Compact 3-manifold

```lean
class CompactThreeManifold (M : Type*) [TopologicalSpace M]
    extends ChartedSpace EuclideanThree M, IsManifold ThreeManifoldModel ∞ M,
      CompactSpace M, T2Space M, ConnectedSpace M where
  nonempty : Nonempty M
```

`EuclideanThree = EuclideanSpace ℝ (Fin 3)`, `ThreeManifoldModel = 𝓡 3`.  Because the
interface is a `class`, the atlas, the `C^∞` structure, compactness, Hausdorffness and
connectedness are all available by instance search; the atlas is data, so the interface
cannot be manufactured without a caller-supplied atlas.

### 2.2 κ-non-collapsing certificate

```lean
abbrev CurvatureBoundedOn (M : Type*) := M → ℝ → Prop

structure KappaNoncollapsingCertificate (M : Type*) [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M) (κ r₀ : ℝ) : Prop where
  kappa_pos : 0 < κ
  r0_pos : 0 < r₀
  volume_ball_lower : ∀ x : M, ∀ r : ℝ, 0 < r → r ≤ r₀ → K x r →
    ENNReal.ofReal (κ * r ^ (3 : ℕ)) ≤ μ (Metric.eball x (ENNReal.ofReal r))
```

`K` is an **opaque** curvature-bound predicate ("`|Rm| ≤ r⁻²` on `B(x,r)`") because the
mathlib pin has no Riemann curvature tensor.  The certificate records exactly the
non-collapsing inequality and its positivity hypotheses.

### 2.3 Normalized-volume lower bounds

Abstract real-valued form:

```lean
structure NormalizedVolumeLowerBound (M : Type*) (normalizedVolume : M → ℝ) (v₀ : ℝ) : Prop where
  lower_bound : ∀ x : M, v₀ ≤ normalizedVolume x
```

Concrete normalized ball volume:

```lean
noncomputable def normalizedBallVolume (μ : Measure M) (x : M) (r : ℝ) : ℝ≥0∞ :=
  μ (Metric.eball x (ENNReal.ofReal r)) / ENNReal.ofReal (r ^ (3 : ℕ))

structure NormalizedBallVolumeLowerBound (M : Type*) [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M) (κ r₀ : ℝ) : Prop where
  kappa_pos : 0 < κ
  r0_pos : 0 < r₀
  normalized_lower : ∀ x r, 0 < r → r ≤ r₀ → K x r →
    ENNReal.ofReal κ ≤ normalizedBallVolume μ x r
```

## 3. Checked consequences of the interfaces

At least two are required; 29 are delivered (plus the generated class projections).

### 3.1 Compact 3-manifold (`CompactThreeManifold.lean`)

| Declaration | Statement | Proof |
| --- | --- | --- |
| `toSigmaCompactSpace` | `SigmaCompactSpace M` | mathlib `CompactSpace.sigmaCompact` |
| `toParacompactSpace` | `ParacompactSpace M` | mathlib `paracompact_of_compact` |
| `toLocallyCompactSpace` | `LocallyCompactSpace M` | `ChartedSpace.locallyCompactSpace` with model `ℝ³` |
| `toSecondCountableTopology` | `SecondCountableTopology M` | `ChartedSpace.secondCountable_of_sigmaCompact` |
| `toTopologicalManifold` | `IsManifold 𝓡3 0 M` | `IsManifold.of_le` and `0 ≤ ∞` |
| `exists_finite_chart_cover` | `∃ s : Finset M, ⋃ x ∈ s, (chartAt ℝ³ x).source = univ` | genuine compactness argument: `IsCompact.elim_finite_subcover` applied to the open chart-source cover `ChartedSpace.iUnion_source_chartAt` |
| `exists_mem_chart_source` | `∃ x, x ∈ (chartAt ℝ³ x).source` | nonemptiness + `mem_chart_source` |

### 3.2 κ-non-collapsing (`Noncollapsing.lean`)

| Declaration | Statement |
| --- | --- |
| `volume_ball_pos` | curvature-bounded balls have positive measure |
| `volume_ball_ne_zero` | curvature-bounded balls have non-zero measure |
| `mono` | certificate at `κ` gives a certificate at any `0 < κ' ≤ κ` |
| `volume_unit_ball_lower` | if `1 ≤ r₀`, then `κ ≤ μ (B(x,1))` when `K x 1` |
| `exists_uniform_unit_ball_lower_bound` | `∃ c > 0, ∀ x, c ≤ μ (B(x,1))` (uniform no-collapsing at unit scale) |
| `apply` | the certificate field, re-exposed as a lemma |

### 3.3 Normalized volume (`NormalizedVolume.lean`)

* Abstract form: `apply`, `nonneg`, `pos`, `mono`, `bddBelow_range`, `exists_lower_bound`,
  `add`, `smul`, `const_iff`.
* Normalized ball form: `normalizedBallVolume_nonneg`, `unit_ball_lower`.
* Cross-interface:
  `kappaNoncollapsingCertificate_iff_normalizedBallVolumeLowerBound` (a kernel-checked
  `ℝ≥0∞` equivalence `κ ≤ μ(B)/r³ ↔ κ r³ ≤ μ(B)`),
  `NormalizedBallVolumeLowerBound.toKappaNoncollapsingCertificate`,
  `KappaNoncollapsingCertificate.toNormalizedBallVolumeLowerBound`,
  `NormalizedBallVolumeLowerBound.volume_ball_pos`,
  `NormalizedBallVolumeLowerBound.mono`.

## 4. Connection to the shared Stage6 statement-only target

`Stage6Bridge.lean` imports `Poincare.Stage6.TopologyBridge` and
`Poincare.Stage6.SphereSimplyConnected` (read-only) and proves:

| Declaration | Statement |
| --- | --- |
| `stage6Target_iff_sphereRecognition` | `Poincare.Stage6.poincareConjectureTopologicalThree M ↔ Nonempty (M ≃ₜ 𝕊³)` (definitional, `Iff.rfl`) |
| `stage6Target_iff_stage6Alias` | the local `stage6Target` abbreviation is definitionally the Stage6 alias |
| `stage6Target_of_sphereRecognition` | `Nonempty (M ≃ₜ 𝕊³) → Poincare.Stage6.poincareConjectureTopologicalThree M` |
| `compactThreeManifold_stage6Hypotheses` | the interface supplies exactly the Stage6 typeclass hypotheses (`T2Space`, `Nonempty (ChartedSpace ℝ³ M)`, `CompactSpace`, `IsManifold 𝓡3 ∞`, `ConnectedSpace`, `Nonempty`) |
| `stage6Target_of_compactThreeManifold` | with the interface and simple connectivity, the sphere-recognition conclusion discharges the Stage6 target |
| `stage6SphereSimplyConnected_iff` | `Poincare.Stage6.sphereThreeSimplyConnected ↔ SimplyConnectedSpace 𝕊³` |
| `stage6SphereThreePiOneTrivial_iff` | `Poincare.Stage6.sphereThreePiOneTrivial ↔ ∀ x, Subsingleton (π₁ 𝕊³ x)` |
| `pathConnectedSpace_sphereThree` | Stage6's checked `PathConnectedSpace 𝕊³`, re-exported |
| `simplyConnectedSpace_sphereThree_iff` | Stage6's checked reduction to path connectivity plus trivial fundamental groups |
| `stage6SphereThreePiOneTrivial_iff_stage6SphereSimplyConnected` | Stage6's checked equivalence of the two sphere targets |

`Mathlib.Wanted` is **not imported** (it is not even importable at this mathlib pin: its
olean does not exist; see `verification/04_mathlib_wanted_probe.log`).  The only textual
mentions of `Mathlib.Wanted` in the sources are documentation of this constraint.

## 5. Exact missing theorems

### 5.1 κ-non-collapsing

Perelman, *The entropy formula for the Ricci flow and its geometric applications*,
arXiv:math/0211159; Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 4–8.

| # | Missing theorem (exact statement) | Lean ledger entry | Prerequisites missing from mathlib `7974e751be` |
| --- | --- | --- | --- |
| K1 | **No local collapsing** (§4 Thm 4.1): for a normalized Ricci flow on `M³` over `[0,T)` with `|Rm| ≤ r⁻²` on `B(x,r)`, `vol B(x,r) ≥ κ r³` with `κ = κ(g(0), T) > 0` | `missingKappaNoncollapsing` | Riemann/Ricci tensor; Riemannian volume measure; Ricci flow |
| K2 | Normalized-volume form of K1: `μ(B(x,r))/r³ ≥ κ` | `missingNormalizedNoLocalCollapsing` | same as K1; equivalent to K1 by the checked equivalence of §3.3 |
| K3 | **Entropy route**: monotonicity of `μ` (equivalently `W`) plus normalization implies K1 | `missingKappaNoncollapsingOfMuMonotonicity` | conjugate heat kernel; log-Sobolev inequality; heat semigroup; integration by parts on manifolds |
| K4 | **Reduced-volume monotonicity** (§7): `Ṽ(τ)` is non-increasing along the flow | `missingReducedVolumeMonotonicity` | reduced length `L`, its minimizers (`L`-geodesics), Jacobian comparison, path-space calculus |
| K5 | **Conjugate heat kernel** (§6–7): existence of a unit-mass measurable family `u τ` | `missingConjugateHeatKernel` | fundamental solution of the conjugate heat equation; parabolic Schauder estimates |
| K6 | **κ persists under surgery** (2003, §4.3): non-collapsing before surgery implies non-collapsing after, with possibly smaller `κ` | `missingKappaPersistenceUnderSurgery` | surgery construction and metric gluing; a priori curvature estimates |
| K7 | **Canonical neighbourhood theorem** (2003, §3): high-curvature points of a 3D κ-solution are ε-close to model geometries | `missingCanonicalNeighborhoodTheorem` | pointed Gromov–Hausdorff convergence; Cheeger–Gromov compactness; Brendle–Schoen classification of 3D κ-solutions |

Foundational gaps shared by K1–K7 (all absent from the mathlib pin): construction of the
Riemann curvature tensor from a connection, Ricci and scalar curvature, the Riemannian
volume form/measure, the divergence theorem and integration by parts on manifolds,
Hamilton's short-time existence for Ricci flow, and the DeTurck/Uhlenbeck trick.

### 5.2 Sphere recognition

| # | Missing theorem (exact statement) | Lean ledger entry | Prerequisites missing from mathlib `7974e751be` |
| --- | --- | --- | --- |
| S1 | `SimplyConnectedSpace 𝕊³` | `missingSphereThreeSimplyConnected` | no sphere simple-connectivity instance; upstream PR leanprover-community/mathlib4#28246 is not in the pin |
| S2 | `π₁(𝕊³) = 0` pointwise | `missingSphereThreePiOneTrivial` | same; equivalent to S1 by the checked Stage6 reduction |
| S3 | **Poincaré conjecture (topological)**: compact `T2` `ℝ³`-charted simply connected `M` satisfies `Nonempty (M ≃ₜ 𝕊³)` | `missingPoincareConjectureTopologicalThree` (uniform), matching `Poincare.Stage6.poincareConjectureTopologicalThree` | S1/S2; full Ricci-flow-with-surgery machinery; the checked Stage6 reduction of `SimplyConnectedSpace` to path connectivity + trivial `π₁` still leaves the fundamental group computation |
| S4 | **Poincaré conjecture (smooth)**: the same with a diffeomorphism `M ≃ₘ⟮𝓡3,𝓡3⟯ 𝕊³` | `missingPoincareConjectureSmoothThree`, matching `Poincare.Stage6.poincareConjectureSmoothThree` | S3 plus smoothing theory |
| S5 | **Sphere recognition algorithm** (Rubinstein 1995; Thompson 1994): there is a decision procedure deciding `M ≃ₜ 𝕊³` for compact 3-manifolds | `missingSphereRecognitionAlgorithm` | normal surface theory, crushing, 0-efficiency, Haken's algorithm, Rubinstein–Scharlemann untelescoping |

Alternative routes recorded for completeness (not formalized as ledger entries): Thurston
geometrization (implies S3 via Kneser/Milnor prime decomposition and JSJ), and the
quarter-pinched sphere theorem (requires Riemannian geometry absent from mathlib).

## 6. Verification evidence

All commands were run from the worktree with
`ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan` and
`PATH=$ELAN_HOME/bin:$PATH`.  Lean is `4.34.0-rc2`, mathlib rev `7974e751be`.

### 6.1 Clean rebuild (empty `.lake/build`)

```text
$ rm -rf .lake/build && lake build Poincare
Build completed successfully (8888 jobs).
exit code: 0
```

### 6.2 Per-file elaboration gate

```text
$ lake env lean Poincare/Longrun/Topology/Basic.lean              # exit code: 0
$ lake env lean Poincare/Longrun/Topology/CompactThreeManifold.lean # exit code: 0
$ lake env lean Poincare/Longrun/Topology/Noncollapsing.lean       # exit code: 0
$ lake env lean Poincare/Longrun/Topology/NormalizedVolume.lean    # exit code: 0
$ lake env lean Poincare/Longrun/Topology/Stage6Bridge.lean        # exit code: 0
$ lake env lean Poincare/Longrun/Topology/MissingTheorems.lean     # exit code: 0
$ lake env lean Poincare/Longrun/Topology/AxiomAudit.lean          # exit code: 0
```

### 6.3 `#print axioms`

`AxiomAudit.lean` prints axioms for **71** declarations (all theorems and consequences, all statement-only `missing...` definitions, and the key definitions).  Every line but one is

```text
'<declaration>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

i.e. only the three standard Lean kernel axioms; the exception is
`missingCanonicalNeighborhoodTheorem`, which depends on no axioms.  No `sorryAx`, no
project-specific postulate, no `Mathlib.Wanted` declaration.  Full output:
`verification/03_axiom_audit.log`.

### 6.4 Constraint scan

```text
pattern: \bsorry\b|\baxiom\b|\bunsafe\b|native_decide|proof_wanted
files scanned: Poincare/Longrun/Topology/*.lean
match count: 0
imports mentioning Wanted: 0
```

Full output: `verification/02_forbidden_scan.log`.  `import Mathlib.Wanted` fails because
no olean exists (`verification/04_mathlib_wanted_probe.log`), so the Wanted region cannot
enter any dependency cone of this layer.

### 6.5 Shared Stage6 files untouched

```text
TopologyBridge.lean   mtime 2026-09-06 01:51:16  sha256 91a74afadd91760ec314c8aba75b0dfe09a2eef87062f3f0a1e0bfb1ea9a39bf
SphereSimplyConnected.lean mtime 2026-09-08 19:37:18  sha256 fc410ebaf6b3b3ec2e0c8a6f6cfa13ce8b2f83ef829b206747da110bb38629b7
```

The worktree accesses them through the read-only symlink `Poincare/Stage6`; their build
artifacts are written only into the worktree's own `.lake/build`.  Full output:
`verification/05_shared_stage6_integrity.log`.

## 7. Promotion instructions

1. Copy `Poincare/Longrun/Topology/` into the shared `poincare-lab/Poincare/Longrun/`
   tree (the shared package already globs `Poincare.+`).
2. Run `lake build Poincare` in `poincare-lab` and
   `lake env lean Poincare/Longrun/Topology/AxiomAudit.lean`; both must exit 0.
3. No change to `Poincare/Stage6/` is needed or permitted.

## 8. Honesty statement

No declaration in this layer is presented as a proof of the Poincaré conjecture, of
Perelman's no-local-collapsing theorem, or of the sphere recognition algorithm.  Every
mathematical assertion beyond a definition is either (a) a kernel-checked lemma listed in
§3–§4, or (b) an explicit hypothesis field of one of the three interfaces.  The `missing...`
declarations of §5 are `def ... : Prop` statement aliases, not theorems, and the checked
companions attached to them are shape lemmas and modus-ponens consequences, not proofs of
the missing mathematics.
