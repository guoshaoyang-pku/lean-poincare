# D7-canonical-neighborhood — canonical neighborhood interface

- **Task:** `D7-canonical-neighborhood`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-canonical-neighborhood`
- **Verdict:** `TASK_DONE`
- **Lean:** `4.34.0-rc2` (`6a10ac8c22beadecabdbb0919c2b50214762f91d`)
- **mathlib:** `7974e751bece493b6ff508039423ca9fa2452fa8`
- **New Lean sources:** `release/Poincare/D7/Canonical/` (8 files, 1673 lines, 95 declarations)
- **Verification transcript:** `longrun/d7cn-logs/`

## 1. Summary

The task asks for the canonical neighborhood interface of Perelman's surgery theorem. The
deliverable has four layers, all built over the accepted D7 curvature layer
(`Poincare.D7.Curvature`, algebraic `RiemannCurvatureData` with `sectionalCurvature`) and the
accepted D7 compactness layer (`Poincare.D7.Compactness`, `PointedMetricSpace`,
`GHConvergenceData`, `GHPrecompactCertificate`).

1. **Definitions.**
   - `EpsilonApproximation ε X Y` is the one-step pointed ε-isometry datum (distortion,
     almost surjectivity, basepoint error) with `refl`, `mono`, `comp` (`ε₁ + 2 ε₂`), and the
     two checked bridges to the compactness layer, `ofGHConvergenceData` and
     `toGHConvergenceData` (a family of εₙ-approximations with `εₙ → 0` *is* pointed GH
     convergence along `atTop`).
   - `CylinderInterface`, `CapInterface`, `SphereInterface` are the metric interfaces of the
     three model spaces of the classification: scale `r > 0`, the characteristic pair of
     points (`π r` for the cylinder cross-section and the sphere, `r` for the cap boundary),
     the diameter bound `π r` where the model is compact, and the scalar curvature
     normalization (`2/r²` for the cylinder, `6/r²` for the cap and sphere).
   - `EpsilonNeck ε r X`, `EpsilonCap ε r X`, `EpsilonSpherical ε r X` are the region data:
     the region is ε-close, in the one-step GH sense, to a model interface of the *same*
     scale `r`.
   - `CurvatureScaleDatum r` is the curvature normalization over the D7 curvature layer: an
     algebraic `RiemannCurvatureData` with a nondegenerate plane of sectional curvature
     `1/r²`.
   - `MetricNoncollapsing κ r X` is the checkable metric shadow of κ-noncollapsing (a pair of
     points at distance at least `κ r`).
   - `CanonicalNeighborhoodCertificate ε κ r X` bundles the kind
     (`neck`/`cap`/`compactSpherical`), the corresponding ε-model data, the curvature
     normalization and the metric noncollapsing witness.
2. **Kernel-checked mathematics.**
   - **Model instance checks.** `cylinder_certificate`, `cap_certificate` and
     `sphere_certificate` inhabit the certificate on the three stated model interfaces at
     their own scale for every `ε ≥ 0` (the identity approximation) and the appropriate
     noncollapsing constants (`κ ≤ π` for the cylinder and sphere, `κ ≤ 1` for the cap).
     `so3CurvatureScaleDatum` realizes the curvature normalization at scale `2` with the D7
     non-flat `so(3)` model (`sec = 1/4 = 1/2²`). Concrete pointed metric spaces witness the
     three interfaces at scale `2` (a line with two points at distance `2π`, an interval of
     diameter `2π`, an interval of diameter `4`), and `exists_all_kinds_at_scale_two` records
     that all three kinds are inhabited.
   - **Classification toy.** `epsilonApproximation_dist_le_two_mul` shows that an
     ε-approximation out of a subsingleton has target diameter at most `2 ε`;
     `scale_le_two_mul_of_subsingleton` turns this into `r ≤ 2 ε` for every certificate on a
     collapsed region; `degenerateModel_not_certificate` proves that the stated degenerate
     model (the one-point/collapsed space) carries **no** certificate at scale `r` whenever
     `2 ε < r`.  `exists_far_pair_of_certificate` gives the general metric-size consequence
     (a pair of points at distance at least `r - 3 ε`) on an arbitrary region.
3. **State-only theorem.** `missingPerelmanCanonicalNeighborhood X H ε` is the full
   statement: for `ε > 0`, the bundled geometric hypotheses `H` (dimension three, curvature
   scale `r₀ > 0`, noncollapsing constant `κ > 0`, and the opaque curvature/scalar-curvature/
   noncollapsing/ancient-solution/derivative-bound propositions) imply the existence of an
   admissible scale `r ≤ r₀`, a curvature normalization at scale `r`, and a certificate.  The
   checked reductions isolate the certificate extraction, the scale extraction and the
   certificate-supplies-the-statement direction; the ledger names 12 missing inputs and 6
   blockers.

No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs in any authored file;
all 95 audited declarations have standard axiom cones
(`{}` × 11, `{propext}` × 2, `{propext, Classical.choice, Quot.sound}` × 82).

## 2. Scaffold

`cp -al ../D7-gh-compactness/. .` failed with `EXDEV Invalid cross-device link` (directories
were created, no files linked), so the documented fallback `cp -a` was used: exit 0.  The
source-integrity check compares 237 non-`.lake`, non-`longrun` files against the scaffold:
**0 changed, 0 removed, 0 added outside the new directory**.  As in every D7 sibling task, the
Lake package root is `release/`, so the new sources live in `release/Poincare/D7/Canonical/`;
the worktree-root `lakefile.toml` re-exposes `release/.lake` through the `.lake` symlink, so
the gate command `lake env lean release/Poincare/D7/Canonical/<File>.lean` resolves the
imports.

## 3. New files

| file | lines | decls | role |
|---|---:|---:|---|
| `Basic.lean` | 503 | 31 | `EpsilonApproximation` + GH bridges, the three model interfaces, `EpsilonNeck`/`EpsilonCap`/`EpsilonSpherical`, `CurvatureScaleDatum`, `MetricNoncollapsing`, `CanonicalKind`, `CanonicalNeighborhoodCertificate` |
| `Curvature.lean` | 70 | 3 | `so3CurvatureScaleDatum`: the D7 `so(3)` model realizes the curvature scale `2` |
| `Models.lean` | 276 | 20 | model instance checks (`cylinder_certificate`, `cap_certificate`, `sphere_certificate`), concrete metric-space witnesses and non-vacuity |
| `Classification.lean` | 223 | 12 | the classification toy: `degenerateModel_not_certificate`, `scale_le_two_mul_of_subsingleton`, `exists_far_pair_of_certificate` |
| `Statements.lean` | 340 | 29 | state-only Perelman canonical neighborhood theorem, checked reductions, 12-entry dependency ledger, 6 blockers |
| `All.lean` | 26 | 0 | umbrella module |
| `Probe.lean` | 128 | 0 | 95 `#check` API probes (generated) |
| `Audit.lean` | 107 | 0 | 95 `#print axioms` commands (generated) |

## 4. Main declarations

### 4.1 One-step ε-approximations (`Basic.lean`)

```lean
structure EpsilonApproximation (ε : ℝ) (X Y : PointedMetricSpace.{u}) where
  ε_nonneg : 0 ≤ ε
  approx : X → Y
  distortion : ∀ x y : X, |dist (approx x) (approx y) - dist x y| ≤ ε
  surjective : ∀ y : Y, ∃ x : X, dist y (approx x) ≤ ε
  base_dist : dist (approx X.base) Y.base ≤ ε
```

Checked API: `dist_approx_le`, `dist_le_dist_approx`, `refl`, `mono`, `comp` (error
`ε₁ + 2 ε₂`), `ofGHConvergenceData`, `toGHConvergenceData`,
`toGHConvergenceData_ofGHConvergenceData`.

### 4.2 The model interfaces (`Basic.lean`)

```lean
structure CylinderInterface where
  space : PointedMetricSpace.{u}
  radius : ℝ;  radius_pos : 0 < radius
  axis : ℝ → space;  axis_base : axis 0 = space.base
  axis_dist : ∀ s t, dist (axis s) (axis t) = |s - t|
  antipodal : space
  antipodal_dist : dist space.base antipodal = Real.pi * radius
  scalarCurvature : ℝ
  scalarCurvature_eq : scalarCurvature = 2 / radius ^ 2

structure CapInterface where
  space : PointedMetricSpace.{u}
  radius : ℝ;  radius_pos : 0 < radius
  boundary : space
  boundary_dist : dist space.base boundary = radius
  diameter_le : ∀ x y, dist x y ≤ Real.pi * radius
  scalarCurvature : ℝ
  scalarCurvature_eq : scalarCurvature = 6 / radius ^ 2

structure SphereInterface where
  space : PointedMetricSpace.{u}
  radius : ℝ;  radius_pos : 0 < radius
  antipodal : space
  antipodal_dist : dist space.base antipodal = Real.pi * radius
  diameter_le : ∀ x y, dist x y ≤ Real.pi * radius
  scalarCurvature : ℝ
  scalarCurvature_eq : scalarCurvature = 6 / radius ^ 2
```

The interfaces record the metric features the classification consumes; they do not assert that
`space` is the smooth round model (see the blockers).

### 4.3 Region data, curvature normalization and the certificate (`Basic.lean`)

```lean
structure EpsilonNeck (ε r : ℝ) (X : PointedMetricSpace.{u}) where
  model : CylinderInterface.{u}
  radius_eq : model.radius = r
  approx : EpsilonApproximation ε X model.space
-- EpsilonCap and EpsilonSpherical are the analogous structures for CapInterface/SphereInterface

structure CurvatureScaleDatum (r : ℝ) where
  V : Type u;  [inst₁ : AddCommGroup V]; [inst₂ : Module ℝ V]; [inst₃ : FiniteDimensional ℝ V]
  ι : Type w;  [inst₄ : Fintype ι];      [inst₅ : DecidableEq ι]
  data : RiemannCurvatureData V ι
  planeX planeY : V
  nondegenerate : data.IsNondegenerate2Plane planeX planeY
  sectional_eq : data.sectionalCurvature planeX planeY = 1 / r ^ 2

structure MetricNoncollapsing (κ r : ℝ) (X : PointedMetricSpace.{u}) where
  κ_pos : 0 < κ
  farPoint : X
  far_dist : κ * r ≤ dist X.base farPoint

inductive CanonicalKind where
  | neck | cap | compactSpherical
  deriving DecidableEq, Repr, Inhabited

structure CanonicalNeighborhoodCertificate (ε κ r : ℝ) (X : PointedMetricSpace.{u}) where
  scale_pos : 0 < r
  kind : CanonicalKind
  neck_data : kind = CanonicalKind.neck → EpsilonNeck ε r X
  cap_data : kind = CanonicalKind.cap → EpsilonCap ε r X
  spherical_data : kind = CanonicalKind.compactSpherical → EpsilonSpherical ε r X
  curvature : CurvatureScaleDatum r
  noncollapsing : MetricNoncollapsing κ r X
```

Checked API: `EpsilonNeck.antipodal_dist`, `EpsilonCap.boundary_dist`,
`EpsilonSpherical.antipodal_dist`, the three `radius_pos` lemmas,
`EpsilonNeck.toGHConvergenceData` (a sequence of εₙ-necks with `εₙ → 0` around a fixed
cylinder GH-converges to it), `CanonicalNeighborhoodCertificate.kind_cases`, `neckOf`, `capOf`,
`sphericalOf`, `scale_pos'`.

### 4.4 The curvature normalization (`Curvature.lean`)

```lean
noncomputable def so3CurvatureScaleDatum : CurvatureScaleDatum.{0, 0} 2
-- V = Fin 3 → ℝ, data = So3.so3, plane = span(e₀,e₁), sec = 1/4 = 1/2²

theorem nonempty_curvatureScaleDatum_two : Nonempty (CurvatureScaleDatum.{0, 0} 2)
theorem so3CurvatureScaleDatum_sectional :
    so3CurvatureScaleDatum.data.sectionalCurvature
      so3CurvatureScaleDatum.planeX so3CurvatureScaleDatum.planeY = 1 / 4
```

### 4.5 Model instance checks (`Models.lean`)

| declaration | statement |
|---|---|
| `cylinder_isEpsilonNeck` | `CylinderInterface` of radius `r` is an `EpsilonNeck ε r` for every `ε ≥ 0` |
| `cylinder_certificate` | kind `neck` certificate at scale `r`, for `0 < κ ≤ π` and any `CurvatureScaleDatum r` |
| `cap_isEpsilonCap` / `cap_certificate` | cap is an `EpsilonCap`, kind `cap` certificate for `0 < κ ≤ 1` |
| `sphere_isEpsilonSpherical` / `sphere_certificate` | sphere is an `EpsilonSpherical`, kind `compactSpherical` certificate for `0 < κ ≤ π` |
| `lineCylinderInterface`, `piIntervalSphereInterface`, `twoIntervalCapInterface` | concrete metric-space witnesses of the three interfaces at scale `2` |
| `lineCylinder_certificate`, `piIntervalSphere_certificate`, `twoIntervalCap_certificate` | concrete certificates at scale `2` using `so3CurvatureScaleDatum` |
| `exists_neck_certificate`, `exists_cap_certificate`, `exists_spherical_certificate`, `exists_all_kinds_at_scale_two` | non-vacuity of the three kinds |

### 4.6 The classification toy (`Classification.lean`)

```lean
abbrev degenerateModel : PointedMetricSpace.{0} := PointedMetricSpace.unit

theorem epsilonApproximation_dist_le_two_mul [Subsingleton X]
    (A : EpsilonApproximation ε X Y) (y₁ y₂ : Y) : dist y₁ y₂ ≤ 2 * ε

theorem scale_le_two_mul_of_subsingleton [Subsingleton X]
    (C : CanonicalNeighborhoodCertificate ε κ r X) : r ≤ 2 * ε

theorem degenerateModel_not_certificate (h : 2 * ε < r) :
    ¬ Nonempty (CanonicalNeighborhoodCertificate ε κ r degenerateModel)

theorem exists_far_pair_of_certificate (C : CanonicalNeighborhoodCertificate ε κ r X) :
    ∃ x y : X, r ≤ dist x y + 3 * ε
```

The three alternatives each contain a pair of model points at distance at least `r`, so a
collapsed region — whose image under any ε-approximation has diameter at most `2 ε` — cannot
carry a certificate at a positive scale.  `degenerateModel_approximates_itself` shows the
exclusion is about the model scale, not the approximation notion.

### 4.7 The state-only theorem (`Statements.lean`)

```lean
structure CanonicalNeighborhoodHypotheses (X : PointedMetricSpace.{u}) where
  dim : ℕ;  dim_eq_three : dim = 3
  curvatureRadius : ℝ;  curvatureRadius_pos : 0 < curvatureRadius
  kappa : ℝ;  kappa_pos : 0 < kappa
  curvatureLowerBound : Prop
  scalarCurvatureLarge : Prop
  noncollapsed : Prop
  ancientKappaSolution : Prop
  boundedCurvatureDerivatives : Prop

def missingPerelmanCanonicalNeighborhood (X : PointedMetricSpace.{u})
    (H : CanonicalNeighborhoodHypotheses X) (ε : ℝ) : Prop :=
  0 < ε → H.curvatureLowerBound → H.scalarCurvatureLarge → H.noncollapsed →
    ∃ r : ℝ, 0 < r ∧ r ≤ H.curvatureRadius ∧
      ∃ curvature : CurvatureScaleDatum.{u, u} r,
        Nonempty (CanonicalNeighborhoodCertificate ε H.kappa r X)
```

Checked reductions: `missingPerelmanCanonicalNeighborhood_iff`,
`certificate_of_missingPerelmanCanonicalNeighborhood`,
`exists_admissible_scale_of_missingPerelmanCanonicalNeighborhood`,
`exists_scale_below_curvatureRadius`,
`missingPerelmanCanonicalNeighborhood_of_certificate`,
`scale_le_two_mul_of_missingPerelman_conclusion`,
`not_conclusion_scale_of_two_mul_lt`.

## 5. Verification transcript

`bash longrun/d7cn-logs/run_verification.sh` (reproducible):

```
lake_build 0
Basic 0
Curvature 0
Models 0
Classification 0
Statements 0
All 0
Probe 0
Audit 0
```

- **Package build:** `cd release && lake build` — exit 0, 9013 jobs
  (`longrun/d7cn-logs/lake_build.log`).
- **Per-file gate:** `lake env lean release/Poincare/D7/Canonical/<File>.lean` from the
  worktree root — all eight files exit 0 (`exit_codes.txt`, per-file `.out`/`.err`).
- **Forbidden scan** (`input/d5-tools/scan_forbidden.py`, comment/string-aware):
  8 Lean files scanned, **hard 0, soft 0** (`forbidden-scan.json`).
- **Axiom audit:** `#print axioms` on 95 declarations (`axioms-print.out`); cones
  `{}` × 11, `{propext}` × 2, `{propext, Classical.choice, Quot.sound}` × 82;
  **nonstandard 0** (`axioms.json`).
- **Source integrity:** 237 files compared with `../D7-gh-compactness`;
  **changed 0, removed 0, added outside the new directory 0** (`source-integrity.json`).

## 6. Missing inputs and blockers

The full theorem needs, and `perelmanCanonicalNeighborhoodDependencies` names (length 12, all
names/reasons nonempty): PCN-1 smooth Riemannian 3-manifold; PCN-2 Ricci flow and the
parabolic neighborhood; PCN-3 `Rm ≥ -r₀⁻²`; PCN-4 `R ≥ r₀⁻²`; PCN-5 κ-noncollapsing;
PCN-6 ancient κ-solution classification; PCN-7 ε-neck smooth closeness; PCN-8 ε-cap smooth
closeness; PCN-9 compact positively curved models; PCN-10 blow-up and pointed GH compactness;
PCN-11 the quantitative scale `r₀(ε, κ)`; PCN-12 surgery-scale consistency.

Named blockers (`perelmanCanonicalNeighborhoodBlockers`, length 6): `B-D7-CN-MANIFOLD`,
`B-D7-CN-CURVATURE`, `B-D7-CN-NONCOLLAPSING`, `B-D7-CN-ANCIENT`,
`B-D7-CN-SMOOTH-CLOSENESS`, `B-D7-CN-QUANTITATIVE`.

## 7. Honest boundary

- No smooth Riemannian 3-manifold, Ricci flow, parabolic neighborhood, curvature tensor,
  injectivity radius, volume comparison or ancient-solution theory is constructed.
- The model interfaces capture the metric-shadow features of the round cylinder, cap and
  sphere, not the smooth round models; the concrete witnesses are a line and two intervals,
  and they inhabit the interface field systems, not the round geometry.
- `CurvatureScaleDatum` is an algebraic normalization over the D7 curvature layer, not the
  curvature of the region.
- `MetricNoncollapsing` is a metric shadow of κ-noncollapsing, not the volume noncollapsing
  theorem.
- `missingPerelmanCanonicalNeighborhood` is a state-only `Prop`, never asserted as a theorem.
- The classification toy excludes the collapsed model at a positive scale; it does not prove
  the full canonical neighborhood classification.

## 8. Artifacts

| artifact | path |
|---|---|
| verification script | `longrun/d7cn-logs/run_verification.sh` |
| exit codes | `longrun/d7cn-logs/exit_codes.txt` |
| per-file logs | `longrun/d7cn-logs/lean_<File>.out` / `.err` |
| axiom print | `longrun/d7cn-logs/axioms-print.out` |
| axiom summary | `longrun/d7cn-logs/axioms.json` |
| forbidden scan | `longrun/d7cn-logs/forbidden-scan.json` |
| source integrity | `longrun/d7cn-logs/source-integrity.json` |
| package build | `longrun/d7cn-logs/lake_build.log` |
| probe generator | `longrun/d7cn-logs/gen_probe_audit.py` |
| result card | `longrun/results/D7-canonical-neighborhood.md` / `.json` |

TASK_DONE — card: longrun/results/D7-canonical-neighborhood.md
