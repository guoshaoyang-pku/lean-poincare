# D7-gh-compactness — pointed Gromov–Hausdorff / Cheeger–Gromov compactness interface

- **Task:** `D7-gh-compactness`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-gh-compactness`
- **Verdict:** `TASK_DONE`
- **Lean:** `4.34.0-rc2` (`6a10ac8c22beadecabdbb0919c2b50214762f91d`)
- **mathlib:** `7974e751bece493b6ff508039423ca9fa2452fa8`
- **New Lean sources:** `release/Poincare/D7/Compactness/` (8 files, 1560 lines, 96 declarations)
- **Verification transcript:** `longrun/d7ghc-logs/`

## 1. Summary

The task asks for a pointed Gromov–Hausdorff / Cheeger–Gromov compactness interface. The
deliverable has three layers.

1. **Definitions.** `GHConvergenceData l X Y` is pointed GH convergence in the
   ε-isometry form: approximation maps `approx i : X i → Y`, distortion bound
   `|dist (approx i x) (approx i y) − dist x y| ≤ ε i`, almost surjectivity, basepoint
   control `dist (approx i pᵢ) p_∞ ≤ ε i`, and `ε i → 0` along an arbitrary filter `l`.
   `GHPrecompactCertificate X` is the hypothesis side of Gromov's pointed precompactness
   theorem: explicit uniform finite ε-nets of the basepoint `R`-balls (with a uniform
   cardinality bound and the basepoint in every net) plus completeness of every member.

2. **Kernel-checked mathematics.**
   - Distortion bounds, basepoint convergence, reflexivity, monotonicity in the error scale
     and in the filter, and composition of two ε-approximations with the triangle
     bookkeeping `ε₁ + 2 ε₂` (`GHConvergenceData.comp`).
   - **Total-boundedness consequences of the certificate fields**: the uniform finite-net
     statement, total boundedness of every basepoint ball and every open ball, compactness
     of every basepoint ball, compactness of *every* closed ball (via the ball about the
     basepoint), properness of every member, and whole-space total boundedness/compactness
     under an explicit diameter bound.
   - **Toy compactness theorem for finite metric-space families by explicit enumeration**:
     a finite-valued sequence has a constant strictly monotone subsequence (pigeonhole:
     the finitely many fibers cover `ℕ`, one is infinite, and an infinite subset of `ℕ` is
     enumerated by `Nat.exists_strictMono_subsequence`); a `Fin n`-indexed family of finite
     pointed spaces satisfies the certificate with nets `Finset.univ` and the uniform bound
     `maxᵢ #(F i)`; and every index sequence has a subsequence GH-converging (with the
     identity approximation data) to one of the family members.

3. **State-only Cheeger–Gromov layer.** `missingCheegerGromovCompactness` fixes the full
   statement for manifold families: bundled geometric hypotheses (dimension, curvature
   radius, injectivity radius, noncollapsing, harmonic bounds) imply the existence of a
   strictly monotone subsequence with both the *checked* metric GH datum and an opaque
   smooth convergence relation `CGConvergesTo`. `missingPointedGHConvergentSubsequence`
   fixes the missing metric extraction (the diagonal argument) from the certificate.
   Checked reductions isolate exactly what is missing: an explicit subsequence datum, or
   the metric extraction plus a uniform smooth upgrade, imply the state-only statement. A
   twelve-entry missing-input ledger and five named blockers record the absent mathematics.

No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs in any authored
file; all 95 audited declarations have standard axiom cones.

## 2. Scaffold

`cp -al ../D7-kappa-noncollapsing-conditional/. .` failed with `EXDEV Invalid cross-device
link` (directories were created, no files linked), so the documented fallback `cp -a` was
used: exit 0, 1365 files. The source-integrity check compares 229 non-`.lake`, non-`longrun`
files against the scaffold: **0 changed, 0 removed, 0 added outside the new directory**.

## 3. New files

| file | lines | decls | role |
|---|---:|---:|---|
| `Basic.lean` | 362 | 19 | `PointedMetricSpace`, `GHConvergenceData`, `GHPrecompactCertificate`, distortion/basepoint lemmas, `refl`/`mono`/`monoFilter`/`comp`, `finiteCompleteSpace` |
| `TotalBounded.lean` | 147 | 12 | total-boundedness, compactness and properness consequences of the certificate fields |
| `ToyCompactness.lean` | 197 | 13 | pigeonhole extraction, explicit finite-family certificate, `toyCompactness_finiteFamily`, finite-family consequences |
| `ManifoldStatements.lean` | 400 | 31 | `ManifoldFamilyHypotheses`, `CheegerGromovConvergenceData`, state-only Props, checked reductions, 12-entry ledger, 5 blockers |
| `Nonvacuity.lean` | 181 | 21 | kernel-checked witnesses on the one-point model and finite one-point families |
| `All.lean` | 30 | 0 | umbrella module |
| `Probe.lean` | 112 | 0 | 81 `#check` API probes |
| `Audit.lean` | 131 | 0 | 95 `#print axioms` commands |

## 4. Main declarations

### 4.1 Pointed metric spaces and GH convergence data (`Basic.lean`)

```lean
structure PointedMetricSpace where
  M : Type u
  inst : PseudoMetricSpace M
  base : M

structure GHConvergenceData {ι : Type v} (l : Filter ι) (X : ι → PointedMetricSpace)
    (Y : PointedMetricSpace) where
  ε : ι → ℝ
  ε_nonneg : ∀ i, 0 ≤ ε i
  ε_tendsto : Tendsto ε l (𝓝 0)
  approx : ∀ i, X i → Y
  distortion : ∀ i (x y : X i), |dist (approx i x) (approx i y) - dist x y| ≤ ε i
  surjective : ∀ i (y : Y), ∃ x : X i, dist y (approx i x) ≤ ε i
  base_dist : ∀ i, dist (approx i (X i).base) Y.base ≤ ε i
```

Checked API: `dist_approx_le`, `dist_le_dist_approx`, `tendsto_abs_distortion`,
`tendsto_base_dist`, `tendsto_approx_base`, `refl`, `mono`, `monoFilter`,
`comp` (scale `ε₁ + 2 ε₂`).

```lean
structure GHPrecompactCertificate {ι : Type v} (X : ι → PointedMetricSpace) where
  netBound : ℝ → ℝ → ℕ
  net : ∀ i, ℝ → ℝ → Finset (X i)
  net_card_le : ∀ i R ε, (net i R ε).card ≤ netBound R ε
  base_mem_net : ∀ i R ε, (X i).base ∈ net i R ε
  net_covers : ∀ i R ε, 0 < ε → ∀ x, dist x (X i).base ≤ R →
    ∃ y ∈ net i R ε, dist x y < ε
  complete : ∀ i, CompleteSpace (X i)
```

### 4.2 Total-boundedness consequences (`TotalBounded.lean`)

| declaration | statement |
|---|---|
| `uniform_finite_net` | one bound `N` works for all members: each basepoint `R`-ball has an `ε`-net of card ≤ `N` |
| `totallyBounded_closedBall` | `TotallyBounded (closedBall (X i).base R)` |
| `totallyBounded_ball` | `TotallyBounded (ball (X i).base R)` |
| `isCompact_closedBall` | completeness + total boundedness ⇒ `IsCompact (closedBall (X i).base R)` |
| `isCompact_closedBall_any` | `IsCompact (closedBall x r)` for every centre, via `closedBall x r ⊆ closedBall p (r + dist x p)` |
| `properSpace` | every member is a `ProperSpace` |
| `totallyBounded_univ_of_bounded` | uniform diameter bound ⇒ whole space totally bounded |
| `compactSpace_of_bounded` | uniform diameter bound ⇒ every member is a `CompactSpace` |

### 4.3 Toy compactness (`ToyCompactness.lean`)

```lean
theorem exists_strictMono_const_of_fin {n : ℕ} (u : ℕ → Fin n) :
    ∃ i : Fin n, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, u (φ k) = i

def finiteFamilyCertificate {n : ℕ} (F : Fin n → PointedMetricSpace) [∀ i, Fintype (F i)] :
    GHPrecompactCertificate F
  -- netBound = max_i #(F i), net = Finset.univ

theorem toyCompactness_finiteFamily {n : ℕ} (F : Fin n → PointedMetricSpace)
    [∀ i, Fintype (F i)] (u : ℕ → Fin n) :
    ∃ i : Fin n, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Nonempty (GHConvergenceData atTop (fun k => F (u (φ k))) (F i))
```

`toyCompactnessData` is the constructive `Σ` form returning the index, the strictly monotone
subsequence and the GH data. Finite-family corollaries: `finiteFamily_totallyBounded`,
`finiteFamily_isCompact_closedBall`, `finiteFamily_properSpace`,
`totallyBounded_univ_of_fintype`, `compactSpace_of_fintype`, `toyCompactness_const`.

### 4.4 State-only Cheeger–Gromov statements (`ManifoldStatements.lean`)

```lean
structure ManifoldFamilyHypotheses (ι : Type v) where
  dim : ℕ; dim_pos : 0 < dim
  curvatureRadius : ℝ; curvatureRadius_pos : 0 < curvatureRadius
  injectivityRadius : ℝ; injectivityRadius_pos : 0 < injectivityRadius
  noncollapsed : Prop
  harmonicBounds : Prop

def missingPointedGHConvergentSubsequence (X : ℕ → PointedMetricSpace.{u}) : Prop :=
  ∀ _Cert : GHPrecompactCertificate X,
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ Y : PointedMetricSpace.{u}, Nonempty (GHConvergenceData atTop (fun k => X (φ k)) Y)

def missingCheegerGromovCompactness (X : ℕ → PointedMetricSpace.{u})
    (H : ManifoldFamilyHypotheses ℕ)
    (CGConvergesTo : (ℕ → PointedMetricSpace.{u}) → PointedMetricSpace.{u} → Prop) : Prop :=
  H.noncollapsed → H.harmonicBounds →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Y : PointedMetricSpace.{u},
      Nonempty (GHConvergenceData atTop (fun k => X (φ k)) Y) ∧
        CGConvergesTo (fun k => X (φ k)) Y
```

Checked reductions: `ghSubsequence_of_cheegerGromov`, `smoothPart_of_cheegerGromov`,
`cheegerGromov_of_ghSubsequence`,
`cheegerGromov_of_ghPrecompact_and_smoothUpgrade` (the two missing inputs are exactly the
metric extraction and the uniform smooth upgrade),
`cheegerGromovConclusion_of_finiteFamily` (the toy theorem supplies the metric half on a
finite family), and `totallyBounded_of_precompactCertificate`.

### 4.5 Non-vacuity (`Nonvacuity.lean`)

The one-point model (`M = PUnit`) witnesses every structure: `unitFamilyPrecompact`,
`unitFamilyGHData`, `unitFamilyComp`, `unitFamilyMonoFilter`, `unitFamily_totallyBounded`,
`unitFamily_isCompact_closedBall`, `unitFamily_properSpace`, `unitFamily_compactSpace`,
`unitManifoldHypotheses`. The state-only statements are instantiated with the smooth
relation `True`: `unitCheegerGromovConclusion`, `missingCheegerGromovCompactness_unit`,
`missingPointedGHConvergentSubsequence_unit`. Finite one-point families witness
`unitFinFamilyCertificate`, `unitFinFamily_toyCompactness`, `unitFinFamily_cheegerGromov`
and the pigeonhole witness lemmas.

## 5. Verification transcript

`bash longrun/d7ghc-logs/run_verification.sh` (reproducible):

```
lake_build 0
Basic 0
TotalBounded 0
ToyCompactness 0
ManifoldStatements 0
Nonvacuity 0
All 0
Probe 0
Audit 0
```

- **Package build:** `cd release && lake build` — exit 0, 9005 jobs
  (`longrun/d7ghc-logs/lake_build.log`).
- **Per-file gate:** `lake env lean release/Poincare/D7/Compactness/<File>.lean` — all
  eight files exit 0 (`exit_codes.txt`, per-file `.out`/`.err`).
- **Forbidden scan** (`input/d5-tools/scan_forbidden.py`, comment/string-aware):
  8 Lean files scanned, **hard 0, soft 0** (`forbidden-scan.json`).
- **Axiom audit:** `#print axioms` on 95 declarations; cones
  `{propext, Classical.choice, Quot.sound}` × 83, `{}` × 10, `{propext}` × 2;
  **nonstandard 0** (`axioms.json`, `axioms-print.out`).
- **Source integrity:** 229 files compared with `../D7-kappa-noncollapsing-conditional`;
  **changed 0, removed 0, added outside the new directory 0**
  (`source-integrity.json`).

## 6. Missing inputs and blockers

The full Cheeger–Gromov theorem needs, and this development names in
`cheegerGromovDependencies` (length 12, all names/reasons nonempty):

CGH-1 pointed Riemannian manifold family; CGH-2 Riemann curvature tensor and bounds;
CGH-3 injectivity radius; CGH-4 Cheeger noncollapsing; CGH-5 harmonic coordinates;
CGH-6 elliptic regularity and a priori bounds; CGH-7 Sobolev embedding and Arzelà–Ascoli;
CGH-8 smooth Cheeger–Gromov convergence relation; CGH-9 pointed GH convergence and its
distance; CGH-10 Gromov precompactness and diagonal extraction; CGH-11 limit manifold and
inherited bounds; CGH-12 smoothness of the limit metric.

Named blockers (`cheegerGromovBlockers`, length 5): `B-D7-GHC-CURVATURE`,
`B-D7-GHC-HARMONIC`, `B-D7-GHC-INJECTIVITY`, `B-D7-GHC-SMOOTH`,
`B-D7-GHC-GH-SUBSEQUENCE`.

## 7. Honest boundary

- No Riemannian manifold, curvature tensor, injectivity radius, harmonic coordinate atlas
  or elliptic regularity estimate is constructed.
- The smooth Cheeger–Gromov convergence relation `CGConvergesTo` is an opaque parameter.
- `missingCheegerGromovCompactness` and `missingPointedGHConvergentSubsequence` are
  state-only `Prop`s, never asserted as theorems.
- The metric diagonal extraction is not proved; only its finite-family toy case is.
- `GHConvergenceData` is the ε-isometry definition; its equivalence with a pointed GH
  distance and the completeness of the limit are not formalized.
- The total-boundedness consequences are conditional on the certificate fields; no family
  of genuine manifolds is certified.
- The toy compactness theorem covers finite families by pigeonhole, not infinite families.

## 8. Artifacts

| artifact | path |
|---|---|
| verification script | `longrun/d7ghc-logs/run_verification.sh` |
| exit codes | `longrun/d7ghc-logs/exit_codes.txt` |
| per-file logs | `longrun/d7ghc-logs/lean_<File>.out` / `.err` |
| axiom print | `longrun/d7ghc-logs/axioms-print.out` |
| axiom summary | `longrun/d7ghc-logs/axioms.json` |
| forbidden scan | `longrun/d7ghc-logs/forbidden-scan.json` |
| source integrity | `longrun/d7ghc-logs/source-integrity.json` |
| package build | `longrun/d7ghc-logs/lake_build.log` |
| result card | `longrun/results/D7-gh-compactness.md` / `.json` |

TASK_DONE — card: longrun/results/D7-gh-compactness.md
