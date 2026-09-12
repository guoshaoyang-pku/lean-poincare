# D12 — comparison geodesics: nonconstant scalar Jacobi/Riccati comparison and the Bishop–Gromov volume-ratio core

Task: D12-comparison-geodesics · Worktree: D12-comparison-geodesics · Status: **TASK_DONE**
(All intended milestone claims hold; independent acceptance requested. A TASK_DONE card is never a claim of Perelman.)

## 1. What was proved (all kernel-checked, no sorry/axiom/admit)

All declarations live in `release/Poincare/D12/ComparisonGeodesics/`, namespace
`Poincare.D12.ComparisonGeodesics`. Semantic classes are labeled per declaration.

**ODE comparison core — general (unconditional, nonconstant coefficients):**
- `SturmComparison.lean`: `wronskian_deriv` (`W' = (k₂−k₁)u₁u₂`), `wronskian_antitoneOn_of_le`,
  and the **Sturm zero comparison** `sturm_zero_comparison`: if `k₂ ≤ k₁` on `[a,b]`, both
  solve `uᵢ'' + kᵢuᵢ = 0` on `(a,b)`, `u₁ a = u₂ a = 0`, `u₂ b = 0`, `u₂ > 0` on `(a,b)`,
  then `u₁` has a zero in `(a,b)` or `k₁ = k₂` on `(a,b)`. Division-free.
- `RiccatiComparison.lean`: **log-derivative (Riccati) comparison** `logDeriv_le_of_le`:
  `k₂ ≤ k₁` on `[a,b]`, both solutions positive on the closed interval `[a,b]`,
  `ρ₁ a ≤ ρ₂ a ⟹ ρ₁ ≤ ρ₂` on `[a,b]` (integrating-factor proof, no division at zero —
  positivity is on the closed interval, so all denominators are bounded away from 0), plus
  `solution_le_of_initial` / `solution_le_of_same_initial`.
- `SingularRiccati.lean`: **singular Riccati comparison, both directions** —
  `riccati_le_of_singular_normalization` (engine for `m ≤ m̄`: `m' + m²/d + k ≤ 0`, model
  equality, `k̄ ≤ k`, quantitative Euclidean normalization `|m t − d/t| ≤ C` on `(0,t₀]`,
  continuity on `Ioc 0 T`) and the mirrored `riccati_ge_of_singular_normalization`
  (engine for `m̄ ≤ m`). Classical ε-regularization; every division is by `ε > 0`, `s ≥ ε`,
  or `d > 0`.

**Correct interval, initial conditions, no division at zero — including a fixed defect:**
version 1 of the singular comparison combined `ContinuousOn m (Icc 0 T)` with the
Euclidean normalization; that combination is **contradictory** (normalization forces
`m t ≥ d/t − C → +∞`, continuity forces a finite limit). This is proved as
`euclideanNormalizedOn_not_continuousOn_zero`, and v2 states continuity on the correct
domain `Ioc 0 T = (0,T]`. The initial conditions are the *quantitative* Euclidean
normalization (the honest `u 0 = 0, u' 0 = 1` form for C² Jacobi data is the documented
bridge for the Rauch corollary, see §3).

**Volume-ratio consequence — conditional analytic (Bishop–Gromov core):**
`VolumeRatio.lean` separates the ODE comparison from the volume-ratio consequence:
- `areaRatio_antitone_of_logDeriv_le`: `m ≤ m̄` on `(0,T)` with `A, Ā > 0` on `(0,T]`
  ⟹ `A/Ā` antitone on `(0,T]` (pairwise, since `(0,T]` is not convex).
- `radialVolume_pos_of_pos`: `Ā` continuous on `[0,T]`, positive on `(0,T]`
  ⟹ `V̄ r = ∫₀ʳ Ā > 0` on `(0,T]` (compact-min on `[r/2,r]`).
- `volumeRatio_antitone`: `A/Ā` antitone, `Ā > 0` on `(0,T]`, `A 0 = Ā 0 = 0`
  ⟹ `V/V̄` antitone on `(0,T]` — the numerator of `(V/V̄)'` is
  `∫₀ʳ (A r·Ā s − A s·Ā r) ds ≤ 0` pointwise from the ratio antitone.
- `bishopGromovVolumeRatio`: the full chain from the singular Riccati comparison under
  **fully expanded analytic hypotheses** (all listed in §2): for every `0 < r ≤ R ≤ T`,
  `V R / V̄ R ≤ V r / V̄ r`; and the explicit form `bishopGromov_volume_le`:
  `V R ≤ (V̄ R/V̄ r)·V r`.

**Non-vacuity witness — concrete nondegenerate example:**
`ModelEuclidean.lean` proves the Euclidean model `m t = d/t` (with `d : ℕ`, `d ≥ 1`),
`A t = t^d` satisfies **all** hypotheses of `riccati_le_of_singular_normalization`,
`riccati_ge_of_singular_normalization` and `bishopGromovVolumeRatio` with `k = k̄ = 0`,
`C = 0` (`euclidModel_singular_comparison`, `euclidModel_singular_comparison_ge`,
`euclidModel_bishopGromov`), plus the explicit Euclidean volume formula
`euclidModel_volume : V t = t^(d+1)/(d+1)`. Hence none of the comparison theorems is
vacuous.

## 2. Expanded hypotheses and their justification

Every hypothesis of the headline theorems is an analytic image of a standard geometric
hypothesis; none is equivalent to the conclusion (the Euclidean model satisfies all of
them while the conclusion is genuinely informative for non-model data):
- `JacobiSolutionOn`: explicit pointwise `HasDerivAtR` data + `C¹` up to the boundary —
  the standard solution predicate; no regularity is assumed for `k` at all.
- Positivity on the **closed** interval in the regular Riccati comparison — the standard
  no-conjugate-point hypothesis, and exactly what keeps all denominators away from 0.
- `Ioc 0 T`-continuity + Euclidean normalization in the singular comparison — the
  normalization is the quantitative initial condition; continuity at 0 would be
  inconsistent (proved).
- `A, Ā > 0` on `(0,T]`, continuous on `[0,T]`, `A 0 = Ā 0 = 0`, `m = A'/A`, `m̄ = Ā'/Ā`,
  `k̄ ≤ k`, `d > 0`, `0 < t₀ ≤ T`, `C ≥ 0` — the analytic image of: positive geodesic
  spheres before the conjugate radius, area of the radius-0 sphere, radial curvature
  bound `Ric ≥ (n−1)K` (after the Cauchy–Schwarz step), and the Euclidean-tangent
  expansion of the area function.
- Non-vacuity is witnessed (see §1).

## 3. What is still missing (geometric construction, not assumed anywhere)

1. **Geometric bridge** — the identification of the density `A` with the `(n−1)`-volume of
   geodesic spheres: shape-operator Riccati equation `S' + S² + R_γ = 0`,
   Cauchy–Schwarz `tr S² ≥ (tr S)²/(n−1)`, the Euclidean normalization of `tr S/(n−1)`.
   Requires a Riemannian-geometry framework not present in the release package.
2. **Model volume constant** — `V̄ t = ω_{n−1}·∫₀ᵗ j_K^(n−1)`; the sphere-measure constant
   `ω_{n−1}` is not yet located in mathlib; all D12 statements are scale-free ratios so
   the constant cancels.
3. **One-sided Rauch corollaries vs the D10 model `j_K`** (the natural next downstream use
   of `riccati_le/ge_of_singular_normalization` with `d = 1`): missing bridge lemmas are
   (i) `|u t/t − 1| ≤ B t` and `|du t − 1| ≤ B t` from `u 0 = 0, du 0 = 1, |ddu| ≤ B`
   (double mean-value theorem); (ii) `|j_K t/t − 1| ≤ √|K|·t/6` for `K ≥ 0`
   (`abs_sub_sin_le`); (iii) the ε → 0 ratio limit `u ε/j_K ε → 1`. The mirrored singular
   comparison needed for the lower direction is already proved here.
4. **Hyperbolic model normalization** (`K < 0`): a quantitative `|sinh x − x|` bound is not
   yet formalized; spherical/flat suffices for the first corollary.

Exact blocker-closure list: **empty** — no pre-existing named blocker was closed by a
constructor plus a checked downstream use in this task; the fixed vacuity defect was a
self-found statement defect, documented by a proof of the contradiction rather than a
claimed closure.

## 4. Evidence

- **Compile**: `cd release && lake build <7 D12 modules>` — exit 0 ("Build completed
  successfully (2751 jobs)"); `lake build Poincare` (whole library incl. D10) — exit 0
  (8939 jobs). Toolchain `leanprover/lean4:v4.34.0-rc2`, mathlib pinned by
  `lake-manifest.json` (leanprover-community/mathlib @ 7974e751…).
- **Gate repair (attempt 1)**: the dispatcher gate had flagged `ok=false` solely because
  nine leftover ad-hoc probe files in `release/scratch/` (Bisect, Cvt, Cvt2, Cvt4, Cvt5,
  Cvt6, InstTest, MinCheck, Probe — bisection/`#check` experiments) failed the gate's
  per-file `lake env lean` sweep. They were archived **out of the package** to
  `<worktree>/scratch-archive/`; no authored D12 source was weakened or changed.
  Re-verified here, mirroring the gate exactly: `lake build` exit 0 (8957 jobs) and a
  per-file sweep `lake env lean <rel>` over **all 83 `.lean` files under `release/`**
  (excluding `.lake`) — **83/83 exit 0**.
- **Axiom audit (fail-closed, programmatic)**: `tools/d12_axiom_audit.py` — compiles the
  audit module, parses all 59 `#print axioms` reports, whitelist
  `{propext, Classical.choice, Quot.sound}` only, negative control (a `sorry` file is
  required to be flagged), forbidden-token scan. **Result: PASSED** (exit 0), 59/59
  declarations audited, 0 violations.
- **Source hashes** (sha256): see `longrun/results/D12-comparison-geodesics.json`
  (`source_hashes`), including the audit script.
- **Kernel trust**: separate from compilation — the audit gate runs on kernel-reported
  axiom sets, not on trust in the proof text; the vacuity defect was found by semantic
  review, not by the kernel.

## 5. Dependency requests (see `checkpoint.json` / result JSON `next_dependency_requests`)

1. mathlib check for the measure of the Euclidean unit sphere `ω_{n−1}` (for absolute
   model volumes; ratios are scale-free).
2. Any Riemannian-geometry Lean development with exponential map, Jacobi fields
   `J'' + R(J,γ')γ' = 0`, geodesic-sphere measures, and the shape-operator Riccati
   equation — to promote the density-level Bishop–Gromov core to the geometric theorem.
3. D10-side small-`t` bounds for `jacobiSol K`/`jacobiDeriv K` (spherical/flat have
   mathlib support; hyperbolic needs `|sinh x − x|`).

TASK_DONE
