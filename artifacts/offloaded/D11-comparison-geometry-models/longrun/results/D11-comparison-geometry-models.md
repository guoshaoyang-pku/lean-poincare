# D11 — Comparison geometry of the constant-curvature model spaces

**Task id:** `D11-comparison-geometry-models`
**Verdict:** **COMPLETE — UNCONDITIONAL.** The three constant-curvature model metrics in polar
form `dr² + j_K(r)² g_{S^{n-1}}` (with the D10 Jacobi solutions `j_K`), the warped-product
metric axioms (reduced to the D10 ODE conditions), the Bishop–Gromov volume comparison at the
ODE level (proved by a derivative sign computation), and the Laplacian comparison in the model
case (explicit radial computation) are all proved in Lean with no `sorry`, no `axiom`, no
`unsafe`, no `native_decide`, no `proof_wanted`, and with kernel axiom cone exactly
`[propext, Classical.choice, Quot.sound]` for every audited declaration.

- **Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-comparison-geometry-models`
- **New Lean files:** `release/Poincare/D11/ComparisonModels/{Basic,ModelMetrics,BishopGromov,LaplacianComparison,AxiomAudit}.lean` (nothing else added or modified)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (`release/lean-toolchain`)
- **mathlib:** `leanprover-community/mathlib4` @ `7974e751bece493b6ff508039423ca9fa2452fa8` (`release/lake-manifest.json`)
- **Date:** 2026-09-11

## 1. Deliverables

| file | lines | declarations | sha256 |
| --- | ---: | ---: | --- |
| `release/Poincare/D11/ComparisonModels/Basic.lean` | 92 | 9 | `14983169904b074a8e0dbaa0b9f68cfc750a635f4bbdf8c7f604d39f30a78b23` |
| `release/Poincare/D11/ComparisonModels/ModelMetrics.lean` | 264 | 25 | `43252554c0f67c58877c8c620c172c61c66df31dcbed0d6dc359447f08e3e162` |
| `release/Poincare/D11/ComparisonModels/BishopGromov.lean` | 416 | 17 | `b63439edab98ebf204ce3c39596a0886453f78034ce34fba0740f54788b3560e` |
| `release/Poincare/D11/ComparisonModels/LaplacianComparison.lean` | 174 | 9 | `3a295d248f6fb8021681a8bab2d7d0c4eba72b83ded188738be0932914b25785` |
| `release/Poincare/D11/ComparisonModels/AxiomAudit.lean` | 84 | 0 (60 `#print axioms` queries) | `4048927985624a3846f3638b00671afea697a7b918008b0d2b15995a0e96e34c` |

All declarations live in namespace `Poincare.D11`.

## 2. Requirement 1 — the three model metrics in polar form; axiom reduction to D10

`ModelMetrics.lean` defines the polar (warped-product) metric form on the tangent space
`ℝ × EuclideanSpace ℝ (Fin (n-1))` at radius `r` (the round metric of `S^{n-1}` is represented
by the Euclidean inner product):

```lean
def polarMetric (n : ℕ) (j : ℝ → ℝ) (r : ℝ) (u v : ℝ × EuclideanSpace ℝ (Fin (n - 1))) : ℝ :=
  u.1 * v.1 + j r ^ 2 * inner ℝ u.2 v.2
```

and the three model metrics by inserting the D10 Jacobi solutions as the warping function:

| space form | warp `j_K` | metric |
| --- | --- | --- |
| spherical (`K > 0`) | `jacobiSolSphere K r = sin (√K r)/√K` | `modelSphereMetric n K r` |
| Euclidean (`K = 0`) | `jacobiSolFlat r = r` | `modelFlatMetric n r` |
| hyperbolic (`K < 0`) | `jacobiSolHyperbolic K r = sinh (√(-K) r)/√(-K)` | `modelHyperbolicMetric n K r` |

The **algebraic warped-product metric axioms** are proved for every warp `j`:
`polarMetric_symm`, `polarMetric_add_left/right`, `polarMetric_smul_left/right`,
`polarMetric_nonneg`, and positive definiteness off the pole
`polarMetric_pos_of_pos : j r ≠ 0 → v ≠ 0 → 0 < polarMetric n j r v v`.

The **analytic axioms of a constant-curvature model space** are bundled as

```lean
structure WarpedProductModel (K : ℝ) (j : ℝ → ℝ) : Prop where
  initial : Poincare.D10.HasNormalizedInitial j     -- j 0 = 0 ∧ j' 0 = 1
  solves_ode : Poincare.D10.SolvesJacobiODE K j     -- ∀ t, j'' t + K·j t = 0
```

and the verification **reduces literally to the D10 ODE theorems**:

```lean
theorem warpedProductModel_jacobiSolSphere {K : ℝ} (hK : 0 < K) :
    WarpedProductModel K (Poincare.D10.jacobiSolSphere K) :=
  ⟨Poincare.D10.jacobiSolSphere_hasNormalizedInitial hK, Poincare.D10.jacobiSolSphere_solvesJacobiODE hK⟩

theorem warpedProductModel_jacobiSolFlat : WarpedProductModel 0 Poincare.D10.jacobiSolFlat :=
  ⟨Poincare.D10.jacobiSolFlat_hasNormalizedInitial, Poincare.D10.jacobiSolFlat_solvesJacobiODE⟩

theorem warpedProductModel_jacobiSolHyperbolic {K : ℝ} (hK : K < 0) :
    WarpedProductModel K (Poincare.D10.jacobiSolHyperbolic K) :=
  ⟨Poincare.D10.jacobiSolHyperbolic_hasNormalizedInitial hK, Poincare.D10.jacobiSolHyperbolic_solvesJacobiODE hK⟩

theorem warpedProductModel_jacobiSol (K : ℝ) : WarpedProductModel K (Poincare.D10.jacobiSol K) :=
  ⟨Poincare.D10.jacobiSol_hasNormalizedInitial K, Poincare.D10.jacobiSol_solvesJacobiODE K⟩
```

The proof terms are *exactly* the D10 `_hasNormalizedInitial` and `_solvesJacobiODE` lemmas —
the constant-curvature axiom `j'' + K·j = 0` with `j 0 = 0`, `j' 0 = 1` is the D10 Jacobi ODE,
so the axiom verification reduces to what D10 already proved.  Positive definiteness of each
model metric on its domain (before the first conjugate point `π/√K` for `K > 0`, everywhere
for `K ≤ 0`) is proved from the D10 sign lemmas (`jacobiSolSphere_pos`) via
`modelSphereMetric_posDef`, `modelFlatMetric_posDef`, `modelHyperbolicMetric_posDef` and the
bundled `polarMetric_jacobiSol_posDef`.

**Status: fully proved, unconditional.**

## 3. Requirement 2 — Bishop–Gromov volume comparison at the ODE level

`BishopGromov.lean` proves: for `K₂ ≤ K₁` the ratio of model ball volumes

`r ↦ V_{K₁}(r) / V_{K₂}(r)`,   `V_K(r) = ∫₀^r j_K(t)^(n-1) dt`   (`ballVolume n K r`),

is **monotone non-increasing**, by a real-analytic **derivative sign computation** in four
steps:

1. **Wronskian sign** (`wronskian_deriv`, `wronskian_le_zero`): for `W = j₁'·j₂ - j₁·j₂'` the
   D10 Jacobi ODE gives `W' = (K₂ - K₁)·j₁·j₂ ≤ 0` with `W 0 = 0`, hence `W ≤ 0`
   (via `antitoneOn_of_deriv_nonpos` on `[0, t]`).
2. **Ratio monotonicity** (`jacobiSol_div_antitoneOn`): `(j₁/j₂)' = W/j₂² ≤ 0`, so `j₁/j₂`
   is antitone; in denominator-free form (`jacobiSol_mul_le_mul_of_le`):

   `0 ≤ t ≤ r`, `r` before the first zero of `j_{K₁}`  ⟹  `j₁(r)·j₂(t) ≤ j₁(t)·j₂(r)`.

3. **Integral estimate** (`ballVolume_ge_jacobiSol_pow`): raising to the `(n-1)`-th power
   (`pow_le_pow_left₀`, both sides nonnegative) and integrating over `[0, r]`
   (`intervalIntegral.integral_mono_on`):

   `j₁(r)^(n-1) · V₂(r) ≤ V₁(r) · j₂(r)^(n-1)`.

4. **Derivative sign of the ratio** (`ballVolume_ratio_deriv_nonpos`): by the fundamental
   theorem of calculus (`intervalIntegral.integral_hasDerivAt_right`),
   `V_K'(r) = j_K(r)^(n-1)`, hence

   `(V₁/V₂)' = (j₁^(n-1)·V₂ - V₁·j₂^(n-1)) / V₂² ≤ 0`.

**Headline statement** (including the endpoint `r₂ = π/√K₁`, where the ball is the whole
sphere; the closed convex interval `[r₁, r₂]` is fed to `antitoneOn_of_deriv_nonpos`, so no
limit argument at the pole is needed):

```lean
theorem bishopGromov_volume_comparison {n : ℕ} {K₁ K₂ : ℝ} (hK : K₂ ≤ K₁) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂) (hdom : 0 < K₁ → r₂ ≤ Real.pi / Real.sqrt K₁) :
    ballVolume n K₁ r₂ / ballVolume n K₂ r₂ ≤ ballVolume n K₁ r₁ / ballVolume n K₂ r₁
```

with the specialisations `bishopGromov_volume_comparison_sphere` (`K₁ > 0`, first zero
`π/√K₁` explicit) and `bishopGromov_volume_comparison_of_nonpos` (`K₁ ≤ 0`, no restriction),
plus the region form `ballVolume_ratio_antitoneOn` on `(0, r₀)`.

**Status: fully proved, unconditional — no comparison theorem is assumed; the only input is
the D10 ODE verification.** (The sphere factor `ω_{n-1}` cancels in the ratio, so the
unnormalised `ballVolume` is the honest ODE-level statement.)

## 4. Requirement 3 — Laplacian comparison in the model case

`LaplacianComparison.lean` defines the warped-product radial Laplacian and its divergence
form, and proves their equivalence by explicit differentiation
(`divergenceLaplacian_eq_radialLaplacian`, dimension `2 ≤ n`):

`Δ f = f'' + (n-1)(j'/j)f' = j^{-(n-1)} (j^{n-1} f')'`.

The **explicit radial computation** of the Laplacian of the distance function
(`radialLaplacian_id`, `radialLaplacian_id_jacobiSol`, `divergenceLaplacian_id_jacobiSol`):

`Δ r = (n-1) · j_K'(r) / j_K(r) = (n-1) · jacobiDeriv K r / jacobiSol K r`

(for each of the three explicit D10 branches).  The model-case **Laplacian comparison** then
holds with equality, hence unconditionally:

```lean
theorem laplacianComparison_model {n : ℕ} {K r : ℝ} :
    radialLaplacian n (Poincare.D10.jacobiSol K) id r ≤
      ((n - 1 : ℕ) : ℝ) * Poincare.D10.jacobiDeriv K r / Poincare.D10.jacobiSol K r :=
  le_of_eq radialLaplacian_id_jacobiSol
```

(the model case is the sharp case of the classical bound `Δr ≤ (n-1) j_K'/j_K`; on the
genuine domain `0 < r < π/√K` the right-hand side is the actual model value since
`j_K(r) > 0` there).  The cross-model comparison, proved from the Wronskian sign of
`BishopGromov.lean`, records that `Δ_K r` is antitone in the curvature:

```lean
theorem radialLaplacian_id_le_of_le {n : ℕ} {K₁ K₂ : ℝ} (hK : K₂ ≤ K₁) {r : ℝ} (hr : 0 < r)
    (hdom : 0 < K₁ → r < Real.pi / Real.sqrt K₁) :
    radialLaplacian n (Poincare.D10.jacobiSol K₁) id r ≤ radialLaplacian n (Poincare.D10.jacobiSol K₂) id r

theorem laplacianComparison_jacobiDeriv {n : ℕ} {K₁ K₂ : ℝ} (hK : K₂ ≤ K₁) {r : ℝ} (hr : 0 < r)
    (hdom : 0 < K₁ → r < Real.pi / Real.sqrt K₁) :
    ((n - 1 : ℕ) : ℝ) * Poincare.D10.jacobiDeriv K₁ r / Poincare.D10.jacobiSol K₁ r ≤
      ((n - 1 : ℕ) : ℝ) * Poincare.D10.jacobiDeriv K₂ r / Poincare.D10.jacobiSol K₂ r
```

**Status: fully proved, unconditional explicit radial computation** (the cross-model
comparison carries exactly the natural domain hypothesis `r` before the first zero of
`j_{K₁}`).

## 5. Requirement 4 — kernel axiom audit

`AxiomAudit.lean` issues **60** `#print axioms` queries covering every definition and
headline theorem of the four modules.  Full log: `logs/d11_AxiomAudit.log`.  Every query
prints exactly

```
'Poincare.D11.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Representative lines (all 60 are in the log):

```
'Poincare.D11.polarMetric' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D11.warpedProductModel_jacobiSol' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D11.wronskian_le_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D11.jacobiSol_div_antitoneOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D11.bishopGromov_volume_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D11.ballVolume_ratio_deriv_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D11.radialLaplacian_id_jacobiSol' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D11.laplacianComparison_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D11.radialLaplacian_id_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- 60 / 60 audited declarations print exactly `[propext, Classical.choice, Quot.sound]`;
- no audit line mentions `sorryAx`, `native_decide`, or any unapproved axiom;
- `Classical.choice` is expected (the D10 `jacobiSol` uses a classical `if`, and
  `Real.sqrt`, `deriv`, interval integrals are classical).

## 6. Compilation evidence

| command (run in worktree root) | exit | log |
| --- | ---: | --- |
| `lake build Poincare.D11.ComparisonModels.AxiomAudit` | 0 | `logs/d11_build_all.log` — 2764 jobs, no diagnostics |
| `lake build Poincare` (whole library, incl. D1–D10) | 0 | `logs/d11_build_Poincare.log` — 9153 jobs, no errors |
| `lake env lean release/Poincare/D11/ComparisonModels/Basic.lean` | 0 | silent |
| `lake env lean release/Poincare/D11/ComparisonModels/ModelMetrics.lean` | 0 | silent |
| `lake env lean release/Poincare/D11/ComparisonModels/BishopGromov.lean` | 0 | silent |
| `lake env lean release/Poincare/D11/ComparisonModels/LaplacianComparison.lean` | 0 | silent |
| `lake env lean release/Poincare/D11/ComparisonModels/AxiomAudit.lean` | 0 | `logs/d11_AxiomAudit.log` — 60 axiom lines |
| compile gate: `lake env lean <file>` for **every** `.lean` under `release/Poincare/` (274 files), cwd = worktree root | 0 for all 274 | `logs/gate_full.log` ends in `GATE_OK=274 GATE_FAIL=0` |

## 7. Forbidden-token scan

A scanner (block comments and `--` comments stripped, so only code counts) searched the five
authored files for `sorry`, `admit`, `sorryAx`, `axiom` declarations, `unsafe`,
`native_decide`, `proof_wanted`, `set_option maxHeartbeats`:

```
FILES_SCANNED=5 TOTAL_HITS=0
```

The raw text contains the word "axioms" only inside the 60 `#print axioms` queries of
`AxiomAudit.lean` and in docstrings (which are kernel queries, not assumptions).

## 8. Honest scope / non-claims

- This card formalises the **model spaces at the ODE level** exactly as requested: the polar
  warped-product metrics with the D10 Jacobi solutions, the axiom reduction to the D10 ODE
  verification, the Bishop–Gromov monotonicity of the *model–model* volume ratio, and the
  Laplacian comparison in the model case.
- `vol(B_K(r))` is the unnormalised ODE volume `∫₀^r j_K(t)^(n-1) dt`; the sphere factor
  `ω_{n-1}` cancels in every ratio and is not formalised (no intrinsic `n`-volume of
  `S^{n-1}` is needed for the statements).
- The Bishop–Gromov statement is the model–model comparison `K₂ ≤ K₁` (the manifold-side
  model `V_{K₁}` against the comparison model `V_{K₂}`); a manifold-level Bishop–Gromov
  theorem (Ric ≥ (n-1)K on a Riemannian manifold) is not claimed — no Riemannian-manifold
  API exists in this codebase yet, and the card explicitly asks for the ODE level.
- The Laplacian `Δ` here is the *radial* Laplacian of the warped metric acting on radial
  functions (the standard warped-product formula); a full intrinsic Laplacian on
  `M_K` is equivalent to it on radial functions and is not separately formalised.
- The comparison is non-strict (`≤`).  Strict versions are not claimed.
- The Bishop–Gromov restriction `r₂ ≤ π/√K₁` (first zero of the larger-curvature field) is
  optimal in the same sense as in D10: beyond it the spherical model ball ceases to be a
  geodesic ball.

## 9. Reproduction

```bash
export ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-comparison-geometry-models
lake build Poincare.D11.ComparisonModels.AxiomAudit                 # exit 0
lake env lean release/Poincare/D11/ComparisonModels/Basic.lean              # exit 0
lake env lean release/Poincare/D11/ComparisonModels/ModelMetrics.lean       # exit 0
lake env lean release/Poincare/D11/ComparisonModels/BishopGromov.lean       # exit 0
lake env lean release/Poincare/D11/ComparisonModels/LaplacianComparison.lean # exit 0
lake env lean release/Poincare/D11/ComparisonModels/AxiomAudit.lean         # exit 0, 60 axiom lines
```

## 10. Environment note — build infrastructure

The dispatcher's compile gate (`lake env lean <abs-file>`, cwd = worktree root) initially
failed before any Lean source was reached: Lake looks for `lake-manifest.json` next to the
workspace `lakefile.toml` (the worktree root), and only `release/lake-manifest.json` was
present, so Lake attempted a fresh manifest and a network `curl` (blocked).  The fix is
infrastructure-only: `cp release/lake-manifest.json lake-manifest.json` (the root `.lake`
symlink already points at `release/.lake`, which contains the prebuilt mathlib package
store).  No `.lean` source was modified by this, and the five authored-file hashes in §1 are
those of the final sources.

TASK_DONE — `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-comparison-geometry-models/longrun/results/D11-comparison-geometry-models.md`
