# D12-kappa-variational — result card

**Task id:** `D12-kappa-variational`
**Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D12-kappa-variational`
**Toolchain:** `leanprover/lean4:v4.34.0-rc2` (commit `6a10ac8c22be`); mathlib
`7974e751bece493b6ff508039423ca9fa2452fa8`
**Verdict:** `TASK_DONE` — a real curve-energy bound/minimizer **and** the Gaussian
reduced-volume normalization are proved over genuine curve/function spaces, with the required
model/conditional/general separation, downstream use in the D7 certificate/κ layer, and a
fail-closed axiom audit. No canonical-neighbourhood or ancient-solution claim is made.

**Not claimed:** no manifold Ricci flow, no general `L`-minimiser existence, no Jacobian
comparison, no reduced-length differential inequality, no ball-volume comparison, no ancient
solution classification, and no Perelman/Poincaré content beyond the explicitly stated
model-space and conditional-transfer results below.

---

## 0. Bottom line

| item | result |
| --- | --- |
| new files (only under `release/Poincare/D12/KappaVariational/`) | **6 Lean files, 66 principal declarations** |
| compiled with `lake env lean` from `release/` (worktree has no root Lake wrapper) | **6/6 exit 0** |
| whole release package `lake build` (fresh, from `release/`) | **exit 0** (9179 jobs) |
| `#print axioms` + programmatic fail-closed audit | **66/66 declarations**; cones `{propext, Classical.choice, Quot.sound}` (63), `{}` (3); **0 nonstandard** |
| fail-closed negative control | project axiom detected, audit exit 1 (as required) |
| forbidden-token scan (comment/string-aware) | **0 hard hits, 0 soft hits** |
| Gaussian reduced-volume normalization | `gaussianReducedVolume_eq_one`: `Ṽ(τ) = ∫ (4πτ)^{-n/2} exp(-‖q‖²/(4τ)) dq = 1` on `ℝⁿ` with Lebesgue measure, all `τ > 0` |
| reduced-length reading | `gaussianReducedVolumeViaL_eq_one`: the same with `exp(-l(q,τ))`, `l(q,τ) = ‖q‖²/(4τ)` (D7 reduced length) |
| constant-curvature curve-energy bound | `constantCurvature_length_le`: `L(P) ≥ ‖q‖²/(2√τ) + (2/3) R₀ τ^{3/2}` for **every** admissible path, `R₀ ≥ 0`, equality for the straight line |
| constant-curvature minimizer | `constantCurvature_isLMinimizer`, `constantCurvatureLMinimizerExistence` (D7 state-only `Prop` proved for the whole `R₀ ≥ 0` family) |
| reduced-length bound with curvature | `constantCurvature_reducedLength_le`: `l(q,τ) ≥ ‖q‖²/(4τ) + (R₀/3) τ`, attained |
| conditional transfer | `gaussianReducedVolumeCertificate` (D7 `ReducedVolumeCertificate`, volume ≡ 1), consumed by `D7.Kappa.uniformReducedVolumeLowerBound`; `gaussianKappaNoncollapsing_of_ballVolumeComparison` |
| named blockers closed | 3 closure records (`rlv10Closure`, `ncf12ModelClosure`, `rlv1ModelClosure`), each with constructor + downstream use |
| remaining named inputs | 13-entry ledger `kappaVariationalRemainingDependencies` (kernel-checked length + naming) |

---

## 1. Source integrity, environment, files

The snapshot had **no root Lake workspace**: everything is built from `release/`
(`release/lakefile.toml`, `release/lean-toolchain`). The full `lake build` was re-run fresh
(exit 0, 9179 jobs) before relying on any prebuilt dependency.

| file | lines | decls | sha256 | role |
| --- | --- | --- | --- | --- |
| `GaussianNormalization.lean` | 296 | 26 | `6faabbf56e991f9c50fe5ca38656bebe430c4b534455b2e4ce4c02cd30fd94b0` | Gaussian reduced-volume normalization on `ℝⁿ` (Lebesgue) |
| `CurvatureEnergy.lean` | 303 | 17 | `f207c06e42ecc09a73e1d93cc69e5c0482e0419dd54730fa8c47e116bbc37268` | constant-curvature `L`-length bound and minimizer |
| `Transfer.lean` | 150 | 9 | `748a4e98be9318cf202f238a3dd32f78609f5c2a4e8c287e10e7d3305bcc0a69` | certificate instance + conditional transfer |
| `Statements.lean` | 207 | 14 | `106a854a9d5881ae24701a6c4788a3036bd2d9756cba23049240f493bf3dd7d7` | closure records, κ-reduction, 13-entry ledger |
| `Audit.lean` | 145 | 0 | `6bb8ecd91658e2092849127bd1efbdfc33c41d3a62bc95bbca6ccca5d96a0534` | task-local audit module (66 `#print axioms`) |
| `All.lean` | 18 | 0 | `dc081213f9e4a5dbecb0ba8b210d689c450691db5cc2ea75fdd9ee6a6997c83b` | umbrella |

Namespace: `Poincare.D12.KappaVariational`. Dependencies: `Poincare.D10.GaussianToolbox`
(`integral_gaussianKernel`, Fubini), `Poincare.D7.Reduced` (interface, `gaussian_length_le`,
`gaussian_reducedLengthAlong`), `Poincare.D7.Kappa` (`uniformReducedVolumeLowerBound`,
`kappaNoncollapsing_of_entropy_and_volumeComparison`), mathlib (`integral_rpow`, Fubini,
`PiLp.volume_preserving_toLp`, `EuclideanSpace.norm_sq_eq`, `Real.pi_gt_three`). No D11
ReducedVolume module exists in this snapshot (only `D11/HeatKernelBridge`); D7 Reduced/Kappa and
D10 GaussianToolbox are the relevant sources, all read.

---

## 2. Model-space calculation A — Gaussian reduced-volume normalization (`GaussianNormalization`)

**Geometric assumptions (all explicit):** the function space is `L¹` over
`EuclideanSpace ℝ (Fin n)` with Lebesgue measure (the honest reduced-volume integration
space); the dimension `n` and the backward time `τ > 0` are the only parameters; the density is
the explicit Gaussian `(4πτ)^{-n/2} exp(-‖q‖²/(4τ))`.

| declaration | statement |
| --- | --- |
| `integral_gaussianKernel_tau` | `∫ t, exp (-(t²/(4τ))) = √(4πτ)` for `τ > 0` (D10 scaling law at `a = 1/(4τ)`) |
| `integral_gaussianVecTau` / `…_eq_rpow` | `∫ x : Fin n → ℝ, ∏ᵢ exp (-(xᵢ²/(4τ))) = (√(4πτ))ⁿ = (4πτ)^{n/2}` (Fubini) |
| `integral_gaussianVecTauNormalized` | **total mass 1** of `(4πτ)^{-n/2} ∏ᵢ exp (-(xᵢ²/(4τ)))` |
| `integral_exp_neg_normSq_div` | `∫ x : ℝⁿ, exp (-‖x‖²/(4τ)) = (4πτ)^{n/2}` (Euclidean-norm form; the measure transfer through `PiLp.volume_preserving_toLp` is explicit) |
| `gaussianReducedVolume_eq_one` | **`Ṽ(τ) = ∫ (4πτ)^{-n/2} exp (-‖q‖²/(4τ)) dq = 1`** for all `τ > 0` |
| `gaussianReducedVolumeViaL_eq_one` | the same integral written as `∫ (4πτ)^{-n/2} exp (-l(q,τ)) dq` with the D7 reduced length `l(q,τ) = ‖q‖²/(4τ)` |
| `gaussianReducedVolumeDensity_pos` / `_ne_zero` | the density is a positive, non-vanishing function (no zero operator) |
| `gaussianReducedVolumeDensity_two_half_zero` / `_ne_one` | concrete non-degenerate value `1/(2π)` at `n = 2, τ = 1/2, q = 0`; it is `≠ 1`, so the constant value `1` of the integral is a genuine cancellation |

This closes the named D7 missing input **RLV-10 "Gaussian normalisation"** (continuum form) and
the model half of **NCF-12**. All integrals are Bochner integrals over `ℝⁿ` with Lebesgue
measure; the only external analytic inputs are mathlib's `integral_gaussian` (via D10) and
Fubini.

## 3. Model-space calculation B — constant-curvature curve-energy bound (`CurvatureEnergy`)

**Geometric assumptions (all explicit):** `E = EuclideanSpace ℝ (Fin n)`; metric = Euclidean
inner product (flat); scalar curvature = **constant** `R₀ ≥ 0`; base point `0`; backward time
`τ > 0`; the admissible-path space is the D7 `LPath (constantCurvatureFlow n R₀) 0 q τ`
(curves with explicit endpoint/continuity/differentiability/integrability fields — a real path
space, not a certificate).

| declaration | statement |
| --- | --- |
| `integral_sqrt` | `∫₀^τ √σ dσ = (2/3) τ^{3/2}` (from `integral_rpow`) |
| `constantCurvature_length_le` | **for every admissible path** `P`: `‖q‖²/(2√τ) + (2/3) R₀ τ^{3/2} ≤ L(P)` — the quantitative curve-energy bound with curvature |
| `constantCurvature_LlengthAlong` | the straight line `γ(σ) = (√σ/√τ)•q` has `L(γ) = ‖q‖²/(2√τ) + (2/3) R₀ τ^{3/2}` (equality) |
| `constantCurvature_isLMinimizer` | the straight line is an `IsLMinimizer` |
| `constantCurvature_reducedLength_le` | `l(q,τ) ≥ ‖q‖²/(4τ) + (R₀/3) τ` for every admissible path, with equality for the minimiser (`constantCurvature_reducedLength`) |
| `constantCurvatureLMinimizerExistence` | the D7 state-only `Prop` `LMinimizerExistence` is **proved** for the whole `R₀ ≥ 0` family (non-vacuity beyond `R ≡ 0`) |
| `constantCurvature_reducedLength_mono_in_R0` | the model reduced length is nondecreasing in `R₀` |

The proof reuses the D7 completing-the-square argument (`gaussian_length_le`) through the
explicit path conversion `toGaussianPath`, and adds the path-independent curvature term. This is
the exact model form of the lower estimate for the reduced length used in Perelman's argument;
for `R₀ = 0` it reproduces the D7 Gaussian bound.

## 4. Conditional transfer (`Transfer`, `Statements`)

| declaration | content |
| --- | --- |
| `gaussianReducedVolumeCertificate` | the Gaussian soliton inhabits the D7 `ReducedVolumeCertificate` with `volume ≡ 1`, `derivative ≡ 0` |
| `gaussianReducedVolumeCertificate_volume` | at every `τ > 0` the certificate's volume field equals the actual reduced-volume integral (consumes `gaussianReducedVolume_eq_one` — **downstream use of the normalization**) |
| `gaussianReducedVolumeCertificate_constant_one`, `…_antitoneOn` | the **critical (equality) case** of Perelman monotonicity: volume constant `1` |
| `gaussianUniformReducedVolumeLowerBound` | the D7 Kappa step `uniformReducedVolumeLowerBound` fires with `v₀ = 1` (the uniform bound the κ-assembly needs) |
| `gaussianReducedVolumeDensity_shape` / `_integral` | the continuum density has exactly the D7 Gaussian-weight shape `exp (-(n/2) log (4πτ) - l(q,τ))`, total mass `1` (continuum analogue of the D7 finite critical certificate) |
| `gaussianKappaNoncollapsing_of_ballVolumeComparison` | **checked reduction**: on `EuclideanSpace ℝ (Fin 3)` with Lebesgue measure and trivial curvature predicate, the D7 conditional theorem fires once a `BallVolumeComparison` is supplied — the only remaining input for κ-noncollapsing on this model is the comparison |

## 5. Semantic classification and general statements

* **model-space calculation:** everything in `GaussianNormalization` and `CurvatureEnergy`.
* **conditional transfer:** everything in `Transfer`; `gaussianKappaNoncollapsing_of_ballVolumeComparison`.
* **general theorem / state-only:** `ballVolumeComparisonExists` (NCF-9) and the 13-entry ledger
  `kappaVariationalRemainingDependencies` (KV-1 … KV-13), all named, kernel-checked
  (`…_length = 13`, `…_all_named`). The general full-Perelman statements remain the D7/D3
  state-only `Prop`s; nothing canonical-neighbourhood- or ancient-solution-related is inferred.

## 6. Exact blockers closed (constructor + downstream use, kernel-checked)

| input | constructor | downstream consumer |
| --- | --- | --- |
| `RLV-10 Gaussian normalisation` | `gaussianReducedVolume_eq_one` | `gaussianReducedVolumeCertificate_volume` |
| `NCF-12 normalisation (Gaussian model half)` | `gaussianReducedVolumeViaL_eq_one` | `gaussianUniformReducedVolumeLowerBound` |
| `RLV-1 path-space minimiser (constant-curvature family case)` | `constantCurvatureLMinimizerExistence` | `constantCurvature_reducedLength_le` |

Each is a `ClosureRecord` carrying the statement as a `Prop` and a proof of it; the ledger
`kappaVariationalClosures` is nonempty and named (`kappaVariationalClosures_nonempty`).

## 7. Remaining blockers (named, honest)

KV-1 (general path-space compactness), KV-2 (L-geodesic ODE), KV-3 (minimiser regularity),
KV-4 (L-exponential map), KV-5 (second variation), KV-6 (Jacobian comparison), KV-7 (reduced-
length differential inequality), KV-8 (differentiation under the integral), KV-9 (manifold
metric flow), KV-10 (NCF-9 ball-volume comparison), KV-11 (NCF-10 rigidity), KV-12 (NCF-11
compactness), KV-13 (general NCF-12 normalisation). None is closed by a weaker statement.

## 8. Verification transcript

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D12-kappa-variational
bash longrun/d12kv-logs/run_verification.sh
```

| command | exit |
| --- | --- |
| `lake env lean release/Poincare/D12/KappaVariational/GaussianNormalization.lean` (cwd `release/`) | 0 |
| `lake env lean release/Poincare/D12/KappaVariational/CurvatureEnergy.lean` | 0 |
| `lake env lean release/Poincare/D12/KappaVariational/Transfer.lean` | 0 |
| `lake env lean release/Poincare/D12/KappaVariational/Statements.lean` | 0 |
| `lake env lean release/Poincare/D12/KappaVariational/All.lean` | 0 |
| `lake env lean release/Poincare/D12/KappaVariational/Audit.lean` | 0 |
| `python3 longrun/d12kv-logs/audit_axioms.py …` (fail-closed) | 0 (`AUDIT_OK: 66 declarations`, cones only `{propext, Classical.choice, Quot.sound}`/`{}`) |
| negative control `longrun/d12kv-logs/negative_control/NegativeAudit.lean` | audit exit **1** (project axiom detected — fail-closedness demonstrated) |
| `python3 input/d5-tools/scan_forbidden.py release/Poincare/D12/KappaVariational` | 0 hard, 0 soft |
| `cd release && lake build` | 0 (9179 jobs) |

Artifacts: `longrun/d12kv-logs/{exit_codes.txt, source_hashes.txt, axioms.json,
forbidden_scan.txt, lake_build_exit.txt, lean_*.out/.err, run_verification.sh, audit_axioms.py,
negative_control/}`.

## 9. Honest boundary

* The normalization and the curve-energy bound are **model-space** results on real spaces
  (`L¹(ℝⁿ, Lebesgue)`, the D7 admissible-path space) — no manifold, tangent bundle or Ricci-flow
  PDE is constructed.
* The general reduced-length differential inequality, Jacobian comparison, L-exponential map
  and ball-volume comparison remain named missing inputs; the κ-assembly is conditional on them
  (`gaussianKappaNoncollapsing_of_ballVolumeComparison` makes this reduction explicit).
* The Gaussian soliton realising `Ṽ ≡ 1` is a computation, not an ancient-solution
  classification theorem; no canonical-neighbourhood inference is made.
* No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs in any authored file;
  every unproved statement is an explicit `Prop`/structure/`String` with a name in the ledger.

TASK_DONE — card: `longrun/results/D12-kappa-variational.md`
