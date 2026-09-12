# D12-entropy-variation — result card (final, invocation 3)

**Task id:** `D12-entropy-variation`
**Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D12-entropy-variation`
**Generated (UTC):** 2026-09-10T16:50:00Z
**Status:** `TASK_DONE` (intended milestone reached and kernel-checked; this card requests
independent acceptance, and does **not** claim Perelman is proved)

All authored files live under `release/Poincare/D12/EntropyVariation/` plus the
task-local audit tooling `tools/d12_axiom_audit.sh`, `tools/d12_token_scan.py`,
`tools/verify_frenzymath_snapshot.py`. Upstream sources (D3/D7/D10/D11, mathlib)
are **unmodified**; the one upstream defect found is handled by a versioned corrected
definition with proved compatibility, as required. Invocation 3 (this card) added the
exact-locus (iff) theorem, the idempotency characterization and the `n = 0`
non-vacuity witness, re-ran every audit, and verified the imported Frenzymath
snapshot (supervisor update 2026-09-11).

---

## 1. The missing analytic step (general, model-independent)

`Poincare.D12.EntropyVariation.hasDerivAt_weightedIntegral` — differentiation of a
time-dependent **weighted** integral

```lean
HasDerivAt (fun t => ∫ x, g t x * ρ t x ∂μ)
  (∫ x, g' t₀ x * ρ t₀ x + g t₀ x * ρ' t₀ x ∂μ) t₀
```

with all obligations explicit: neighbourhood `s ∈ 𝓝 t₀`, pointwise `HasDerivAt` of
`t ↦ g t x` and `t ↦ ρ t x` on `s` (μ-a.e. x), a.e.-pointwise domination of the
derivative combination `g'·ρ + g·ρ'` by an integrable bound, integrability of the
integrand at `t₀`, and measurability. It **returns** integrability of the
derivative combination (the iteration obligation). The time-dependent-measure
obligation is the term `g t₀ x * ρ' t₀ x`; the fixed-measure corollary
`hasDerivAt_weightedIntegral_constWeight` drops it. Proved from mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`
(`Mathlib/Analysis/Calculus/ParametricIntegral.lean`). **Class: general analytic theorem.**

## 2. Tracing D3/D7 entropy objects; the D3 double-square defect, versioned

* `EntropyData.riccHess` (D3) is the pointwise density `|Ric + ∇²f|²`.
* `EntropyData.FDissipation` (D3), documented as `2∫|Ric+∇²f|² dm`, is defined as
  `∫ 2·riccHess²·ρ dμ` — the density is **squared a second time**. Perelman's first
  variation needs `∫ 2·riccHess·ρ dμ`.
* `FDissipationCorrected` (versioned, in `EntropyDerivative.lean`) is the correct
  definition; compatibility `FDissipation_eq_corrected_of_idempotent`: the two agree
  exactly when `riccHess² = riccHess` (covers the D7 zero datum, so the existing
  non-vacuity instance is unaffected). The defect is **witnessed**:
  `shrinkerEntropyData_FDissipation_ne_corrected_one` (dim-1 shrinker, τ ≠ 1/2) and
  `fflow_FDissipation_ne_corrected_one` (n=1, τ₀=2, t=1: 1/8 ≠ 1/2).

## 3. Conditional closure of the named blocker `B-D7-F-DERIVATIVE`

`fDerivativeCorrected_at_of_pointwise` (and its uniform-in-time version) **constructs**
the corrected D7 first-variation input from strictly weaker hypotheses: fixed measure
(`∂ₜρ ≡ 0`), the pointwise first variation `∂ₜ(R+|∇f|²) = 2·riccHess`, plus explicit
integrability/domination/measurability. `fDerivativeStatement_of_corrected_of_idempotent`
constructs the literal D7 `FDerivativeStatement` from the proved corrected derivative
under idempotency. Nothing assumes `FDerivativeStatement` or monotonicity.
**Class: conditional (reduces to fixed-measure + pointwise variation), with the
pointwise hypothesis documented as stronger than what the F-flow model satisfies
(see §4).**

## 4. The F-flow model: exact `dF/dt = 2∫|Ric+∇²f|² dm` on the shrinking flat Gaussian

`FFlowModel.lean`. Model: `ℝⁿ` flat (`Ric = 0`, `R = 0`), `f = ‖x‖²/(4τ₀)`,
**fixed measure** `ρ = gaussianKernel n τ₀` (normalized, `∫ρ = 1`), metric
`g(t) = λ(t)g₀`, `λ(t) = 1 - t/τ₀`; `fflowMetricFlow_consistency` proves the model
satisfies `∂ₜg = -2(Ric + ∇²f)` (using the proved `∇²f = g₀/(2τ₀)`). Geometric domain
`t < τ₀`; `fflow_rho_deriv_zero` discharges the time-dependent-measure obligation.

* **Main theorem** `fflow_F_hasDerivAt`: for `t < τ₀`,
  `HasDerivAt (fun u => (fflowEntropyData n τ₀ hτ₀ u).F) (FDissipationCorrected (fflowEntropyData n τ₀ hτ₀ t)) t`,
  proved by differentiating the genuine integral functional through
  `hasDerivAt_F_of_pointwise` with the honest pointwise variation, explicit
  domination (`normSq_exp_neg_mul_le`-style coefficient bound) and integrability.
  Closed form `fflow_F_hasDerivAt_closedForm`: `dF/dt = n/(2(τ₀-t)²)`.
* **Sign**: `fflow_F_deriv_pos` (`0 < n/(2(τ₀-t)²)` for n ≥ 1); **F strictly
  increasing** on the geometric domain (`fflow_F_strictMonoOn`,
  `fflow_F_increasing_on_Iio`) — the correct Perelman convention
  `derivative = +FDissipation`.
* **Honest divergence accounting — now with the exact locus**: the pointwise identity
  `∂ₜ(R+|∇f|²) = 2·riccHess` **fails** at `x = 0`
  (`fflow_variation_ne_two_riccHess_at_zero`), and `fflow_variation_eq_two_riccHess_iff`
  proves it holds **if and only if** `‖x‖² = 2nτ₀` — the strong pointwise hypothesis of
  the D7-style reduction is satisfied on the model exactly on the radius-`√(2nτ₀)`
  sphere, nowhere else. The integrated identity
  `∫ ∂ₜ|∇f|² dm = 2∫|Ric+∇²f|² dm` **holds** (`fflow_integrated_variation_eq_dissipation`)
  via the Gaussian moment `∫‖x‖²ρ = 2nτ₀` — the model's exact replacement for the
  integration by parts.
* **Where the literal D7 field can and cannot hold — now a complete characterization**:
  `fflow_literal_FDerivative_inconsistent` proves `¬ FDerivativeStatement
  (fun u => fflowEntropyData 1 2 … u)` (computed derivative `1/2` vs D3
  `FDissipation = 1/8` at `t = 1`, uniqueness of `HasDerivAt`);
  `fflow_idempotency_iff_zero_dim` proves the idempotency hypothesis of
  `fflow_literal_FDerivativeStatement_of_idempotent` holds on the geometric domain
  **iff `n = 0`** (`fflow_idempotency_forces_zero_dim`: idempotency at `t = τ₀/2`
  forces `n/(4τ₀²) ∈ {0,1/4}`, at `t = 3τ₀/4` forces `n/(4τ₀²) ∈ {0,1/16}`, common
  value `0`); and `fflow_literal_FDerivativeStatement_zero_dim` **inhabits** the
  degenerate case: for `n = 0`, `F ≡ 0` and `FDissipation ≡ 0`, so the literal D7
  `FDerivativeStatement` holds for every `t > 0`. The literal D7 field is thus
  satisfiable **exactly** on the degenerate zero-dimensional model, inconsistent on
  every nontrivial one, while the corrected identity holds on every model.
  **Class: model theorems (nontrivial, n ≥ 1, all constants computed; the `n = 0`
  witness is the proved non-vacuity of the idempotency hypothesis).**

## 5. Sign distinction: increasing Perelman `F` vs nonincreasing toy functionals

`SignDistinction.lean` states the two facts **side by side with full types**:

* `perelmanFFlow_increasing_toy_nonincreasing`:
  `(∀ s t, s < t → t < τ₀ → F(E s) < F(E t)) ∧ (∀ ⦃s t⦄, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t → perelmanF c (traj t) ≤ perelmanF c (traj s))`.
* `derivative_sign_distinction`: `HasDerivAt F (n/(2(τ₀-t)²)) t ∧ 0 < n/(2(τ₀-t)²)`
  against the toy's `HasDerivWithinAt` derivative `-Σᵢ Fᵢ((λᵢ-1)²+(cᵢ-1))e^{-λᵢ} ≤ 0`.
* `toy_heatEnergy_nonincreasing`: the D2 heat-grid ℓ² energy is antitone in discrete
  time (CFL `0 ≤ α ≤ 1/2`).

The toy `perelmanF` is a finite sum over a reaction network, a different object from
the continuum integral — the sign difference is real, documented, not renamed away.

## 6. The shrinker `W`-derivative identity (both sides computed independently)

`shrinker_W_derivative_identity`:
`HasDerivAt (fun u => shrinkerWOfTau n u) (shrinkerWDissipation n τ) τ` where
`shrinkerWDissipation n τ = -2τ∫|Ric+∇²f-g/(2τ)|² dm` on the shrinker.
Left side: `W(τ) ≡ 0` (proved `shrinkerEntropyData_W_value`, normalization + second
moment enter) ⇒ derivative `0`. Right side: `shrinkerWDissipationDensity_zero` —
the density vanishes pointwise from `Ric = 0` and the proved Hessian identity
`∇²f = g/(2τ)`. This is Perelman's equality case of W-monotonicity, computed, not
assumed. **Class: model theorem.**

## 7. The Gaussian shrinker model (nontrivial)

`GaussianShrinker.lean`: normalization `∫ρ = 1`, second moment `∫‖x‖²ρ = 2nτ`
(obtained by differentiating the Gaussian integral in its parameter **through**
`hasDerivAt_integral_param` — a downstream use of the delivered theorem), `F = n/(2τ)`,
`W = 0`, the Hessian identity `∇²f = (1/(2τ))g` (`iteratedFDeriv_two_shrinkerFpot`),
`riccHess = n/(4τ²)` justified pointwise (`shrinker_riccHess_justified`), and the
dissipation values for both definitions.

## 8. Kernel trust, compilation, axioms (invocation-3 re-audit)

* **Compile evidence** (cwd `release/`, toolchain `leanprover/lean4:v4.34.0-rc2`
  (binary `Lean (version 4.34.0-rc2, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d)`),
  mathlib rev `7974e751bece493b6ff508039423ca9fa2452fa8` from `lake-manifest.json`):
  * `lake build Poincare.D12.EntropyVariation.All Poincare.D12.EntropyVariation.AxiomAudit`
    → exit 0 (8916 jobs; log `longrun/ev-logs/lakebuild-inv3.log`).
  * `lake env lean Poincare/D12/EntropyVariation/<File>.lean` for each of the 7 files
    → exit 0 each (logs `longrun/ev-logs/inv3-lean-<File>.log`,
    `longrun/ev-logs/d12_axiom_report.txt`).
* **Axiom evidence**: task-local module `AxiomAudit.lean` (one `#print axioms` per
  declaration) and the fail-closed programmatic audit `tools/d12_axiom_audit.sh`:
  * **87** declarations extracted and reported; 86 depend exactly on
    `{propext, Classical.choice, Quot.sound}`, 1 (`eventually_of_forall`) depends on no
    axioms; no other axiom names anywhere in the report (logs
    `longrun/ev-logs/d12_axiom_audit_inv3.log`, report
    `longrun/ev-logs/d12_axiom_report.txt`, sha256 `2a13314bb2d073c9d6d5c45eb0e2b47655481f9b01819a8633e12af568bb0f4e`).
  * Negative control: a generated file with `axiom d12AuditFakeAxiom` + a dependent
    theorem is correctly flagged by the same machinery (checker is fail-closed).
* **Forbidden tokens**: `tools/d12_token_scan.py` (comment/string-aware, new in
  invocation 3): 0 hits for `sorry|axiom|admit|unsafe|native_decide|proof_wanted|opaque`
  across all 7 files; scanner negative control catches an injected `sorry` (log
  `longrun/ev-logs/d12_token_scan.log`).
* **Source hashes** (sha256): see the JSON card. The 5 unchanged files match the
  invocation-2 hashes; `FFlowModel.lean` and `AxiomAudit.lean` are new hashes
  (invocation-3 additions). Upstream files untouched.
* Separation of concerns: the *kernel* accepts the derivations (no axioms beyond the
  allowlist); *compilation* is evidenced by the commands above; *statement correctness*
  is the semantic review summarized in §§1–7 (each headline type quoted in the JSON
  card); the named blocker `B-D7-F-DERIVATIVE` is closed conditionally (§3) and
  unconditionally on the model (§4) — a constructor of the missing input
  (`fflow_F_hasDerivAt`, and for the literal D7 field
  `fDerivativeStatement_of_corrected_of_idempotent`) with downstream checked uses
  (`fflow_F_hasDerivAt_closedForm` → `fflow_F_strictMonoOn`/`fflow_F_increasing_on_Iio`
  → `derivative_sign_distinction`).

## 9. Frenzymath snapshot (supervisor update 2026-09-11)

The pinned snapshot `third_party/frenzymath/Poincare-Conjecture` (frenzymath/
Poincare-Conjecture, commit `bb91a091f0b968f8bbe8d861e025a88d82b161be`, Apache-2.0)
was verified by the new `tools/verify_frenzymath_snapshot.py` (log
`longrun/ev-logs/frenzymath-verify.log`): 2801 tracked files, 2352 Lean files,
657189 Lean lines, package roots `PoincareConjecture` + `shared` present, toolchain
pin `leanprover/lean4:v4.32.1` (both packages), mathlib pin
`520045ab14e26149ee970e2e617ca04b09bde5d6` (both manifests), zero build caches.
Per `docs/UPSTREAM-INTEGRATION.md` the snapshot is **reference-only** in this
worktree: it needs Lean `v4.32.1` while the local release build is pinned to
`v4.34.0-rc2`, so it is not built and not counted as local proof evidence. This
task's milestone needs no general-manifold geometry (the model is flat Euclidean),
so no Frenzymath import was required; the compatibility-audit dependency is
recorded in `next_dependency_requests` for the general-manifold tracks. (The file
`third_party/frenzymath/IMPORT.md` referenced by the update is absent from this
worktree; the integration content is carried by `docs/UPSTREAM-INTEGRATION.md` and
`longrun/frenzymath-source.json`.)

## 10. What remains (exact, not part of this task's milestone)

For the general-manifold Perelman chain (other D12 tracks): a proved pointwise
evolution identity `∂ₜ(R+|∇f|²) = Δ(R+|∇f|²) - 2|Ric+∇²f|² + ⟨divergence terms⟩` under
`∂ₜg = -2(Ric+∇²f)`, `∂ₜf = -(R+Δf)`; a weighted integration-by-parts theorem with
explicit regularity/domination; the Bochner identity as a theorem; conjugate
heat-equation evolution of the measure. On the model these are replaced by the proved
Hessian identity and the Gaussian moment — this is stated explicitly, never papered
over. The old toy functional remains a different object (finite reaction network).

TASK_DONE
