# D12-volume-ibp — result card

**Task id:** `D12-volume-ibp`
**Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D12-volume-ibp`
**Updated (UTC):** 2026-09-10T20:23:40Z (gate repair attempt 1)
**Status:** `TASK_DONE` (request for independent acceptance) — all intended milestone claims hold:
target statement, dependency search, choice of approach, compiling first lemma (checkpoint 1);
nontrivial lemmas with full types + axiom cones (12h); concrete downstream use (24h:
`chart_weighted_ibp` is the exact chart form of D7's `WeightedIBPStatement`, with the
`gradInner`-compatibility lemma `inner_grad_eq_gradInnerInverse` proved); independently
reproducible deliverable with fail-closed axiom audit and non-vacuity witnesses (72h).

## What is constructed (all kernel-checked, axioms ⊆ {propext, Classical.choice, Quot.sound})

On the Euclidean chart `Vec d = Fin d → ℝ` with a `ChartMetric G` (smooth entrywise
positive-definite metric matrix):

1. **Density/measure bridge** (`Basic`, `Regularity`): `density = √(det g)`, positive,
   smooth/continuous/measurable (inverse-metric entries smooth entrywise through
   adjugate/det — no smoothness assumed); `riemannianMeasure = volume.withDensity ρ`;
   `∫ f dvol = ∫ f·ρ dx`; absolute continuity; `dvol = dx` for the Euclidean metric.
2. **Chart divergence theorem with compact support** (`Divergence`):
   `∫ ∑ᵢ ∂ᵢ(ω·Xᵢ) dx = 0` proved from mathlib's box divergence theorem
   (`integral_divergence_of_hasFDerivAt_off_countable'`) — no divergence theorem assumed;
   corollary `∫ div_g X dvol = 0`, `div_g X = ρ⁻¹∑ᵢ∂ᵢ(ρXᵢ)`.
3. **Metric integration by parts** (`IBP`): metric gradient `grad u = g⁻¹·du`, Laplacian
   `Δ_g v = div_g(grad v)`, inverse-metric pairing; **`chart_ibp`**:
   `∫ u·Δ_g v·ρ dx = -∫ ⟨∇u,∇v⟩_{g⁻¹}·ρ dx` for `C² u,v` with `u` compactly supported
   (product-rule expansion `weighted_divergence_mul_grad` via `fderiv_mul`, cancellation by
   `ring`). Corollaries: `∫ Δv dvol = 0`, `∫ u Δu dvol = -∫ |∇u|² dvol`,
   Bochner-chain `∫ u Δ(Δu) dvol = -∫ ⟨∇u,∇(Δu)⟩ dvol` (`u` smooth compactly supported).
4. **Entropy-chain drift IBP** (`IBP`): **`chart_weighted_ibp`** with `dm = e^{-f}ρ dx` and
   `Δ_f u = Δu - ⟨∇f,∇u⟩_{g⁻¹}`:
   `∫ (Δ_f u)·v·e^{-f} dvol = -∫ ⟨∇u,∇v⟩_{g⁻¹}·e^{-f} dvol` for `C² f,u,v`, `v` compactly
   supported — the exact chart-level form of D7's `WeightedIBPStatement`; the restricted
   statement is proved in D7's shape (`Blocked.chartWeightedIBPStatementRestricted_holds`,
   a downstream consumer use of the D7 entropy bridge module). The classical
   `∫ (Δf)e^{-f} dvol = ∫ |∇f|² e^{-f} dvol` needs `v ≡ 1`, i.e. a closed manifold —
   recorded as blocker `B-D12-ENTROPY-CLOSED-MANIFOLD` (state-only `Prop`, never used).
5. **Chart change of variables** (`ChangeOfVariables`): pullback metric
   `ψ*G = Jᵀ g(ψ·) J` with positive definiteness from the explicit rank condition
   `fderiv_injective` (`x ↦ x³` documented as the reason injectivity of `ψ` alone fails);
   **pullback density law** `ρ_{ψ*G}(x) = ρ_G(ψx)·|det J(x)|`; **measure naturality**
   `∫ g(ψx) ρ_{ψ*G}(x) dx = ∫ g(y) ρ_G(y) dy` proved from mathlib's Jacobian theorem
   (`integral_image_eq_integral_abs_det_fderiv_smul`) — no CoV assumed. Compatibility
   `⟨∇u,∇v⟩_g = ⟨du,dv⟩_{g⁻¹}` (`inner_grad_eq_gradInnerInverse`).
6. **Non-vacuity** (`Example`): Euclidean density = 1; `expMetricOne` (d = 1, metric
   `e^{2x₀}`) has density `e^{x₀}` ≠ 1 at a witness point; `chart_ibp_euclidean_one`
   instantiates the IBP identity in dimension 1.
7. **API comparison** (`Compat`): fresh probe of pinned mathlib
   `Orientation.volumeForm`/`volumeForm_robust`, Haar measure, box divergence theorem,
   Jacobian CoV; manifold Riemannian volume/Stokes explicitly absent → named blockers.
8. **Fail-closed axiom audit** (`Audit` + `audit.py`): 63 declared axioms-cones all within
   {propext, Classical.choice, Quot.sound}; negative control (`negativeControl`, never
   used) correctly flagged; forbidden-token scan of all sources clean.

## Honest boundary (semantic class)

**Model** — Euclidean chart of a Riemannian metric; **conditional** for closed-manifold
use (partition-of-unity gluing, boundary theory, Stokes, orientation — all recorded as
explicit state-only `Prop`s with named blockers `B-D12-MANIFOLD-GLUING`,
`B-D12-BOUNDARY-STOKES`, `B-D12-MANIFOLD-ORIENTATION`,
`B-D12-ENTROPY-CLOSED-MANIFOLD`; none is used as a hypothesis by any theorem). The D7
statement `WeightedIBPStatement` in its unrestricted (`∀ u v`, no support hypotheses)
form does **not** follow on the noncompact chart; the restricted (honest) form is proved.

## Gate repair attempt 1 (2026-09-10T20:30Z)

The gate reported `ok: false` on exactly one file: `release/ProbeScratch.lean` (exit 1),
the historical API-discovery probe from checkpoint 1 (a scratch `#check` file; it is not a
test or a negative control, which live outside `release/`). Twelve of its `#check` lines
used identifiers that do not exist at the pinned mathlib revision. The gate diagnostic is
truncated at the top; the full failure set was recovered by recompiling against the
pinned-revision olean cache (`lake build` had refreshed it):

- `MeasureTheory.integral_withDensity_eq_integral_smul{₀}` and
  `MeasureTheory.setIntegral_withDensity_eq_setIntegral_smul₀` — these are declared at the
  **root** namespace (`MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`, after
  `end ContinuousLinearMap`), so the correct spellings are bare
  `integral_withDensity_eq_integral_smul{₀}` / `setIntegral_withDensity_eq_setIntegral_smul₀`.
- `continuous_det` → `Matrix.GeneralLinearGroup.continuous_det` (the `protected` lemma in
  `Topology/Algebra/Group/Matrix.lean`).
- `Matrix.det_pos` → `Matrix.PosDef.eigenvalues_pos` (plain `Matrix.det_pos` does not exist;
  `Matrix.PosDef.det_pos` was already checked on the next line).
- `support` → `Function.support`; `isCompact_tsupport`, `Matrix.det_toLin'` (→
  `LinearMap.det_toLin'`), `Matrix.nonsing_inv` (→ `Matrix.inv_def`), `Matrix.det_inv` (→
  `Matrix.det_nonsing_inv`), `Matrix.dotProduct` (→ root `dotProduct`),
  `Measurable.matrix_det` (no such lemma; measurability follows from
  `Continuous.matrix_det` + `Continuous.measurable`).

All spellings were verified against the pinned mathlib source before editing. **No theorem,
definition, or D12 layer source changed**: every `Poincare/D12/VolumeIBP/*.lean` sha256 is
identical to the previous checkpoint; only `ProbeScratch.lean` (new sha256
`cfb65fd54c200fd2e7b38f49ac67f25aa57c0b46fd5abea1ba2fcfa402d5c93a`) was touched.

Post-repair verification (all run from `release/`):

- `lake build` → **exit 0** (8956 jobs).
- Per-file gate reproduction: `lake env lean <f>` over the full 74-file gate list → **0
  failures**. The 74 files are exactly the complete set of `.lean` files under `release/`
  (excluding `.lake`) — no other orphans.
- `python3 Poincare/D12/VolumeIBP/audit.py` → **AUDIT PASS** (63 cones within
  {propext, Classical.choice, Quot.sound}; negative control flagged).

## Reproducibility

- Toolchain: `leanprover/lean4:v4.34.0-rc2`; mathlib pinned `7974e751bece493b6ff508039423ca9fa2452fa8`.
- Build: `cd release && lake build` → exit 0 (8956 jobs, full package).
- Audit: `cd release && python3 Poincare/D12/VolumeIBP/audit.py` → `AUDIT PASS` (63 cones,
  negative control flagged).
- Fresh source hashes: see `longrun/results/D12-volume-ibp.json` (`source_hashes`).
- Authoring note: `maxHeartbeats 4000000` module option in `IBP.lean`/`ChangeOfVariables.lean`
  (elaborator budget only, no axioms); the `rw`-on-instance-def fallback (which can silently
  emit `sorry` in Lean 4.34) was replaced everywhere by `unfold`/`simp only` — zero `sorry`
  in the layer (grep-verified and audit-script-verified).

TASK_DONE
