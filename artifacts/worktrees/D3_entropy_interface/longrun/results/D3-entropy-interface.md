# D3-entropy-interface — result card

> **Honesty boundary (read first).** This task defines a measure/metric-flow-compatible
> *interface* for F/W-style functionals, a monotonicity *certificate*, and a *statement-only*
> bridge for the missing integration-by-parts/regularity theorems. It is **not** a proof of
> Perelman's entropy monotonicity, **not** a proof of the Poincaré conjecture, and no
> declaration is named after a Perelman proof. The one unproved analytic content is isolated
> in `Poincare.Longrun.Entropy.Bridge` as a hypotheses bundle; only a checked *reduction*
> from that bundle to the certificate is proved.

- **Task id:** `D3-entropy-interface`
- **Stage / lane:** D3 / builder (`requires_lean: true`)
- **Model:** `deepseek-v4.1-flash-expires-on-0910`
- **Session:** `session-55b1a7c2-4662-4f14-af0f-ae02ec0379eb`
- **Started:** `2026-09-08T23:57:00+08:00`
- **Finished:** `2026-09-09T00:10:00+08:00`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D3_entropy_interface`
  (the prompt's `Worktree:` line names `…/worktrees/D3_entropy`; that directory does not exist
  on disk, and the current runtime snapshot assigns `D3_entropy_interface`. All work was done
  in `D3_entropy_interface`.)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (commit `6a10ac8c22be`)
- **mathlib:** revision `7974e751bece493b6ff508039423ca9fa2452fa8`
- **Status:** `done` (all authored files check; one external delivery caveat in §10)

## 1. D2 result cards consumed

Both accepted predecessors were read in full and their Lean sources copied **byte-identically**
into this worktree (never modified):

| Consumed card | Worktree source | sha256 |
| --- | --- | --- |
| `D2-geometry-foundation` | `Poincare/Longrun/Geometry/MetricData.lean` | `adb51294b15f16ff34e322f453f81eda3fdfdb5c1d810ef98ab18a5aa9dcd61c` |
| `D2-geometry-foundation` | `Poincare/Longrun/Geometry/ConnectionAdapter.lean` | `db06e597d552b1cba852f5022e7a1e1a51d8e36e36487e14852261bf6f78aefd` |
| `D2-geometry-foundation` | `Poincare/Longrun/Geometry/Contraction.lean` | `e1bdca9cf795f045e92b9e567d52cb30fd6b96c7942f8a3cb2389e9e2817b5d7` |
| `D2-geometry-foundation` | `Poincare/Longrun/Geometry/LeviCivitaBlocked.lean` | `47f8a7f8598f10c6f2de41a24d2cd2457557e6d8b80f4529edbf3830391685fd` |
| `D2-geometry-foundation` | `Poincare/Longrun/Geometry.lean` (umbrella) | `136065c47e12130a9368cee1bb2f21a43949df701410930c245d03eaecf344fa` |
| `D2-pde-foundation` | `Poincare/Longrun/PDE/HeatGrid.lean` | `5af646e311cda429596e6bdf478e93417248f6b37f4eb2e867b3b39c0c5ac381` |
| `D2-pde-foundation` | `Poincare/Longrun/PDE/DiscreteMaximumPrinciple.lean` | `5a6699a007260f522dd663f74897907ce8ac94fe08b44bcbf16a223113b67b24` |
| `D2-pde-foundation` | `Poincare/Longrun/PDE/Energy.lean` | `33031a059c609e6e4d87128133e19fdebfefeb5540ce16098373729dd38c7d28` |
| `D2-pde-foundation` | `Poincare/Longrun/PDE/ContinuousInterface.lean` | `2dbb7cba03628271e04deb513b100f439122df844de248f41bd84e9c9ff37093` |
| `D2-pde-foundation` | `Poincare/Longrun/PDE/AxiomAudit.lean` | `5adf788c67a62ba874d8837ce85aac90b0cc03487ea5c2297203b9b61045d2d5` |

The five geometry hashes match the values recorded in the D2-geometry card exactly.
Shared Stage1 files (`Poincare/Stage1/CurvatureAlgebra.lean`,
`Poincare/Stage1/RiemannAdapter.lean`) were copied from `poincare-lab` and also match the
D2-geometry card hashes (`d2295c74…`, `a19c6708…`).

What the D2 cards constrain (and why the interface is abstract, not smooth-geometric):

- D2-geometry: mathlib has **no** Ricci/scalar curvature; the accepted cluster is the
  *algebraic* contraction `ricci K eᵢ eᵢ` with `scalarCurvature_eq_sum_basis`, plus explicit
  `BLOCKED` Levi-Civita/curvature statements. Consequently the entropy interface must take
  `R`, `|∇f|²`, `|Ric + ∇²f|²` as data.
- D2-pde: mathlib has **no** heat-equation theory; the accepted checked content is the
  finite-grid heat scheme and its ℓ² energy monotonicity (`energy_succ_le`,
  `energy_nonincreasing`). Consequently the only non-vacuous *discrete* instance of the
  certificate available today is the D2 ℓ² energy.

## 2. What was built

| File | Lines | sha256 |
| --- | --- | --- |
| `Poincare/Longrun/Entropy/Functional.lean` | 162 | `3128733f2fe542e528f407ee76b44cf4c06cb464eacf7297afa30ad89ef7c99f` |
| `Poincare/Longrun/Entropy/Certificate.lean` | 396 | `c12f810405380e7b3c92b10d794df328885514bcbfab9f3e487644fd4ff50d3f` |
| `Poincare/Longrun/Entropy/Bridge.lean` | 214 | `0d482a78b13c5ed190d75189b62b895ed1be5823ed12fb2a682b4d0162ddd471` |
| `Poincare/Longrun/Entropy/DiscreteHeat.lean` | 102 | `fa3ed4224192ec8f976a0552ce22112397d81661938265c83f15932fde56b2d8` |
| `Poincare/Longrun/Entropy/FiniteGeometry.lean` | 122 | `4d48a82f436acb47ac13b4004fadd970e24f22e872d61cc3290013bbce3c89e5` |
| `Poincare/Longrun/Entropy/AxiomAudit.lean` | 97 | `d96ca4853963b0258919651369c8b968a56c5ddeb41d7b0e5f5c350bf518be62` |
| `Poincare/Longrun/Entropy.lean` (umbrella) | 39 | `b87ca5144a8f9b7f6c3193e9900946d609ce0e7660a849b6249632c22d3e450a` |

Total authored Lean: 1132 lines. Every file has an inline `#print axioms` section; the
consolidated audit is `AxiomAudit.lean` (66 declarations).

## 3. Requirement mapping

### 3.1 Measure/metric-flow-compatible F/W interface (`Functional.lean`)

```lean
structure EntropyData (X : Type u) [MeasurableSpace X] (μ : Measure X) where
  R : X → ℝ            -- scalar-curvature density
  gradSq : X → ℝ       -- |∇f|² density
  f : X → ℝ            -- potential
  ρ : X → ℝ            -- entropy-measure density: dm = ρ dμ
  τ : ℝ                -- coupling parameter
  τ_pos : 0 < τ
  n : ℝ                -- dimension parameter
  riccHess : X → ℝ     -- pointwise |Ric + ∇²f|² density (abstract datum)
  ρ_nonneg : ∀ x, 0 ≤ ρ x
  integrable_F : Integrable (fun x => (R x + gradSq x) * ρ x) μ
  integrable_W : Integrable (fun x => (τ * (gradSq x + R x) + (f x - n)) * ρ x) μ

noncomputable def F  (D) : ℝ := ∫ x, (D.R x + D.gradSq x) * D.ρ x ∂μ
noncomputable def W  (D) : ℝ := ∫ x, (D.τ * (D.gradSq x + D.R x) + (D.f x - D.n)) * D.ρ x ∂μ
noncomputable def FDissipation (D) : ℝ := ∫ x, 2 * (D.riccHess x)^2 * D.ρ x ∂μ
def HasConjugateWeight (D) : Prop := ∀ x, D.ρ x = Real.exp (-(D.f x))
```

The weight `ρ` is a density with respect to the background measure `μ`, so the interface is
measure-compatible by construction; `HasConjugateWeight` records the exponential part
`e^{-f}` of the geometric weight (the `(4πτ)^{-n/2}` factor is absorbed into `μ` or `ρ`).
Both functionals use the **same** weight, so the checked decomposition below is an algebraic
identity, not a normalization claim.

Checked interface consequences:

| Declaration | Statement |
| --- | --- |
| `EntropyData.W_eq` | `D.W = D.τ * D.F + D.extra`, i.e. `W = τ F + ∫ (f - n) dm` |
| `EntropyData.FDissipation_nonneg` | `0 ≤ D.FDissipation` (square × nonnegative weight) |
| `EntropyData.integrable_extra` | the potential term `∫ (f - n) dm` is integrable, derived from the `F`/`W` integrability fields |
| `EntropyData.conjugateWeight_pos` | a conjugate weight is strictly positive |
| `EntropyData.F_mono_integrand` | pointwise domination of the `F`-integrands gives `D₁.F ≤ D₂.F` |

### 3.2 Monotonicity certificate with all analytic assumptions explicit (`Certificate.lean`)

```lean
structure ContinuousMonotoneCertificate (E : ℝ → EntropyData X μ) where
  dissipation : ℝ → ℝ
  hasDerivAt_F : ∀ t, 0 < t → HasDerivAt (fun s => (E s).F) (dissipation t) t
  continuousOn_F : ContinuousOn (fun s => (E s).F) (Ici 0)
  dissipation_nonneg : ∀ t, 0 < t → 0 ≤ dissipation t
  upperBound : ℝ
  upper_le : ∀ t, 0 ≤ t → (E t).F ≤ upperBound
```

Every analytic input is a *field*: differentiability along the flow with the stated
derivative, continuity on `[0, ∞)` (including the endpoint), the derivative sign, and the
one-sided bound. Integrability of the integrands is a field of `EntropyData`. The
`ContinuousAntitoneCertificate` mirror has `dissipation_nonpos` and a `lowerBound`; the
`LinearDecayCertificate` adds a positive `rate` and the decay inequality
`F (E t) ≤ F (E 0) - rate * t`. The order-algebraic certificates
`MonotoneCertificate` / `AntitoneCertificate` over an arbitrary preorder are also provided.

### 3.3 Checked algebraic consequences of the certificate (≥ 2 required; 8 listed)

| # | Declaration | Statement |
| --- | --- | --- |
| 1 | `ContinuousMonotoneCertificate.monotoneOn` | from `dissipation ≥ 0` + continuity, `MonotoneOn (fun t => F (E t)) (Ici 0)` (mean-value theorem) |
| 2 | `ContinuousMonotoneCertificate.F_ge_initial` | `∀ t ≥ 0, F (E 0) ≤ F (E t)` |
| 3 | `ContinuousMonotoneCertificate.eq_on_Icc_of_eq_at` | if `F (E t) = F (E 0)` for `t ≥ 0`, then `F (E s) = F (E 0)` for all `s ∈ [0, t]` (flat-spot rigidity) |
| 4 | `ContinuousAntitoneCertificate.antitoneOn` | from `dissipation ≤ 0` + continuity, `AntitoneOn (fun t => F (E t)) (Ici 0)` |
| 5 | `ContinuousAntitoneCertificate.F_le_initial` | `∀ t ≥ 0, F (E t) ≤ F (E 0)` |
| 6 | `ContinuousAntitoneCertificate.lower_le_initial` | `lowerBound ≤ F (E 0)` |
| 7 | `ContinuousAntitoneCertificate.eq_on_Icc_of_eq_at` | flat-spot rigidity for the nonincreasing certificate |
| 8 | `LinearDecayCertificate.time_le` | `t ≤ (F (E 0) - lowerBound) / rate` for every `t ≥ 0` (finite-lifetime bound) |

The order-algebraic certificates contribute the comparison and flat-spot lemmas
`MonotoneCertificate.F_le_of_le`, `MonotoneCertificate.eq_of_le_of_eq`,
`AntitoneCertificate.F_le_of_le`, `AntitoneCertificate.eq_of_le_of_eq`, which are reused by
the continuous certificates via `toMonotoneCertificateOnIci` /
`toAntitoneCertificateOnIci`.

Non-vacuity witnesses: `zeroEntropyData`, `zeroEntropyData_F`,
`continuousMonotoneCertificate_zero`, `continuousAntitoneCertificate_zero` show the interface
and both certificates are inhabited (the zero datum on `Unit` with counting measure).

### 3.4 Statement-only bridge for the missing IBP/regularity theorems (`Bridge.lean`)

The abstract calculus datum `WeightedCalculus` carries a gradient, ordinary Laplacian,
weighted Laplacian, squared Hessian, metric and Ricci pairing. The following are `def … : Prop`
or `Prop`-valued structure fields and have **no proof** (statement-only):

| Declaration | Missing theorem marked |
| --- | --- |
| `WeightedIBPStatement` | weighted integration by parts `∫ (Δ_f u) v dm = -∫ ⟨∇u, ∇v⟩ dm` |
| `WeightedLaplacianStatement` | compatibility `Δ_f u = Δu - ⟨∇f, ∇u⟩` |
| `BochnerStatement` | Bochner identity `Δ|∇u|² = 2|∇²u|² + 2⟨∇u, ∇Δu⟩ + 2 Ric(∇u, ∇u)` |
| `ConjugateMeasureEvolutionStatement` | conjugate heat equation `∂_t ρ = -Δρ` |
| `FDerivativeStatement` | differentiation under the integral sign: `d/dt F = 2∫|Ric + ∇²f|² dm` |
| `EntropyFunctionalRegularityStatement` | `C¹` regularity of `t ↦ F (E t)` on `[0, ∞)` |
| `EntropyRegularityBridge` | bundles the six statements above as a hypotheses structure |

The only *checked* content in this file is the reduction
`continuousMonotoneCertificateOfBridge : EntropyRegularityBridge C E → (∀ t ≥ 0, F (E t) ≤ B)
→ ContinuousMonotoneCertificate E`, where the derivative sign is derived from
`EntropyData.FDissipation_nonneg` (not assumed), plus the zero-calculus non-vacuity instance
`entropyRegularityBridge_zero` and its corollary
`continuousMonotoneCertificate_zero_viaBridge`.

### 3.5 D2 consumption

**D2-pde-foundation** (`DiscreteHeat.lean`): the new checked
`HeatGridEvolution.energy_antitone` strengthens the D2 `energy_nonincreasing` to full
antitonicity in discrete time; `heatEnergyCertificate` packages the D2 ℓ² energy as an
`AntitoneCertificate ℕ`, and `heatEnergy_le_initial`, `heatEnergy_nonneg`,
`heatEnergy_eq_of_eq_initial` are the certificate consequences specialized back to the D2
energy. `zeroHeatGridEvolution` witnesses non-vacuity.

**D2-geometry-foundation** (`FiniteGeometry.lean`): `finiteCurvatureDatum` builds a
counting-measure `EntropyData` on the finite index type with
`R i = ricci K (basis i) (basis i)` and `ρ i = exp (-f i)`.
`finiteCurvatureDatum_F_zero` proves that at zero potential the interface's `F` **equals**
the D2 `scalarCurvature K m.toScalarContractionData` (via
`MetricData.scalarCurvature_eq_sum_basis`); `finiteCurvatureDatum_F` gives the finite-sum
formula, `finiteCurvatureDatum_W` specializes the `W = τF + ∫(f-n)dm` identity, and
`finiteCurvatureDatum_F_add` consumes the D2 contraction additivity
`CurvatureOperator.ricci_add`.

## 4. Exact commands and exit codes

Environment for every command:

```text
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D3_entropy_interface
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
```

### 4.1 Bootstrap build of the consumed D2 modules

```text
lake build Poincare.Longrun.Geometry Poincare.Longrun.PDE.Energy
exit code: 0
# Build completed successfully (8887 jobs).
```

### 4.2 Clean rebuild of the authored cluster

The local `Poincare/Longrun/Entropy` build tree was deleted first, so this is a from-source
build of the authored cluster:

```text
rm -rf .lake/build/lib/lean/Poincare/Longrun/Entropy .lake/build/lib/lean/Poincare/Longrun/Entropy.olean
lake build Poincare.Longrun.Entropy Poincare.Longrun.Entropy.AxiomAudit
exit code: 0
# Build completed successfully (8891 jobs).
```

Full-library build:

```text
lake build Poincare
exit code: 0
# Build completed successfully (8899 jobs).
```

### 4.3 `lake env lean` on every authored file

```text
lake env lean Poincare/Longrun/Entropy/Functional.lean      exit code: 0
lake env lean Poincare/Longrun/Entropy/Certificate.lean     exit code: 0
lake env lean Poincare/Longrun/Entropy/Bridge.lean          exit code: 0
lake env lean Poincare/Longrun/Entropy/DiscreteHeat.lean    exit code: 0
lake env lean Poincare/Longrun/Entropy/FiniteGeometry.lean  exit code: 0
lake env lean Poincare/Longrun/Entropy/AxiomAudit.lean      exit code: 0
lake env lean Poincare/Longrun/Entropy.lean                 exit code: 0
```

Per-file transcripts are in `longrun/logs/*.compile.log` (all empty of errors and warnings);
the build transcripts are `longrun/logs/*.build.log` and `longrun/logs/full_library_build.log`.

### 4.4 `#print axioms`

```text
lake env lean Poincare/Longrun/Entropy/AxiomAudit.lean > longrun/logs/AxiomAudit.compile.log 2>&1
exit code: 0
```

66 declarations audited; **every** declaration reports exactly

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

Representative lines:

```text
'Poincare.Longrun.Entropy.EntropyData.W_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Entropy.EntropyData.FDissipation_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Entropy.ContinuousAntitoneCertificate.antitoneOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Entropy.LinearDecayCertificate.time_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Entropy.continuousMonotoneCertificateOfBridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Entropy.heatEnergy_le_initial' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Entropy.finiteCurvatureDatum_F_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no project axiom, no `unsafe`, no `native_decide`.

## 5. Hygiene checks

```text
grep -h "sorryAx" longrun/logs/*.compile.log | wc -l                         → 0
grep -nE "^[[:space:]]*(sorry|axiom|unsafe|native_decide|proof_wanted)\b" \
     Poincare/Longrun/Entropy/*.lean Poincare/Longrun/Entropy.lean | wc -l    → 0
```

The only textual occurrences of the forbidden words are inside the honesty docstrings that
state their absence. The D2 and Stage1 consumed sources are byte-identical copies (hashes in
§1); no shared source was modified.

## 6. Assumptions displayed at the main theorems (summary)

- The interface is **abstract measure-theoretic**: a background measure `μ`, a density `ρ`,
  and scalar curvature/gradient/dissipation *densities as data*. No manifold, connection,
  Levi-Civita, or Ricci-flow structure is constructed.
- `F` and `W` are the weighted integrals above; `W = τ F + ∫ (f - n) dm` is proved from the
  explicit integrability fields.
- `FDissipation ≥ 0` is purely algebraic (square times a nonnegative weight).
- The continuous certificates assume, explicitly: `HasDerivAt` of `t ↦ F (E t)` with the
  stated derivative, `ContinuousOn` on `[0, ∞)`, the sign of that derivative, and the
  one-sided bound. The discrete D2 instance assumes `0 ≤ α ≤ 1/2`, zero Dirichlet boundary,
  and the ℓ² energy.
- The bridge is a hypotheses bundle: the derivative formula, weighted IBP, weighted-Laplacian
  compatibility, Bochner identity, conjugate heat equation, and `C¹` regularity are all
  **unproved** `Prop`s. The checked reduction derives the certificate from them.

## 7. Blockers and suggested follow-ups

| Blocker | Evidence | Suggested follow-up |
| --- | --- | --- |
| Differentiation under the integral sign / first variation of `F` is not available | `FDerivativeStatement` is an unproved `Prop` | formalize a parametric-integral + IBP theorem for a smooth weighted manifold |
| Weighted integration by parts and Bochner identity not in mathlib | `WeightedIBPStatement`, `BochnerStatement` are unproved `Prop`s; D1 card records no Riemannian geometry API | upstream/implement weighted Laplace–Beltrami theory |
| Conjugate heat equation / measure evolution not available | `ConjugateMeasureEvolutionStatement` is an unproved `Prop`; D2 card records no heat-equation theory | build on the D2 discrete scheme or a heat-kernel development |
| `C¹` regularity of the functional is assumed | `EntropyFunctionalRegularityStatement` is an unproved `Prop` | smoothness of the flow and dominated-convergence bounds |
| The upper/lower one-sided bounds are hypotheses, not derived | `upper_le` / `lower_le` fields | derive from normalization/monotonicity inputs in a later task |
| Smooth Riemannian manifold absent from mathlib | D1/D2 cards; `WeightedCalculus` is abstract data | track mathlib geometry roadmap |

No blocking condition prevented completion of the requested interface work: every authored
file checks with exit code 0, the cluster builds from a clean local build tree, and the
missing analysis is explicit rather than faked.

## 8. Files changed (all under the worktree; no shared source modified)

Authored:

- `Poincare/Longrun/Entropy/Functional.lean`
- `Poincare/Longrun/Entropy/Certificate.lean`
- `Poincare/Longrun/Entropy/Bridge.lean`
- `Poincare/Longrun/Entropy/DiscreteHeat.lean`
- `Poincare/Longrun/Entropy/FiniteGeometry.lean`
- `Poincare/Longrun/Entropy/AxiomAudit.lean`
- `Poincare/Longrun/Entropy.lean`
- `longrun/logs/*.log`, `longrun/results/D3-entropy-interface.{md,json}`

Bootstrap (copied/symlinked, read-only or byte-identical):

- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`
- `.lake/packages` → shared prebuilt mathlib packages (symlink); local `.lake/build` and
  `.lake/config`
- `Poincare/Basic.lean`, `Poincare/Stage1/{CurvatureAlgebra,RiemannAdapter}.lean`
- consumed D2 sources listed in §1

## 9. Reproduce from scratch

```bash
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D3_entropy_interface
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
lake build Poincare
for f in Poincare/Longrun/Entropy/Functional.lean \
         Poincare/Longrun/Entropy/Certificate.lean \
         Poincare/Longrun/Entropy/Bridge.lean \
         Poincare/Longrun/Entropy/DiscreteHeat.lean \
         Poincare/Longrun/Entropy/FiniteGeometry.lean \
         Poincare/Longrun/Entropy/AxiomAudit.lean \
         Poincare/Longrun/Entropy.lean; do
  lake env lean "$f" || exit 1
done
lake env lean Poincare/Longrun/Entropy/AxiomAudit.lean
```

## 10. Sandbox / delivery note

The canonical shared control-plane directory
`/data3/guoshaoyang/workdir/lean_poincare/longrun/results/` is outside this session's
`workspace-write` sandbox (workspace = the task worktree). This card and its JSON twin are
therefore written at `longrun/results/D3-entropy-interface.{md,json}` inside the worktree.

Direct write to the shared path was attempted:

```text
cp <worktree>/longrun/results/D3-entropy-interface.md \
   /data3/guoshaoyang/workdir/lean_poincare/longrun/results/D3-entropy-interface.md
→ cp: cannot create regular file '...': Permission denied   (exit code 1)
```

The one-shot escalation retry (`sandbox_permissions=danger-full-access`) failed closed:
`requires approval, but no approval channel is available`. **Integrator action:** copy the
two mirrored files to the shared `longrun/results/` directory, or grant the worker write
access to it.
