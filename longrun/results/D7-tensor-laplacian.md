# D7-tensor-laplacian — result card

**Task id:** `D7-tensor-laplacian`
**Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-tensor-laplacian`
**Generated (UTC):** 2026-09-09T18:33:09Z
**Verdict:** `TASK_DONE` — kernel-checked tensor Laplacian layer: a rough-Laplacian interface on
tensor data over the D7 connection layer; the commutation formula in the finite-dimensional model
under a stated curvature certificate (general form, commuting-frame form, parallel-curvature form
`Δ(∇_X s) - ∇_X(Δ s) = 2 • ∑ᵢ R(eᵢ,X)(∇ᵢ s)`, stated Ricci certificate, and the frame trace
`(2 * scal) • s`); the scalar-curvature evolution identity
`∂ₜ scal = Δ scal + 2 |Ric|²` as an exact identity between interface fields under the stated flow
equation `∂ₜ g = -2 Ric`; and the smooth commutation/evolution formulas as state-only `Prop`s with
six named blockers and eight exact missing mathlib dependencies. No
`sorry` / `axiom` / `unsafe` / `native_decide` / `proof_wanted`.

---

## 0. Bottom line

| item | result |
| --- | --- |
| new files (only under `release/Poincare/D7/TensorLaplacian/`, plus the umbrella `release/Poincare/D7/TensorLaplacian.lean`) | **8 Lean files, 1803 lines, 109 authored declarations** |
| compiled with `lake env lean` from the worktree root | **8/8 authored files exit 0** (`longrun/d7tl-logs/gate_exit_codes.txt`) |
| whole release package `lake build` | **exit 0** (8982 jobs, `longrun/d7tl-logs/lake_build_full.log`); scaffold `D6AUDIT` verdict `PASS` |
| `#print axioms` audit | **159 principal declarations**: cone `{propext, Classical.choice, Quot.sound}` (147), no axioms (10), `{propext}` (2); **0 nonstandard cones, 0 `sorryAx`** |
| forbidden-token scan (comment/string aware) | **0 hard, 0 soft** in the 7 `TensorLaplacian/` files and the umbrella; D7-wide scan (36 files) also **0 hard, 0 soft** |
| copied scaffold files modified | **0** (345 files sha256-checked against `../D7-hamilton-short-time`, `.lake`/new files/logs excluded: 0 changed, 0 missing, 0 added) |
| item 1 | `TensorConnectionData` (tensor data over the D7 connection layer) + rough Laplacian `Δ s = ∑ᵢ ∇_{eᵢ}∇_{eᵢ} s` with linearity lemmas |
| item 2a | `roughLaplacian_commutator_general` (exact, no extra hypotheses), `..._of_bracket_zero`, `..._of_parallel` (`= 2 • ricciContraction`), `..._ricci` (stated Ricci certificate), `..._frame_trace` (`= (2 * scal) • s`) |
| item 2b | `scalarDeriv_eq : ∂ₜ scal = Δ scal + 2 |Ric|²` and `scalar_evolution` / `scalar_evolution_iff`, under the stated flow equation `h = -2 Ric` |
| item 3 | 4 state-only smooth `Prop`s, 6 named blockers (`B-D7-TL-*`), 8 exact missing mathlib dependencies, 5 present dependencies |
| non-vacuity | `so(3)` model: `|Ric|² > 0`, `so3EvolutionCertificate`, identity with strictly positive right-hand side; negative control `wrongBianchi_identity_fails` |

**Not claimed:** no smooth-manifold commutation formula, no smooth scalar-curvature evolution, no
construction of a smooth tensor bundle/connection, rough Laplacian, manifold curvature or Ricci
endomorphism, no Ricci-flow existence, and no Poincaré/Perelman content. The Ricci/scalar
identifications in the commutation layer and the Lichnerowicz/Bianchi inputs of the evolution layer
are **stated certificates**, not theorems of this layer.

---

## 1. Scaffold, environment, source integrity

The worktree was scaffolded from the direct dependency `../D7-hamilton-short-time` as instructed.

| command | exit | note |
| --- | --- | --- |
| `cp -al ../D7-hamilton-short-time/. .` | **1** | every entry fails with `Invalid cross-device link` (`EXDEV`); hard links are rejected on this filesystem, matching the sibling D7 cards |
| `cp -a ../D7-hamilton-short-time/. .` | **0** | full copy (383 MB, including the prebuilt `.lake`); scaffold intact |
| sha256 comparison against `../D7-hamilton-short-time` | **0** | 345 shared files checked, **0 changed, 0 missing, 0 added** (`.lake`, `release/Poincare/D7/TensorLaplacian*`, `longrun/d7tl-logs`, and this card excluded); `longrun/d7tl-logs/source_integrity.json` |

Environment:

| key | value |
| --- | --- |
| Lean | `4.34.0-rc2` (commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`) |
| Lake | `5.0.0-src+6a10ac8` |
| mathlib | `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by `release/lake-manifest.json`) |
| `ELAN_HOME` | `/data3/guoshaoyang/workdir/lean_poincare/elan` |
| root package | `D7RiemannCurvatureTensorRoot` (re-exposes `release/.lake`, so `lake env lean` works from the worktree root) |
| release package | `PoincareRelease` (`release/lakefile.toml`) |

New files (all under `release/`):

| file | lines | authored decls | role |
| --- | --- | --- | --- |
| `Poincare/D7/TensorLaplacian.lean` | 38 | 0 | umbrella module |
| `Poincare/D7/TensorLaplacian/Basic.lean` | 225 | 36 | `TensorConnectionData`, curvature certificate, `curvature_skew`, rough Laplacian |
| `Poincare/D7/TensorLaplacian/Commutation.lean` | 275 | 11 | per-direction identity, general/frame/parallel commutation, Ricci and scalar certificates |
| `Poincare/D7/TensorLaplacian/Evolution.lean` | 272 | 19 | `ricciNormSq`, `traceH`, `pairingH`, `ScalarEvolutionCertificate`, the identity |
| `Poincare/D7/TensorLaplacian/Example.lean` | 289 | 13 | scalar/vector/product inhabitants, `so(3)` witnesses, negative control |
| `Poincare/D7/TensorLaplacian/Blocked.lean` | 396 | 30 | smooth state-only `Prop`s, blockers, missing dependencies, zero-data consistency |
| `Poincare/D7/TensorLaplacian/Probe.lean` | 136 | 0 | compilable API probe: 81 `#check`, 12 `#check_failure` |
| `Poincare/D7/TensorLaplacian/Audit.lean` | 172 | 0 | 159 `#print axioms` commands |

Source hashes are recorded in the `.json` card (`new_files[].sha256`); per-file line/declaration
metrics are in `longrun/d7tl-logs/file_metrics.json`.

---

## 2. Item 1 — the rough Laplacian interface on tensor data

`release/Poincare/D7/TensorLaplacian/Basic.lean`:

```lean
structure TensorConnectionData (D : RiemannCurvatureData V ι) (T : Type*) [AddCommGroup T]
    [Module ℝ T] where
  nabla : V →ₗ[ℝ] T →ₗ[ℝ] T
  curvature : V →ₗ[ℝ] V →ₗ[ℝ] T →ₗ[ℝ] T
  curvature_certificate : ∀ (X Y : V) (s : T),
    nabla X (nabla Y s) - nabla Y (nabla X s) - nabla (D.conn.lie.bracket X Y) s =
      curvature X Y s
```

The base connection is the D7 `RiemannCurvatureData` (the D2 abstract Koszul connection with the
metric datum and the D7 curvature/Ricci layers); `T` is the module of tensor values. The
**curvature certificate** is the stated commutation relation `∇_X∇_Y s - ∇_Y∇_X s - ∇_{[X,Y]}s =
R(X,Y)s`. From it the layer derives `curvature_skew : R(X,Y)s = -R(Y,X)s`, `curvature_self`, and
`second_covariant_derivative_commutation`.

The **rough (connection) Laplacian** is defined as a linear map over the orthonormal basis
`eᵢ = D.metric.basis i`:

```lean
noncomputable def roughLaplacianₗ : T →ₗ[ℝ] T :=
  ∑ i : ι, (TD.nabla (D.metric.basis i)).comp (TD.nabla (D.metric.basis i))

noncomputable def roughLaplacian (s : T) : T := TD.roughLaplacianₗ s
```

with `roughLaplacian_apply : Δ s = ∑ᵢ ∇_{eᵢ}(∇_{eᵢ} s)` and the linearity lemmas
`roughLaplacian_zero/add/smul/neg/sub` and `roughLaplacian_eq_zero_of_nabla_nabla_eq_zero`.

The interface is inhabited: `scalarTensorData` (`T = ℝ`, zero connection), `vectorTensorData`
(`T = V`, `nabla = D.conn.nabla`, `curvature = D.curvature`, whose certificate is `rfl`), and
`prodTensorData` (componentwise product).

---

## 3. Item 2a — the commutation formula under the curvature certificate

`release/Poincare/D7/TensorLaplacian/Commutation.lean`.

### 3.1 The per-direction identity

`commutator_term` applies the curvature certificate twice (to `s` and to `∇ᵢ s`):

```
∇ᵢ∇ᵢ∇_X s - ∇_X∇ᵢ∇ᵢ s
  = R(eᵢ,X)∇ᵢ s + ∇_{[eᵢ,X]}∇ᵢ s + ∇ᵢ∇_{[eᵢ,X]} s + ∇ᵢ(R(eᵢ,X)s).
```

### 3.2 The general formula (unconditional under the certificate)

```lean
theorem roughLaplacian_commutator_general (X : V) (s : T) :
    Δ(∇_X s) - ∇_X(Δ s) =
      ∑ i, (R(eᵢ,X)(∇ᵢ s) + ∇_{[eᵢ,X]}(∇ᵢ s) + ∇ᵢ∇_{[eᵢ,X]} s + ∇ᵢ(R(eᵢ,X)s))
```

proved by summing `commutator_term` over the frame. No extra hypothesis is used.

### 3.3 Commuting frame and parallel curvature

`roughLaplacian_commutator_of_bracket_zero` drops the bracket terms under `[eᵢ,X] = 0`.
`HasParallelCurvature` is the certificate `∇ᵢ(R(eᵢ,X)s) = R(eᵢ,X)(∇ᵢ s)`, and
`ricciContraction X s = ∑ᵢ R(eᵢ,X)(∇ᵢ s)`; then

```lean
theorem roughLaplacian_commutator_of_parallel ... :
    Δ(∇_X s) - ∇_X(Δ s) = (2 : ℝ) • TD.ricciContraction X s
```

(the classical factor `2`).

### 3.4 The Ricci and scalar forms (stated certificates)

* `RicciCommutationCertificate` states `ricciContraction X s = ricciEndo X s`; then
  `roughLaplacian_commutator_ricci : Δ(∇_X s) - ∇_X(Δ s) = 2 • ricciEndo X s`.
* `ScalarCurvatureCommutationCertificate` adds the frame-trace certificate
  `∑ⱼ ricciEndo(eⱼ) s = scal • s`; then, for a self-commuting frame,
  `roughLaplacian_commutator_frame_trace : ∑ⱼ (Δ(∇_{eⱼ}s) - ∇_{eⱼ}(Δ s)) = (2 * scal) • s`,
  where `scal = D.scalarCurvature` is the D7 scalar curvature.
* `roughLaplacian_commutator_eq_zero_of_flat`: the flat consistency check.

The Ricci and scalar identifications are **certificates** (true for specific tensor
representations, not for an arbitrary `T`); the general and parallel formulas are unconditional.

---

## 4. Item 2b — the scalar-curvature evolution identity

`release/Poincare/D7/TensorLaplacian/Evolution.lean`.

### 4.1 The D7 interface quantities

* `ricciNormSq D = ∑ᵢ ∑ⱼ Ric(eᵢ,eⱼ)²` — `|Ric|²` in the orthonormal frame (`ricciNormSq_nonneg`);
* `traceH D h = ∑ᵢ h(eᵢ,eᵢ)`, `pairingH D h = ∑ᵢ ∑ⱼ h(eᵢ,eⱼ) Ric(eᵢ,eⱼ)`;
* `ricciFlowVelocity D = -2 Ric`, `IsRicciFlowVelocity D h := ∀ X Y, h X Y = -2 Ric X Y`;
* `traceH_ricciFlowVelocity : traceH D (-2Ric) = -2 scal` and
  `pairingH_ricciFlowVelocity : pairingH D (-2Ric) = -2 |Ric|²`.

### 4.2 The certificate and the identity

```lean
structure ScalarEvolutionCertificate (D : RiemannCurvatureData V ι) (h : V → V → ℝ) where
  scalPath : ℝ → ℝ
  scalDeriv : ℝ → ℝ            -- ∂ₜ scal
  lapScal : ℝ → ℝ              -- Δ scal
  divdivH : ℝ → ℝ              -- ∇ⁱ∇ʲhᵢⱼ
  velocity : IsRicciFlowVelocity D h          -- the stated flow equation ∂ₜ g = -2 Ric
  flow : ∀ t, HasDerivAt scalPath (scalDeriv t) t
  variation : ∀ t, HasDerivAt scalPath (-(-2 * lapScal t) + divdivH t - pairingH D h) t
  bianchi : ∀ t, divdivH t = -lapScal t
  anchor : scalPath 0 = D.scalarCurvature
```

The `variation` field is the Lichnerowicz trace variation `∂ₜ scal = -Δ(tr h) + ∇ⁱ∇ʲhᵢⱼ -
⟨h,Ric⟩` with `Δ(tr h) = -2 Δ scal`; `bianchi` is the contracted Bianchi identity for `h = -2 Ric`.
The proven chain is

```
-(-2 Δ scal) + ∇ⁱ∇ʲhᵢⱼ - ⟨h,Ric⟩
  = 2 Δ scal - Δ scal + 2 |Ric|²
  = Δ scal + 2 |Ric|².
```

The main results:

```lean
theorem ScalarEvolutionCertificate.scalarDeriv_eq (C) (t) :
    C.scalDeriv t = C.lapScal t + 2 * ricciNormSq D        -- exact identity between interface fields
theorem ScalarEvolutionCertificate.scalar_evolution (C) (t) :
    HasDerivAt C.scalPath (C.lapScal t + 2 * ricciNormSq D) t
theorem ScalarEvolutionCertificate.scalar_evolution_iff (C) (t) :
    HasDerivAt C.scalPath (C.lapScal t + 2 * ricciNormSq D) t ↔
      C.scalDeriv t = C.lapScal t + 2 * ricciNormSq D
```

plus `traceH_eq`, `pairingH_eq`, `variation_rhs_eq`, `scalar_evolution_forall`,
`scalPath_zero`, and the inhabited `flatCertificate`.

### 4.3 Non-vacuity and the negative control

`Example.lean`:

| item | result |
| --- | --- |
| `so3_ricciNormSq_pos` | `0 < |Ric|²` on the concrete `so(3)` model of `Poincare.D7.Curvature.Example` (`|Ric|² ≥ (1/2)²`) |
| `so3EvolutionCertificate` | a `ScalarEvolutionCertificate` over `so3` with `scal(t) = scal₀ + 2|Ric|²t`, `Δ scal = 0` |
| `so3_evolution_identity` | `∂ₜ scal = Δ scal + 2 |Ric|²` holds there |
| `so3_evolution_rhs_pos` | the right-hand side is strictly positive (not the trivial `0 = 0`) |
| `so3_vector_curvature_witness` | the vector representation has nonzero curvature `R(e₀,e₁)e₁ = ¼ e₀` |
| `wrongBianchiExample`, `wrongBianchi_identity_fails` | with the **opposite** Bianchi sign the model satisfies the flow and variation equations but the identity fails (`5 ≠ 1 + 2`); the Bianchi certificate is essential |

---

## 5. Item 3 — state-only smooth `Prop`s

`release/Poincare/D7/TensorLaplacian/Blocked.lean`. All items are `def ... : Prop` (or
structures), never axioms and never proved:

| declaration | content |
| --- | --- |
| `SmoothTensorLaplacianDatum` | schematic smooth datum: metric pairing, tensor covariant derivative, rough Laplacian, curvature/Ricci actions, abstract Lie bracket, smoothness predicate |
| `IsSmoothTensorLaplacianDatum` | the defining properties the missing constructions would satisfy (curvature certificate, smooth commutation, preservation of smooth fields) |
| `SmoothCurvatureCertificateStatement` | smooth `∇_X∇_Y s - ∇_Y∇_X s - ∇_{[X,Y]}s = R(X,Y)s` |
| `SmoothCommutationStatement` | smooth `Δ(∇_X s) - ∇_X(Δ s) = 2 Ric(X)s` |
| `SmoothFrameTraceCommutationStatement` | smooth frame trace `∑ᵢ (Δ(∇_{eᵢ}s) - ∇_{eᵢ}(Δ s)) = (2 scal) • s` over the datum's frame field |
| `SmoothScalarEvolutionDatum`, `IsSmoothScalarEvolutionDatum` | scalar fields, metric velocity, Ricci form, the flow equation, trace variation, Bianchi identity, pairing |
| `SmoothScalarEvolutionStatement` | smooth `∂ₜ R = ΔR + 2 |Ric|²` under `∂ₜ g = -2 Ric` |

Named blockers (each checked nonempty by `..._ne_nil`):

| blocker | missing construction |
| --- | --- |
| `B-D7-TL-SMOOTH-TENSOR-BUNDLE` | smooth tensor bundle `T^{r,s}M` and its smooth sections |
| `B-D7-TL-SMOOTH-TENSOR-CONNECTION` | covariant derivative on a tensor bundle induced by Levi-Civita |
| `B-D7-TL-SMOOTH-ROUGH-LAPLACIAN` | rough Laplacian `∇*∇` on smooth tensor fields |
| `B-D7-TL-MANIFOLD-CURVATURE` | manifold curvature endomorphism acting on tensors and its Ricci contraction |
| `B-D7-TL-SMOOTH-COMMUTATION` | the smooth commutation formula |
| `B-D7-TL-SMOOTH-SCALAR-EVOLUTION` | the smooth scalar evolution identity and its Lichnerowicz/Bianchi inputs |

Exact missing mathlib dependencies: 8 entries (`MissingMathlibDependencies`, length checked);
present and reused: 5 entries (`PresentMathlibDependencies`, length checked). Consistency:
`SmoothTensorLaplacianDatum.isSmooth_zero` and `SmoothScalarEvolutionDatum.isSmooth_zero` prove the
zero data satisfy the predicates, so the statements are not vacuous by construction.

---

## 6. Verification

### 6.1 Compile gate

Every authored file was compiled with `lake env lean <file>` from the worktree root:

```
release/Poincare/D7/TensorLaplacian.lean 0
release/Poincare/D7/TensorLaplacian/Basic.lean 0
release/Poincare/D7/TensorLaplacian/Commutation.lean 0
release/Poincare/D7/TensorLaplacian/Evolution.lean 0
release/Poincare/D7/TensorLaplacian/Example.lean 0
release/Poincare/D7/TensorLaplacian/Blocked.lean 0
release/Poincare/D7/TensorLaplacian/Probe.lean 0
release/Poincare/D7/TensorLaplacian/Audit.lean 0
```

(`longrun/d7tl-logs/gate_exit_codes.txt`, full output `longrun/d7tl-logs/gate.log`.) The whole
release package also builds: `cd release && lake build` exit 0 (8982 jobs,
`longrun/d7tl-logs/lake_build_full.log`), and the scaffold's `D6AuditReport` prints
`D6AUDIT VERDICT PASS — no sorryAx, no project axiom, no unsafe, no native_decide, no unapproved
axiom, no proof_wanted` (`longrun/d7tl-logs/d6audit_report.log`).

### 6.2 `#print axioms` audit

`release/Poincare/D7/TensorLaplacian/Audit.lean` runs `#print axioms` on all **159** principal
declarations of the namespace (the environment contains 343 constants in
`Poincare.D7.TensorLaplacian`; the remaining 184 are compiler-generated structure/eq/proof
auxiliaries). Cone summary:

| cone | count |
| --- | --- |
| `{propext, Classical.choice, Quot.sound}` | 147 |
| no axioms | 10 |
| `{propext}` | 2 |

**0** declarations with a nonstandard cone, **0** `sorryAx`, **0** `proof_wanted`, **0**
`native_decide`. Headline declarations (`roughLaplacian_commutator_general`,
`roughLaplacian_commutator_of_parallel`, `roughLaplacian_commutator_frame_trace`,
`scalarDeriv_eq`, `scalar_evolution`, `scalar_evolution_iff`, `so3_ricciNormSq_pos`,
`so3_evolution_identity`, `wrongBianchi_identity_fails`) all have the cone
`{propext, Classical.choice, Quot.sound}`. Machine-readable per-declaration records:
`longrun/d7tl-logs/axiom-records.json`; raw output `longrun/d7tl-logs/audit_out.txt`.

### 6.3 Forbidden-token scan

`input/d5-tools/scan_forbidden.py` (comment/string aware):

| scope | files | hard | soft |
| --- | --- | --- | --- |
| `release/Poincare/D7/TensorLaplacian` | 7 | **0** | 0 |
| umbrella + `release/Poincare/D7` | 36 | **0** | 0 |

### 6.4 Source integrity

345 shared files sha256-compared against `../D7-hamilton-short-time` (`.lake`, the new
`TensorLaplacian*` files, logs and this card excluded): **0 changed, 0 missing, 0 added**
(`longrun/d7tl-logs/source_integrity.json`).

### 6.5 Probe

`Probe.lean` compiles (exit 0) with **81 `#check`** and **12 `#check_failure`** commands. The
absent declarations recorded are `Hessian`, `LaplaceBeltrami`, `Riemann`, `Ricci`,
`roughLaplacian`, `TensorBundle`, `CovariantDerivative.curvature`,
`CovariantDerivative.secondCovariantDerivative`, `Manifold.curvature`, `Manifold.divergence`,
`RiemannianVolumeMeasure`, `Manifold.stokes`.

---

## 7. Honest boundary

This card claims exactly what the kernel checked:

* a finite-dimensional rough-Laplacian interface on tensor data over the D7 connection layer, with
  the curvature certificate and the derived first-pair antisymmetry;
* the unconditional general commutation formula, its commuting-frame specialization, and the
  parallel-curvature form `Δ(∇_X s) - ∇_X(Δ s) = 2 • ∑ᵢ R(eᵢ,X)(∇ᵢ s)`;
* the Ricci form and the frame-trace form `(2 * scal) • s` under **stated** Ricci/scalar
  certificates;
* the scalar-curvature evolution identity `∂ₜ scal = Δ scal + 2 |Ric|²` as an exact identity
  between interface fields, under the **stated** flow equation `∂ₜ g = -2 Ric` and the **stated**
  Lichnerowicz trace variation and contracted Bianchi identity;
* state-only `Prop`s for the smooth commutation formulas and the smooth scalar evolution, with
  named blockers and exact missing mathlib dependencies.

It does **not** claim the smooth commutation formula, the smooth scalar-curvature evolution, the
construction of a smooth tensor bundle/connection, rough Laplacian or manifold curvature, or any
Ricci-flow existence or Poincaré/Perelman content.

---

## 8. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-tensor-laplacian
for f in release/Poincare/D7/TensorLaplacian.lean release/Poincare/D7/TensorLaplacian/*.lean; do
  lake env lean "$f" || exit 1
done
cd release && lake build
cd .. && python3 input/d5-tools/scan_forbidden.py release/Poincare/D7/TensorLaplacian
```

Logs: `longrun/d7tl-logs/` (`gate_exit_codes.txt`, `gate.log`, `lake_build_full.log`,
`lake_build_exit.txt`, `d6audit_report.log`, `audit_out.txt`, `axiom-records.json`,
`forbidden-scan-tensorlaplacian.txt`, `forbidden-scan-d7-wide.txt`, `source_integrity.json`,
`file_metrics.json`).

---

TASK_DONE — `longrun/results/D7-tensor-laplacian.md`
