# D1-perelman-ledger — theorem ledger and interface map

**Task id:** `D1-perelman-ledger`
**Worker id:** `D1-perelman-ledger-builder`
**Model:** `deepseek-v4.1-flash-expires-on-0910`
**Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D1_perelman_ledger`
**Started:** 2026-09-08T19:51:00+08:00
**Finished:** 2026-09-08T19:58:00+08:00
**Overall status:** `CHECKED INTERFACE LAYER` — both Lean files compile with exit code 0 and every
toy declaration depends only on `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`).
No monotonicity theorem is claimed; the F/W/μ and κ-noncollapsing statements are explicit
hypothesis structures.

**Sandbox note.** The shared result-card directory
`/data/home/guoshaoyang/workdir/lean_poincare/longrun/results/` is outside the session
workspace (`.../longrun/worktrees/D1_perelman_ledger`) and every write there was denied under
`workspace-write`; the required escalation had no approval channel. The two result cards are
therefore stored inside the worktree at `longrun/results/D1-perelman-ledger.md` and
`longrun/results/D1-perelman-ledger.json` (plus identical copies at the worktree root) for the
integrator to promote.

## 1. Files changed

| Path (worktree-relative) | Role |
| --- | --- |
| `lean-toolchain` | pins `leanprover/lean4:v4.34.0-rc2` |
| `lakefile.toml` | isolated `PerelmanLedger` package, `Ledger` library, mathlib pinned to rev `7974e751bece493b6ff508039423ca9fa2452fa8` |
| `lake-manifest.json` | manifest copied from `poincare-lab` with the package name updated |
| `.lake/packages` | symlink to the prebuilt `poincare-lab/.lake/packages` (mathlib reused, never rebuilt) |
| `Ledger/PerelmanDefinitions.lean` | the interface layer (329 lines) |
| `Ledger/DefinitionSmoke.lean` | toy lemmas + `#print axioms` evidence (203 lines) |
| `verification/00_clean_rebuild.log` … `04_smoke.log` | captured command outputs and exit codes |

No shared `Poincare/` file was touched. No file outside the worktree could be written.

## 2. Verification evidence

All commands were run from the worktree with
`ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan`.

```text
$ lake env lean Ledger/PerelmanDefinitions.lean
exit code: 0

$ lake build +Ledger.PerelmanDefinitions:olean
Build completed successfully (2999 jobs).
exit code: 0

$ lake build +Ledger.DefinitionSmoke:olean
Build completed successfully (3554 jobs).
exit code: 0

$ lake env lean Ledger/DefinitionSmoke.lean
exit code: 0 (axiom report below)
```

Forbidden-token scan over the two deliverables
(`\bsorry\b|\baxiom\b|\bunsafe\b|native_decide|proof_wanted`): **0 matches**. The only literal
occurrences of the word `axioms` are the required `#print axioms` commands.

The same commands were then repeated from an empty `.lake/build` directory
(`verification/00_clean_rebuild.log`); all exited `0`, and
`lake build +Ledger.DefinitionSmoke:olean` produced both
`.lake/build/lib/lean/Ledger/PerelmanDefinitions.olean` and
`.lake/build/lib/lean/Ledger/DefinitionSmoke.olean` (exit code 0).

### 2.1 `#print axioms` output (verbatim from `verification/04_smoke.log`)

```text
'Perelman.MetricFlowData.Icc_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'Perelman.MetricFlowData.Icc_zero_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'Perelman.hasMetricTimeDerivative_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'Perelman.satisfies_ricciFlow_const_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Perelman.toyF_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'Perelman.toyW_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Perelman.perelmanMu_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Perelman.FMonotonicity.apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Perelman.WMonotonicity.apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Perelman.MuMonotonicity.apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Perelman.FMonotonicity_iff_antitoneOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Perelman.WMonotonicity_iff_antitoneOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Perelman.riemannianVolumeDensity_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Perelman.riemannianVolumeDensity_pos_of_posDef' depends on axioms: [propext, Classical.choice, Quot.sound]
'Perelman.CurvatureBoundedOn.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The three reported constants are Lean's standard logical axioms. `sorryAx` is absent, as are
project axioms, `unsafe`, and `native_decide`.

## 3. Interface inventory

The layer is deliberately split into **data**, **hypotheses**, and **checked toy lemmas**.
Structures are conditional interfaces: they never assert that a Ricci flow, a Riemannian volume
form, or a monotonicity theorem exists.

### 3.1 Metric flow data (`Ledger/PerelmanDefinitions.lean`)

| Lean declaration | Kind | Statement | Explicit assumptions |
| --- | --- | --- | --- |
| `MetricFamily` | abbrev | `ℝ → Bundle.RiemannianMetric (fun x => TangentSpace I x)` | charted-space context |
| `RicciTensor`, `RicciFamily` | abbrev | pointwise symmetric bilinear form; time-dependent | no mathlib Ricci tensor exists |
| `HasMetricTimeDerivative g dg t` | def | `∀ x v w, HasDerivAt (s ↦ g s (v,w)) (dg x v w) t` | none beyond data |
| `negTwoRicci` | def | the bilinear form `-2 Ric` | none |
| `MetricFlowData` | structure | time domain + metric family + Ricci tensor + `∂ₜg = -2Ric` | `0 ∈ T`; `OrdConnected T`; `ContDiff ℝ ⊤` of every coefficient; `Ric` symmetric; the pointwise flow equation |
| `MetricFlowData.Icc_subset` | **checked lemma** | `s, t ∈ T → Icc s t ⊆ T` | `flow : MetricFlowData` |

`MetricFlowData` does **not** assert existence of a flow: the `ricciFlow_equation` field is a
derivative identity that a term must prove. The structure is nevertheless inhabited: see
`constantFlow` in the smoke file.

### 3.2 Volume form

| Lean declaration | Kind | Statement | Explicit assumptions |
| --- | --- | --- | --- |
| `gramMatrix` | def | `(g x (b i) (b j))ᵢⱼ` | basis `b : Basis (Fin n) ℝ (TangentSpace I x)` |
| `riemannianVolumeDensity` | def | `√det (gramMatrix g x b)` (local `√det g`) | basis |
| `RiemannianVolumePredicate` | abbrev | `ℝ → MetricFamily → Measure M → Prop`, a **parameter** | `[MeasurableSpace M]` |
| `HasFrameVolumeDensity` | def | concrete predicate: `μ = μ₀.withDensity (ofReal √det g)` in a global frame | reference measure, global frame |
| `VolumeFormData` | structure | measure family + is-Riemannian-volume + locally finite + non-zero | the three hypotheses are fields |

The Riemannian-volume property is a parameter because mathlib has no Riemannian volume form.
`HasFrameVolumeDensity` supplies the classical local formula; a global construction still needs
a partition-of-unity gluing argument (blocker).

### 3.3 Scalar curvature

| Lean declaration | Kind | Statement | Explicit assumptions |
| --- | --- | --- | --- |
| `scalarCurvatureInBasis` | def | `∑ᵢⱼ g^{ij} Ric_{ij}` in a basis | basis |
| `IsScalarCurvature g Ric R` | def | `R t x` equals the trace formula **in every basis** | basis-independence is part of the statement |
| `ScalarCurvatureData` | structure | `scalar : ℝ → M → ℝ` + trace hypothesis + spatial continuity | `is_scalar`, `scalar_continuous` |

The trace is not constructed from a Riemann tensor; it is data satisfying the trace formula.

### 3.4 F/W functionals and profiles

| Lean declaration | Kind | Statement | Explicit assumptions |
| --- | --- | --- | --- |
| `perelmanF` | def | `∫ (R + |∇f|²) e^{-f} dμ` (Bochner integral) | `[MeasurableSpace M]` |
| `perelmanW` | def | `∫ [τ(|∇f|²+R) + f - n] (4πτ)^{-n/2} e^{-f} dμ` | `[MeasurableSpace M]`, `n : ℕ` |
| `HasUnitMass` | def | `∫ (4πτ)^{-n/2} e^{-f} dμ = 1` | admissibility predicate |
| `perelmanMu` | def | `sInf (Set.range W)` | no minimizer asserted |
| `FProfile`, `WProfile` | def | time profiles `t ↦ F(t)`, `t ↦ W(t)` | `[MeasurableSpace M]` |
| `directionalDerivative` | def | `mfderiv I 𝓘(ℝ,ℝ) f x (b i)` | basis |
| `gradientNormSqInBasis` | def | `∑ᵢⱼ g^{ij} ∂ᵢf ∂ⱼf` | basis |

The integrals are total Bochner integrals; finiteness/integrability is **not** asserted and must
be supplied as a hypothesis in any monotonicity theorem.

### 3.5 Monotonicity and curvature hypotheses

| Lean declaration | Kind | Statement |
| --- | --- | --- |
| `FMonotonicity flow F` | structure (Prop) | `AntitoneOn F flow.timeDomain` |
| `WMonotonicity flow W` | structure (Prop) | `AntitoneOn W flow.timeDomain` |
| `MuMonotonicity J μ` | structure (Prop) | `MonotoneOn μ J` |
| `ScalarCurvatureLowerBound S c` | structure (Prop) | `∀ t ∈ T, ∀ x, c ≤ S.scalar t x` |
| `RicciLowerBound flow κ` | structure (Prop) | `∀ t ∈ T, ∀ x v, κ g(v,v) ≤ Ric(v,v)` |
| `CurvatureBoundedOn Rm t K s` | def | `∀ y ∈ s, |Rm t y| ≤ K` |
| `KappaNoncollapsing flow Rm vol κ r₀` | structure (Prop) | `κ > 0`, `r₀ > 0`, and curvature bound on a ball implies `Vol ≥ κ rⁿ` |

## 4. Major Perelman steps mapped to interfaces

Status legend: `interface` = compiles but is a conditional statement layer; `checked` =
kernel-checked Lean declaration; `blocked` = mathematical step not yet formalizable; `planned` =
no interface yet.

| Step | Perelman / Morgan–Tian source | Lean interface | Depends on | Status | Principal blockers | Next task ids |
| --- | --- | --- | --- | --- | --- | --- |
| **P-F-MONO** F monotone | Perelman 2002 §1 Thm 1.1; MT Ch. 5 | `FMonotonicity` over `FProfile`/`perelmanF` | `MetricFlowData`, `ScalarCurvatureData`, `gradientNormSqInBasis`, `perelmanF` | blocked | no backward heat equation, no manifold integration by parts, no integrability, scalar curvature is data | `D3-entropy-interface`, `D4-evolution-theorem` |
| **P-W-MONO** W monotone | Perelman 2002 §3 Thm 1.1; MT Ch. 5–6 | `WMonotonicity` over `WProfile`/`perelmanW` | P-F-MONO, `perelmanW`, `HasUnitMass` | blocked | all of P-F-MONO plus τ-differentiation and Gaussian normalization | `D3-entropy-interface` |
| **P-MU-MONO** μ non-decreasing | Perelman 2002 §6; MT Ch. 6 | `MuMonotonicity`, `perelmanMu` | P-W-MONO, `HasUnitMass` | blocked | minimizer of the unit-mass infimum not constructed | `D3-entropy-interface` |
| **P-NLC** no local collapsing | Perelman 2002 §4 Thm 4.1; MT Ch. 8 | `KappaNoncollapsing` | P-W-MONO, P-MU-MONO, `CurvatureBoundedOn`, `VolumeFormData` | blocked | reduced length/volume absent; only scalar `|Rm|` stand-in; no ball-volume comparison | `D3-kappa-ledger` |
| **P-REDUCED-VOL** reduced length/volume | Perelman 2002 §7 | none yet | P-F-MONO | planned | path spaces, reduced-length minimizers, Jacobian comparison | `D3-kappa-ledger`, `D3-surgery-ledger` |
| **P-HARNACK** Harnack inequality | Perelman 2002 §9 | none yet | P-W-MONO, P-REDUCED-VOL | planned | conjugate heat kernel, Li–Yau argument | `D3-entropy-interface` |
| **P-KAPPA-SOL** κ-solution classification | Perelman 2003 §1; MT Ch. 9 | none yet | P-NLC | planned | full curvature operator, 3D ancient-solution classification | `D3-surgery-ledger` |
| **P-CANON** canonical neighborhoods | Perelman 2003 §3; MT Ch. 12–13 | none yet (needs pointed GH structure) | P-KAPPA-SOL, P-NLC | planned | pointed Gromov–Hausdorff compactness; ε-close model geometries | `D3-surgery-ledger` |
| **P-LONG** long-time behaviour | Perelman 2003 §2; MT Part III | none yet | P-CANON, P-NLC | planned | collapsing theory, hyperbolic 3-manifold geometry, compactness | `D3-surgery-ledger` |
| **P-SURG** surgery | Perelman 2003 §4; MT Ch. 13–18 | none yet | P-CANON, P-LONG | planned | surgery algorithm, a priori curvature estimates, discrete flow | `D3-surgery-ledger` |
| **P-EXT** extinction / Poincaré | Perelman 2003 §3–4; MT Ch. 18–19 | none yet | P-SURG | planned | topological classification of the surgery decomposition | `D3-surgery-ledger`, `D6-weekly-release` |

The machine-readable version of this table, with the full node/edge DAG (43 nodes, 60 edges,
11 major-step nodes), is `longrun/results/D1-perelman-ledger.json`.

## 5. Checked toy lemmas (the compile-first evidence)

The smoke file proves the following, all kernel-checked:

1. `MetricFlowData.Icc_subset` and `MetricFlowData.Icc_zero_subset` — the `OrdConnected` time
   domain is an interval, so `Icc 0 t ⊆ T` for every `t ∈ T`.
2. `hasMetricTimeDerivative_const` and `satisfies_ricciFlow_const_zero` — a constant metric
   family has zero time derivative, and with zero Ricci tensor it satisfies the pointwise
   Ricci-flow equation. This shows the `MetricFlowData` equation field is satisfiable.
3. `constantFlow` — the constant family with zero Ricci tensor is a term of `MetricFlowData` for
   any interval containing `0`; the interface is inhabited without claiming a Ricci flow exists.
4. `toyF_mono` — the finite F model is monotone in the scalar curvature when the weights are
   non-negative.
5. `toyW_nonneg` — the finite W model is non-negative when every bracket and every weight is
   non-negative.
6. `perelmanMu_le` — `perelmanMu W ≤ W f` whenever `Set.range W` is bounded below.
7. `FMonotonicity.apply`, `WMonotonicity.apply`, `MuMonotonicity.apply` — monotonicity
   hypotheses transfer to ordered pairs of times/scales.
8. `FMonotonicity_iff_antitoneOn`, `WMonotonicity_iff_antitoneOn` — the hypothesis structures
   are exactly the `AntitoneOn` statements they record.
9. `riemannianVolumeDensity_nonneg`, `riemannianVolumeDensity_pos_of_posDef` — `√det g ≥ 0`, and
   `√det g > 0` when the Gram matrix is positive definite.
10. `CurvatureBoundedOn.mono` — the curvature-bound predicate is monotone in the bound.

## 6. Unresolved blockers and follow-up

1. **Curvature objects.** Mathlib v4.34.0-rc2 has no Riemann/Ricci tensor and no scalar
   curvature. `RicciTensor` and `ScalarCurvatureData` are data; the trace formula is a field.
   Follow-up: a `D2-ricci-ode-cluster` / geometry-foundation task to construct the Ricci tensor
   from a connection, then prove basis-independence of the trace.
2. **Riemannian volume form.** No global volume form; `HasFrameVolumeDensity` is frame-based.
   Follow-up: `D2-geometry-foundation` should add a partition-of-unity construction.
3. **Flow existence and smoothness.** No smooth manifold of metrics and no Hamilton short-time
   existence; `MetricFlowData` records only the equation. Follow-up: `D2-pde-foundation`.
4. **Heat equation / integration by parts.** Required for P-F-MONO and P-W-MONO. Follow-up:
   `D3-entropy-interface`, `D4-evolution-theorem`.
5. **Reduced length/volume, compactness, surgery.** Required from P-NLC onward. Follow-up:
   `D3-kappa-ledger`, `D3-surgery-ledger`.
6. **Result-card placement.** The shared `longrun/results/` directory is not writable from this
   sandbox; the integrator must copy `longrun/results/D1-perelman-ledger.{md,json}` from the
   worktree.

## 7. Honesty statement

No statement in this ledger is presented as a proof of the Poincaré conjecture or of Perelman's
monotonicity theorems. Every mathematical assertion beyond a definition is either (a) a
kernel-checked toy/structural lemma listed in §5, or (b) an explicit hypothesis field of a
structure. The forbidden constructs `sorry`, `axiom`, `unsafe`, `native_decide`, and
`proof_wanted` do not occur in either Lean file.
