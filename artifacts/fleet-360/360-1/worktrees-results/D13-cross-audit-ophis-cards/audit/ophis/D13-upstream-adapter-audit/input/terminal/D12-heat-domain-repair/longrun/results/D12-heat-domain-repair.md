# D12-heat-domain-repair — result card

- **Task id:** `D12-heat-domain-repair`
- **Stage / lane:** D12 / repair of the D7 initial-condition domain (NOT the heat equation)
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D12-heat-domain-repair`
- **Generated (UTC):** `2026-09-10T15:47:00Z` (elapsed ~1.9 h of the 4 h invocation; the milestone content is complete ahead of the 12 h/24 h/72 h schedule)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2`; mathlib `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by `lake-manifest.json`)
- **Module root:** `release/Poincare/D12/HeatDomain/` (6 files, all authored in this worktree)
- **Verdict:** **UNCONDITIONAL — THE D7/D11 INITIAL-CONDITION DOMAIN IS REPAIRED: A VERSIONED ADMISSIBLE-TEST-FUNCTION INTERFACE (V1, `C_c` AND CONTINUOUS-INTEGRABLE CLASSES) IS DEFINED, THE D11 EUCLIDEAN CORE INHABITS IT IN EVERY DIMENSION, COMPACT FINITE-MEASURE COMPATIBILITY WITH THE UNCHANGED LEGACY D7 FIELD IS PROVED WITH A DOWNSTREAM UPGRADE CONSTRUCTION, AND AN EXPLICIT FAST-GROWING COUNTEREXAMPLE (`exp ‖y‖⁴`) FORMALLY FALSIFIES THE LEGACY LITERAL CONDITION IN EVERY POSITIVE DIMENSION.**

> Every declaration is kernel-checked with no `sorry`, no `axiom`, no `unsafe`, no `native_decide`
> and no `proof_wanted`. All **50** audited declarations depend only on
> `[propext, Classical.choice, Quot.sound]` (programmatic fail-closed `Lean.collectAxioms`
> re-check: `D12HeatDomainAxiomCheck: PASS`). No D7/D10/D11 source was edited (only the six files
> under `release/Poincare/D12/HeatDomain/` are new); the Laplacian is untouched (the D11
> `laplacianLinearMap`, which is mathlib's `Δ` on all `C²` functions).

---

## 0. Bottom line

| item | result |
| --- | --- |
| new files (only under `release/Poincare/D12/HeatDomain/`) | **6 Lean files, 50 audited declarations** |
| `lake build` from `release/` | **exit 0**, `Build completed successfully (9179 jobs)` |
| compile gate (dispatcher form: `lake env lean <file>`, cwd = worktree root) | **6/6 authored files exit 0**; full worktree gate **297/297 exit 0** |
| forbidden-token scan (`input/d5-tools/scan_forbidden.py`) | **0 hard / 0 soft** matches |
| `#print axioms` / `Lean.collectAxioms` | **50/50 in the single approved cone**, fail-closed (`D12HeatDomainAxiomCheck: PASS`) |
| versioned admissible-test-function interface (v1) | `AdmissibleTestClass` + `WeakInitialConditionFor`, with the `C_c` and continuous-integrable classes |
| D11 Euclidean core inhabits the interface | **every dimension `n : ℕ`**, both classes (`flatHeatKernelCore_weakInitialConditionFor_integrableClass`, `…_ccClass`); nondegenerate bump example with limit `1` |
| compact finite-measure compatibility | `WeakInitialCondition ↔ FullInitialCondition` (and versioned variants) under `[CompactSpace X] [IsFiniteMeasure D.volume] [OpensMeasurableSpace X]`; downstream upgrade `toHeatKernelData_of_weak_compact_finiteMeasure : HeatKernelData X`; legacy D7 `punitHeatKernelData` checked |
| explicit counterexample to the legacy condition | `fastFunction n y = exp (‖y‖⁴)`: `¬ Integrable (K · f)` for every `t > 0`, `n ≥ 1`; `¬ (flatHeatKernelCore n).FullInitialCondition` for every `n ≥ 1` |
| legacy definitions | **unchanged** (`Poincare.D7.HeatKernel.HeatKernelData`, D11 `HeatKernelCore`/`FullInitialCondition`/`WeakInitialCondition` untouched); justified in the compact finite-measure scope by proved compatibility |

**Not claimed:** no manifold heat-kernel existence, no parametrix, no parabolic regularity, no
Gaussian bounds on manifolds, nothing about the Poincaré conjecture or Ricci flow. The repair is a
domain repair of the initial-condition test-function quantifier, exactly as tasked.

---

## 1. What was built

| file | lines | role |
| --- | --- | --- |
| `TestFunction.lean` | 149 | the versioned admissible-test-function interface (v1): `AdmissibleTestClass` (class + continuity/integrability certificates), the `C_c` and continuous-integrable classes, `WeakInitialConditionFor`, tightness to D11's `WeakInitialCondition` |
| `FlatInstance.lean` | 148 | the D11 Euclidean core inhabits the v1 interface in **every dimension**, both classes; nondegenerate compactly supported bump `max 0 (1 - ‖z‖²)` with limit `1` |
| `CompactCompatibility.lean` | 173 | precisely scoped compact finite-measure compatibility: full = weak = versioned; downstream upgrade to the legacy D7 datum; `PUnit` check on the legacy D7 instance |
| `Counterexample.lean` | 327 | product structure of Lebesgue measure on `EuclideanSpace ℝ (Fin n)`, infinite measure of half-spaces, `fastFunction`, non-integrability of `K · f` for every `t > 0`, `¬ FullInitialCondition` for every `n ≥ 1`, no D7 datum with the explicit kernel in positive dimensions |
| `All.lean` | 28 | umbrella module |
| `AxiomAudit.lean` | 161 | 50 `#print axioms` + fail-closed programmatic `Lean.collectAxioms` re-check |
| **total** | **986** | |

Namespace: `Poincare.D12.HeatDomain`. Nothing outside `release/Poincare/D12/HeatDomain/` was
written (verified with `find release -name '*.lean' -newer <snapshot>`); the root-level
`lakefile.toml` / `lake-manifest.json` / `lean-toolchain` / `.lake -> release/.lake` scaffold added
for the worktree-root compile gate is pure build configuration (same pattern as the D11 repair
attempt-1 scaffold, documented there).

---

## 2. The versioned admissible-test-function interface (v1)

The defect repaired (D11 `HeatKernelBridge.Basic`, D7 `HeatKernel.Basic`): the literal
initial condition quantifies over **all** continuous test functions

```
FullInitialCondition D := ∀ (x) (f), Continuous f →
  Tendsto (fun t => ∫ y, D.kernel x y t * f y ∂D.volume) (𝓝[>] 0) (𝓝 (f x))
```

The Bochner integral of a non-integrable integrand is `0` (`MeasureTheory.integral_undef`), so a
continuous test function growing faster than every Gaussian makes the left side vanish identically
while `f x ≠ 0` (formalised in §5). The v1 repair makes the test-function domain an explicit part
of the statement:

```
structure AdmissibleTestClass (X) [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X) where
  cls : (X → ℝ) → Prop
  cls_continuous : ∀ ⦃f⦄, cls f → Continuous f
  cls_integrable : ∀ ⦃f⦄, cls f → Integrable f μ

def WeakInitialConditionFor (D : HeatKernelCore X) (C : AdmissibleTestClass X D.volume) : Prop :=
  ∀ (x : X) (f : X → ℝ), C.cls f →
    Tendsto (fun t : ℝ => ∫ y, D.kernel x y t * f y ∂D.volume) (𝓝[>] (0 : ℝ)) (𝓝 (f x))
```

* the two standard classes (v1) are `continuousCompactSupportClass μ` (`C_c`:
  `Continuous f ∧ HasCompactSupport f`) and `continuousIntegrableClass μ`
  (`Continuous f ∧ Integrable f μ`);
* `AdmissibleTestClass.v1 : ℕ := 1` is the version tag; versioning is by naming + tag, the legacy
  definitions are never edited;
* `WeakInitialConditionFor.iff_integrableClass`: for the integrable class the v1 condition is
  *exactly* D11's `HeatKernelCore.WeakInitialCondition` — the repair is an interface change (the
  class is part of the statement), not a change of the proved mathematics;
* `C_c` is an admissible subclass of the integrable class
  (`continuousCompactSupportClass_subset_continuousIntegrableClass`), via
  `Continuous.integrable_of_hasCompactSupport` under the standard hypothesis
  `[IsFiniteMeasureOnCompacts μ]` (expanded: satisfied by Lebesgue measure on `ℝⁿ` and by every
  finite measure);
* no use of `FullInitialCondition` is made anywhere in positive dimension; the D11 core datum is
  consumed as it is, and its Laplacian (D11 `laplacianLinearMap`, mathlib's `Δ` on `C²`) is not
  replaced or redefined.

## 3. The D11 Euclidean core inhabits the interface in every dimension

```
flatHeatKernelCore_weakInitialConditionFor_integrableClass (n : ℕ) :
  WeakInitialConditionFor (flatHeatKernelCore n)
    (AdmissibleTestClass.continuousIntegrableClass (flatHeatKernelCore n).volume)

flatHeatKernelCore_weakInitialConditionFor_ccClass (n : ℕ) :
  WeakInitialConditionFor (flatHeatKernelCore n)
    (AdmissibleTestClass.continuousCompactSupportClass volume)
```

Both are re-typed from the D11 theorems `flatKernel_tendsto_integral` /
`flatKernel_tendsto_integral_of_hasCompactSupport` (proved there from the D10 Gaussian mass,
semigroup and peak-function machinery); `(flatHeatKernelCore n).volume = volume` is D11 `rfl`.

**Non-vacuity, tested concretely.** `bump n z = max 0 (1 - ‖z‖²)` is continuous, compactly
supported (support inside the compact closed unit ball), `bump n 0 = 1 ≠ 0`, and

```
bump_weakInitialCondition (n : ℕ) :
  Tendsto (fun t => ∫ y, flatKernel n 0 y t * bump n y) (𝓝[>] 0) (𝓝 1)
```

so the interface is inhabited by a nondegenerate test function and the asserted limit value is
nonzero — the repaired condition is not vacuous and not the trivial zero statement.

## 4. Precisely scoped compatibility for compact finite-measure settings

The regularity hypothesis that makes the legacy literal field sound is exactly: *every continuous
test function is integrable*. It is proved automatic in the compact finite-measure scope, with all
hypotheses expanded:

```
continuous_integrable_of_compactSpace_finiteMeasure {X} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Continuous f) : Integrable f μ
```

(boundedness from compactness via `BoundedContinuousFunction.mkOfCompact`, integrability from
boundedness + finite measure via `BoundedContinuousFunction.integrable`). Consequences:

```
weakInitialCondition_iff_full_of_compact_finiteMeasure :
  D.WeakInitialCondition ↔ D.FullInitialCondition

weakInitialConditionFor_integrableClass_iff_full_of_compact_finiteMeasure :
  WeakInitialConditionFor D (continuousIntegrableClass D.volume) ↔ D.FullInitialCondition

weakInitialConditionFor_ccClass_iff_full_of_compact_finiteMeasure :
  WeakInitialConditionFor D (continuousCompactSupportClass D.volume) ↔ D.FullInitialCondition
```

(the last one additionally uses that on a compact space every continuous function has compact
support, `ccClass_cls_iff_continuous_of_compactSpace`, so all three conditions coincide there).

**Downstream use (construction, not proposition):**

```
noncomputable def toHeatKernelData_of_weak_compact_finiteMeasure [CompactSpace X]
    [IsFiniteMeasure D.volume] [OpensMeasurableSpace X] (h : D.WeakInitialCondition) :
    Poincare.D7.HeatKernel.HeatKernelData X
```

a core satisfying the repaired condition upgrades to a genuine legacy D7 datum through the
unchanged D11 bridge map `toHeatKernelData`; `toHeatKernelData_of_weak_compact_finiteMeasure_toCore`
returns the original core (`rfl`), and the resulting datum carries the legacy literal
`initialCondition` field. The legacy D7 definitions are therefore **kept unchanged and justified in
exactly the scope where they are correct** (compact manifolds have finite Riemannian volume, which
is the intended downstream setting). The compatibility is exercised on an existing D7 object, not
an ad hoc one: `punitHeatKernelData_core_weak_iff_full` (Dirac measure on the compact space
`PUnit`).

## 5. The explicit fast-growing counterexample to the old condition

The D11 card documented the obstruction informally (`f y = exp (‖y‖³)` on `ℝⁿ`, `n ≥ 1`, "not
formalised"). It is now **formalised** (with the algebraically cleaner quartic `exp (‖y‖⁴)`, which
gives the elementary comparison `‖y‖⁴ ≥ ‖y‖²/(4t)` for `‖y‖² ≥ 1/(4t)`):

* measure preparation (uses the product structure of Lebesgue measure on
  `EuclideanSpace ℝ (Fin n)` through the measure-preserving `PiLp.ofLp`):
  `volume_halfspace_eq_top : volume {y | R ≤ y ⟨0, hn⟩} = ⊤` for `n ≥ 1` (the factor at
  coordinate `0` is `volume (Ici R) = ∞`), and hence `volume_set_norm_ge_eq_top : volume {y | R ≤ ‖y‖} = ⊤`;
* `fastFunction n y = exp (‖y‖⁴)` is continuous, nonnegative, `fastFunction n 0 = 1`;
* **non-integrability for every positive time**:
  `notIntegrable_fast_times_kernel (n) (hn : 0 < n) {t} (ht : 0 < t) :
  ¬ Integrable (fun y => flatKernel n 0 y t * fastFunction n y) volume` — on
  `{y | R ≤ ‖y‖}` with `R = √(1/(4t)) + 1` the exponent `-‖y‖²/(4t) + ‖y‖⁴` is nonnegative, so the
  integrand dominates the positive constant `(4 π t)^(-n/2)`; the `lintegral` lower bound against
  the indicator of an infinite-measure set gives `∫⁻ ENNReal.ofReal ∘ f = ∞`, hence no finite
  integral (`HasFiniteIntegral` fails), hence not integrable;
* `integral_fast_times_kernel_eq_zero : ∫ y, flatKernel n 0 y t * fastFunction n y = 0` for every
  `t > 0` (`integral_undef`);
* therefore, by uniqueness of limits in `ℝ`,

```
not_fullInitialCondition_flat_of_pos (n : ℕ) (hn : 0 < n) :
  ¬ (flatHeatKernelCore n).FullInitialCondition

not_fullInitialCondition_flat_one :
  ¬ (flatHeatKernelCore 1).FullInitialCondition

flat_positive_dimension_weak_not_full (n : ℕ) (hn : 0 < n) :
  (flatHeatKernelCore n).WeakInitialCondition ∧ ¬ (flatHeatKernelCore n).FullInitialCondition

not_exists_heatKernelData_flat_of_pos (n : ℕ) (hn : 0 < n) :
  ¬ ∃ D : Poincare.D7.HeatKernel.HeatKernelData (EuclideanSpace ℝ (Fin n)),
      D.toCore = flatHeatKernelCore n

not_exists_heatKernelData_flat_one :
  ¬ ∃ D : Poincare.D7.HeatKernel.HeatKernelData (EuclideanSpace ℝ (Fin 1)),
      D.toCore = flatHeatKernelCore 1
```

The last two are the downstream use of the counterexample at the D7 level: D11's tightness theorem
`flat_exists_heatKernelData_iff` reduces the existence of a legacy `HeatKernelData` with the
explicit Euclidean kernel to the legacy full condition, so no such datum exists in any positive
dimension — the weak (versioned) condition of this repair is exactly the statement available there.
`flat_positive_dimension_weak_not_full` states the **precise scope** of the repair: in every
positive dimension the repaired condition holds for the D11 Euclidean core while the legacy literal
condition fails; on compact finite-measure spaces they coincide (§4). The informal obstruction of
the D11 card is thereby superseded by a checked counterexample.

## 6. Semantic classification (per acceptance rules)

| declaration group | class | justification |
| --- | --- | --- |
| `AdmissibleTestClass`, `WeakInitialConditionFor`, class definitions | model/interface (v1 definitions) | definitional; certificates make the condition well-posed; nothing assumed |
| `flatHeatKernelCore_weakInitialConditionFor_{integrableClass,ccClass}`, bump theorems | model — explicit Euclidean model, unconditional in `n` | proved from D11 weak-condition theorems (themselves kernel-checked); no dimension restriction, no extra hypothesis |
| `continuous_integrable_of_compactSpace_finiteMeasure` and the three compact compatibility equivalences + upgrade | general, with fully expanded hypotheses `[CompactSpace X] [IsFiniteMeasure D.volume] [OpensMeasurableSpace X]` | hypotheses are expanded (compactness ⇒ boundedness ⇒ integrability under finite measure) and justified for the compact-manifold application (finite Riemannian volume) |
| `volume_{halfspace,set_norm_ge}_eq_top`, `fastFunction`, `notIntegrable_fast_times_kernel`, `not_fullInitialCondition_flat_of_pos` | general — all `n ≥ 1`, `t > 0`, unconditional | the counterexample is a theorem about the explicit kernel, not a model assumption |
| conditional | none | no declaration assumes `FullInitialCondition` or any equivalent hypothesis in positive dimension; `iff_integrableClass` is a definitional equivalence |

No theorem is a restatement of an assumption; every hypothesis is expanded to a mathlib-level
regularity condition and consumed by a downstream theorem (see §4).

## 6.1 Independent adversarial review

An independent adversarial source audit (separate subagent, 8-point checklist against the final
checksummed state, cross-checking every mathlib lemma cited against the pinned mathlib source)
returned **ALL 8 ITEMS OK — no defects**, with three minor notes, all addressed:

| review item | verdict |
| --- | --- |
| statement correctness / no hidden vacuity | OK — `WeakInitialConditionFor` is exactly the class-restricted D11 condition; classes inhabited; limit `1` realised |
| `FullInitialCondition` never a hypothesis in positive dimension | OK — appears only inside refuted assumptions of negated conclusions, in genuine compact-scope equivalences, and as the D7 datum's own field in the PUnit check |
| counterexample genuine (`exp (‖y‖⁴)`, kernel expansion, dominance, `integral_undef`, NeBot limit contradiction) | OK — line-by-line verification against mathlib |
| measure transport (WithLp projection, `PiLp.volume_preserving_ofLp`, `volume_pi_pi`, `prod_eq_top_iff`) | OK — no gap |
| compact compatibility hypotheses sufficient | OK — `mkOfCompact` + `BoundedContinuousFunction.integrable`; genuine constructions |
| interface sanity (honest exposure of `IsFiniteMeasureOnCompacts`; genuine iff with D11) | OK |
| no sorry/axiom/unsafe; fail-closed audit | OK — build-log PASS, 50/50 declarations |
| non-vacuity (bump is the real bump, nonzero limit) | OK |

Minor notes addressed: the `ofLp` description is now precise (projection from the `WithLp` wrapper,
not literally `id`); the audit module documents that the `#print axioms` lines are informational and
the enforceable gate is the fail-closed `run_cmd`; the redundant `measurableSet_halfspace` lemma is
retained as a documented fact. The review record is in
`longrun/results/D12-heat-domain-repair.json` (`independent_review`).

## 7. Compile evidence

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D12-heat-domain-repair

# 1. build the release package (cwd = release/)
cd "$WT/release"
lake build                                   # exit 0: "Build completed successfully (9179 jobs)"
lake build Poincare.D12.HeatDomain.AxiomAudit # exit 0

# 2. per-file gate exactly as the dispatcher runs it (cwd = worktree root)
cd "$WT"
for f in release/Poincare/D12/HeatDomain/{TestFunction,FlatInstance,CompactCompatibility,Counterexample,All,AxiomAudit}.lean; do
  lake env lean "$f"    # 6/6 exit 0
done

# 3. full worktree gate (cwd = worktree root, all 297 .lean files)
find . -name '*.lean' -not -path './.lake/*' -not -path './.git/*' -not -path './.dshpkg/*' \
  -print0 | xargs -0 -n1 -P8 sh -c 'lake env lean "$0" > /dev/null 2>&1; echo "$?:$0"' \
  > logs/d12_gate_raw.txt                    # 297/297 exit 0, 0 failures

# 4. forbidden-token scan (comment/string aware)
python3 input/d5-tools/scan_forbidden.py release/Poincare/D12/HeatDomain
                                             # 0 hard / 0 soft matches, exit 0
```

Evidence files: `logs/d12_gate_raw.txt`, `logs/D12_axiom_audit.out`.

## 8. Axiom evidence (kernel trust, separate from compilation)

`release/Poincare/D12/HeatDomain/AxiomAudit.lean` prints `#print axioms` for all 50 declarations
and re-checks every cone programmatically with `Lean.collectAxioms`, **failing the build** on any
axiom outside `{propext, Classical.choice, Quot.sound}` (fail-closed: the `run_cmd` block collects
all unapproved dependencies and `throwError`s if any exist).

| item | value |
| --- | --- |
| `#print axioms` declarations | **50 / 50** (49 depend on the approved cone, 1 — `AdmissibleTestClass.v1` — depends on no axioms) |
| programmatic re-check | `D12HeatDomainAxiomCheck: PASS — all 50 declarations of the D12 heat-domain repair depend only on [propext, Classical.choice, Quot.sound]` |
| `sorryAx` / project axiom / `unsafe` / `native_decide` / `proof_wanted` / `admit` | **0 / 0 / 0 / 0 / 0 / 0** |

Fail-closed behaviour is verified by an explicit negative control (`logs/D12_audit_negcontrol.lean`,
run in `/tmp`, outside the package): the same audit logic applied to a declaration depending on an
unapproved axiom `badAxiom` triggers `logError` + `throwError` (exit 1) — the audit cannot silently
pass a bad cone.

`Classical.choice` enters only through mathlib's classical lemmas (e.g. the D11
`laplacianLinearMap` used by the core datum, and measure-theory library results); no project
axiom is introduced.

## 9. Source hashes (fresh, sha256)

| file | sha256 |
| --- | --- |
| `release/Poincare/D12/HeatDomain/TestFunction.lean` | `ef9e4e33e41a2619b142be105a284a5406f1325b12310a181e84dfcf44be707e` |
| `release/Poincare/D12/HeatDomain/FlatInstance.lean` | `d575c81e52b484194efb7d611c2e6e0fb706dd22c85734a80e287cdf47c5d67b` |
| `release/Poincare/D12/HeatDomain/CompactCompatibility.lean` | `73f0428c505502b1334429caa9e20d2d73c61ae67a350c392a3af9973033afd3` |
| `release/Poincare/D12/HeatDomain/Counterexample.lean` | `c73cb9a65d8fb163c5faae6bfff251dfa1ca4ab9b70875c74f8c96f346369e2e` |
| `release/Poincare/D12/HeatDomain/All.lean` | `60e994aaf2f2d2a171d045b8c967db4c7a4cf9b5203650340f6606b292f33be9` |
| `release/Poincare/D12/HeatDomain/AxiomAudit.lean` | `f4cb2fd6f407186623640a8b5d8815d2ef9c9279e29399eccf1512bad9dc80bc` |
| root `lakefile.toml` (build config only) | `b56f13927f2c63a07221b0fde9a31d20d42f99b80e90d4330aa7c06de6c642fa` |
| root `lake-manifest.json` (build config only) | `cbc45ee0bd591606b3bb5ba38c38e41f3d317c59f99cb2dfb0adc7d33b32c3d0` |
| root `lean-toolchain` (build config only) | `8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88` |

No D7/D10/D11 source file was modified (only the six D12 files are newer than the task snapshot).

## 10. Reuse and licenses

mathlib4 is consumed at the pinned revision `7974e751bece493b6ff508039423ca9fa2452fa8`
(`https://github.com/leanprover-community/mathlib4`, Apache 2.0) through `lake`; no source was
copied into this worktree, no upstream PR was made, and no admitted proof from any external
development was imported. The only outside-package input is mathlib itself (pinned in
`lake-manifest.json`).

## 11. Honest scope and deviations

- **Proved and unconditional:** the v1 interface and its two admissible classes; inhabitation by
  `flatHeatKernelCore n` for every `n` (both classes); nondegenerate bump test; compact
  finite-measure compatibility (full = weak = versioned) with expanded hypotheses; the downstream
  D7 upgrade construction; infinite measure of half-spaces; non-integrability of `K · exp (‖y‖⁴)`
  for every `t > 0`; `¬ (flatHeatKernelCore n).FullInitialCondition` for every `n ≥ 1`; no D7
  `HeatKernelData` with the explicit Euclidean kernel exists in any positive dimension.
- **Deviation from the D11 informal note:** the counterexample uses `exp (‖y‖⁴)` instead of the
  informal `exp (‖y‖³)` (identical mathematical role — growth faster than every Gaussian — with
  cleaner algebra); the informal obstruction is superseded by the checked one, both documented.
- **Legacy definitions unchanged:** `Poincare.D7.HeatKernel.HeatKernelData` and D11
  `HeatKernelCore`/`FullInitialCondition`/`WeakInitialCondition` are imported and consumed, never
  edited; downstream compatibility is proved, not assumed, before any claim about the legacy
  interface is made.
- **Laplacian untouched:** no new operator is defined; the interface builds on `HeatKernelCore`,
  whose Laplacian is D11's `laplacianLinearMap` (mathlib's `Δ` on all `C²` functions).
- **Not claimed:** anything about the heat equation itself (D11 proved `∂ₜK = ΔK`), manifold heat
  kernels, uniqueness of the Cauchy problem, distribution theory, or the Poincaré conjecture.

Result card (machine-readable): `longrun/results/D12-heat-domain-repair.json`.

TASK_DONE — `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D12-heat-domain-repair/longrun/results/D12-heat-domain-repair.md`
