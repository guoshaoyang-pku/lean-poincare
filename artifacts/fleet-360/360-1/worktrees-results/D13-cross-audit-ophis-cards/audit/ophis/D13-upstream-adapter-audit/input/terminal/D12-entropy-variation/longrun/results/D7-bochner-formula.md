# D7-bochner-formula — result card

**Task id:** `D7-bochner-formula`
**Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-bochner-formula`
**Generated (UTC):** 2026-09-09T17:52:32Z
**Verdict:** `TASK_DONE` — kernel-checked Bochner/Weitzenböck layer: `BochnerCertificate` with the
1-form Laplacian, rough Laplacian and Ricci contraction as explicit fields; a kernel-checked
Euclidean instance (`Ric = 0`) whose identity is exactly the finite-dimensional Laplacian
commutation; a kernel-checked gradient-estimate toy `Δ(|∇f|²) ≥ 2|Hess f|²` under the `Ricci ≥ 0`
certificate field; and the smooth Bochner formula as an explicit state-only `Prop` with named
blockers and the exact missing mathlib dependencies.

---

## 0. Bottom line

| item | result |
| --- | --- |
| new files (only under `release/Poincare/D7/Bochner/`) | **7 Lean files, 1469 lines, 103 declarations** |
| compiled with `lake env lean` from the worktree root | **7/7 authored files exit 0** (`longrun/d7-bochner-logs/gate_exit_codes.txt`) |
| whole release package `lake build` | **exit 0** (8987 jobs); the scaffold's own `D6AUDIT` verdict is `PASS` |
| `#print axioms` audit | **103 declarations**: cone `{propext, Classical.choice, Quot.sound}` (91), cone `{propext}` (2), no dependencies (10); **0 nonstandard cones, 0 incomplete-proof markers** |
| forbidden-token scan (comment/string aware) | **0 hard** in the 7 authored files; D7-wide scan (41 files) also **0 hard**, 0 soft |
| copied scaffold files modified | **0** (`diff -rq` against `../D7-divergence-ibp`, `.lake` and the new files/logs excluded: **empty**) |
| `BochnerCertificate` | explicit fields `oneFormLaplacian`, `roughLaplacian`, `ricciContraction` + proof field `oneFormLaplacian = roughLaplacian + ricciContraction` + `Ricci ≥ 0` field |
| Euclidean instance | `euclideanBochnerCertificate` with `Ric = 0`; the identity is proved by the kernel-checked commutation `diff j (laplacian f) = laplacian (diff j f)` |
| gradient estimate | `GradientCertificate.gradient_estimate : 2 * |Hess f|² ≤ Δ(|∇f|²)`; sharpness `… = 2 * |Hess f|² ↔ Ric = 0`; negative control shows `Ric ≥ 0` is essential |
| blocked items | 3 state-only `Prop`s (`SmoothBochnerFormulaStatement`, `SmoothBochnerWeitzenbockStatement`, `SmoothBochnerGradientEstimateStatement`), 5 named blockers, 7 exact missing mathlib dependencies |

**Not claimed:** no proof of the smooth Bochner formula, the smooth Weitzenböck identity or a
smooth gradient estimate; no construction of the Hessian, the Laplace–Beltrami operator, the rough
Laplacian or manifold-level Riemann/Ricci curvature. Those are the blocked `Prop`s of Section 6.

---

## 1. Scaffold, environment, and source integrity

The worktree was scaffolded from `../D7-divergence-ibp/` as instructed.

| command | exit | note |
| --- | --- | --- |
| `cp -al ../D7-divergence-ibp/. .` | **1** | every entry fails with `Invalid cross-device link` (hard links are rejected on this filesystem); this matches the D7-divergence card |
| `cp -a ../D7-divergence-ibp/. .` | **0** | full copy (393 MB, including the prebuilt `.lake`); scaffold intact |
| `diff -rq ../D7-divergence-ibp . -x .lake -x Bochner -x d7-bochner-logs -x 'D7-bochner-formula.md' -x 'D7-bochner-formula.json'` | **0** | no output: **no shared file differs**; the only additions are the new `release/Poincare/D7/Bochner/` files and this card |

Environment:

| key | value |
| --- | --- |
| Lean | `4.34.0-rc2` (commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`) |
| mathlib | `7974e751bece493b6ff508039423ca9fa2452fa8` |
| root package | `D7RiemannCurvatureTensorRoot` (re-exposes `release/.lake`, so `lake env lean` works from the worktree root) |
| release package | `PoincareRelease` (`release/lakefile.toml`) |

New files:

| file | lines | declarations | role |
| --- | --- | --- | --- |
| `release/Poincare/D7/Bochner/Basic.lean` | 213 | 20 | finite-dimensional pointwise model, scalar Bochner quantities, `BochnerCertificate` |
| `release/Poincare/D7/Bochner/Euclidean.lean` | 255 | 28 | finite cyclic difference model, Laplacian commutation, Euclidean (`Ric = 0`) certificate |
| `release/Poincare/D7/Bochner/GradientEstimate.lean` | 174 | 10 | `GradientCertificate`, unconditional Bochner inequality and the gradient estimate |
| `release/Poincare/D7/Bochner/Example.lean` | 228 | 21 | concrete flat/curved certificates, estimate instances, negative control |
| `release/Poincare/D7/Bochner/Blocked.lean` | 329 | 24 | state-only smooth Bochner formula, Weitzenböck and gradient-estimate `Prop`s, blockers, missing dependencies |
| `release/Poincare/D7/Bochner/Probe.lean` | 122 | 0 | compilable mathlib/D7 API probe (`#check` / `#check_failure`) |
| `release/Poincare/D7/Bochner/Audit.lean` | 148 | 0 | 103 `#print axioms` commands |

Source hashes are recorded in the `.json` card (`new_files[].sha256`).

---

## 2. Mathlib probe (task item 1 of the layer)

`release/Poincare/D7/Bochner/Probe.lean` compiles (exit 0): **49 `#check`** commands and
**12 `#check_failure`** commands.

### 2.1 Present and reused

`CovariantDerivative`, `CovariantDerivative.leviCivitaConnection`,
`CovariantDerivative.IsLeviCivitaConnection`,
`CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection`,
`CovariantDerivative.IsLeviCivitaConnection.apply_eq` (the Koszul formula),
`CovariantDerivative.IsLeviCivitaConnection.uniqueness`, `CovariantDerivative.torsion`,
`CovariantDerivative.IsMetricCompatible`, `mfderiv`, `ContMDiff`, `TangentSpace`,
`RiemannianBundle`, `IsRiemannianManifold`, `ModelWithCorners`, `IsManifold`, `iteratedFDeriv`,
`fderiv`, `Finset.sum_sub_distrib`, `Finset.sum_congr`, `Fin.sum_univ_two`, `Pi.single`, `Matrix`.

The pinned mathlib therefore **does** provide a covariant derivative and a constructed Levi-Civita
connection on the tangent bundle; the connection itself is not a blocker.

### 2.2 Absent at the pinned revision (recorded with `#check_failure`)

`Hessian`, `LaplaceBeltrami`, `Riemann`, `Ricci`, `Bochner`, `Weitzenbock`,
`CovariantDerivative.secondCovariantDerivative`, `CovariantDerivative.curvature`,
`Manifold.curvature`, `Laplacian`, `roughLaplacian`, `RiemannianVolumeMeasure`.

There is **no curvature file at all** under `Mathlib/Geometry/Manifold` at this revision, so the
D7 curvature/Ricci layers remain finite-dimensional algebraic models. Consequently the smooth
Bochner formula is the blocked `Prop` of Section 6.

---

## 3. `BochnerCertificate` (task item 1)

`release/Poincare/D7/Bochner/Basic.lean`:

```lean
structure BochnerCertificate where
  dim : ℕ
  grad : Fin dim → ℝ
  hess : Matrix (Fin dim) (Fin dim) ℝ
  ric : Matrix (Fin dim) (Fin dim) ℝ
  oneFormLaplacian : ℝ     -- ⟨Δ₁ df, df⟩
  roughLaplacian : ℝ       -- ⟨∇*∇ df, df⟩
  ricciContraction : ℝ     -- Ric(∇f, ∇f)
  bochner : oneFormLaplacian = roughLaplacian + ricciContraction
  ricci_eq : ricciContraction = ricciPairing ric grad
  ricci_nonneg : 0 ≤ ricciContraction
```

The three terms of the Weitzenböck identity are **fields**, the identity
`oneFormLaplacian = roughLaplacian + ricciContraction` is a **proof field**, `ricci_eq` ties the
Ricci contraction to the model pairing `ricciPairing ric grad = ∑ i, ∑ j, grad i * ric i j * grad j`,
and `ricci_nonneg` is the `Ricci ≥ 0` certificate field used by the estimate. The scalar
quantities are

* `hessNormSq hess = ∑ i, ∑ j, (hess i j)² = |Hess f|²` (`hessNormSq_nonneg`),
* `gradLaplacianDot grad gradLap = ∑ i, grad i * gradLap i = ⟨∇f, ∇Δf⟩`,
* `ricciPairing ric grad = Ric(∇f, ∇f)`.

Certificate lemmas: `bochner'`, `oneFormLaplacian_eq_roughLaplacian_of_ricci_zero`,
`roughLaplacian_le_oneFormLaplacian`, `ricciPairing_nonneg`, `ricciContraction_eq_sub`.

---

## 4. The Euclidean instance: the identity reduces to Laplacian commutation (task item 2a)

`release/Poincare/D7/Bochner/Euclidean.lean` builds a genuine finite-dimensional model in which the
`Ric = 0` identity is a commutation theorem rather than a tautology.

**The model.** For a finite direction type `ι` and modulus `N`, the configuration space is the
finite abelian group `Conf ι N = ι → ZMod N`; with `eᵢ = Pi.single i 1`,

```lean
shift i f x = f (x + eᵢ)                    -- translation in direction i
diff  i f x = shift i f x - f x             -- forward difference in direction i
laplacian f = ∑ i, diff i (diff i f)        -- discrete Laplacian
```

**The commutation.** Because the configuration space is an abelian group, shifts commute
(`shift_comm`), hence differences commute (`diff_comm`), and the Laplacian commutes with every
difference:

```lean
theorem diff_laplacian_comm (j : ι) (f : Conf ι N → ℝ) :
    diff j (laplacian f) = laplacian (diff j f)
```

**The Euclidean certificate.** For `ι = Fin n`, the model gradient and Hessian at `x` are
`grad i = diff i f x` and `hess i j = diff i (diff j f) x` (symmetric by `hess_symm`), and the two
pairings are

```lean
oneFormLaplacian f x = ∑ i, laplacian (diff i f) x * diff i f x   -- ⟨Δ₁ df, df⟩
roughLaplacian  f x = ∑ i, diff i (laplacian f) x * diff i f x    -- ⟨∇*∇ df, df⟩
```

The reduction is stated exactly:

```lean
theorem oneFormLaplacian_eq_roughLaplacian_of_commutation
    (h : ∀ i, laplacian (diff i f) x = diff i (laplacian f) x) :
    oneFormLaplacian f x = roughLaplacian f x
```

and the actual identity follows by summing `diff_laplacian_comm`:

```lean
theorem oneFormLaplacian_eq_roughLaplacian : oneFormLaplacian f x = roughLaplacian f x
def euclideanBochnerCertificate (f x) : BochnerCertificate := …   -- ric = 0, ricciContraction = 0
```

The certificate's fields are witnessed by
`euclideanBochnerCertificate_ric : (euclideanBochnerCertificate f x).ric = 0`,
`euclideanBochnerCertificate_ricciContraction`,
`euclideanBochnerCertificate_oneFormLaplacian` and `euclideanBochnerCertificate_hess_symm`.

**Why this is the flat Bochner identity.** On flat space the Hodge–de Rham Laplacian on `df` and
the rough Laplacian both compute `d(Δf)` by commuting partial derivatives; the model above is the
finite-difference form of that commutation, so the `Ric = 0` case of `Δ₁ = ∇*∇ + Ric` is *exactly*
Laplacian commutation.

---

## 5. The gradient-estimate toy (task item 2b)

`release/Poincare/D7/Bochner/GradientEstimate.lean` records the remaining pointwise scalar fields
of the Bochner formula on top of a `BochnerCertificate`:

```lean
structure GradientCertificate where
  B : BochnerCertificate
  gradLap : Fin B.dim → ℝ                    -- ∇Δf
  laplacianGradNormSq : ℝ                    -- Δ(|∇f|²)
  rough_decomposition : B.roughLaplacian = hessNormSq B.hess + gradLaplacianDot B.grad gradLap
  product_rule : laplacianGradNormSq = 2 * B.oneFormLaplacian
  harmonic : gradLaplacianDot B.grad gradLap = 0
```

The main theorem is the requested estimate:

```lean
theorem gradient_estimate (C : GradientCertificate) :
    2 * hessNormSq C.B.hess ≤ C.laplacianGradNormSq
```

Its proof uses the certificate identity, the rough decomposition, the product rule, harmonicity
`⟨∇f, ∇Δf⟩ = 0`, and **essentially** the `Ricci ≥ 0` field `C.B.ricci_nonneg`. The unconditional
form is also proved:

```lean
theorem bochner_inequality (C : GradientCertificate) :
    2 * hessNormSq C.B.hess ≤ C.laplacianGradNormSq - 2 * gradLaplacianDot C.B.grad C.gradLap
```

Sharpness: in the harmonic model the estimate is an equality exactly when the Ricci contraction
vanishes,

```lean
theorem gradient_estimate_eq_iff_ricci_zero (C : GradientCertificate) :
    C.laplacianGradNormSq = 2 * hessNormSq C.B.hess ↔ C.B.ricciContraction = 0
```

and `laplacianGradNormSq_nonneg` shows `Δ(|∇f|²) ≥ 0` in the model under harmonicity and
`Ric ≥ 0`. `gradientCertificateOfData` packages explicit `grad`/`hess`/`gradLap`/`ric` data into a
`GradientCertificate`.

### 5.1 Non-vacuity and the negative control

`release/Poincare/D7/Bochner/Example.lean`:

| example | data | result |
| --- | --- | --- |
| `flatExampleCertificate` | `∇f = (1,2)`, `Hess = [[3,1],[1,4]]`, `Ric = 0` | `oneFormLaplacian = roughLaplacian = 27`, `|Hess|² = 27` |
| `curvedExampleCertificate` | `∇f = (1,2)`, `Hess = [[3,1],[1,4]]`, `Ric = [[2,0],[0,3]]` | `|Hess|² = 27`, `Ric(∇f,∇f) = 14`, `roughLaplacian = 27`, `oneFormLaplacian = 41` |
| `curvedExampleGradient` | same, harmonic | `Δ(|∇f|²) = 82`, estimate `54 ≤ 82` **strict** (`curvedExampleGradient_estimate_strict`) |
| `flatExampleGradient` | same, `Ric = 0`, harmonic | `Δ(|∇f|²) = 2|Hess f|² = 54` (`flatExampleGradient_estimate_eq`) |
| `negativeControl` | `RawGradientModel` **without** the Ricci-sign field: `|Hess|² = 27`, `Ric = -100`, `Δ(|∇f|²) = -146` | `negativeControl_estimate_fails : ¬ (2*27 ≤ -146)` |

The negative control keeps every scalar relation of the pointwise model (Weitzenböck, rough
decomposition, product rule, harmonicity) but drops `Ric ≥ 0`; the estimate then fails. This shows
the Ricci-sign certificate field is essential, not decorative.

---

## 6. State-only smooth Bochner formula with missing dependencies (task item 3)

`release/Poincare/D7/Bochner/Blocked.lean` records the smooth statements as `def … : Prop` with
named blockers; there is no proof attempt anywhere.

```lean
def SmoothBochnerFormulaStatement : Prop :=
  ∀ … (D : SmoothBochnerDatum I M), IsSmoothBochnerDatum I M D →
    ∀ f x, D.laplacianGradNormSq f x
      = 2 * D.hessNormSq f x + 2 * D.gradLapPairing f x + 2 * D.ricciPairing f x

def SmoothBochnerWeitzenbockStatement : Prop :=
  ∀ … , D.oneFormLaplacian f x = D.roughLaplacian f x + D.ricciPairing f x

def SmoothBochnerGradientEstimateStatement : Prop :=
  ∀ … , D.laplaceBeltrami f x = 0 → 2 * D.hessNormSq f x ≤ D.laplacianGradNormSq f x
```

`SmoothBochnerDatum` collects the metric pairing, the gradient, and the missing scalar quantities
(`laplaceBeltrami`, `hessNormSq`, `gradLapPairing`, `ricciPairing`, `oneFormLaplacian`,
`roughLaplacian`, `laplacianGradNormSq`); `IsSmoothBochnerDatum` records the geometric properties
the missing constructions would have to satisfy, including that the gradient is the metric dual of
`mfderiv` of a smooth function, the Weitzenböck decomposition, the rough expansion, `Ric ≥ 0`, and
harmonicity. Consistency is checked: `SmoothBochnerDatum.isSmooth_zero_of_isEmpty` proves the zero
datum satisfies the predicate on an empty manifold, while
`SmoothBochnerDatum.zero_not_isSmooth_of_nontrivial` records that it fails on a nontrivial one.

Named blockers (each checked nonempty by `…_ne_nil`):

| blocker | missing construction |
| --- | --- |
| `B-D7-BOCHNER-HESSIAN` | second covariant derivative (Hessian) `∇²f` and `|∇²f|²` |
| `B-D7-BOCHNER-LAPLACE-BELTRAMI` | Laplace–Beltrami operator `Δf = tr_g ∇²f` |
| `B-D7-BOCHNER-ROUGH-LAPLACIAN` | rough Laplacian `∇*∇` on 1-forms and its pairing with `df` |
| `B-D7-BOCHNER-MANIFOLD-CURVATURE` | manifold Riemann curvature endomorphism and Ricci contraction |
| `B-D7-BOCHNER-WEITZENBOCK` | the identity `Δ₁ = ∇*∇ + Ric` and the scalar formula |

Exact missing mathlib dependencies (`MissingMathlibDependencies`, 7 entries): Hessian, Laplace–
Beltrami operator, rough Laplacian on 1-forms, manifold curvature, the Weitzenböck identity, the
scalar Bochner formula, and the gradient estimate. Present dependencies
(`PresentMathlibDependencies`, 5 entries): `CovariantDerivative`,
`CovariantDerivative.leviCivitaConnection` and its metric-compatibility/torsion-free proofs,
`mfderiv`/`ContMDiff`/`TangentSpace`/`RiemannianBundle`/`IsRiemannianManifold`,
`ModelWithCorners`/`IsManifold`, and the D7 finite-dimensional certificates.

---

## 7. Verification

### 7.1 Compile gate

Every authored file was compiled with `lake env lean <file>` from the worktree root:

```
release/Poincare/D7/Bochner/Audit.lean 0
release/Poincare/D7/Bochner/Basic.lean 0
release/Poincare/D7/Bochner/Blocked.lean 0
release/Poincare/D7/Bochner/Euclidean.lean 0
release/Poincare/D7/Bochner/Example.lean 0
release/Poincare/D7/Bochner/GradientEstimate.lean 0
release/Poincare/D7/Bochner/Probe.lean 0
```

(`longrun/d7-bochner-logs/gate_exit_codes.txt`, full output in `gate.log`.) The whole release
package also builds: `cd release && lake build` exit 0 (8987 jobs), and the scaffold's own
`D6AUDIT` verdict is `PASS`.

Harness-gate replication (every `.lean` file in the worktree except `.lake`, compiled with
`lake env lean` from the worktree root): **105 files, 0 failures**
(`longrun/d7-bochner-logs/harness_gate_exit_codes.txt`).

### 7.2 `#print axioms` audit

`release/Poincare/D7/Bochner/Audit.lean` runs `#print axioms` on all **103** principal
declarations. Cone summary:

| cone | count |
| --- | --- |
| no dependencies | 10 |
| `{propext}` | 2 |
| `{propext, Classical.choice, Quot.sound}` | 91 |

**0** declarations with a nonstandard cone, **0** incomplete-proof markers, **0** `native_decide`,
**0** `proof_wanted`. Machine-readable per-declaration records:
`longrun/d7-bochner-logs/axiom-records.json`; full output:
`longrun/d7-bochner-logs/audit_build.log`.

### 7.3 Forbidden-token scan

`input/d5-tools/scan_forbidden.py` (comment/string aware) reports:

| scope | files | hard | soft |
| --- | --- | --- | --- |
| `release/Poincare/D7/Bochner` | 7 | **0** | 0 |
| `release/Poincare/D7` | 41 | **0** | 0 |

### 7.4 Source integrity

`diff -rq ../D7-divergence-ibp . -x .lake -x Bochner -x d7-bochner-logs -x 'D7-bochner-formula.md'
-x 'D7-bochner-formula.json'` exits 0 with no output: **0 shared scaffold files changed**.

---

## 8. Honest boundary

This card claims exactly what the kernel checked:

* a finite-dimensional `BochnerCertificate` with the three terms of the Weitzenböck identity as
  explicit fields and the identity as a proof field;
* a finite-dimensional Euclidean instance (`Ric = 0`) whose identity is the discrete Laplacian
  commutation;
* a finite-dimensional gradient-estimate toy `Δ(|∇f|²) ≥ 2|Hess f|²` under the `Ricci ≥ 0`
  certificate field, with sharpness and a negative control;
* state-only `Prop`s for the smooth Bochner formula, the smooth Weitzenböck identity and the smooth
  gradient estimate, with named blockers and exact missing dependencies.

It does **not** claim the smooth Bochner formula, the smooth Weitzenböck identity, a smooth gradient
estimate, or the construction of the Hessian, Laplace–Beltrami operator, rough Laplacian or
manifold curvature. The D7 curvature/Ricci layers remain finite-dimensional algebraic models.

---

## 9. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-bochner-formula
for f in release/Poincare/D7/Bochner/*.lean; do lake env lean "$f" || exit 1; done
cd release && lake build
cd .. && python3 input/d5-tools/scan_forbidden.py release/Poincare/D7/Bochner
```

Logs: `longrun/d7-bochner-logs/` (`gate_exit_codes.txt`, `gate.log`, `audit_build.log`,
`axiom-records.json`, `lake_build_full.log`, `forbidden-scan-bochner.json`,
`forbidden-scan-d7-wide.json`, `source_integrity_diff.txt`).

---

TASK_DONE — `longrun/results/D7-bochner-formula.md`
