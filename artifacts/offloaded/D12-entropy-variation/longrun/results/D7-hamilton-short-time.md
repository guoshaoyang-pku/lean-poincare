# D7-hamilton-short-time — result card

**Task id:** `D7-hamilton-short-time`
**Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-hamilton-short-time`
**Generated (UTC):** 2026-09-09T16:48:27Z
**Verdict:** `TASK_DONE` — Hamilton 1982 short-time existence layer, kept honest. The
finite-dimensional matrix model defines `RicciFlowData` and `DeTurckCertificate` with every field
explicit; the algebraic Ricci–DeTurck equivalence is **kernel-checked in both directions** under
the stated gauge transform; uniqueness of the ODE system is proved from a **Lipschitz
interface**; parabolic short-time existence for the DeTurck flow and its conversion back to
Ricci flow are **state-only `Prop`s** with an eight-entry missing-dependency ledger. No
`sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted` in any authored file.

---

## 0. Bottom line

| item | result |
| --- | --- |
| new files (only under `release/Poincare/D7/ShortTime/`, plus the umbrella `ShortTime.lean`) | **10 Lean files, 1656 lines, 86 declarations** |
| compiled with `lake env lean` from the worktree root | **10/10 exit 0** (`longrun/d7hs-logs/exit_codes.txt`) |
| whole release package `lake build` | **exit 0** (8974 jobs, `longrun/d7hs-logs/lake_build_exit.txt`) |
| `#print axioms` audit | **85/85 principal declarations**, cones `{propext, Classical.choice, Quot.sound}` (79), `{}` (5), `{propext}` (1); **0 nonstandard** |
| forbidden-token scan (comment/string-aware) | **0 hard hits, 0 soft hits** in 10 files (`longrun/d7hs-logs/forbidden-scan.json`) |
| copied scaffold files modified | **0** (207 files sha256-checked vs `D7-ricci-scalar-curvature`) |
| item 1 | `RicciFlowData`, `deTurckRHS`, `DeTurckCertificate` — all fields explicit |
| item 2 | algebraic equivalence **both directions** + ODE uniqueness under `RicciLipschitzInterface` |
| item 3 | `DeTurckShortTimeExistence`, `DeTurckToRicciConversion` state-only; 8 named missing dependencies |
| non-vacuity | Einstein flow `exp(-2ct) • G₀`; flat datum; trivial gauge; **nonzero-gauge nilpotent certificate** with explicit `3 × 3` matrices |

**Not claimed:** no manifold-level Ricci flow, no PDE solution, no proof of parabolic short-time
existence, no proof of the manifold-level gauge covariance of the Ricci tensor, no Poincaré or
Perelman content. The gauge covariance of the Ricci operator is an explicit hypothesis
(`RicciFlowData.ricci_congruence`), not derived from a connection.

---

## 1. Scaffold, environment, source integrity

The worktree was empty. The prescribed hard-link scaffold was attempted first:

| command | exit | note |
| --- | --- | --- |
| `cp -al ../D7-ricci-scalar-curvature/. .` | **1** | cross-worktree hard links rejected by the filesystem (`Invalid cross-device link`, `EXDEV`); only an empty directory skeleton was created |
| `cp -a ../D7-ricci-scalar-curvature/. .` | **0** | fallback used; 207 files copied (0 hard links) |
| `.lake` / `release/.lake/packages` | — | copied as symlinks, pointing at the shared pinned mathlib prebuild |

Integrity check (`.lake` excluded, symlinks skipped, sha256):

| comparison | files checked | changed | missing |
| --- | --- | --- | --- |
| worktree vs `D7-ricci-scalar-curvature` (non-ShortTime files) | 207 | 0 | 0 |

Environment:

| key | value |
| --- | --- |
| Lean | `4.34.0-rc2` (commit `6a10ac8c22be`) |
| Lake | `5.0.0-src+6a10ac8` |
| mathlib | `7974e751bece493b6ff508039423ca9fa2452fa8` |
| `ELAN_HOME` | `/data3/guoshaoyang/workdir/lean_poincare/elan` |

New files (all under `release/Poincare/D7/`):

| file | lines | declarations | role |
| --- | --- | --- | --- |
| `ShortTime.lean` | 42 | 0 | umbrella module |
| `ShortTime/Basic.lean` | 240 | 15 | `RicciFlowData`, `deTurckRHS`, `DeTurckCertificate` |
| `ShortTime/ODE.lean` | 134 | 8 | `LipschitzVectorField`, `RicciLipschitzInterface`, ODE uniqueness |
| `ShortTime/MatrixDeriv.lean` | 132 | 10 | entrywise transpose/product rules + arithmetic wrappers |
| `ShortTime/Gauge.lean` | 106 | 8 | pullback algebra, gauge correction, inverse-gauge covariance |
| `ShortTime/Equivalence.lean` | 217 | 11 | both directions of the algebraic DeTurck equivalence + uniqueness |
| `ShortTime/Statements.lean` | 233 | 15 | abstract continuum interface, state-only `Prop`s, missing-dependency ledger |
| `ShortTime/Example.lean` | 296 | 19 | Einstein/flat models, trivial and nilpotent certificates, explicit matrices |
| `ShortTime/Probe.lean` | 134 | 0 | compilable API probe (`#check`) |
| `ShortTime/Audit.lean` | 122 | 0 | 85 `#print axioms` commands |

---

## 2. Item 1 — `RicciFlowData` and `DeTurckCertificate`, all fields explicit

**`RicciFlowData n`** (`Poincare.D7.ShortTime.RicciFlowData`), the finite-dimensional matrix
model of Ricci flow data:

| field | type | meaning |
| --- | --- | --- |
| `ricci` | `Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ` | the Ricci operator |
| `ricci_symm` | `∀ G, Gᵀ = G → (ricci G)ᵀ = ricci G` | symmetry on symmetric matrices |
| `ricci_congruence` | `∀ G A, IsUnit A.det → ricci (Aᵀ * G * A) = Aᵀ * ricci G * A` | **gauge covariance** |
| `metric` | `ℝ → Matrix (Fin n) (Fin n) ℝ` | a metric path |
| `metric_symm` | `∀ t, (metric t)ᵀ = metric t` | symmetry of the path |
| `ricci_flow` | `∀ t, HasDerivAt metric ((-2 : ℝ) • ricci (metric t)) t` | **Ricci flow equation** |

The modified right-hand side is the explicit definition

```
deTurckRHS D B G = (-2 : ℝ) • D.ricci G - Bᵀ * G - G * B
```

with the sign convention `A' = B A` for the gauge family (recorded in the module docstring).

**`DeTurckCertificate D`** (`Poincare.D7.ShortTime.DeTurckCertificate`), the gauge certificate,
all fields explicit:

| field | type | meaning |
| --- | --- | --- |
| `gauge` | `ℝ → Matrix (Fin n) (Fin n) ℝ` | gauge family `A(t)` |
| `gaugeInv` | `ℝ → Matrix (Fin n) (Fin n) ℝ` | inverse family `A(t)⁻¹` |
| `gaugeField` | `ℝ → Matrix (Fin n) (Fin n) ℝ` | gauge vector field `B(t)` |
| `gauge_ode` | `∀ t, HasDerivAt gauge (gaugeField t * gauge t) t` | **gauge ODE** `A' = B A` |
| `gaugeInvDeriv` | `ℝ → Matrix (Fin n) (Fin n) ℝ` | derivative of the inverse family |
| `gaugeInv_ode` | `∀ t, HasDerivAt gaugeInv (gaugeInvDeriv t) t` | differentiability of `A⁻¹` |
| `gauge_zero`, `gaugeInv_zero` | `gauge 0 = 1`, `gaugeInv 0 = 1` | initial conditions |
| `inv_mul`, `mul_inv` | `∀ t, gaugeInv t * gauge t = 1`, `∀ t, gauge t * gaugeInv t = 1` | inverse identities |
| `deturckMetric` | `ℝ → Matrix (Fin n) (Fin n) ℝ` | DeTurck metric `G(t)` |
| `deturck_symm` | `∀ t, (deturckMetric t)ᵀ = deturckMetric t` | symmetry |
| `deturck_flow` | `∀ t, HasDerivAt deturckMetric (deTurckRHS D (gaugeField t) (deturckMetric t)) t` | **modified flow equation** |
| `deturck_zero` | `deturckMetric 0 = D.metric 0` | initial condition |

`DeTurckCertificate.isUnit_det_gauge` proves `IsUnit (A t).det` from `A⁻¹A = 1` by taking
determinants, and `DeTurckCertificate.gaugeInvDeriv_eq` **derives** the inverse gauge ODE
`(A⁻¹)' = -A⁻¹ B` from the product rule and the two inverse identities; it is not an extra
assumption.

---

## 3. Item 2 — algebraic equivalence and Lipschitz uniqueness

### 3.1 The gauge algebra (`Gauge.lean`)

| declaration | statement |
| --- | --- |
| `gaugeAction` | `gaugeAction A G = Aᵀ * G * A` |
| `gauge_pullback_algebra` | `(B*A)ᵀ*G*A + Aᵀ*G'*A + Aᵀ*G*(B*A) = Aᵀ*(Bᵀ*G + G' + G*B)*A` |
| `deTurckRHS_add_gauge` | `Bᵀ*G + deTurckRHS D B G + G*B = (-2) • D.ricci G` |
| `gauge_pullback_deTurckRHS` | `(B*A)ᵀ*G*A + Aᵀ*deTurckRHS D B G*A + Aᵀ*G*(B*A) = (-2) • D.ricci (Aᵀ*G*A)` (uses `ricci_congruence`) |
| `gaugeInv_ricci_congruence` | `A⁻¹ᵀ * Ric(Aᵀ G A) * A⁻¹ = Ric G` |

### 3.2 Forward direction (`Equivalence.lean`)

```
DeTurckCertificate.pullback_hasDerivAt_at :
  (hG : HasDerivAt G (deTurckRHS D (B t) (G t)) t) →
  HasDerivAt (fun s => A(s)ᵀ * G(s) * A(s)) ((-2) • D.ricci (A(t)ᵀ * G(t) * A(t))) t
```

with the global version `pullback_hasDerivAt_of`, the interval version
`pullback_hasDerivAt_of_Ioo` (used for solutions on `(0,T)`), the certificate version
`pullback_hasDerivAt`, and the packaged `pullback_solves_ricciFlow`. The proof uses the entrywise
matrix calculus of `MatrixDeriv.lean` (`hasDerivAt_transpose`, `hasDerivAt_mul`) and the gauge
algebra above.

### 3.3 Uniqueness under the Lipschitz interface (`ODE.lean`, `Equivalence.lean`)

* `LipschitzVectorField E` bundles `toFun : ℝ → E → E`, an explicit constant `K : NNReal`, and
  `lipschitz : ∀ t, LipschitzWith K (toFun t)`.
* `LipschitzVectorField.solution_unique` / `solution_eq` — **uniqueness of `y' = v(t,y)`** for
  two global solutions with the same initial value, proved from mathlib's
  `ODE_solution_unique_univ` (Grönwall).
* `RicciLipschitzInterface D` specializes the interface to `G ↦ -2 Ric(G)`;
  `RicciLipschitzInterface.solution_unique` is the specialization used below.
* `DeTurckCertificate.pullback_eq_metric` — under the Lipschitz interface, the pullback of the
  DeTurck metric equals the Ricci flow metric of the datum:
  `A(t)ᵀ * G(t) * A(t) = D.metric t` for all `t`, since both sides solve the same Lipschitz ODE
  with the same initial value (`gauge 0 = 1`, `deturck 0 = metric 0`).

### 3.4 Reverse direction (`Equivalence.lean`)

```
DeTurckCertificate.gaugeInv_hasDerivAt :
  (hH : ∀ t, HasDerivAt H ((-2) • D.ricci (H t)) t) →
  HasDerivAt (fun s => A(s)⁻¹ᵀ * H(s) * A(s)⁻¹)
    (deTurckRHS D (B t) (A(t)⁻¹ᵀ * H(t) * A(t)⁻¹)) t
```

`ricciFlow_gauge_recover` is the packaged solution-level form. Together with the forward
direction, the gauge action is a bijection between solutions of the modified flow and solutions
of the Ricci flow **at the algebraic level** (`pullback` and `gaugeInv` are mutually inverse by
`gauge_conj_inv` and `gaugeAction_inv`).

---

## 4. Item 3 — state-only `Prop`s and the missing-dependency ledger

`DeTurckParabolicProblem` is an abstract continuum interface: a normed state space of metrics,
`ricciOp`, `deTurckOp`, the initial metric, the gauge transform `gaugeTransform` (with
`gaugeTransform_zero`), and the solution predicates, *defined* to be the corresponding
`HasDerivAt` equations. The intended instantiation is the space of smooth Riemannian metrics on
a closed manifold; the manifold structure is exactly what the pinned mathlib does not have.

Two **state-only `Prop`s** (definitions, never axioms):

| `Prop` | content |
| --- | --- |
| `DeTurckShortTimeExistence P` | `∃ T > 0, ∃ u, u 0 = initial ∧ P.IsDeTurckSolutionOn T u` — parabolic short-time existence for the DeTurck flow |
| `DeTurckToRicciConversion P` | every DeTurck solution on `(0,T)` pulls back along the gauge flow to a Ricci flow on `(0,T)` |

`matrixProblem D C` is the finite-dimensional matrix model as an instance of the interface, and
`matrixProblem_deTurckToRicciConversion` **proves** the conversion `Prop` for this instance by
the algebraic equivalence; this is a consistency/non-vacuity witness for the statement. The
general continuum conversion statement and the existence statement remain unproved.

**Missing dependencies** (`quasilinearParabolicDependencies : List MissingDependency`, 8 entries;
`quasilinearParabolicDependencies_all_named` checks every entry has a nonempty name and reason):

1. `QP-1 linearization` — the second-order linearization of the Ricci tensor and its principal
   symbol;
2. `QP-2 strict parabolicity` — the DeTurck gauge removes the diffeomorphism degeneracy and the
   principal symbol becomes the Laplacian;
3. `QP-3 a priori estimates` — Schauder / Sobolev estimates for the linear parabolic operator;
4. `QP-4 quasilinear short-time existence` — Nash–Moser / inverse function theorem on tame
   Fréchet spaces (Hamilton 1982, Section 3);
5. `QP-5 regularity and continuation` — parabolic smoothing and the maximal existence time;
6. `QP-6 diffeomorphism flow` — flow of the DeTurck vector field, smooth dependence on the
   initial condition, pullback action on metrics;
7. `QP-7 manifold gauge covariance` — diffeomorphism invariance of the Ricci tensor (in the
   matrix model this is the hypothesis `RicciFlowData.ricci_congruence`);
8. `QP-8 manifold Ricci flow theory` — smooth metrics, manifold Ricci tensor, covariant
   derivative calculus (inherited blocker `Poincare.D7.Curvature`).

Named blockers (nonempty, kernel-checked): `BlockerDeTurckShortTime`
(`B-D7-HST-PARABOLIC-EXISTENCE`) and `BlockerDeTurckConversion` (`B-D7-HST-CONVERSION`).

---

## 5. Item 4 — no forbidden tokens

Comment/string-aware scan of all 10 authored files for `sorry`, `axiom`, `unsafe`,
`native_decide`, `proof_wanted`, `sorryAx`, `admit` (hard) and `implemented_by`, `extern`
(soft): **0 hard hits, 0 soft hits** (`longrun/d7hs-logs/forbidden-scan.json`, plus
`forbidden-scan-with-umbrella.json` for the umbrella file). All unproved content is a
`def ... : Prop` / `structure` / `def ... : String`, never an axiom.

The 85-entry `#print axioms` audit (`ShortTime/Audit.lean`) reports the cones

| cone | count |
| --- | --- |
| `{propext, Classical.choice, Quot.sound}` | 79 |
| `{}` (definitions, blockers, ledger data) | 5 |
| `{propext}` | 1 |
| any other | 0 |

No `sorryAx`, no `Lean.ofReduceBool`, no `Lean.trustCompiler`, no project axiom.

---

## 6. Verification transcript

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-hamilton-short-time
bash longrun/d7hs-logs/run_verification.sh    # per-file compiles + scan + axiom summary
cd release && lake build                      # 8974 jobs, exit 0
```

| command | exit |
| --- | --- |
| `lake env lean release/Poincare/D7/ShortTime/Basic.lean` | 0 |
| `lake env lean release/Poincare/D7/ShortTime/ODE.lean` | 0 |
| `lake env lean release/Poincare/D7/ShortTime/MatrixDeriv.lean` | 0 |
| `lake env lean release/Poincare/D7/ShortTime/Gauge.lean` | 0 |
| `lake env lean release/Poincare/D7/ShortTime/Equivalence.lean` | 0 |
| `lake env lean release/Poincare/D7/ShortTime/Statements.lean` | 0 |
| `lake env lean release/Poincare/D7/ShortTime/Example.lean` | 0 |
| `lake env lean release/Poincare/D7/ShortTime/Probe.lean` | 0 |
| `lake env lean release/Poincare/D7/ShortTime/Audit.lean` | 0 |
| `lake env lean release/Poincare/D7/ShortTime.lean` | 0 |
| `cd release && lake build` | 0 (8974 jobs) |

Headline declarations and their cones (all in `{propext, Classical.choice, Quot.sound}` unless
noted):

| declaration | axioms |
| --- | --- |
| `RicciFlowData.ricciVectorField` | `{propext, Classical.choice, Quot.sound}` |
| `deTurckRHS` | `{propext, Classical.choice, Quot.sound}` |
| `DeTurckCertificate` | `{propext, Classical.choice, Quot.sound}` |
| `LipschitzVectorField.solution_unique` | `{propext, Classical.choice, Quot.sound}` |
| `RicciLipschitzInterface.solution_unique` | `{propext, Classical.choice, Quot.sound}` |
| `hasDerivAt_transpose` | `{propext, Classical.choice, Quot.sound}` |
| `hasDerivAt_mul` | `{propext, Classical.choice, Quot.sound}` |
| `gauge_pullback_algebra` | `{propext, Classical.choice, Quot.sound}` |
| `gauge_pullback_deTurckRHS` | `{propext, Classical.choice, Quot.sound}` |
| `DeTurckCertificate.gaugeInvDeriv_eq` | `{propext, Classical.choice, Quot.sound}` |
| `DeTurckCertificate.pullback_hasDerivAt_at` | `{propext, Classical.choice, Quot.sound}` |
| `DeTurckCertificate.pullback_solves_ricciFlow` | `{propext, Classical.choice, Quot.sound}` |
| `DeTurckCertificate.pullback_eq_metric` | `{propext, Classical.choice, Quot.sound}` |
| `DeTurckCertificate.gaugeInv_hasDerivAt` | `{propext, Classical.choice, Quot.sound}` |
| `matrixProblem_deTurckToRicciConversion` | `{propext, Classical.choice, Quot.sound}` |
| `BlockerDeTurckShortTime` | `{}` |
| `quasilinearParabolicDependencies` | `{}` |
| `einsteinRicciFlowData` | `{propext, Classical.choice, Quot.sound}` |
| `nilpotentDeTurckCertificate` | `{propext, Classical.choice, Quot.sound}` |
| `nilpotentB_H_add_ne_zero` | `{propext, Classical.choice, Quot.sound}` |

Artifacts:

| artifact | path |
| --- | --- |
| verification script | `longrun/d7hs-logs/run_verification.sh` |
| per-file exit codes | `longrun/d7hs-logs/exit_codes.txt` |
| per-file compile logs | `longrun/d7hs-logs/lean_release_Poincare_D7_ShortTime_*.log` |
| `#print axioms` output | `longrun/d7hs-logs/lean_release_Poincare_D7_ShortTime_Audit.lean.log` |
| axiom summary | `longrun/d7hs-logs/axioms.json` |
| forbidden-token scan | `longrun/d7hs-logs/forbidden-scan.json`, `forbidden-scan-with-umbrella.json` |
| full package build exit | `longrun/d7hs-logs/lake_build_exit.txt` |

---

## 7. Non-vacuity witnesses

* **Einstein model.** `einsteinRicci c G = c • G` satisfies symmetry and gauge covariance;
  `einsteinRicciFlowData c G₀ hG₀` is a `RicciFlowData` whose metric
  `t ↦ Real.exp (-2*c*t) • G₀` solves `G' = -2 Ric(G)` (`hasDerivAt_exp_smul`).
* **Flat model.** `flatRicciFlowData G₀ hG₀` has `Ric = 0` and constant metric.
* **Trivial gauge.** `trivialDeTurckCertificate D` (with `A = A⁻¹ = 1`, `B = 0`) exists for
  every `RicciFlowData`; `trivial_pullback_eq` shows its pullback is the metric itself.
* **Nonzero gauge.** `nilpotentDeTurckCertificate H₀ B hH₀ hB hBH` has
  `A(t) = 1 + tB`, `A⁻¹(t) = 1 - tB`, and `G(t) = H₀ - t (Bᵀ H₀ + H₀ B)`; the key algebra
  `nilpotent_gauge_correction` and `nilpotent_deTurckRHS` proves the modified flow equation.
* **Explicit matrices.** `nilpotentB = E₁₂`, `nilpotentH = E₁₃ + E₃₁` satisfy `B² = 0`,
  `Bᵀ H₀ B = 0`, `H₀ᵀ = H₀`, and `Bᵀ H₀ + H₀ B ≠ 0` (kernel-checked entry computations), so
  `concreteDeTurckCertificate` is a genuine certificate with a **nonzero** gauge field and a
  genuinely nonconstant DeTurck metric (`concreteDeTurck_metric_deriv_ne_zero`).
* **Interface consistency.** `matrixProblem_deTurckToRicciConversion` proves the conversion
  `Prop` for the finite-dimensional instance.

---

## 8. Honest boundary

* The model is **finite-dimensional and pointwise**: `n × n` matrices play the role of symmetric
  `(0,2)`-tensors at a point, and congruence by `A` is the algebraic shadow of the action of a
  diffeomorphism on a metric. No manifold, tangent bundle or covariant derivative is involved.
* **Gauge covariance is a hypothesis**, not a theorem: `RicciFlowData.ricci_congruence` is a
  field. Deriving it from a connection requires the blocked manifold curvature layer
  (`Poincare.D7.Curvature.ManifoldCurvatureStatement`, blocker `B-D7-MANIFOLD-CURVATURE`).
* The reverse direction assumes the inverse gauge family is differentiable
  (`gaugeInv_ode`); the *value* of its derivative is derived, but differentiability of matrix
  inversion itself is not formalized.
* `DeTurckShortTimeExistence` is **not proved**. The finite-dimensional analogue is a
  Picard–Lindelöf statement under a Lipschitz hypothesis, but the continuum DeTurck operator is
  unbounded and quasilinear; the eight missing inputs are listed above.
* `DeTurckToRicciConversion` is state-only for the general continuum interface; it is proved for
  the matrix instance only.
* No Ricci-flow existence, no monotonicity, no κ-noncollapsing, no surgery and no Poincaré
  content is claimed.

**Last line:** TASK_DONE — card: `longrun/results/D7-hamilton-short-time.md`
