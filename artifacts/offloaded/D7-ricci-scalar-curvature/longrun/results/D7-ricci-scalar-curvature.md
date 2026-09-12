# D7-ricci-scalar-curvature — result card

**Task id:** `D7-ricci-scalar-curvature`
**Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-ricci-scalar-curvature`
**Generated (UTC):** 2026-09-09T16:11:52Z
**Verdict:** `TASK_DONE` — kernel-checked Ricci and scalar curvature layer on top of the accepted
D7 Riemann curvature tensor: Ricci as a finite-basis trace with basis-independence, scalar
curvature as the metric trace with basis-independence, Ricci symmetry for metric-compatible
torsion-free data, definitional compatibility with the D2 `CurvatureOperator.ricci`, scalar
additivity for a constructed product datum, and a state-only variation interface for
`d/dt scal(g(t))` with the two exact missing dependencies named and blocked. No
`sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted` anywhere in the new sources.

---

## 0. Bottom line

| item | result |
| --- | --- |
| new files (only under `release/Poincare/D7/RicciScalar/`) | **9 Lean files, 1457 lines, 89 declarations** |
| compiled with `lake env lean` from the worktree root | **9/9 exit 0** (`longrun/d7rs-logs/exit_codes.txt`) |
| whole release package `lake build` | **exit 0** (8964 jobs, `longrun/d7rs-logs/lake_build_all.log`) |
| `#print axioms` audit | **100/100 principal declarations**, cones `{propext, Classical.choice, Quot.sound}` (96) and `{}` (4 blocker strings); 0 nonstandard |
| forbidden-token scan (comment/string-aware) | **0 hard hits** in 9 files (`longrun/d7rs-logs/forbidden-scan.json`) |
| copied files modified | **0** (sha256: 287 files vs `D7-riemann-curvature-tensor`, 179 files vs `D6_weekly_release`) |
| non-vacuity | `so3` model: `Ric(X,Y) = ½⟨X,Y⟩`, `scal = 3/2`; product `so3 × so3`: `scal = 3 = 3/2 + 3/2` |
| unproved items | `LeviCivitaEvolutionStatement`, `TraceCommutationStatement`, `CurvatureEvolutionStatement`, `ScalarVariationStatement`, `PerelmanScalarCurvatureRealization` (state-only `Prop`s with named blockers) |

**Not claimed:** no manifold-level curvature tensor, no proof of the Levi-Civita evolution or of
the commutation of `d/dt` with the trace, no scalar-variation formula under Ricci flow, no
Ricci-flow existence, no Poincaré or Perelman content. The connection datum remains the D2
abstract algebraic Koszul connection on a finite-dimensional real inner-product space.

---

## 1. Scaffold, environment, source integrity

The worktree was empty. The prescribed hard-link scaffold was attempted first:

| command | exit | note |
| --- | --- | --- |
| `cp -al ../D7-riemann-curvature-tensor/. .` | **1** | cross-worktree hard links rejected by the filesystem (`Invalid cross-device link`, `EXDEV`); only an empty directory skeleton was created |
| `cp -a ../D7-riemann-curvature-tensor/. .` | **0** | fallback used by the D7-riemann run as well; **867 files** copied (0 hard links) |
| `.lake` / `release/.lake/packages` | — | copied as symlinks, pointing at the shared pinned mathlib prebuild |

The D7-riemann worktree is the gate that this task depends on; its result card records
`TASK_DONE` with `ManifoldCurvatureStatement`/`SecondBianchiStatement` as explicit blockers.

Integrity checks (`.lake` excluded, symlinks skipped, sha256):

| comparison | files checked | changed | missing | log |
| --- | --- | --- | --- | --- |
| worktree vs `D7-riemann-curvature-tensor` | 287 | 0 | 0 | `longrun/d7rs-logs/source-integrity.json` |
| worktree vs `D6_weekly_release` (D6 subset) | 179 | 0 | 0 | `longrun/d7rs-logs/source-integrity-d6.json` |

Environment:

| key | value |
| --- | --- |
| Lean | `4.34.0-rc2` (commit `6a10ac8c22be`) |
| Lake | `5.0.0-src+6a10ac8` |
| mathlib | `7974e751bece493b6ff508039423ca9fa2452fa8` |
| `ELAN_HOME` | `/data3/guoshaoyang/workdir/lean_poincare/elan` |

New files (all under `release/Poincare/D7/`):

| file | lines | role |
| --- | --- | --- |
| `RicciScalar.lean` | 31 | umbrella module |
| `RicciScalar/Basic.lean` | 182 | `ricciTrace`, basis-independence, `ricciTensor`, D2 `ricci` compatibility, Ricci symmetry |
| `RicciScalar/Scalar.lean` | 176 | `scalarMetricTrace`, `scalarBasisSum`, basis-independence of both traces, D2 `scalarCurvature` compatibility |
| `RicciScalar/Product.lean` | 286 | product bracket/connection/metric/datum, curvature/Ricci splitting, `prodData_scalarCurvature` |
| `RicciScalar/Variation.lean` | 304 | `FlowPath`, flow equations, `LeviCivitaEvolution`, `TraceCommutationStatement`, `ScalarVariationStatement`, reduction theorem, blockers |
| `RicciScalar/Example.lean` | 117 | non-vacuity: `so3` Ricci/scalar, basis-independence witness, product witness |
| `RicciScalar/Bridge.lean` | 124 | D2 linearity/consistency restatements, blocked Perelman-ledger target |
| `RicciScalar/Probe.lean` | 92 | compilable mathlib/D7 API probe (`#check` / `#check_failure`) |
| `RicciScalar/Audit.lean` | 145 | 100 `#print axioms` commands |

---

## 2. Item 1 — Ricci as a basis trace; scalar as the metric trace; basis-independence

**Ricci.** For a `RiemannCurvatureData D` and any finite basis `e` of `V`,

```
ricciTrace D e X Y = ∑ i, e.repr (D.curvature (e i) X Y) i
```

(`Poincare.D7.RicciScalar.ricciTrace`). It is definitionally the D2 coordinate contraction
`CurvatureOperator.ricciSum`, and `ricciTrace_eq_ricciForm` proves it equals the D2 basis-free
`LinearMap.trace` of `Z ↦ R(Z,X)Y`. **Basis-independence** is
`ricciTrace_basis_independent`: for any two finite bases (possibly different index types),
the diagonal sums agree, because both compute the basis-free trace. The named alias
`ricciTensor D = D.ricciForm` has the basis-trace formula `ricciTensor_eq_basisTrace`.

**Scalar.** `scalarMetricTrace D = tr (MetricData.raiseIndex D.ricciForm)` is the metric trace
of the raised Ricci endomorphism, and `scalarBasisSum D = ∑ i, Ric(eᵢ,eᵢ)` is the
orthonormal-basis form; `scalarMetricTrace_eq_scalarCurvature`,
`scalarBasisSum_eq_scalarCurvature` and `scalarBasisSum_eq_metricTrace` identify them with the
D7 `RiemannCurvatureData.scalarCurvature`. **Basis-independence** is proved twice:

* `scalarMetricTrace_eq_trace_basis` / `scalarMetricTrace_basis_independent`: for any finite
  basis `e`, the trace is the diagonal coordinate sum `∑ i, e.repr (Ric^♯ (eᵢ)) i`, hence any
  two bases agree;
* `raiseIndex_congr` (two metric data with the same bilinear form induce the same index raising,
  by nondegeneracy of the metric adjoint) and `scalarBasisSum_congr_orthonormal`: the
  orthonormal-basis sum is the same for every orthonormal basis of the metric form.

`scalarCurvature_eq_basisTrace` states the acceptance-named basis-trace formula
`scal = ∑ i, Ric(eᵢ,eᵢ)`.

---

## 3. Item 2 — symmetry, D2 compatibility, product additivity

**Symmetry.** `ricciForm_symm_via_symmetries` reproves `Ric(X,Y) = Ric(Y,X)` in this layer from
the four-index symmetries (`curvatureForm_interchange`, `curvatureForm_skew₃₄`,
`curvatureForm_skew₁₂`) on the orthonormal basis, for metric-compatible torsion-free data.
`ricciTrace_symm`, `ricciForm_symm'` and `ricciTensor_symm` are the trace/tensor forms.

**D2 compatibility.** `ricciForm_eq_ricciOperator` (definitional `rfl`),
`ricciTensor_eq_ricciOperator`, `ricciTrace_eq_d2`, `ricciTrace_eq_d2_ricciSum`,
`scalarCurvature_eq_d2`, `scalarMetricTrace_eq_d2`, `scalarCurvature_eq_d2_sum_basis`, and the
D2 linearity restatements `ricci_add_d2`, `ricci_smul_d2`, `scalarCurvature_add_d2`,
`scalarCurvature_smul_d2` (Bridge.lean). The D7 objects are the D2 contractions of the packaged
`(1,3)` tensor with no redefinition.

**Product additivity.** `prodData D₁ D₂` is a stated product structure on `V₁ × V₂` with index
`ι₁ ⊕ ι₂`: the product bracket, the product connection, the product metric `g₁ ⊕ g₂` (whose
orthonormal basis is mathlib's direct-sum `Basis.prod`), and the product datum. The curvature,
the metric-lowered form, the Ricci endomorphism and the Ricci form all split
(`prodData_curvature_apply`, `prodData_curvatureForm_apply`, `prodData_endoRicci`,
`prodData_ricciForm`, the last via `LinearMap.trace_prodMap'`). The main theorem is

```
prodData_scalarCurvature : scal (D₁ × D₂) = scal D₁ + scal D₂
```

proved by splitting the orthonormal-basis trace over `ι₁ ⊕ ι₂`.

---

## 4. Item 3 — the variation interface for `d/dt scal(g(t))`

`FlowPath` is a path of metric-compatible torsion-free data with a time-independent orthonormal
frame and a time-independent bracket. The stated flow equations are
`MetricFlowEquation (∂ₜ g = h)` and `RicciFlowEquation (∂ₜ g = -2 Ric)`. The exact missing
dependencies are state-only:

1. **`LeviCivitaEvolution` / `LeviCivitaEvolutionStatement`** — the connection velocity
   `∂ₜ∇` exists, is bilinear, and satisfies the linearized Koszul formula; the formula needs
   directional derivatives `dirh` of the variation tensor field `h = ∂ₜ g`, the first-order
   calculus absent from the abstract algebraic setting. Differentiability of the connection is
   stated componentwise in the fixed frame (the abstract space has no norm).
2. **`TraceCommutationStatement`** — the derivative of the Ricci trace
   `Ric_t(X,Y) = tr(Z ↦ R_t(Z,X)Y)` is the trace of the derivative of the endomorphism,
   i.e. `d/dt` commutes with `LinearMap.trace`.

The conclusion `ScalarVariationStatement Ricdot` says
`d/dt scal = ∑ᵢ Ricdot(eᵢ,eᵢ)` in the fixed frame. What is **proved** is the reduction
`scalarVariation_of_traceCommutation`: from the trace-commutation hypothesis (which supplies
`Ricdot`), the scalar variation follows by differentiating the finite orthonormal-frame
expansion. `ScalarVariationInterface` bundles the flow equation, the two dependencies and the
conclusion as one `Prop`. The chain
`Levi-Civita evolution → curvature velocity (curvVel) → Ricci velocity → scalar variation` is
made explicit (`CurvatureEvolutionStatement`, `RicciFlowScalarVariationStatement`). Named
blockers: `BlockerLeviCivitaEvolution`, `BlockerTraceCommutation`, `BlockerScalarVariation`
(all nonempty, kernel-checked). The reduction is non-vacuous: on the constant path,
`constFlow_scalarVariation` proves the conclusion with `Ricdot = 0`.

The classical Ricci-flow formula `∂ₜ R = ΔR + 2|Ric|²` is not stated as a theorem; the blocker
records that it additionally needs a Laplacian on tensor fields, absent from mathlib.

---

## 5. Item 4 — no forbidden tokens

Comment/string-aware scan of all 9 new files for `sorry`, `axiom`, `unsafe`, `native_decide`,
`proof_wanted`: **0 hits** (`longrun/d7rs-logs/forbidden-scan.json`). All unproved content is
`def ... : Prop` / `structure` / `def ... : String`, never an axiom. The 100-entry `#print axioms`
audit (`RicciScalar/Audit.lean`) reports only the cones `{propext, Classical.choice,
Quot.sound}` and `{}`; 0 nonstandard entries.

---

## 6. Verification transcript

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-ricci-scalar-curvature
bash longrun/d7rs-logs/run_verification.sh          # transcript: longrun/d7rs-logs/verify_transcript.log
cd release && lake build                            # 8964 jobs, exit 0
```

| command | exit |
| --- | --- |
| `lake env lean release/Poincare/D7/RicciScalar/Basic.lean` | 0 |
| `lake env lean release/Poincare/D7/RicciScalar/Scalar.lean` | 0 |
| `lake env lean release/Poincare/D7/RicciScalar/Product.lean` | 0 |
| `lake env lean release/Poincare/D7/RicciScalar/Variation.lean` | 0 |
| `lake env lean release/Poincare/D7/RicciScalar/Example.lean` | 0 |
| `lake env lean release/Poincare/D7/RicciScalar/Bridge.lean` | 0 |
| `lake env lean release/Poincare/D7/RicciScalar/Probe.lean` | 0 |
| `lake env lean release/Poincare/D7/RicciScalar/Audit.lean` | 0 |
| `lake env lean release/Poincare/D7/RicciScalar.lean` | 0 |
| `cd release && lake build` | 0 (8964 jobs) |

Axiom cones (from the 100 `#print axioms` entries in
`longrun/d7rs-logs/lean_release_Poincare_D7_RicciScalar_Audit.lean.log`):

| cone | count |
| --- | --- |
| `{propext, Classical.choice, Quot.sound}` | 96 |
| `{}` (the four blocker strings) | 4 |
| any other | 0 |

Headline declarations and their cones:

| declaration | axioms |
| --- | --- |
| `ricciTrace` | `propext, Classical.choice, Quot.sound` |
| `ricciTrace_basis_independent` | `propext, Classical.choice, Quot.sound` |
| `ricciTensor_eq_ricciOperator` | `propext, Classical.choice, Quot.sound` |
| `ricciForm_symm_via_symmetries` | `propext, Classical.choice, Quot.sound` |
| `scalarMetricTrace_basis_independent` | `propext, Classical.choice, Quot.sound` |
| `scalarBasisSum_congr_orthonormal` | `propext, Classical.choice, Quot.sound` |
| `scalarCurvature_eq_d2` | `propext, Classical.choice, Quot.sound` |
| `prodData_scalarCurvature` | `propext, Classical.choice, Quot.sound` |
| `FlowPath.scalarVariation_of_traceCommutation` | `propext, Classical.choice, Quot.sound` |
| `FlowPath.constFlow_scalarVariation` | `propext, Classical.choice, Quot.sound` |
| `so3_scalarCurvature` | `propext, Classical.choice, Quot.sound` |
| `prodData_so3_scalarCurvature` | `propext, Classical.choice, Quot.sound` |

Logs and machine-readable records:

| artifact | path |
| --- | --- |
| verification transcript | `longrun/d7rs-logs/verify_transcript.log` |
| per-file exit codes | `longrun/d7rs-logs/exit_codes.txt` |
| `#print axioms` output | `longrun/d7rs-logs/lean_release_Poincare_D7_RicciScalar_Audit.lean.log` |
| axiom summary | `longrun/d7rs-logs/lean_release_Poincare_D7_RicciScalar_Audit.lean.axioms.json` |
| forbidden-token scan | `longrun/d7rs-logs/forbidden-scan.json` |
| source integrity | `longrun/d7rs-logs/source-integrity.json`, `source-integrity-d6.json` |
| declaration inventory | `longrun/d7rs-logs/declarations.json` |
| full package build | `longrun/d7rs-logs/lake_build_all.log` |

---

## 7. Non-vacuity witnesses

* `so3_ricciForm_apply : so3.ricciForm X Y = ½ (X ⬝ᵥ Y)` — from the scalar triple product
  identity `Y × (X × Z) = (Y·Z)X − (X·Y)Z` and `tr(f.smulRight x) = f x`;
* `so3_scalarCurvature : so3.scalarCurvature = 3/2`;
* `so3_ricciTrace_e0_e0 = 1/2` and
  `so3_ricciTrace_basis_independent_witness`: the standard basis and a permuted basis give the
  same Ricci trace on the non-flat model;
* `prodData_so3_scalarCurvature : scal(so3 × so3) = 3 = 3/2 + 3/2`;
* `FlowPath.constFlow_scalarVariation`: the variation reduction is non-vacuous.

---

## 8. Honest boundary

* The connection is the D2 **abstract algebraic** Koszul connection on a finite-dimensional real
  inner-product space, not a `CovariantDerivative` on a smooth manifold. The manifold-level
  curvature tensor is the blocked `Poincare.D7.Curvature.ManifoldCurvatureStatement`.
* The variation interface is **state-only**: neither `LeviCivitaEvolutionStatement` nor
  `TraceCommutationStatement` is proved. The kernel-checked content is the reduction from the
  trace-commutation dependency to the scalar variation, plus the finite-sum differentiation.
* The Perelman-ledger compatibility is stated as the blocked `Prop`
  `PerelmanScalarCurvatureRealization` (`Nonempty (Perelman.ScalarCurvatureData flow)`); the
  algebraic layer proves the finite-dimensional trace formula, but the manifold-level
  inverse-Gram trace identity and the pointwise identification with tangent-space data are not
  constructed. Blocker `B-D7-RS-PERELMAN-REALIZATION`.
* No Ricci-flow existence, monotonicity, κ-noncollapsing, surgery or Poincaré content is
  claimed.

**Last line:** TASK_DONE — card: `longrun/results/D7-ricci-scalar-curvature.md`
