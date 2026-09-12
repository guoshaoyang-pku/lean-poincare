# D7-riemann-curvature-tensor — result card

**Task id:** `D7-riemann-curvature-tensor`
**Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-riemann-curvature-tensor`
**Generated (UTC):** 2026-09-09T07:38:29Z
**Repair attempt 1 re-verified (UTC):** 2026-09-09T12:55:31Z (compile-gate environment fix, see §14)
**Verdict:** `TASK_DONE` — kernel-checked algebraic Riemann curvature tensor layer on the D6
release; the manifold-level curvature construction and the second Bianchi identity are explicit
unproved `Prop`s with named blockers (never `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`).

---

## 0. Bottom line

| item | result |
| --- | --- |
| new files (only under `release/Poincare/D7/`) | **9 Lean files, 1672 lines, 99 declarations** |
| compiled with `lake env lean` | **9/9 authored exit 0** (`longrun/d7-logs-verify/exit_codes.txt`) |
| harness compile gate (`lake env lean` from the worktree root, all 73 `.lean`) | **73/73 exit 0** (`longrun/d7-logs-repair/gate_replication.json`) |
| whole release package `lake build` (D7 artifacts deleted first) | **exit 0** (8955 jobs) |
| `#print axioms` audit | **59/59 principal declarations**, single cone `{propext, Classical.choice, Quot.sound}` |
| forbidden-token scan (comment/string-aware) | **0 hard, 0 soft** matches in 9 files |
| copied D6 source files modified | **0** (sha256 over 179 files, `.lake` excluded) |
| mathlib curvature declarations | **absent** at pinned rev `7974e751…` (1 docstring hit in all of `Mathlib/`) |
| non-vacuity | concrete **non-flat** model `So3.so3` with `sec = 1/4`, `Ric = 1/2` |
| blocked items | `ManifoldCurvatureStatement`, `SecondBianchiStatement` (named blockers, unproved `Prop`s) |

**Not claimed:** no manifold-level curvature tensor, no construction of
`CovariantDerivative.curvature`, no second Bianchi identity, no Levi-Civita existence, no
smoothness of `leviCivitaConnection`, no Ricci-flow or Poincaré content. The connection datum is
the D2 *abstract algebraic* Koszul connection, not a `CovariantDerivative` on a manifold.

---

## 1. Scaffold, environment, and source integrity

The worktree was already scaffolded from `D6_weekly_release` by an earlier run of this same task
id (the D7 layer files were present). This session:

| command | exit | note |
| --- | --- | --- |
| `cp -al ../D6_weekly_release/. .` | **1** | idempotent re-run: every entry already exists (`File exists`); nothing changed |
| `.lake/packages` symlink | — | was **absent**; restored to the same target as D6: `/data3/guoshaoyang/workdir/lean_poincare/poincare-lab/.lake/packages` (environment repair only, no source touched) |
| sha256 integrity check, `D6_weekly_release` vs worktree (`.lake` excluded) | **0** | 179 files checked, **0 changed, 0 missing** (`longrun/d7-logs-verify/source-integrity.json`) |

The D6 scaffold files are full copies (link count 1, distinct inodes); hard links were rejected
on the overlay filesystem by the earlier run, which used `cp -a`. No copied file was edited.

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
| `Curvature.lean` | 33 | umbrella module |
| `Curvature/Basic.lean` | 279 | `RiemannCurvatureData`, `(1,3)`/`(0,4)` tensors, four-slot linearity, `alternating_bilinear_apply`, `zero`/`mean` |
| `Curvature/Symmetries.lean` | 329 | first-pair skew, first Bianchi, second-pair skew, pair interchange, Ricci/scalar contraction, index raising |
| `Curvature/Sectional.lean` | 256 | Gram determinant, nondegenerate 2-plane, sectional curvature, scaling/shear/GL(2) invariance, `TwoPlane` |
| `Curvature/Blocked.lean` | 148 | the unproved `Prop`s and named blockers |
| `Curvature/Bridge.lean` | 138 | `Poincare.Longrun.Geometry.RiemannCurvatureTensor`, `Probe.CurvatureTensor` bridge |
| `Curvature/Probe.lean` | 151 | compilable mathlib/D7 API probe (`#check` / `#check_failure`) |
| `Curvature/Example.lean` | 235 | **concrete non-flat `so(3)` model** (non-vacuity witness) |
| `Curvature/Audit.lean` | 103 | 59 `#print axioms` commands |

---

## 2. Mathlib probe (task item 1)

`release/Poincare/D7/Curvature/Probe.lean` compiles (exit 0); it records the probe.

### 2.1 Present and reused

`CovariantDerivative`, `CovariantDerivative.torsion`, `CovariantDerivative.torsion_apply`,
`CovariantDerivative.torsion_antisymm`, `CovariantDerivative.IsMetricCompatible`,
`CovariantDerivative.IsLeviCivitaConnection`,
`CovariantDerivative.IsLeviCivitaConnection.uniqueness`,
`CovariantDerivative.leviCivitaConnection`,
`CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection`,
`CovariantDerivative.isMetricCompatible_leviCivitaConnection`,
`CovariantDerivative.torsion_leviCivitaConnection_eq_zero`, `Bundle.RiemannianBundle`,
`Bundle.RiemannianMetric`, `inner`, `real_inner_self_nonneg`, `LinearMap.trace`,
`LinearMap.trace_smulRight`, `LinearMap.trace_comp_comm`, `Module.finrank`, `Module.Basis`.
The example additionally reuses mathlib's `crossProduct`, `dotProductBilin`, `dotProduct`,
`triple_product_permutation`, `jacobi_cross`, `cross_anticomm`.

From the D6 release (imported, never modified):

- `Poincare.Longrun.Geometry.AbstractConnection.curvature` — the D2 abstract curvature
  `R(X,Y)Z = ∇_X∇_Y Z − ∇_Y∇_X Z − ∇_{[X,Y]}Z`, with kernel-checked `curvature_skew` and
  `curvature_bianchi`. The D7 `(1,3)` tensor **is** this object (not redefined).
- `Poincare.Longrun.Geometry.curvatureForm` — the D2 metric-lowered `(0,4)` form. The D7
  `(0,4)` tensor **is** this object (not redefined).
- `Poincare.CurvatureAlgebra.CurvatureOperator.ricci` — the D2 Ricci contraction. The D7
  `ricciForm` **is** this object (`ricciForm_eq_ricciOperator`, `rfl`).
- `Poincare.Longrun.Geometry.MetricData` and `MetricData.raiseIndex` — explicit
  finite-dimensional metric datum and index raising.
- `Poincare.Longrun.Geometry.CovariantDerivativeCurvatureStatement` — the D2 blocked
  manifold-level contract, quantified over by the D7 `ManifoldCurvatureStatement`.

### 2.2 Absent at the pinned revision

```
$ grep -rin curvature Mathlib/ --include='*.lean' | wc -l
1
$ grep -rin curvature Mathlib/ --include='*.lean'
Mathlib/MeasureTheory/Measure/Doubling.lean:44: ... a disc ... of curvature -1 ...
```

The single hit is a docstring. `Probe.lean` records the gap with `#check_failure` for
`CovariantDerivative.curvature`, `RiemannTensor`, `RiemannianCurvature`, `RicciTensor`,
`Bianchi`, `CovariantDerivative.Curvature`, `CovariantDerivative.ricci`; because these names are
unknown the commands succeed and `lake env lean Probe.lean` exits 0. Consequence: the curvature
is defined algebraically from the D2 abstract connection, and the manifold-level construction is
a blocked `Prop` (Section 7).

---

## 3. Definitions (task item 2)

`release/Poincare/D7/Curvature/Basic.lean`:

- **`RiemannCurvatureData V ι`** — a metric-compatible torsion-free connection datum:
  - `conn : AbstractConnection ℝ V` (D2 abstract Koszul connection; torsion-freeness
    `∇_X Y − ∇_Y X = [X,Y]` is a field of `AbstractConnection`);
  - `metric : MetricData V ι` (D2 explicit finite-dimensional metric datum: a symmetric
    positive-definite bilinear `form` plus a chosen orthonormal basis indexed by a finite type
    `ι`);
  - `compatible : ∀ X Y Z, ⟨∇_X Y, Z⟩ + ⟨Y, ∇_X Z⟩ = 0` (metric compatibility).
  - **Explicit finite-dimensionality:** `[FiniteDimensional ℝ V]` *and* `MetricData`'s basis
    field `Module.Basis ι ℝ V` with `[Fintype ι] [DecidableEq ι]`.
- **`RiemannCurvatureData.curvature`** — the `(1,3)` tensor, definitionally `conn.curvature`
  (D2).
- **`RiemannCurvatureData.curvatureForm`** — the `(0,4)` tensor
  `R(X,Y,Z,W) = ⟨R(X,Y)Z, W⟩`, definitionally `Poincare.Longrun.Geometry.curvatureForm` (D2).
- `curvatureForm_add₁` … `curvatureForm_smul₄` — four-slot linearity.
- `alternating_bilinear_apply` — the algebra engine
  `B (a•X+b•Y) (c•X+d•Y) = (ad−bc) · B X Y` for an alternating bilinear `B`.
- `zero`, `mean` — inhabitants (the zero connection and the mean connection
  `∇_X Y = ½[X,Y]` for a metric-skew bracket).
- `toCurvatureOperator` — bridge into the D2 Stage1 `CurvatureOperator`.

**Index raising is explicit** in `Symmetries.lean`: `ricciEndo := metric.raiseIndex ricciForm`
(D2 `raiseIndex` is built from the chosen orthonormal basis), with the adjoint property
`form_ricciEndo : ⟨Ric^♯ X, Y⟩ = Ric(X,Y)`, its self-adjointness `form_ricciEndo_symm`, and
`scalarCurvature := trace ricciEndo`.

---

## 4. Kernel-checked symmetries and Ricci agreement (task item 3)

`release/Poincare/D7/Curvature/Symmetries.lean`:

| theorem | statement | proof content |
| --- | --- | --- |
| `curvature_skew₁₂` | `R(X,Y)Z = −R(Y,X)Z` | D2 `AbstractConnection.curvature_skew` (bracket skew) |
| `curvatureForm_skew₁₂` | `R(X,Y,Z,W) = −R(Y,X,Z,W)` | D2 `curvatureForm_first_pair_skew` |
| `curvature_bianchi` | `R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0` | D2 `AbstractConnection.curvature_bianchi` (torsion-free + Jacobi) |
| `curvatureForm_bianchi` | `R(X,Y,Z,W)+R(Y,Z,X,W)+R(Z,X,Y,W)=0` | D2 `curvatureForm_first_bianchi` |
| `form_comp_sub_skew` | `⟨[∇_X,∇_Y]Z, W⟩ = −⟨Z, [∇_X,∇_Y]W⟩` | metric compatibility applied 4× |
| `curvatureForm_skew₃₄` | `R(X,Y,Z,W) = −R(X,Y,W,Z)` | **new**: `[∇,∇]` skew-adjoint + `∇_{[X,Y]}` skew-adjoint |
| `curvatureForm_interchange` | `R(X,Y,Z,W) = R(Z,W,X,Y)` | **new**: four Bianchi applications (`h1`–`h5`) |
| `curvatureForm_self₁/₂` | `R(X,X,Z,W)=0`, `R(X,Y,Z,Z)=0` | corollaries |
| `curvatureForm_swap_pairs` | `R(X,Y,Z,W)=R(Y,X,W,Z)` | corollary of the two skews |
| `ricciForm` | `Ric(X,Y) = tr(Z ↦ R(Z,X)Y)` | **is** D2 `CurvatureOperator.ricci` (`ricciForm_eq_ricciOperator`, `rfl`) |
| `ricciForm_eq_sum_basis` | `Ric(X,Y) = ∑ᵢ R(eᵢ,X,Y,eᵢ)` | D2 `ricci_eq_ricciSum` + orthonormality |
| `ricciForm_symm` | `Ric(X,Y) = Ric(Y,X)` | termwise `R(eᵢ,X,Y,eᵢ)=R(Y,eᵢ,eᵢ,X)=−R(Y,eᵢ,X,eᵢ)=R(eᵢ,Y,X,eᵢ)` |
| `scalarCurvature_eq_sum_basis` | `Sc = ∑ᵢ Ric(eᵢ,eᵢ)` | D2 `raiseIndex_eq_sum_smulRight` + `trace_smulRight` |
| `scalarCurvature_eq_d2` | D7 `Sc` = D2 `CurvatureOperator.scalarCurvature` | D2 `MetricData.scalarCurvature_eq_sum_basis` |

First-pair skew and first Bianchi are **proved in D2** from the torsion-free and Jacobi fields;
second-pair skew and pair interchange are **new D7 proofs** and genuinely use metric
compatibility. The Ricci contraction is not redefined: it is the D2
`CurvatureOperator.ricci` of the packaged `(1,3)` tensor (`rfl`).

---

## 5. Sectional curvature (task item 4)

`release/Poincare/D7/Curvature/Sectional.lean`:

- `gramForm D X Y = ⟨X,X⟩⟨Y,Y⟩ − ⟨X,Y⟩²`;
- `IsNondegenerate2Plane D X Y := gramForm D X Y ≠ 0` (nondegeneracy of the restricted
  bilinear form);
- `sectionalCurvature D X Y = R(X,Y,Y,X) / gramForm D X Y`, with
  `R(X,Y,Y,X) = ⟨R(X,Y)Y, X⟩`;
- `TwoPlane D` bundles a nondegenerate plane with a chosen basis and
  `TwoPlane.sectionalCurvature` evaluates it.

| theorem | statement |
| --- | --- |
| `sectionalCurvature_swap` | `sec X Y = sec Y X` |
| `sectionalCurvature_smul` | `sec (a•X) (b•Y) = sec X Y` for `a,b ≠ 0` (explicit scaling statement) |
| `sectionalCurvature_smul_left/right` | single-sided scaling |
| `sectionalCurvature_shear_left/right` | `sec (X+tY) Y = sec X Y`, `sec X (Y+tX) = sec X Y` |
| `gramForm_gl2` | `gram (aX+bY) (cX+dY) = (ad−bc)² gram X Y` |
| `isNondegenerate2Plane_gl2` | nondegeneracy preserved by invertible basis change |
| `sectionalCurvature_gl2` | **`sec (aX+bY) (cX+dY) = sec X Y` for `ad−bc ≠ 0`** (full GL(2) invariance) |
| `TwoPlane.sectionalCurvature_congr` | any other basis of the same plane computes the same value |

The GL(2) proof applies `alternating_bilinear_apply` to the curvature form in the first pair and
in the last pair; the two determinants multiply to `(ad−bc)²`, and `gramForm_gl2` supplies the
same factor for the denominator.

---

## 6. Non-vacuity: a concrete non-flat model

`release/Poincare/D7/Curvature/Example.lean` (added in this session) exhibits a concrete
inhabitant with **nonzero** curvature, so the symmetry and sectional-curvature theorems are not
vacuous:

- `V = ℝ³`, `stdForm` = standard dot product, `stdBasis` = standard orthonormal basis ⇒
  `stdMetric : MetricData V (Fin 3)`;
- `crossBracket : LieBracketData ℝ V` from mathlib's `crossProduct`
  (`skew` from `cross_anticomm`, `jacobi` from `jacobi_cross`);
- `crossBracket_compatible : ⟨[X,Y],Z⟩ + ⟨Y,[X,Z]⟩ = 0` (the triple-product identity) — the
  metric-compatibility hypothesis of `RiemannCurvatureData.mean`;
- `so3 := RiemannCurvatureData.mean stdMetric crossBracket crossBracket_compatible` — the
  classical `so(3)` mean connection `∇_X Y = ½[X,Y]` with the bi-invariant metric.

Kernel-checked values (see `#check` output in `longrun/d7-logs-verify/lean_Poincare_D7_Curvature_Probe.lean.log`):

| theorem | statement |
| --- | --- |
| `so3_curvature_e0_e1_e1` | `so3.curvature (e 0) (e 1) (e 1) = (1/4) • e 0` |
| `so3_gramForm_e0_e1` | `so3.gramForm (e 0) (e 1) = 1` |
| `so3_isNondegenerate2Plane_e0_e1` | `so3.IsNondegenerate2Plane (e 0) (e 1)` |
| `so3_sectionalCurvature_e0_e1` | `so3.sectionalCurvature (e 0) (e 1) = 1/4` |
| `so3_sectionalCurvature_gl2_witness` | `sec (2e₀+3e₁) (e₀−e₁) = 1/4` (concrete GL(2) instance) |
| `so3_ricciForm_e0_e0` | `so3.ricciForm (e 0) (e 0) = 1/2` |

These are the round `S³`/`so(3)` values (`sec ≡ 1/4`, `Ric = ½g`, `Sc = 3/2`) in the algebraic
model, and they make the D7 layer demonstrably non-vacuous. They are **not** claims about any
smooth manifold.

---

## 7. Blocked items (task item 5)

`release/Poincare/D7/Curvature/Blocked.lean`. Each blocked item is a `def … : Prop` with no proof
plus a named blocker `def … : String`, and each blocker name is kernel-checked nonempty
(`BlockerManifoldCurvature_ne_nil`, `BlockerSecondBianchi_ne_nil`).

| blocked `Prop` | blocker | why unproved |
| --- | --- | --- |
| `ManifoldCurvatureStatement` | `B-D7-MANIFOLD-CURVATURE` | pinned mathlib has no `CovariantDerivative.curvature`; the construction needs second covariant derivatives of sections and smoothness of the connection. The statement quantifies the D2 contract `CovariantDerivativeCurvatureStatement`. |
| `SecondBianchiStatement` | `B-D7-SECOND-BIANCHI` | needs a covariant-derivative calculus on tensor fields (`∇R`); the abstract connection is a single bilinear map. The statement is parametrized by `CovariantDerivativeOfCurvature` (directional derivative `dir` + Leibniz rule for `∇R`); `SecondBianchiIdentity` is the cyclic identity. |

No `sorry`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`, `sorryAx` or `admit` occurs in
any authored file (Section 9).

---

## 8. Verification commands and exit codes

Transcript: `longrun/d7-logs-verify/verify_transcript.log`; rerunnable script:
`longrun/d7-logs-verify/run_verification.sh`. All commands run from `release/` with
`export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan; export PATH="$ELAN_HOME/bin:$PATH"`.

| # | command | exit | evidence |
| --- | --- | --- | --- |
| 1 | `rm -rf .lake/build/{lib/lean,ir}/Poincare/D7` then `lake build` | **0** | `lake_build_all.log` (8955 jobs, all D7 modules rebuilt) |
| 2 | `lake env lean Poincare/D7/Curvature/Basic.lean` | **0** | `lean_Poincare_D7_Curvature_Basic.lean.log` |
| 3 | `lake env lean Poincare/D7/Curvature/Symmetries.lean` | **0** | `…_Symmetries.lean.log` |
| 4 | `lake env lean Poincare/D7/Curvature/Sectional.lean` | **0** | `…_Sectional.lean.log` |
| 5 | `lake env lean Poincare/D7/Curvature/Example.lean` | **0** | `…_Example.lean.log` |
| 6 | `lake env lean Poincare/D7/Curvature/Blocked.lean` | **0** | `…_Blocked.lean.log` |
| 7 | `lake env lean Poincare/D7/Curvature/Bridge.lean` | **0** | `…_Bridge.lean.log` |
| 8 | `lake env lean Poincare/D7/Curvature/Probe.lean` | **0** | `…_Probe.lean.log` (API index output) |
| 9 | `lake env lean Poincare/D7/Curvature/Audit.lean` | **0** | `…_Audit.lean.log` (59 `#print axioms`) |
| 10 | `lake env lean Poincare/D7/Curvature.lean` | **0** | `…_Curvature.lean.log` (umbrella) |
| 11 | `python3 input/d5-tools/scan_forbidden.py Poincare/D7` | **0** | `forbidden-scan.json` (9 files, 0 hard, 0 soft) |
| 12 | sha256 integrity, D6 vs worktree (`.lake` excluded) | **0** | `source-integrity.json` (179 checked, 0 changed) |
| 13 | `grep -rin curvature Mathlib/ --include='*.lean'` (pinned mathlib) | **0** | 1 line, docstring only |

Per-file exit codes: `longrun/d7-logs-verify/exit_codes.txt` = `0` for all nine files.

---

## 9. Axiom audit

Command: `lake env lean Poincare/D7/Curvature/Audit.lean` (exit 0). It runs `#print axioms` on
**59 principal declarations**: the datum, both tensors, all symmetry theorems, the Ricci and
scalar curvature declarations, the sectional-curvature declarations, the generic algebra lemma,
the acceptance-named bridges, the blocked `Prop`s, and the 11 declarations of the concrete
`so(3)` model.

**Result:** all 59 report the single cone

```
'<declaration>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No declaration depends on `sorryAx`, `native_decide`, `proof_wanted`, or any unapproved axiom.
Full output: `longrun/d7-logs-verify/lean_Poincare_D7_Curvature_Audit.lean.log`; machine summary:
`longrun/d7-logs-verify/axiom-summary.json` (`print_axioms_entries=59`, `nonstandard_cones=NONE`).

---

## 10. Forbidden-token scan

```
$ python3 input/d5-tools/scan_forbidden.py Poincare/D7
exit 0
{"lean_files_scanned": 9, "hard_match_count": 0, "soft_match_count": 0, "matches": []}
```

Scanner: `input/d5-tools/scan_forbidden.py` (comment/string-aware). Hard tokens: `sorry`,
`axiom`, `unsafe`, `native_decide`, `proof_wanted`, `sorryAx`, `admit`. Soft:
`implemented_by`, `extern`. Zero matches. (A raw `grep` finds the tokens only inside docstrings
that state their absence.)

---

## 11. Acceptance mapping

| acceptance criterion | status |
| --- | --- |
| probe mathlib curvature declarations and reuse them | `Probe.lean` exit 0; `#check_failure` records the absence; mathlib `CovariantDerivative`/Levi-Civita API probed and used in the blocked statement; D2 `AbstractConnection.curvature` and `CurvatureOperator.ricci` reused |
| define `(1,3)` and `(0,4)` tensors, finite-dimensionality/index raising explicit | `RiemannCurvatureData`, `curvature`, `curvatureForm`; `[FiniteDimensional ℝ V]`, orthonormal basis, `MetricData.raiseIndex` |
| kernel-checked first-pair skew | `curvature_skew₁₂`, `curvatureForm_skew₁₂` |
| kernel-checked second-pair skew (metric compatibility) | `form_comp_sub_skew`, `curvatureForm_skew₃₄` |
| kernel-checked pair interchange | `curvatureForm_interchange` |
| kernel-checked first Bianchi | `curvature_bianchi`, `curvatureForm_bianchi` |
| Ricci agrees with D2 `CurvatureOperator.ricci` | `ricciForm_eq_ricciOperator` (`rfl`), `ricciForm_eq_sum_basis`, `ricciForm_symm` |
| sectional curvature for a nondegenerate 2-plane, well-defined under scaling | `sectionalCurvature`, `IsNondegenerate2Plane`, `sectionalCurvature_smul`, `sectionalCurvature_gl2`, `TwoPlane.sectionalCurvature_congr` |
| at least one new `.lean` file compiles (`lake env lean`, exit 0) | 9/9 exit 0 |
| `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}` | 59/59, single cone |
| no `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted` | scan 0 matches |
| unproved inputs as explicit `Prop`s with named blockers | `ManifoldCurvatureStatement` (`B-D7-MANIFOLD-CURVATURE`), `SecondBianchiStatement` (`B-D7-SECOND-BIANCHI`) |
| result card with exact commands, exit codes and axiom output | this card + `.json` |

---

## 12. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-riemann-curvature-tensor
bash longrun/d7-logs-verify/run_verification.sh   # full transcript, all gates
```

or manually:

```bash
cd release
lake build                                            # exit 0, whole D6 release + D7 (8955 jobs)
for f in Poincare/D7/Curvature/{Basic,Symmetries,Sectional,Example,Blocked,Bridge,Probe,Audit}.lean \
         Poincare/D7/Curvature.lean; do
  lake env lean "$f"                                  # each exit 0
done
lake env lean Poincare/D7/Curvature/Audit.lean        # exit 0, 59 #print axioms
cd .. && python3 input/d5-tools/scan_forbidden.py release/Poincare/D7   # exit 0, 0 matches
```

---

## 13. Honest boundary

- The connection is the **D2 abstract algebraic** Koszul connection on a real vector space, not a
  mathlib `CovariantDerivative` on a smooth manifold. The bracket is abstract data, not the Lie
  bracket of vector fields.
- The `(1,3)` tensor is the D2 abstract curvature; the D7 contribution is the metric datum,
  metric compatibility, the `(0,4)` lowering, the second-pair and interchange symmetries, the
  Ricci/scalar contraction layer with explicit index raising, sectional curvature, and the
  non-flat consistency model.
- The manifold-level curvature tensor (`CovariantDerivative.curvature`) is **not** constructed;
  it is the blocked `ManifoldCurvatureStatement`.
- The second Bianchi identity is **not** proved; it is the blocked `SecondBianchiStatement`
  (needs `∇R` and a tensor covariant-derivative calculus).
- No claim is made about the Levi-Civita existence theorem, smoothness of
  `leviCivitaConnection`, Ricci flow, or the Poincaré conjecture.

---

## 14. Repair attempt 1 — harness compile-gate environment fix (2026-09-09T20:50Z+08:00)

### 14.1 What the gate does, and what failed

The harness gate (`longrun/bin/dispatch_loop.py:compile_gate`) walks the worktree for every
`*.lean` file (skipping `.lake`, `.git`, `.dshpkg`) and runs

```bash
lake env lean <absolute path>      # cwd = worktree root
```

with `ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan`. The original verification
(§8) ran `lake env lean` from `release/`, which contains the Lake package
(`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`); the gate instead runs from the
**worktree root**, which had no toolchain file. Result: every one of the 73 files failed
immediately with

```
error: no default toolchain configured. run `elan default stable` ...
```

(exit 1, `real 0m0.002s`) — an environment failure, not a source error. Reproduced verbatim
before the fix with `lake env lean release/Poincare/D7/Curvature/Basic.lean` from the root.

### 14.2 Fix (environment only — no `.lean` source edited)

The root package re-exposes the already-built `release/.lake` tree, the same pattern used by
the repaired sibling D7/D8 worktrees:

| root entry | value |
| --- | --- |
| `lean-toolchain` | copy of `release/lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`) |
| `lake-manifest.json` | copy of `release/lake-manifest.json` (pinned mathlib `7974e751…`) |
| `lakefile.toml` | minimal package `D7RiemannCurvatureTensorRoot`, `packagesDir = ".lake/packages"`, requires mathlib |
| `.lake` | symlink `→ release/.lake` (build artifacts + packages, nothing re-fetched) |

No authored or D6-copied file was modified: sha256 integrity against `D6_weekly_release` is
still **179 files checked, 0 changed, 0 missing**, and the 9 authored D7 files are untouched
(mtimes 15:17–15:37, i.e. from the original session). The fix adds only build scaffolding at
the worktree root.

### 14.3 Re-verification with the gate command

`longrun/d7-logs-repair/gate_replication.py` replicates `compile_gate` exactly (same walk,
same skip list, same cwd, same env, same 1800 s timeout) and writes one log per file:

| check | result | evidence |
| --- | --- | --- |
| `lake env lean <file>` from worktree root, all 73 `.lean` files | **73/73 exit 0** | `longrun/d7-logs-repair/gate_replication.json`, `gate_replication.log`, per-file `*.log` |
| authored D7 layer (9 files) | **9/9 exit 0** | same, plus `longrun/d7-logs-verify/exit_codes.txt` |
| forbidden-token scan (`release/Poincare/D7`) | **0 hard, 0 soft** in 9 files | re-run 2026-09-09, same `scan_forbidden.py` |
| D6 source integrity | **179 checked, 0 changed, 0 missing** | re-run 2026-09-09 |

No mathematical content changed in this repair; the card of §0–§13 stands, and no new claims
are made.

**Repair verdict: TASK_DONE**

