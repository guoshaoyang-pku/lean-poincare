# D7-orientability-volume-form — result card

**Task id:** `D7-orientability-volume-form`
**Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-orientability-volume-form`
**Generated (UTC):** 2026-09-09T16:44:05Z
**Verdict:** `TASK_DONE` — kernel-checked volume-form algebra on an oriented finite-dimensional real
inner product space (determinant interface, metric-scaling law `vol (c • g) = c^(n/2) vol g`,
orientation-reversal sign law, finite-dimensional change of variables for linear maps with nonzero
determinant), plus the manifold-level Riemannian volume form and measure as explicit unproved
`Prop`s with named blockers and the exact missing mathlib dependencies (never
`sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`).

---

## 0. Bottom line

| item | result |
| --- | --- |
| new files (only under `release/Poincare/D7/Volume/`, plus the umbrella `release/Poincare/D7/Volume.lean`) | **8 Lean files, 1115 lines, 63 declarations** |
| compiled with `lake env lean` from the worktree root | **8/8 authored files exit 0** (`longrun/d7-volume-logs/exit_codes.txt`) |
| harness-gate replication (every `.lean` in the worktree, `lake env lean` from the root) | **90/90 exit 0** (`longrun/d7-volume-logs/gate_exit_codes.txt`, `gate_replication.json`) |
| whole release package `lake build` | **exit 0** (8972 jobs) |
| `#print axioms` audit | **59 principal declarations**; cones `{propext, Classical.choice, Quot.sound}` (53), `{propext}` (1), none (5); **no nonstandard cone** |
| forbidden-token scan (comment/string-aware) | **0 hard, 0 soft** in 7 files under `release/Poincare/D7/Volume/`; D7-wide scan (26 files, incl. the umbrella) also **0 hard, 0 soft** |
| copied scaffold files modified | **0** (`diff -rq` against `../D7-ricci-scalar-curvature`, `.lake` and the new `Volume` files excluded: the only differences are the new log directory and this result card) |
| non-vacuity | concrete `EuclideanSpace ℝ (Fin n)` model: `vol (e₀,e₁) = 1`, `2×2` determinant formula, scaling factor `4` for `c = 4`, reversed value `-1`, `det (2 • id) = 4` |
| blocked items | `RiemannianVolumeFormExistsStatement`, `RiemannianVolumeFormSmoothStatement`, `RiemannianVolumeMeasureStatement` (named blockers; exact missing mathlib dependencies listed) |

**Not claimed:** no construction of a manifold orientation, no smooth top alternating-form bundle,
no smooth global Riemannian volume form, no Riemannian volume measure, no integration of top forms
on manifolds. The manifold-level statements are state-only `Prop`s (Section 7).

---

## 1. Scaffold, environment, and source integrity

The worktree was scaffolded from `../D7-ricci-scalar-curvature/` as instructed. Hard links are
rejected on this filesystem (`ln` and `cp -al` fail with `Invalid cross-device link` even for two
files on the same device), so the scaffold was copied with `cp -a` (full copies, no shared inodes);
this is an environment property, not a source change.

| command | exit | note |
| --- | --- | --- |
| `cp -al ../D7-ricci-scalar-curvature/. .` | **1** | every entry fails with `Invalid cross-device link`; hard links are not permitted here |
| `cp -a ../D7-ricci-scalar-curvature/. .` | **0** | full copy; scaffold intact |
| `diff -rq ../D7-ricci-scalar-curvature . -x .lake -x Volume -x Volume.lean` | **1** | only the new `longrun/d7-volume-logs` directory and `longrun/results/D7-orientability-volume-form.md` are extra; **no shared file differs** |

Environment:

| key | value |
| --- | --- |
| Lean | `4.34.0-rc2` (commit `6a10ac8c22be`) |
| mathlib | `7974e751bece493b6ff508039423ca9fa2452fa8` |
| `ELAN_HOME` | `/data3/guoshaoyang/workdir/lean_poincare/elan` |

New files:

| file | lines | role |
| --- | --- | --- |
| `release/Poincare/D7/Volume.lean` | 37 | umbrella module |
| `release/Poincare/D7/Volume/Basic.lean` | 193 | `VolumeFormData`, `volumeForm`, determinant interface, orientation reversal, isometry laws, `std` |
| `release/Poincare/D7/Volume/Scaling.lean` | 161 | `scaledBasis`, `scaledVolumeForm`, metric-scaling law `vol (c • g) = c^(n/2) • vol g` |
| `release/Poincare/D7/Volume/ChangeOfVariables.lean` | 123 | algebraic and measure-theoretic change of variables for linear maps with nonzero determinant |
| `release/Poincare/D7/Volume/Example.lean` | 124 | concrete Euclidean non-vacuity witnesses |
| `release/Poincare/D7/Volume/Blocked.lean` | 223 | state-only `Prop`s, named blockers, exact missing mathlib dependencies |
| `release/Poincare/D7/Volume/Probe.lean` | 153 | compilable mathlib/D7 API probe (`#check` / `#check_failure`) |
| `release/Poincare/D7/Volume/Audit.lean` | 101 | 59 `#print axioms` commands |

---

## 2. Mathlib probe (task item 1 of the layer)

`release/Poincare/D7/Volume/Probe.lean` compiles (exit 0) and records the probe.

### 2.1 Present and reused (not redefined)

`Orientation R M ι` (an orientation as a ray in the top alternating forms),
`Orientation.volumeForm`, `Orientation.volumeForm_robust`, `Orientation.volumeForm_robust_neg`,
`Orientation.volumeForm_neg_orientation`, `Orientation.volumeForm_map`,
`Orientation.volumeForm_comp_linearIsometryEquiv`,
`Orientation.abs_volumeForm_apply_of_orthonormal`, `Orientation.map`,
`Orientation.map_eq_iff_det_pos`, `Orientation.map_eq_neg_iff_det_neg`, `OrthonormalBasis`,
`OrthonormalBasis.toBasis`, `OrthonormalBasis.adjustToOrientation`, `stdOrthonormalBasis`,
`orthonormal_iff_ite`, `AlternatingMap.map_smul_univ`, `Module.Basis.det`,
`Module.Basis.det_apply`, `Module.Basis.det_self`, `Module.Basis.det_comp`,
`Module.Basis.det_unitsSMul`, `Module.Basis.unitsSMul`, `Module.Basis.unitsSMul_apply`,
`Module.Basis.orientation_unitsSMul`, `Module.Basis.orientation_eq_iff_det_pos`,
`Module.Ray.units_smul_of_pos`, `LinearMap.det_smul`, `LinearMap.det_comp`,
`LinearMap.det_conj`, `Measure.map_linearMap_addHaar_eq_smul_addHaar`,
`Measure.addHaar_preimage_linearMap`, `Measure.addHaar_image_linearMap`, `Measure.addHaar`,
`Measure.IsAddHaarMeasure`, `lintegral_map`, `lintegral_smul_measure`, `ModelWithCorners`,
`IsManifold`, `TangentSpace`, `RiemannianBundle`, `IsRiemannianManifold`,
`IsContMDiffRiemannianBundle`, `ContMDiffSection`, `FiberBundle`, `VectorBundle`,
`ContMDiffVectorBundle`, `tangentSpaceCastModel`.

### 2.2 Absent at the pinned revision (recorded with `#check_failure`)

`Manifold.Orientation`, `IsManifold.Orientable`, `Orientable`, `RiemannianVolumeForm`,
`RiemannianVolumeMeasure`, `Bundle.AlternatingMap`, `RiemannianDensity`, `OrientableManifold`.
Full-text counts on the pinned checkout are 0 for each of these names. Consequently the
manifold-level volume form/measure are the blocked `Prop`s of Section 7.

---

## 3. `VolumeFormData` and the determinant interface (task item 1)

`release/Poincare/D7/Volume/Basic.lean`:

```lean
structure VolumeFormData (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] where
  n : ℕ
  finrank_eq : finrank ℝ V = n
  orientation : Orientation ℝ V (Fin n)
```

The dimension equality is a field, so the `Fact (finrank ℝ V = n)` instance required by
`Orientation.volumeForm` is installed locally (`letI`) in every lemma; no global instance is
imposed and there is no diamond.

| declaration | statement |
| --- | --- |
| `volumeForm` | the top alternating form `V [⋀^Fin D.n]→ₗ[ℝ] ℝ`, definitionally mathlib's `Orientation.volumeForm` |
| `volumeForm_def` | the definitional unfolding with the local `Fact` instance |
| `volumeForm_eq_det` | **explicit determinant interface**: for a positively oriented orthonormal basis `b`, `D.volumeForm = b.toBasis.det` |
| `volumeForm_eq_neg_det_of_orientation_ne` | for a negatively oriented orthonormal basis `b`, `D.volumeForm = -b.toBasis.det` |
| `volumeForm_apply_basis` | `D.volumeForm b = 1` on a positively oriented orthonormal basis |
| `abs_volumeForm_apply_of_orthonormal` | `|D.volumeForm b| = 1` for any orthonormal basis |
| `reverse` | the datum with `orientation := -D.orientation` |
| `reverse_volumeForm` | **orientation-reversal sign law**: `D.reverse.volumeForm = -D.volumeForm` |
| `volumeForm_comp_linearIsometryEquiv_of_det_pos` | `det φ > 0 ⇒ D.volumeForm (φ ∘ v) = D.volumeForm v` |
| `volumeForm_comp_linearIsometryEquiv_of_det_neg` | `det φ < 0 ⇒ D.volumeForm (φ ∘ v) = -D.volumeForm v` |
| `std` | the standard datum of `stdOrthonormalBasis`, witnessing that `VolumeFormData` is inhabited |
| `std_volumeForm_eq_det` | `(std V).volumeForm = (stdOrthonormalBasis ℝ V).toBasis.det` |

The determinant interface is not a redefinition: `volumeForm_eq_det` is mathlib's
`Orientation.volumeForm_robust`, and `reverse_volumeForm` is mathlib's
`Orientation.volumeForm_neg_orientation`. The negative-isometry sign law is a new D7 proof via
`Orientation.volumeForm_map` and `Orientation.map_eq_neg_iff_det_neg`.

---

## 4. The metric-scaling law `vol (c • g) = c^(n/2) vol g` (task item 1)

`release/Poincare/D7/Volume/Scaling.lean` proves the scaling law through the explicit determinant
interface. If `b` is an orthonormal basis of the metric `g`, the rescaled metric `c • g`
(`c > 0`) has the orthonormal basis `i ↦ (√c)⁻¹ • b i`:

| declaration | statement |
| --- | --- |
| `sqrtInvUnit c hc` | the unit `(√c)⁻¹` of `ℝ` |
| `sqrt_pow_eq_rpow_half` | `(√c) ^ n = c ^ (n / 2 : ℝ)` for `c > 0` |
| `scaledBasis b c hc` | the basis `i ↦ (√c)⁻¹ • b i` |
| `scaledBasis_apply` | `D.scaledBasis b c hc i = (√c)⁻¹ • b i` |
| `scaledBasis_orthonormal` | `c * inner ℝ (scaledBasis i) (scaledBasis j) = if i = j then 1 else 0`, i.e. the scaled basis is orthonormal for the explicit form `c • g` |
| `scaledBasis_orientation` | positive rescaling preserves the orientation: `(D.scaledBasis b c hc).orientation = b.toBasis.orientation` |
| `scaledBasis_det_apply` | `(D.scaledBasis b c hc).det v = c ^ (n / 2 : ℝ) * b.toBasis.det v` (from `Module.Basis.det_unitsSMul`) |
| `scaledVolumeForm b c hc` | the determinant in the scaled basis, i.e. the volume form of `c • g` |
| `scaledVolumeForm_apply` | `D.scaledVolumeForm b c hc v = c ^ (D.n / 2 : ℝ) * D.volumeForm v` |
| `volumeForm_smul_metric` | **`D.scaledVolumeForm b c hc = c ^ (D.n / 2 : ℝ) • D.volumeForm`** |
| `scaledVolumeForm_one` | `c = 1` gives back `D.volumeForm` |

The determinant computation is genuinely `(√c)^n` and is rewritten to the task's exponent notation
by `sqrt_pow_eq_rpow_half`; the two directions are both kernel-checked.

---

## 5. Change of variables for linear maps with nonzero determinant (task item 2)

`release/Poincare/D7/Volume/ChangeOfVariables.lean` proves both layers.

**Algebraic (volume-form) layer** — the determinant change-of-variables rule for top forms,
proved from the explicit determinant interface and `Module.Basis.det_comp`:

```lean
theorem VolumeFormData.volumeForm_comp_linearMap (b) (hb : b.toBasis.orientation = D.orientation)
    (T : V →ₗ[ℝ] V) (v : Fin D.n → V) :
    D.volumeForm (T ∘ v) = LinearMap.det T * D.volumeForm v
```

and the nonzero corollary `volumeForm_comp_linearMap_ne_zero`
(`det T ≠ 0` and `vol v ≠ 0` imply `vol (T ∘ v) ≠ 0`).

**Measure-theoretic layer** — the finite-dimensional linear change of variables for a Haar measure
`μ` on a finite-dimensional real normed space, with `LinearMap.det T ≠ 0`:

```lean
theorem lintegral_comp_linearMap_eq :
    ∫⁻ x, g (T x) ∂μ = ENNReal.ofReal |(LinearMap.det T)⁻¹| * ∫⁻ y, g y ∂μ
theorem lintegral_linearMap_eq :
    ∫⁻ y, g y ∂μ = ENNReal.ofReal |LinearMap.det T| * ∫⁻ x, g (T x) ∂μ
```

These are proved from mathlib's `Measure.map_linearMap_addHaar_eq_smul_addHaar` and
`lintegral_map`/`lintegral_smul_measure`. The set-level corollaries
`addHaar_preimage_linearMap'` and `addHaar_image_linearMap'`, and the measure restatement
`map_linearMap_eq_smul_addHaar`, are recorded too.

---

## 6. Non-vacuity: concrete Euclidean witnesses

`release/Poincare/D7/Volume/Example.lean` instantiates the theory on
`EuclideanSpace ℝ (Fin n)` with the standard orthonormal basis `EuclideanSpace.basisFun`:

| theorem | statement |
| --- | --- |
| `euclideanVolumeFormData_volumeForm_eq_det` | the determinant interface for the standard datum |
| `euclideanVolumeFormData_one_apply` | `vol v = v 0 0` in dimension `1` |
| `euclideanVolumeFormData_two_apply` | `vol v = v 0 0 * v 1 1 - v 0 1 * v 1 0` in dimension `2` |
| `euclideanVolumeFormData_apply_basis` | `vol (basisFun) = 1` in every dimension |
| `euclideanVolumeFormData_scaling_witness` | with `c = 4` in dimension `2`, `scaledVolumeForm v = 4 * volumeForm v` (since `4^(2/2) = 4`) |
| `euclideanVolumeFormData_reverse_apply_basis` | the reversed-orientation volume form on the standard basis is `-1` |
| `euclideanVolumeFormData_changeOfVariables_witness` | `vol ((2 • id) ∘ v) = 4 * vol v`, i.e. the determinant factor `det (2 • id) = 4` |

---

## 7. Blocked items: manifold-level volume form and measure (task item 3)

`release/Poincare/D7/Volume/Blocked.lean`. Each blocked item is a `def … : Prop` with no proof
plus a named blocker `def … : String`, and each blocker name is kernel-checked nonempty.

| blocked `Prop` | blocker | why unproved |
| --- | --- | --- |
| `RiemannianVolumeFormExistsStatement` | `B-D7-RIEMANNIAN-VOLUME-FORM` | needs a manifold orientation and the smooth top alternating-form bundle; only the pointwise `Orientation.volumeForm` exists |
| `RiemannianVolumeFormSmoothStatement` | `B-D7-RIEMANNIAN-VOLUME-FORM` | needs the bundle contract `TopFormBundle` (fiberwise `AlternatingMap ℝ (TangentSpace I x) ℝ (Fin n)` with `FiberBundle`/`VectorBundle`/`ContMDiffVectorBundle`) and a smooth positively oriented orthonormal frame |
| `RiemannianVolumeMeasureStatement` | `B-D7-MANIFOLD-MEASURE-THEORY` | no `MeasurableSpace`/`BorelSpace` for charted spaces, no integration of top forms, no Riemannian density gluing by partition of unity |

The exact missing mathlib dependencies are listed in `MissingMathlibDependencies` (6 entries,
kernel-checked nonempty and of length 6):

1. **Manifold orientation** — no tangent-bundle orientation, no manifold orientability predicate,
   no orientation double cover (only `Orientation R M ι` for a module).
2. **Top alternating-form bundle** — no `FiberBundle`/`VectorBundle`/`ContMDiffVectorBundle`
   instances for `x ↦ AlternatingMap ℝ (TangentSpace I x) ℝ n` (top exterior power of the
   cotangent bundle).
3. **Smooth frame field** — `stdOrthonormalBasis`/`Orientation.finOrthonormalBasis` are
   noncomputable and not smooth in the base point.
4. **Manifold measure theory** — no `MeasurableSpace`/`BorelSpace` instance for a `ChartedSpace`,
   no integration of top-degree forms, no Riemannian volume density `√(det g)`.
5. **Partition of unity** — mathlib has `SmoothPartitionOfUnity` but no gluing of local volume
   forms/densities into a global measure.
6. **Haar measure** — `IsAddHaarMeasure` is only for locally compact topological groups and
   finite-dimensional real vector spaces, not for manifolds.

No `sorry`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`, `sorryAx` or `admit` occurs in
any authored file (Section 10).

---

## 8. Verification commands and exit codes

All commands run from the worktree root with
`export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan; export PATH="$ELAN_HOME/bin:$PATH"`.

| # | command | exit | evidence |
| --- | --- | --- | --- |
| 1 | `cd release && lake build` | **0** | 8972 jobs, whole release package |
| 2 | `lake env lean release/Poincare/D7/Volume/Basic.lean` | **0** | `longrun/d7-volume-logs/release_Poincare_D7_Volume_Basic.lean.log` |
| 3 | `lake env lean release/Poincare/D7/Volume/Scaling.lean` | **0** | `…_Scaling.lean.log` |
| 4 | `lake env lean release/Poincare/D7/Volume/ChangeOfVariables.lean` | **0** | `…_ChangeOfVariables.lean.log` |
| 5 | `lake env lean release/Poincare/D7/Volume/Example.lean` | **0** | `…_Example.lean.log` |
| 6 | `lake env lean release/Poincare/D7/Volume/Blocked.lean` | **0** | `…_Blocked.lean.log` |
| 7 | `lake env lean release/Poincare/D7/Volume/Probe.lean` | **0** | `…_Probe.lean.log` (API index output) |
| 8 | `lake env lean release/Poincare/D7/Volume/Audit.lean` | **0** | `…_Audit.lean.log` (59 `#print axioms`) |
| 9 | `lake env lean release/Poincare/D7/Volume.lean` | **0** | `…_Volume.lean.log` (umbrella) |
| 10 | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D7/Volume` | **0** | `longrun/d7-volume-logs/forbidden-scan.json` (7 files, 0 hard, 0 soft) |
| 10b | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D7` (includes the umbrella `Volume.lean` and the sibling D7 layers) | **0** | `longrun/d7-volume-logs/forbidden-scan-d7.json` (26 files, 0 hard, 0 soft) |
| 11 | `diff -rq ../D7-ricci-scalar-curvature . -x .lake -x Volume -x Volume.lean` | **1** | only the new `longrun/d7-volume-logs` directory and the new result card are extra; no shared file differs |
| 12 | `bash longrun/d7-volume-logs/run_gate.sh` (harness-gate replication: `lake env lean` on every `.lean`, cwd = worktree root) | **0** | **90/90 exit 0**, `longrun/d7-volume-logs/gate_exit_codes.txt` and `gate_replication.json` |

Per-file exit codes: `longrun/d7-volume-logs/exit_codes.txt` = `0` for all eight files.

---

## 9. Axiom audit

Command: `lake env lean release/Poincare/D7/Volume/Audit.lean` (exit 0), output
`longrun/d7-volume-logs/audit.log`. It runs `#print axioms` on **59 principal declarations**: the
datum, the volume form and its determinant interface, the orientation-reversal and isometry laws,
the scaling layer, the change-of-variables layer, the concrete Euclidean witnesses, the blocked
`Prop`s, the named blockers and the missing-dependency list.

**Result** (`longrun/d7-volume-logs/axiom-summary.json`):

| cone | count |
| --- | --- |
| `{propext, Classical.choice, Quot.sound}` | 53 |
| `{propext}` | 1 (`MissingMathlibDependencies_ne_nil`) |
| no axioms | 5 (the three blocker strings and the two missing-dependency data declarations) |
| nonstandard cones | **0** |

No declaration depends on `sorryAx`, `native_decide`, `proof_wanted`, or any unapproved axiom.

---

## 10. Forbidden-token scan

```
$ python3 input/d5-tools/scan_forbidden.py release/Poincare/D7/Volume
exit 0
{"lean_files_scanned": 7, "hard_match_count": 0, "soft_match_count": 0, "matches": []}
```

Scanner: `input/d5-tools/scan_forbidden.py` (comment/string-aware). Hard tokens: `sorry`,
`axiom`, `unsafe`, `native_decide`, `proof_wanted`, `sorryAx`, `admit`. Soft: `implemented_by`,
`extern`. Zero matches. The umbrella `release/Poincare/D7/Volume.lean` lies outside the `Volume/`
directory, so the whole `release/Poincare/D7` tree was scanned as well (26 files including the
sibling D7 layers, `hard_match_count = 0`, `soft_match_count = 0`). (A raw `grep` finds the tokens
only inside docstrings that state their absence.)

---

## 11. Acceptance mapping

| acceptance criterion | status |
| --- | --- |
| define `VolumeFormData` on an oriented finite-dimensional inner-product space | `VolumeFormData` with `n`, `finrank_eq`, `orientation`; `volumeForm` is mathlib `Orientation.volumeForm` |
| kernel-checked scaling law `vol (c • g) = c^(n/2) vol (g)` via an explicit determinant interface | `scaledBasis_det_apply`, `scaledVolumeForm_apply`, `volumeForm_smul_metric`, `sqrt_pow_eq_rpow_half`; determinant interface `volumeForm_eq_det` |
| orientation-reversal sign law | `reverse_volumeForm`, `volumeForm_eq_neg_det_of_orientation_ne`, `volumeForm_comp_linearIsometryEquiv_of_det_neg` |
| checked finite-dimensional change-of-variables lemma for linear maps with nonzero determinant | algebraic `volumeForm_comp_linearMap`; measure-theoretic `lintegral_comp_linearMap_eq` / `lintegral_linearMap_eq` with `LinearMap.det T ≠ 0` |
| state-only `Prop`s for existence and smoothness of the Riemannian volume form on an oriented smooth manifold | `RiemannianVolumeFormExistsStatement`, `RiemannianVolumeFormSmoothStatement` |
| list exact missing mathlib dependencies (manifold measure theory) | `MissingMathlibDependencies` (6 entries), `BlockerManifoldMeasureTheory`, `BlockerManifoldOrientation` |
| every authored file compiles (`lake env lean`, exit 0) | 8/8 exit 0 |
| `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}` | 59/59 entries, no nonstandard cone |
| no `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted` | scan 0 hard, 0 soft |
| result card with exact commands, exit codes and axiom output | this card + `.json` |

---

## 12. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-orientability-volume-form

cd release && lake build                                  # exit 0, whole release package
cd ..
for f in release/Poincare/D7/Volume/{Basic,Scaling,ChangeOfVariables,Example,Blocked,Probe,Audit}.lean \
         release/Poincare/D7/Volume.lean; do
  lake env lean "$f"                                      # each exit 0
done
lake env lean release/Poincare/D7/Volume/Audit.lean       # exit 0, 59 #print axioms
python3 input/d5-tools/scan_forbidden.py release/Poincare/D7/Volume   # exit 0, 0 matches
```

Full-gate replication for every `.lean` file in the worktree:
`bash longrun/d7-volume-logs/run_gate.sh` (writes `gate_exit_codes.txt`).

---

## 13. Honest boundary

- The `VolumeFormData` layer is **finite-dimensional linear algebra** on a single inner product
  space; it does not construct a volume form on a manifold.
- The metric-scaling law is proved for the metric represented by the explicit scaled form
  `(x, y) ↦ c * ⟪x, y⟫` and the explicitly constructed `(c • g)`-orthonormal basis
  `scaledBasis`; it does not introduce a second `InnerProductSpace` instance on the same type.
- The measure-theoretic change of variables is the linear Haar-measure statement; it is not a
  change-of-variables formula for smooth maps between manifolds.
- The manifold orientation, the smooth top alternating-form bundle, the smooth global volume
  form and the Riemannian volume measure are **not** constructed; they are the blocked `Prop`s of
  Section 7 with the exact missing mathlib dependencies listed there.
- No claim is made about Ricci flow, the Poincaré conjecture, or any manifold-level curvature.
- The Euclidean witnesses are concrete consistency checks on `EuclideanSpace ℝ (Fin n)`, not
  claims about smooth manifolds.

**Verdict: TASK_DONE**
