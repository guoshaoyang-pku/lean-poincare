# D7-divergence-ibp — result card

**Task id:** `D7-divergence-ibp`
**Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-divergence-ibp`
**Generated (UTC):** 2026-09-09T17:22:49Z
**Verdict:** `TASK_DONE` — kernel-checked discrete divergence theorem on a finite oriented graph
(sum of interior divergences equals boundary flux), kernel-checked integration by parts on a
finite-difference slab with vanishing boundary terms, `DivergenceData` / `IBPCertificate` with
explicit boundary-term fields, and the smooth-manifold divergence theorem as an explicit unproved
`Prop` with named blockers and the exact missing mathlib dependencies (Stokes, Riemannian volume
measure, boundary manifold, metric divergence). No
`sorry` / `axiom` / `unsafe` / `native_decide` / `proof_wanted`.

---

## 0. Bottom line

| item | result |
| --- | --- |
| new files (only under `release/Poincare/D7/Divergence/`, plus the umbrella `release/Poincare/D7/Divergence.lean`) | **8 Lean files, 1518 lines, 102 declarations** |
| compiled with `lake env lean` from the worktree root | **8/8 authored files exit 0** (`longrun/d7-div-logs/exit_codes.txt`) |
| harness-gate replication (every `.lean` in the worktree, `lake env lean` from the root) | **98/98 exit 0**, no failures (`longrun/d7-div-logs/gate_exit_codes.txt`) |
| whole release package `lake build` | **exit 0** (8980 jobs); the scaffold's own `D6AUDIT` verdict is `PASS` |
| `#print axioms` audit | **102 principal declarations**: cone `{propext, Classical.choice, Quot.sound}` (90), cone `{propext}` (4), no axioms (8); **no nonstandard cone, no `sorryAx`** |
| forbidden-token scan (comment/string-aware) | **0 hard** in the 8 authored files; D7-wide scan (34 files) also **0 hard** |
| copied scaffold files modified | **0** (`diff -rq` against `../D7-orientability-volume-form`, `.lake` and the new files/logs excluded: **empty**) |
| non-vacuity | concrete single edge (`div = 3, -3`; flux `3, -3`), oriented triangle (`div = -3, 1, 2`, total `0`), two-node slab (`interior = -2`, `flux = 2`, boundary `0`) |
| blocked items | `SmoothManifoldDivergenceTheoremStatement` with 4 named blockers (`B-D7-STOKES`, `B-D7-RIEMANNIAN-VOLUME-MEASURE`, `B-D7-MANIFOLD-BOUNDARY`, `B-D7-MANIFOLD-DIVERGENCE`) and 7 exact missing mathlib dependencies |

**Not claimed:** no proof of the smooth-manifold divergence theorem, no Stokes theorem for
manifolds, no construction of a Riemannian volume measure, no boundary manifold/measure, no metric
divergence. The smooth-manifold statement is a state-only `Prop` (Section 7).

---

## 1. Scaffold, environment, and source integrity

The worktree was scaffolded from `../D7-orientability-volume-form/` as instructed.

| command | exit | note |
| --- | --- | --- |
| `cp -al ../D7-orientability-volume-form/. .` | **1** | every entry fails with `Invalid cross-device link` (hard links are rejected on this filesystem, even for two files on the same device); this matches the D7-orientability card |
| `cp -a ../D7-orientability-volume-form/. .` | **0** | full copy (372 MB, including the prebuilt `.lake`); scaffold intact |
| `diff -rq ../D7-orientability-volume-form . -x .lake -x Divergence -x Divergence.lean -x d7-div-logs -x 'D7-divergence-ibp.md' -x 'D7-divergence-ibp.json'` | **0** | no output: **no shared file differs**; the only additions are the new `release/Poincare/D7/Divergence*` files and this card |

Environment:

| key | value |
| --- | --- |
| Lean | `4.34.0-rc2` (commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`) |
| mathlib | `7974e751bece493b6ff508039423ca9fa2452fa8` |
| root package | `D7RiemannCurvatureTensorRoot` (re-exposes `release/.lake`, so `lake env lean` works from the worktree root) |
| release package | `PoincareRelease` (`release/lakefile.toml`) |

New files:

| file | lines | role |
| --- | --- | --- |
| `release/Poincare/D7/Divergence.lean` | 43 | umbrella module |
| `release/Poincare/D7/Divergence/Basic.lean` | 297 | `DivergenceData`, the discrete operators, the pairings, and `IBPCertificate` |
| `release/Poincare/D7/Divergence/Graph.lean` | 148 | discrete divergence theorem + discrete integration by parts |
| `release/Poincare/D7/Divergence/Slab.lean` | 165 | telescoping, product rule, slab IBP with vanishing boundary terms |
| `release/Poincare/D7/Divergence/Example.lean` | 242 | concrete non-vacuity witnesses |
| `release/Poincare/D7/Divergence/Blocked.lean` | 288 | state-only smooth-manifold statement, blockers, missing dependencies |
| `release/Poincare/D7/Divergence/Probe.lean` | 187 | compilable mathlib/D7 API probe (`#check` / `#check_failure`) |
| `release/Poincare/D7/Divergence/Audit.lean` | 148 | 102 `#print axioms` commands |

---

## 2. Mathlib probe (task item 1 of the layer)

`release/Poincare/D7/Divergence/Probe.lean` compiles (exit 0) and records the probe.

### 2.1 Present and reused

Discrete side: `Finset.sum_filter`, `Finset.sum_ite_eq`, `Finset.sum_ite_eq'`,
`Finset.sum_comm`, `Finset.sum_fiberwise`, `Finset.sum_fiberwise_of_maps_to`,
`Finset.sum_sub_distrib`, `Finset.sum_add_distrib`, `Finset.sum_eq_zero`, `Finset.sum_congr`,
`Finset.sum_bij`, `Finset.mul_sum`, `Finset.sum_mul`, `Fin.sum_univ_succ`,
`Fin.sum_univ_castSucc`.

Smooth side: `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` (the **Euclidean box
divergence theorem**), `MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le`,
`ModelWithCorners.boundary`, `ModelWithCorners.IsInteriorPoint`,
`ModelWithCorners.IsBoundaryPoint`, `mfderiv`, `ContMDiff`, `TangentSpace`, `RiemannianBundle`,
`IsRiemannianManifold`, `Measure.addHaar`, `Measure.IsAddHaarMeasure`, `Measure.haar`,
`Measure.IsHaarMeasure`.

### 2.2 Absent at the pinned revision (recorded with `#check_failure`)

`Stokes`, `Manifold.stokes`, `StokesTheorem`, `RiemannianVolumeMeasure`, `Manifold.divergence`,
`ManifoldOrientation`, `MeasureTheory.Measure.riemannianVolume`, `Bundle.AlternatingMap`.
Full-text search on the pinned checkout finds `stokes` only in the documentation of the Euclidean
box theorem, and there is no integration of top-degree forms on manifolds. Consequently the
smooth-manifold divergence theorem is the blocked `Prop` of Section 7.

### 2.3 API notes for this revision

The pinned mathlib reorganized the big-operator files: `Finset.sum_comm` lives in
`Mathlib.Algebra.BigOperators.Group.Finset.Sigma`, `Finset.sum_ite_eq` / `sum_ite_eq'` in
`...Group.Finset.Piecewise`, and `Fin.sum_univ_succ` / `Fin.sum_univ_castSucc` in
`Mathlib.Algebra.BigOperators.Fin`. `TangentSpace` is deliberately not reducible for type class
inference, so the directional derivative `mfderiv I 𝓘(ℝ) f x (X x)` is written with an explicit
`show ℝ from ...` in the Leibniz-rule field of `IsRiemannianDivergenceDatum`.

---

## 3. `DivergenceData` and `IBPCertificate` (task item 1)

`release/Poincare/D7/Divergence/Basic.lean`:

```lean
structure DivergenceData (V E : Type*) [Fintype V] [Fintype E] [DecidableEq V] where
  src : E → V
  tgt : E → V
```

The incidence data of a finite oriented graph: every edge `e : E` is oriented from `src e` to
`tgt e`. The discrete operators are

```lean
outFlow F v      = ∑ e ∈ univ.filter (src e = v), F e          -- outflow at v
inFlow  F v      = ∑ e ∈ univ.filter (tgt e = v), F e          -- inflow at v
divergence F v   = outFlow F v - inFlow F v                     -- net outflow
outFlux F S      = ∑ e ∈ univ.filter (src e ∈ S), F e
inFlux  F S      = ∑ e ∈ univ.filter (tgt e ∈ S), F e
boundaryFlux F S = (∑ e ∈ filter (src ∈ S ∧ tgt ∉ S), F e)
                     - (∑ e ∈ filter (tgt ∈ S ∧ src ∉ S), F e)  -- outward sign
```

and the integration-by-parts pairings

```lean
outPairing F φ S      = ∑ e ∈ filter (src ∈ S),        φ (src e) * F e
inPairing  F φ S      = ∑ e ∈ filter (tgt ∈ S),        φ (tgt e) * F e
boundaryOut F φ S     = ∑ e ∈ filter (src ∈ S ∧ tgt ∉ S), φ (src e) * F e
boundaryIn  F φ S     = ∑ e ∈ filter (tgt ∈ S ∧ src ∉ S), φ (tgt e) * F e
boundaryPairing F φ S = boundaryOut F φ S - boundaryIn F φ S
gradientPairing F φ S = ∑ e ∈ filter (src ∈ S ∧ tgt ∈ S), F e * (φ (tgt e) - φ (src e))
divPairing F φ S      = ∑ v ∈ S, φ v * divergence F v
```

**`IBPCertificate` with explicit boundary-term fields.** The certificate is not a tautology
package: the two boundary terms are *fields*, and the identity is a proof field.

```lean
structure IBPCertificate where
  interiorTerm : ℝ
  fluxTerm     : ℝ
  outBoundary  : ℝ     -- explicit outgoing boundary term
  inBoundary   : ℝ     -- explicit incoming boundary term
  ibp : interiorTerm + fluxTerm = outBoundary - inBoundary
```

with `IBPCertificate.boundaryTerm = outBoundary - inBoundary`, the restated identity
`IBPCertificate.ibp'`, and the cancellation lemma
`IBPCertificate.eq_zero_of_boundaryTerm_eq_zero` (plus its `interior = -flux` corollary).

The combinatorial engine is the fiberwise sum lemma (`DivergenceData.sum_fiber_of_mem`)

`∑_{j ∈ S} ∑_{i ∈ s, g i = j} f i = ∑_{i ∈ s, g i ∈ S} f i`,

proved by `Finset.sum_filter` → `Finset.sum_comm` → `Finset.sum_ite_eq` → `Finset.sum_filter`, and
the filter-splitting lemma (`DivergenceData.sum_filter_split`)

`∑_{i ∈ s, p i} f i = ∑_{i ∈ s, p i ∧ q i} f i + ∑_{i ∈ s, p i ∧ ¬q i} f i`.

---

## 4. Discrete divergence theorem on a finite graph (task item 2a)

`release/Poincare/D7/Divergence/Graph.lean`:

```lean
theorem DivergenceData.sum_divergence_eq_boundaryFlux (D : DivergenceData V E)
    (F : E → ℝ) (S : Finset V) :
    ∑ v ∈ S, D.divergence F v = D.boundaryFlux F S
```

Proof: `divergence = outFlow - inFlow`; summing over `S` and exchanging the order of summation
with `sum_fiber_of_mem` gives
`∑_{v ∈ S} divergence F v = outFlux F S - inFlux F S`; each of `outFlux` and `inFlux` is split by
`sum_filter_split` into its interior part (`src ∈ S ∧ tgt ∈ S`, resp. `tgt ∈ S ∧ src ∈ S`) and its
boundary part; the two interior parts are equal (`and_comm`), so only the outward boundary terms
survive, which is `boundaryFlux F S`. Kernel-checked, no `sorry`.

Corollaries:

* `DivergenceData.sum_divergence_univ_eq_zero` — **flow conservation on a closed graph**:
  `∑_v divergence F v = 0`;
* `DivergenceData.sum_divergence_eq_zero_of_closed` — for a region with no boundary edge
  (`∀ e, src e ∈ S ↔ tgt e ∈ S`), the divergence summed over `S` vanishes;
* `DivergenceData.sum_divergence_eq_boundaryFlux_of_ibp` — the divergence theorem recovered as
  the `φ = 1` case of the graph integration by parts, an independent cross-check of the direct
  proof.

**Discrete integration by parts on a graph** (the pairing form, with explicit boundary terms):

```lean
theorem DivergenceData.graph_ibp (D : DivergenceData V E) (F : E → ℝ) (φ : V → ℝ)
    (S : Finset V) :
    D.divPairing F φ S + D.gradientPairing F φ S = D.boundaryPairing F φ S
```

i.e. `∑_{v ∈ S} φ v * div F v + ∑_{interior e} F e * (φ (tgt e) - φ (src e))
= ∑_{leaving e} φ (src e) F e - ∑_{entering e} φ (tgt e) F e`. The certificate
`DivergenceData.ibpCertificate F φ S : IBPCertificate` packages it with `outBoundary`/`inBoundary`
fields. Also `boundaryPairing_one : boundaryPairing F 1 S = boundaryFlux F S` and
`gradientPairing_one : gradientPairing F 1 S = 0`.

---

## 5. Integration by parts on a finite-difference slab (task item 2b)

`release/Poincare/D7/Divergence/Slab.lean`. A slab is a product `α × Fin (n + 1)` of a finite
cross-section with `n + 1` nodes; `Δ⁺u a i = u a (i+1) - u a i`.

```lean
theorem sum_telescope (g : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (g i.succ - g i.castSucc) = g (Fin.last n) - g 0

theorem slab_product_rule (u v : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, u i.castSucc * (v i.succ - v i.castSucc))
      + (∑ i : Fin n, (u i.succ - u i.castSucc) * v i.succ)
      = u (Fin.last n) * v (Fin.last n) - u 0 * v 0
```

`sum_telescope` is proved from `Fin.sum_univ_succ` / `Fin.sum_univ_castSucc` by `abel`; the product
rule is the telescoping identity for `g i = u i * v i` after `ring` on each summand.

**Integration by parts with vanishing boundary terms** (the required kernel-checked statement):

```lean
theorem slab_ibp_vanishing (u v : α → Fin (n + 1) → ℝ)
    (hu0 : ∀ a, u a 0 = 0) (hvN : ∀ a, v a (Fin.last n) = 0) :
    (∑ a, ∑ i : Fin n, u a i.castSucc * (v a i.succ - v a i.castSucc))
      + (∑ a, ∑ i : Fin n, (u a i.succ - u a i.castSucc) * v a i.succ) = 0

theorem slab_ibp_vanishing' ... :
    (∑ a, ∑ i, u a i.castSucc * (v a i.succ - v a i.castSucc))
      = -∑ a, ∑ i, (u a i.succ - u a i.castSucc) * v a i.succ
```

with the divergence-form restatement `slab_ibp_divergence_form` (using the named
`slabForwardDiff` / `slabDivergence`), the general identity `slab_ibp` keeping the two boundary
terms explicit, and the certificate

```lean
def slabIBPCertificate (u v : α → Fin (n + 1) → ℝ) : IBPCertificate
-- interiorTerm = ∑ u Δv, fluxTerm = ∑ (Δu) v⁺,
-- outBoundary = ∑_a u a (last n) * v a (last n), inBoundary = ∑_a u a 0 * v a 0
```

together with `slabIBPCertificate_boundaryTerm_eq_zero` and `slabIBPCertificate_eq_zero`
(the interior pairings cancel under the vanishing boundary conditions).

---

## 6. Concrete non-vacuity witnesses

`release/Poincare/D7/Divergence/Example.lean`, all kernel-checked by computation:

| witness | value |
| --- | --- |
| single edge `0 → 1`, flow `3` | `divergence 0 = 3`, `divergence 1 = -3`, `∑ = 0` |
| boundary flux through `{0}` / `{1}` | `3` / `-3` |
| divergence theorem on `{0}` | `∑_{v ∈ {0}} div = 3 = boundaryFlux` |
| graph IBP on the single edge, potential `(1,2)` | `divPairing = -3`, `gradientPairing = 3`, `boundaryPairing = 0`; `(-3) + 3 = 0` |
| oriented triangle `0 → 1 → 2 → 0`, flow `(2,3,5)` | `div = (-3, 1, 2)`; `-3 + 1 + 2 = 0`; closed region ⇒ boundary flux `0` |
| slab `u = (0,2,7)`, `v = (3,1,0)` | `interiorTerm = -2`, `fluxTerm = 2`, `boundaryTerm = 0`; `(-2) + 2 = 0` |

---

## 7. Smooth-manifold divergence theorem: state-only `Prop` (task item 3)

`release/Poincare/D7/Divergence/Blocked.lean` records the theorem as an **explicit unproved
`Prop`** with named blockers; there is no `sorry`/`axiom`/`proof_wanted`.

The schematic datum collects the four blocked objects (volume measure, boundary measure,
divergence, metric normal pairing):

```lean
structure ManifoldDivergenceDatum (I : ModelWithCorners ℝ E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M] where
  volume          : Measure M
  boundaryMeasure : Measure M
  divergence      : (∀ x : M, TangentSpace I x) → M → ℝ
  normalPairing   : (∀ x : M, TangentSpace I x) → M → ℝ
```

The geometric requirements are separated into a predicate (`IsRiemannianDivergenceDatum`): the
volume is positive on nonempty open sets and finite on compacts; the boundary measure and the
normal pairing are supported on `ModelWithCorners.boundary I M`; the divergence is `ℝ`-linear and
satisfies the Leibniz rule `div (f • X) = f * div X + df (X)` for `ContMDiff I 𝓘(ℝ) 1 f`; the
normal pairing is `ℝ`-linear. The zero datum is a non-Riemannian inhabitant
(`not_isRiemannian_zero`), and the predicate is consistent on an empty manifold
(`isRiemannian_zero_of_isEmpty`).

The blocked statement is

```lean
def SmoothManifoldDivergenceTheoremStatement : Prop :=
  ∀ (E) [..] (H) [..] (I : ModelWithCorners ℝ E H)
    (M) [..] [IsManifold I (⊤ : WithTop ℕ∞) M] [MeasurableSpace M] [BorelSpace M]
    [RiemannianBundle (TangentSpace I : M → Type uE)],
    ∀ D : ManifoldDivergenceDatum I M, IsRiemannianDivergenceDatum I M D →
      ∀ X : ∀ x : M, TangentSpace I x,
        Integrable (fun x => D.divergence X x) D.volume →
        Integrable (fun x => D.normalPairing X x) D.boundaryMeasure →
        ∫ x, D.divergence X x ∂D.volume = ∫ x, D.normalPairing X x ∂D.boundaryMeasure
```

i.e. `∫_M div X dvol = ∫_{∂M} ⟨X, n⟩ dσ`.

Named blockers (each with a kernel-checked `..._ne_nil`):

| blocker | content |
| --- | --- |
| `B-D7-STOKES` | Stokes' theorem for differential forms on manifolds / integration of top forms; mathlib has only the Euclidean box theorem |
| `B-D7-RIEMANNIAN-VOLUME-MEASURE` | no global Riemannian volume form, no density `√(det g)`, no partition-of-unity gluing |
| `B-D7-MANIFOLD-BOUNDARY` | `ModelWithCorners.boundary` is only a set; no boundary manifold, induced orientation/measure, collar, or outward normal |
| `B-D7-MANIFOLD-DIVERGENCE` | no covariant derivative/trace and no metric normal pairing |

`MissingMathlibDependencies` (7 entries, `_length = 7`): Stokes on manifolds; Riemannian volume
measure; boundary manifold; metric divergence; metric normal pairing; chart/partition-of-unity
transfer of `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`; integration of
densities on manifolds. `PresentMathlibDependencies` (5 entries) lists the reused pieces
(Euclidean box theorem, boundary set API, `mfderiv`/`ContMDiff`/`TangentSpace`/`RiemannianBundle`,
Haar measure on vector spaces/groups, Bochner integral).

---

## 8. Compile gate and `#print axioms` audit

### 8.1 Authored files (`lake env lean` from the worktree root)

| file | exit |
| --- | --- |
| `release/Poincare/D7/Divergence.lean` | 0 |
| `release/Poincare/D7/Divergence/Basic.lean` | 0 |
| `release/Poincare/D7/Divergence/Graph.lean` | 0 |
| `release/Poincare/D7/Divergence/Slab.lean` | 0 |
| `release/Poincare/D7/Divergence/Example.lean` | 0 |
| `release/Poincare/D7/Divergence/Blocked.lean` | 0 |
| `release/Poincare/D7/Divergence/Probe.lean` | 0 |
| `release/Poincare/D7/Divergence/Audit.lean` | 0 |

(`longrun/d7-div-logs/exit_codes.txt`; per-file output in
`longrun/d7-div-logs/lake_env_lean.log`.)

### 8.2 Harness-gate replication

Every `.lean` file in the worktree (98 files: `negcontrol/`, the pre-existing `release/` modules,
and the 8 new divergence files) was compiled with `lake env lean` from the worktree root:
**98/98 exit 0**, no failures (`longrun/d7-div-logs/gate_exit_codes.txt`; full output in
`longrun/d7-div-logs/gate.log`). The eight new files are the last eight entries of that list.

| scope | files | exit 0 | nonzero |
| --- | --- | --- | --- |
| whole worktree | 98 | 98 | 0 |
| new D7 divergence layer | 8 | 8 | 0 |

### 8.3 `#print axioms`

`release/Poincare/D7/Divergence/Audit.lean` runs 102 `#print axioms` commands, one per principal
declaration of the layer. Parsed cones (`longrun/d7-div-logs/axiom-summary.json`):

| cone | count |
| --- | --- |
| `{propext, Classical.choice, Quot.sound}` | 90 |
| `{propext}` | 4 |
| no axioms | 8 |

No `sorryAx`, no `native_decide`, no `proof_wanted`, and no other unapproved axiom appears.

---

## 9. Forbidden-token scan

A comment/string-aware scanner (nested `/- -/`, `--`, `"..."` stripped) searched for `sorry`,
`admit`, `native_decide`, `unsafe`, `proof_wanted`, and `axiom` (excluding `#print axioms`):

| scope | files | hard hits |
| --- | --- | --- |
| `release/Poincare/D7/Divergence/*.lean` + umbrella | 8 | **0** |
| `release/Poincare/D7/**/*.lean` (D7-wide) | 34 | **0** |

Reports: `longrun/d7-div-logs/forbidden-scan-div.json`,
`longrun/d7-div-logs/forbidden-scan-d7-wide.json`.

---

## 10. Reproduction

```bash
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-divergence-ibp
# 1. build the new modules (produces oleans used by the per-file gate)
(cd release && lake build Poincare.D7.Divergence Poincare.D7.Divergence.Audit)
# 2. per-file compile gate
for f in release/Poincare/D7/Divergence.lean release/Poincare/D7/Divergence/*.lean; do
  lake env lean "$f" || echo "FAIL $f"
done
# 3. axiom audit (the #print axioms output is the audit)
lake env lean release/Poincare/D7/Divergence/Audit.lean
# 4. source integrity
diff -rq ../D7-orientability-volume-form . -x .lake -x Divergence -x Divergence.lean \
  -x d7-div-logs -x 'D7-divergence-ibp.md' -x 'D7-divergence-ibp.json'
```

Machine-readable card: `longrun/results/D7-divergence-ibp.json`.

TASK_DONE — longrun/results/D7-divergence-ibp.md
