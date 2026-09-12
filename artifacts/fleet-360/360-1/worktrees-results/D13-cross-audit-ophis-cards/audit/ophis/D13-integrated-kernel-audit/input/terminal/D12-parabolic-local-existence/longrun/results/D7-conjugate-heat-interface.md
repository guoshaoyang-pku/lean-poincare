# D7-conjugate-heat-interface — result card

**Task id:** `D7-conjugate-heat-interface`
**Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-conjugate-heat-interface`
**Generated (UTC):** 2026-09-09T18:03:46Z
**Verdict:** `TASK_DONE` — kernel-checked conjugate-heat layer: `ConjugateHeatData` (the backward heat
operator `□* = -∂_t - Δ + R` over a stated metric-flow interface), formal adjointness of the heat
and conjugate-heat operators at the algebraic level under an explicit integration-by-parts
certificate, a discrete conjugate-heat slab monotonicity toy, and the conjugate heat kernel
existence theorem as a state-only `Prop` with named blockers and the exact missing mathlib
dependencies. No `sorry` / `axiom` / `unsafe` / `native_decide` / `proof_wanted`.

---

## 0. Bottom line

| item | result |
| --- | --- |
| new files (only under `release/Poincare/D7/ConjugateHeat/`) | **9 Lean files, 1987 lines, 127 audited declarations** |
| compiled with `lake env lean` from the worktree root | **9/9 authored files exit 0** (`longrun/d7-conj-logs/exit_codes.txt`) |
| harness-gate replication (every `.lean` in the worktree, `lake env lean` from the root) | **107/107 exit 0**, no failures (`longrun/d7-conj-logs/gate_exit_codes.txt`) |
| `#print axioms` audit | **127 principal declarations**: cone `{propext, Classical.choice, Quot.sound}` (115), no axioms (10), `{propext, Quot.sound}` (1), `{propext}` (1); **no `sorryAx`, no nonstandard cone** |
| forbidden-token scan (comment/string-aware) | **0 hard** in the 9 authored files; D7-wide scan (43 files) also **0 hard** |
| copied scaffold files modified | **0** (`diff -rq` against `../D7-divergence-ibp`, `.lake` and the new files/logs excluded: **empty**) |
| non-vacuity | concrete two-vertex cycle: `Δu = (-3,2)`, `Δv = (3,-2)`, `H j = (5,2)`, `□*k = (1,10)`, `⟨Hj,k⟩ = 30`, `⟨j,□*k⟩ = 2`, volume variation `4`, boundary form `-24`, `30 - 2 = 28 = 4 - (-24)`; slab energies `5 → 125 → 3125` |
| blocked items | `ConjugateHeatKernelExistenceStatement` with 6 named blockers and 7 exact missing mathlib dependencies |

**Not claimed:** no proof of existence/uniqueness of the conjugate heat kernel, no heat kernel on a
Riemannian manifold, no distribution theory or Dirac delta, no Gaussian bounds, no Ricci flow
spacetime, no parabolic maximum principle. The kernel existence statement is a state-only `Prop`
(Section 8).

---

## 1. Scaffold, environment, and source integrity

The worktree was scaffolded from `../D7-divergence-ibp/` as instructed.

| command | exit | note |
| --- | --- | --- |
| `cp -al ../D7-divergence-ibp/. .` | **1** | every entry fails with `Invalid cross-device link` (hard links are rejected on this filesystem); this matches the D7-divergence-ibp card |
| `cp -a ../D7-divergence-ibp/. .` | **0** | full copy (387 MB, including the prebuilt `.lake`); scaffold intact |
| `diff -rq ../D7-divergence-ibp . -x .lake -x ConjugateHeat -x d7-conj-logs -x 'D7-conjugate-heat-interface.md' -x 'D7-conjugate-heat-interface.json'` | **0** | no output: **no shared file differs**; the only additions are `release/Poincare/D7/ConjugateHeat/` and this card |

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
| `release/Poincare/D7/ConjugateHeat/All.lean` | 35 | umbrella module |
| `release/Poincare/D7/ConjugateHeat/Laplacian.lean` | 433 | finite weighted-graph Laplace–Beltrami operator, mass-weighted pairing, Green / IBP identities |
| `release/Poincare/D7/ConjugateHeat/Basic.lean` | 321 | `MetricFlowInterface`, `Jet`, `ConjugateHeatData`, formal adjointness, `ConjugateHeatIBPCertificate` |
| `release/Poincare/D7/ConjugateHeat/Instance.lean` | 155 | concrete finite weighted-graph instance of the interface and of the conjugate-heat data |
| `release/Poincare/D7/ConjugateHeat/Slab.lean` | 145 | discrete conjugate-heat step and slab monotonicity toy |
| `release/Poincare/D7/ConjugateHeat/Example.lean` | 268 | concrete numeric non-vacuity witnesses |
| `release/Poincare/D7/ConjugateHeat/Blocked.lean` | 240 | state-only conjugate heat kernel existence `Prop`, blockers, missing dependencies |
| `release/Poincare/D7/ConjugateHeat/Probe.lean` | 116 | compilable mathlib/D7 API probe (`#check` / `#check_failure`) |
| `release/Poincare/D7/ConjugateHeat/Audit.lean` | 274 | 127 `#print axioms` commands |

---

## 2. `ConjugateHeatData`: backward heat operator over a stated metric-flow interface (task item 1)

### 2.1 The metric-flow interface

`release/Poincare/D7/ConjugateHeat/Basic.lean`:

```lean
structure MetricFlowInterface (F : Type*) [AddCommGroup F] [Module ℝ F] where
  pairing : F →ₗ[ℝ] F →ₗ[ℝ] ℝ            -- the L² pairing ⟨u, v⟩ = ∫ u v dV_t
  laplacian : F →ₗ[ℝ] F                    -- the Laplace–Beltrami operator Δ
  scalarMul : F →ₗ[ℝ] F                    -- multiplication by the scalar curvature R
  boundaryForm : F → F → ℝ                 -- the Green boundary form of Δ
  volumeVariation : Jet F → Jet F → ℝ      -- ∂_t⟨u, v⟩
  volumeVariation_apply : ∀ j k : Jet F,
    volumeVariation j k = pairing j.2 k.1 + pairing j.1 k.2 - pairing (scalarMul j.1) k.1
  pairing_symm : ∀ u v, pairing u v = pairing v u
  laplacian_ibp : ∀ u v, pairing (laplacian u) v - pairing u (laplacian v) = boundaryForm u v
  scalarMul_selfAdjoint : ∀ u v, pairing (scalarMul u) v = pairing u (scalarMul v)
  boundaryForm_antisymm : ∀ u v, boundaryForm v u = -boundaryForm u v
```

The field `volumeVariation_apply` is the **stated metric-flow relation**: under `∂_t g = -2 Ric`
the volume density satisfies `∂_t dV = -R dV`, hence
`∂_t⟨u, v⟩ = ⟨∂_t u, v⟩ + ⟨u, ∂_t v⟩ - ⟨R u, v⟩`. The field `laplacian_ibp` is the explicit
integration-by-parts certificate for `Δ`, and `boundaryForm_antisymm` records that the Green
boundary form is antisymmetric.

### 2.2 The conjugate-heat data

```lean
structure ConjugateHeatData (F : Type*) [AddCommGroup F] [Module ℝ F]
    extends MetricFlowInterface F where
  forwardHeat : Jet F →ₗ[ℝ] F               -- H = ∂_t - Δ
  backwardHeat : Jet F →ₗ[ℝ] F              -- □* = -∂_t - Δ + R
  forwardHeat_apply : ∀ j, forwardHeat j = j.2 - laplacian j.1
  backwardHeat_apply : ∀ j, backwardHeat j = -j.2 - laplacian j.1 + scalarMul j.1
```

A **jet** `Jet F = F × F` is the value/time-derivative pair `(u, ∂_t u)`. The two pinning
equations are fields, so every instance must certify that its operators are the stated ones;
`ConjugateHeatData.ofInterface` builds the canonical data from any interface.

Structural lemmas: `ConjugateHeatData.isConjugateHeatJet_iff` (the conjugate-heat equation is
`∂_t u = -Δu + R u`), `isHeatJet_iff`, and the non-vacuity lemmas
`isConjugateHeatJet_self` / `isHeatJet_self` (every value extends to a solution).

---

## 3. Green identities and the explicit IBP certificate

`release/Poincare/D7/ConjugateHeat/Laplacian.lean` develops the concrete finite weighted-graph
model on which the interface is instantiated. For a finite oriented graph `D` with conductances
`w`, mass density `m`, and region `S`:

* `pairingOn m S u v = ∑_{x ∈ S} m x * u x * v x`;
* `laplaceBeltrami D w m u x = (m x)⁻¹ * (∑_e edge contribution of e at x)`, where an edge `e`
  contributes `w e * (u (tgt e) - u x)` at its tail and `w e * (u (src e) - u x)` at its head;
* `dirichletForm D w S u v` sums `w e * (u (tgt e) - u (src e)) * (v (tgt e) - v (src e))` over the
  edges interior to `S`;
* `boundaryPair D w S u v` collects the explicit contributions of the edges crossing `∂S`;
* `boundaryForm D w S u v = boundaryPair u v - boundaryPair v u`.

The two kernel-checked Green identities are

```lean
theorem green_first (D) (w) (m) (hm : ∀ x, m x ≠ 0) (S) (u v) :
    pairingOn m S (laplaceBeltrami D w m u) v
      = -dirichletForm D w S u v + boundaryPair D w S u v

theorem green_second (D) (w) (m) (hm : ∀ x, m x ≠ 0) (S) (u v) :
    pairingOn m S (laplaceBeltrami D w m u) v
      - pairingOn m S (laplaceBeltrami D w m v) u
      = boundaryForm D w S u v
```

with the per-edge evaluation `sum_edgeLap_mul`, the closed-region vanishing
`boundaryPair_eq_zero_of_closed`, `boundaryPair_univ`, the full-graph self-adjointness
`laplaceBeltrami_selfAdjoint_univ`, and the nonnegativity `dirichletForm_nonneg`.

---

## 4. Formal adjointness of the heat and conjugate-heat operators (task item 2a)

The main algebraic theorem is

```lean
theorem ConjugateHeatData.formal_adjoint (D : ConjugateHeatData F) (j k : Jet F) :
    D.pairing (D.forwardHeat j) k.1 - D.pairing j.1 (D.backwardHeat k)
      = D.volumeVariation j k - D.boundaryForm j.1 k.1
```

i.e. `⟨H j, k⟩ - ⟨j, □* k⟩ = ∂_t⟨j, k⟩ - boundaryForm j k`. The proof expands the two operators,
uses the pairing linearity, the metric-flow volume variation, the IBP certificate
`laplacian_ibp`, and the self-adjointness `scalarMul_selfAdjoint`; it is pure algebra over the
stated interface.

Corollaries:

* `formal_adjoint_of_boundaryForm_eq_zero` — on a closed region
  `⟨H j, k⟩ - ⟨j, □* k⟩ = ∂_t⟨j, k⟩`;
* `formal_adjoint_of_volumeVariation_eq_zero` — for a stationary metric
  `⟨H j, k⟩ - ⟨j, □* k⟩ = -boundaryForm j k`;
* `formal_adjoint_closed` — on a closed stationary region `⟨H j, k⟩ = ⟨j, □* k⟩`;
* `volumeVariation_eq_boundaryForm_of_heat_and_conjugate` — for a heat jet `j` and a
  conjugate-heat jet `k`, `∂_t⟨j, k⟩ = boundaryForm j k`, the algebraic content of the
  conservation of `∫ u v dV` for Perelman's conjugate heat equation.

**The explicit certificate** `ConjugateHeatIBPCertificate D j k` carries the heat pairing, the
conjugate-heat pairing, the volume variation, and the boundary form as fields, with the identity
`heatPairing - conjugatePairing = volumeVariation - boundaryForm` as a proof field.
`conjugateHeatIBPCertificate D j k` is the canonical instance, and
`heatPairing_sub_conjugatePairing` / `heatPairing_eq_conjugatePairing` record the vanishing-boundary
and closed-stationary cases.

---

## 5. The concrete finite weighted-graph instance

`release/Poincare/D7/ConjugateHeat/Instance.lean` instantiates the interface and the data on the
function space `V → ℝ`:

* `pairingOnLM m S` — the region pairing as a bilinear form (via the restricted density `massOn`);
* `metricFlowInterface D w m R hm S` — all ten interface fields are discharged:
  * `volumeVariation_apply` is the computation `∂_t m = -R m` gives
    `∑ (-R m) u v + ∑ m (∂_t u) v + ∑ m u (∂_t v) = ⟨∂_t u, v⟩ + ⟨u, ∂_t v⟩ - ⟨R u, v⟩`;
  * `laplacian_ibp` is exactly `green_second`;
  * `pairing_symm`, `scalarMul_selfAdjoint`, `boundaryForm_antisymm` are the corresponding
    finite-sum computations;
* `conjugateHeatData D w m R hm S` — the concrete `ConjugateHeatData (V → ℝ)`;
* `conjugateHeatData_forwardHeat_apply`, `conjugateHeatData_backwardHeat_apply`,
  `conjugateHeatData_formal_adjoint` — the concrete operator equations and the instantiated formal
  adjointness.

---

## 6. Discrete conjugate-heat slab monotonicity toy (task item 2b)

`release/Poincare/D7/ConjugateHeat/Slab.lean`. The discrete conjugate-heat step with
scalar-curvature term is the explicit Euler step for `∂_t u = -Δu + R u`:

```lean
conjugateHeatStep D w m R u = u + R • u - Δ u
```

and the mass-weighted energy of a slice is `energy m u = ∑_x m x * (u x)^2`.

```lean
theorem energy_le_energy_conjugateHeatStep (D) (w) (m) (R)
    (hm : ∀ x, 0 < m x) (hw : ∀ e, 0 ≤ w e) (hR : ∀ x, 0 ≤ R x) (u) :
    energy m u ≤ energy m (conjugateHeatStep D w m R u)

theorem energy_mono_slab {n : ℕ} (D) (w) (m) (R) (hm) (hw) (hR)
    (u : Fin (n + 1) → V → ℝ)
    (hstep : ∀ k : Fin n, u k.succ = conjugateHeatStep D w m R (u k.castSucc)) :
    energy m (u 0) ≤ energy m (u (Fin.last n))
```

The one-step proof is the exact algebraic decomposition

`energy m (u + X) - energy m u = 2 * ∑_x m x * u x * X x + ∑_x m x * (X x)^2`,

with `X = R • u - Δ u`. The cross term equals
`∑_x m x * R x * (u x)^2 + dirichletForm D w univ u u ≥ 0` by the sign hypotheses and Green's
first identity, and the square term is nonnegative because the mass is positive. The slab statement
telescopes the one-step inequality with `Poincare.D7.Divergence.sum_telescope`.

---

## 7. Concrete non-vacuity witnesses

`release/Poincare/D7/ConjugateHeat/Example.lean`, all kernel-checked by computation on the
two-vertex cycle `0 → 1 → 0` with conductances `(1, 2)`, mass `(2, 3)`, scalar curvature `(1, 2)`,
region `S = {0}`, fields `u = (1, -1)`, `v = (3, 5)`, jets `∂_t u = (2, 4)`, `∂_t v = (-1, 2)`:

| quantity | value |
| --- | --- |
| `Δu` at `0`, `1` | `-3`, `2` |
| `Δv` at `0`, `1` | `3`, `-2` |
| `H j = ∂_t u - Δu` | `(5, 2)` |
| `□*k = -∂_t v - Δv + R v` | `(1, 10)` |
| `⟨H j, k⟩` over `{0}` | `30` |
| `⟨j, □*k⟩` over `{0}` | `2` |
| volume variation `∂_t⟨j, k⟩` | `4` |
| Green boundary form | `-24` |
| formal adjointness `30 - 2 = 4 - (-24)` | `28 = 28` |
| slab energies (two conjugate-heat steps from `u`) | `5 → 125 → 3125`, monotonicity `5 ≤ 3125` |

The witnesses are `cycle_laplaceBeltrami_u_zero/one`, `cycle_laplaceBeltrami_v_zero/one`,
`cycle_boundaryPair_uv/vu`, `cycle_boundaryForm_value`, `cycle_green_first_value`,
`cycle_green_second_value`, `cycle_pairing_forwardHeat`, `cycle_pairing_backwardHeat`,
`cycle_volumeVariation_value`, `cycle_formal_adjoint_value`, `cycle_certificate_value`,
`cycle_conjugateHeatJet`, `cycle_heatJet`, `cycleSlab_step`, `cycleSlab_energy_zero`,
`cycleSlab_energy_last`, `cycleSlab_energy_mono_value`.

---

## 8. Conjugate heat kernel existence: state-only `Prop` (task item 3)

`release/Poincare/D7/ConjugateHeat/Blocked.lean` records the theorem as an **explicit unproved
`Prop`** with named blockers; there is no `sorry`/`axiom`/`proof_wanted`.

The schematic analytic datum collects the four blocked objects:

```lean
structure ConjugateHeatSpacetime (M : Type*) [TopologicalSpace M] [MeasurableSpace M] where
  volume : Measure M                                   -- Riemannian volume of the slice
  laplacian : (M → ℝ) →ₗ[ℝ] (M → ℝ)                     -- Laplace–Beltrami operator
  scalarMul : (M → ℝ) →ₗ[ℝ] (M → ℝ)                     -- multiplication by R
  backwardTimeDerivative : (M → ℝ) →ₗ[ℝ] (M → ℝ)        -- ∂_t
```

with `ConjugateHeatSpacetime.conjugateHeat u = -∂_t u - Δu + R u`. The geometric requirements are
the predicate `IsRiemannianConjugateHeatSpacetime` (positive volume on nonempty open sets, finite
volume on compacts), and the kernel properties are `IsConjugateHeatKernel S t₀ K`: positivity, the
conjugate heat equation `□*K = 0`, normalization `∫ K dV = 1`, and convergence to the Dirac delta
at the terminal time `t₀`. The blocked statement is

```lean
def ConjugateHeatKernelExistenceStatement : Prop :=
  ∀ (M : Type*) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (S : ConjugateHeatSpacetime M), IsRiemannianConjugateHeatSpacetime S →
      ∀ y₀ : M, ∀ t₀ : ℝ, ∃ K : M → M → ℝ → ℝ, IsConjugateHeatKernel S t₀ K
```

Consistency checks (no proof of the statement itself): `ConjugateHeatSpacetime.not_isRiemannian_zero`
(the zero datum is not Riemannian on a space with a nonempty open set),
`ConjugateHeatSpacetime.isRiemannian_zero_of_isEmpty` (it is Riemannian vacuously on an empty
manifold), and `not_isConjugateHeatKernel_zero` (the zero kernel is not a kernel on a nonempty
manifold).

Named blockers (each with a kernel-checked list entry; `blockers_length = 6`):

| blocker | content |
| --- | --- |
| `B-D7-CONJUGATE-HEAT-KERNEL-EXISTENCE` | no existence/uniqueness theory for the fundamental solution of a parabolic PDE; no parametrix, no Duhamel principle |
| `B-D7-HEAT-KERNEL-MANIFOLD` | no heat kernel on Riemannian manifolds; no spectral theorem for the Laplace–Beltrami operator on a compact manifold |
| `B-D7-DIRAC-DELTA` | no distribution theory or Dirac delta; the terminal condition cannot be stated as a distributional limit |
| `B-D7-GAUSSIAN-BOUNDS` | no Gaussian bounds, no Li–Yau differential Harnack inequality |
| `B-D7-RICCI-FLOW-SPACETIME` | no Ricci flow evolution equation, no spacetime manifold; the metric-flow interface is axiomatic |
| `B-D7-PARABOLIC-MAXIMUM-PRINCIPLE` | no parabolic maximum principle, no backward uniqueness, no positivity-preserving semigroup theory |

`MissingMathlibDependencies` (7 entries, `_length = 7`): existence/uniqueness of the fundamental
solution; heat kernel on a compact Riemannian manifold; Dirac delta and distributional convergence;
Gaussian bounds; Ricci flow spacetime; parabolic maximum principle; Riemannian volume measure.
`PresentMathlibDependencies` (4 entries) lists the reused pieces (measure and Bochner integral,
`Tendsto`/filters, `LinearMap`, the finite-graph Laplacian and Green identities).

---

## 9. Compile gate and `#print axioms` audit

### 9.1 Authored files (`lake env lean` from the worktree root)

| file | exit |
| --- | --- |
| `release/Poincare/D7/ConjugateHeat/Laplacian.lean` | 0 |
| `release/Poincare/D7/ConjugateHeat/Basic.lean` | 0 |
| `release/Poincare/D7/ConjugateHeat/Instance.lean` | 0 |
| `release/Poincare/D7/ConjugateHeat/Slab.lean` | 0 |
| `release/Poincare/D7/ConjugateHeat/Example.lean` | 0 |
| `release/Poincare/D7/ConjugateHeat/Blocked.lean` | 0 |
| `release/Poincare/D7/ConjugateHeat/All.lean` | 0 |
| `release/Poincare/D7/ConjugateHeat/Probe.lean` | 0 |
| `release/Poincare/D7/ConjugateHeat/Audit.lean` | 0 |

(`longrun/d7-conj-logs/exit_codes.txt`; per-file output in
`longrun/d7-conj-logs/release_Poincare_D7_ConjugateHeat_*.log`.) The modules were built first with
`cd release && lake build Poincare.D7.ConjugateHeat.All Poincare.D7.ConjugateHeat.Probe
Poincare.D7.ConjugateHeat.Audit` (exit 0, 3438 jobs, no warnings), which produces the oleans the
per-file gate resolves.

### 9.2 Harness-gate replication

Every `.lean` file in the worktree (107 files: `negcontrol/`, the pre-existing `release/` modules,
and the 9 new conjugate-heat files) was compiled with `lake env lean` from the worktree root:
**107/107 exit 0**, no failures (`longrun/d7-conj-logs/gate_exit_codes.txt`; full output in
`longrun/d7-conj-logs/gate.log`).

### 9.3 `#print axioms`

`release/Poincare/D7/ConjugateHeat/Audit.lean` runs 127 `#print axioms` commands, one per principal
declaration of the layer. Parsed cones (`longrun/d7-conj-logs/axiom-summary.json`):

| cone | count |
| --- | --- |
| `{propext, Classical.choice, Quot.sound}` | 115 |
| no axioms | 10 |
| `{propext, Quot.sound}` | 1 |
| `{propext}` | 1 |

No `sorryAx`, no `native_decide`, no `proof_wanted`, and no other unapproved axiom appears.

---

## 10. Forbidden-token scan

A comment/string-aware scanner (nested `/- -/`, `--`, `"..."` stripped) searched for `sorry`,
`admit`, `native_decide`, `unsafe`, `proof_wanted`, and `axiom` (excluding `#print axioms`):

| scope | files | hard hits |
| --- | --- | --- |
| `release/Poincare/D7/ConjugateHeat/*.lean` | 9 | **0** |
| `release/Poincare/D7/**/*.lean` (D7-wide) | 43 | **0** |

Report: `longrun/d7-conj-logs/forbidden-scan.json`.

---

## 11. Reproduction

```bash
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-conjugate-heat-interface
# 1. build the new modules (produces oleans used by the per-file gate)
(cd release && lake build Poincare.D7.ConjugateHeat.All Poincare.D7.ConjugateHeat.Probe \
  Poincare.D7.ConjugateHeat.Audit)
# 2. per-file compile gate
for f in release/Poincare/D7/ConjugateHeat/*.lean; do
  lake env lean "$f" || echo "FAIL $f"
done
# 3. axiom audit (the #print axioms output is the audit)
lake env lean release/Poincare/D7/ConjugateHeat/Audit.lean
# 4. source integrity
diff -rq ../D7-divergence-ibp . -x .lake -x ConjugateHeat -x d7-conj-logs \
  -x 'D7-conjugate-heat-interface.md' -x 'D7-conjugate-heat-interface.json'
```

Machine-readable card: `longrun/results/D7-conjugate-heat-interface.json`.

TASK_DONE — longrun/results/D7-conjugate-heat-interface.md
