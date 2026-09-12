# D7-heat-kernel-existence — result card

**Task id:** `D7-heat-kernel-existence`
**Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-heat-kernel-existence`
**Generated (UTC):** 2026-09-09T18:28:22Z
**Verdict:** `TASK_DONE` — kernel-checked heat-kernel interface layer: `HeatKernelData` with Gaussian
upper/lower bounds and the semigroup (Chapman–Kolmogorov) properties as explicit fields; uniqueness
of a heat kernel satisfying the stated bounds on a finite grid; monotonicity of the discrete heat
content (total heat) and of the `L²` energy along the finite-grid heat flow; and the heat-kernel
existence theorem on closed manifolds as a state-only `Prop` with named blockers and the exact
missing mathlib dependencies (parabolic regularity, Sobolev embedding, spectral theorem, Dirac
delta, Gaussian bounds, maximum principle). No `sorry` / `axiom` / `unsafe` / `native_decide` /
`proof_wanted`.

---

## 0. Bottom line

| item | result |
| --- | --- |
| new files (only under `release/Poincare/D7/HeatKernel/`) | **9 Lean files, 1551 lines, 102 audited declarations** |
| compiled with `lake env lean` from the worktree root | **9/9 authored files exit 0** (`longrun/d7hk-logs/exit_codes.txt`) |
| harness-gate replication (every `.lean` in the worktree, `lake env lean` from the root) | **116/116 exit 0**, no failures (`longrun/d7hk-logs/gate_exit_codes.txt`) |
| `#print axioms` audit | **102 principal declarations**: cone `{propext, Classical.choice, Quot.sound}` (93), `{propext}` (1), no axioms (8); **no `sorryAx`, no nonstandard cone** |
| forbidden-token scan (comment/string-aware) | **0 hard** in the 9 authored files; D7-wide scan (52 files) also **0 hard** |
| copied scaffold files modified | **0** (`diff -rq` against `../D7-conjugate-heat-interface`, `.lake`, `HeatKernel`, logs and the new card excluded: **empty**) |
| non-vacuity | one-point `HeatKernelData` inhabitant; two-point grid kernel with bounds `1/4 ≤ K n x y ≤ 1` for `n ≥ 1`; heat content `4 → 2 → 1`, `L²` energy `10 → 2 → 1/2` |
| blocked items | `HeatKernelExistenceStatement` with 7 named blockers and 8 exact missing mathlib dependencies |

**Not claimed:** no proof of existence/uniqueness of the heat kernel on a Riemannian manifold, no
parametrix, no parabolic regularity, no Sobolev theory, no spectral theorem, no distribution theory,
no Gaussian bounds on manifolds, no parabolic maximum principle. The manifold existence statement is
a state-only `Prop` (Section 6). Uniqueness and monotonicity are proved **only** for the finite
(discrete) grid model.

---

## 1. Scaffold, environment, and source integrity

The worktree was scaffolded from `../D7-conjugate-heat-interface/` as instructed.

| command | exit | note |
| --- | --- | --- |
| `cp -al ../D7-conjugate-heat-interface/. .` | **1** | every entry fails with `Invalid cross-device link` (hard links are rejected on this filesystem); this matches the D7-conjugate-heat-interface card |
| `cp -a ../D7-conjugate-heat-interface/. .` | **0** | full copy (411 MB of `.lake` build artifacts included); scaffold intact |
| `diff -rq ../D7-conjugate-heat-interface . -x .lake -x HeatKernel -x d7hk-logs -x 'D7-heat-kernel-existence.md' -x 'D7-heat-kernel-existence.json'` | **0** | no output: **no shared file differs**; the only additions are `release/Poincare/D7/HeatKernel/` and this card |

Environment:

| key | value |
| --- | --- |
| Lean | `4.34.0-rc2` (commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`) |
| mathlib | `7974e751bece493b6ff508039423ca9fa2452fa8` |
| root package | `D7RiemannCurvatureTensorRoot` (re-exposes `release/.lake`, so `lake env lean` works from the worktree root) |
| release package | `PoincareRelease` (`release/lakefile.toml`, glob `Poincare.+`) |

New files:

| file | lines | decls | role |
| --- | --- | --- | --- |
| `release/Poincare/D7/HeatKernel/Basic.lean` | 146 | 6 | `HeatKernelData`: Gaussian bounds, semigroup, normalization, symmetry, heat equation, initial condition; basic corollaries |
| `release/Poincare/D7/HeatKernel/Grid.lean` | 230 | 18 | discrete heat step, finite-grid heat kernels, `K n = step ^ n`, **uniqueness under the stated bounds**, bounded-solution uniqueness, grid flow |
| `release/Poincare/D7/HeatKernel/Content.lean` | 159 | 9 | heat content and `L²` energy, weighted Cauchy–Schwarz, **monotonicity** one-step and in time, kernel-flow instantiations |
| `release/Poincare/D7/HeatKernel/Instance.lean` | 121 | 8 | concrete `HeatKernelData PUnit` inhabitant (non-vacuity of the interface) |
| `release/Poincare/D7/HeatKernel/Example.lean` | 232 | 41 | two-point grid kernel with bounds, concrete uniqueness, numeric heat-content/energy witnesses |
| `release/Poincare/D7/HeatKernel/Blocked.lean` | 263 | 20 | state-only `HeatKernelExistenceStatement`, closed-manifold predicate, heat-kernel predicate, 7 blockers, missing dependencies |
| `release/Poincare/D7/HeatKernel/All.lean` | 38 | 0 | umbrella module |
| `release/Poincare/D7/HeatKernel/Probe.lean` | 132 | 0 | compilable mathlib/D7 API probe (`#check` / `#check_failure`) |
| `release/Poincare/D7/HeatKernel/Audit.lean` | 230 | 0 | 102 `#print axioms` commands |

---

## 2. `HeatKernelData`: the heat-kernel interface (task item 1)

`release/Poincare/D7/HeatKernel/Basic.lean` defines the interface. Every analytic property is an
**explicit field**:

```lean
structure HeatKernelData (X : Type*) [TopologicalSpace X] [MeasurableSpace X] where
  volume : Measure X
  dist : X → X → ℝ
  dim : ℝ
  C_up : ℝ
  c_up : ℝ
  C_lo : ℝ
  c_lo : ℝ
  kernel : X → X → ℝ → ℝ
  laplacian : (X → ℝ) →ₗ[ℝ] (X → ℝ)
  dist_self : ∀ x, dist x x = 0
  dist_nonneg : ∀ x y, 0 ≤ dist x y
  dist_symm : ∀ x y, dist x y = dist y x
  c_up_pos : 0 < c_up
  c_lo_pos : 0 < c_lo
  C_up_nonneg : 0 ≤ C_up
  C_lo_nonneg : 0 ≤ C_lo
  kernel_nonneg : ∀ x y t, 0 ≤ kernel x y t
  gaussianUpperBound : ∀ x y t, 0 < t →
    kernel x y t ≤ C_up * t ^ (-(dim / 2)) * Real.exp (-(dist x y) ^ 2 / (c_up * t))
  gaussianLowerBound : ∀ x y t, 0 < t → dist x y ≤ 1 →
    C_lo * t ^ (-(dim / 2)) * Real.exp (-(dist x y) ^ 2 / (c_lo * t)) ≤ kernel x y t
  symmetry : ∀ x y t, kernel x y t = kernel y x t
  semigroup : ∀ x y s t, 0 < s → 0 < t →
    kernel x y (s + t) = ∫ z, kernel x z s * kernel z y t ∂volume
  normalization : ∀ x t, 0 < t → ∫ y, kernel x y t ∂volume = 1
  initialCondition : ∀ (x : X) (f : X → ℝ), Continuous f →
    Tendsto (fun t : ℝ => ∫ y, kernel x y t * f y ∂volume) (𝓝[>] (0 : ℝ)) (𝓝 (f x))
  heatEquation : ∀ x y t, 0 < t →
    HasDerivAt (fun s : ℝ => kernel x y s) (laplacian (fun z => kernel z y t) x) t
```

The **semigroup properties** required by the task are the fields `semigroup` (Chapman–Kolmogorov),
`normalization` (mass preservation `∫ K = 1`), `symmetry` (`K x y t = K y x t`), `initialCondition`
(convergence to the Dirac delta against continuous test functions), and `heatEquation`
(`∂_t K = Δ K`). The **Gaussian upper and lower bounds** are the fields `gaussianUpperBound` and
`gaussianLowerBound`, parameterised by `dim`, `C_up, c_up, C_lo, c_lo` and the distance `dist`.

Kernel-checked corollaries:

| theorem | content |
| --- | --- |
| `HeatKernelData.kernel_pos_of_lowerBound` | `0 < C_lo` and `dist x y ≤ 1` force `0 < K x y t` for `t > 0` |
| `HeatKernelData.upperBound_self` | on the diagonal, `K x x t ≤ C_up * t ^ (-(dim / 2))` |
| `HeatKernelData.semigroup_symm` | `K x y (s + t) = ∫ z, K x z s * K y z t ∂volume` (symmetry in the second factor) |
| `HeatKernelData.normalization_symm` | `∫ y, K y x t ∂volume = 1` |
| `HeatKernelData.gaussian_factor_nonneg` | the Gaussian factor is nonnegative for `t > 0` |

`Instance.lean` proves the interface is **inhabited**: `punitHeatKernelData : HeatKernelData PUnit`
with the Dirac measure at the unique point, zero distance, dimension `0`, all four constants `1`,
and the constant kernel `1`. All fields are discharged (`1 ≤ 1` for both Gaussian bounds,
`1 = ∫ z, 1 * 1 ∂δ`, `∫ y, 1 ∂δ = 1`, constant-function derivative, `tendsto_const_nhds`), together
with `punitHeatKernelData_pos`.

---

## 3. Finite-grid heat kernels and uniqueness (task item 2a)

`release/Poincare/D7/HeatKernel/Grid.lean`. The discrete heat step is the explicit sum

```lean
def heatStep (P : Matrix X X ℝ) (u : X → ℝ) : X → ℝ := fun x => ∑ y, P x y * u y
```

with `heatStep_one` (`1 *ᵥ u = u`) and `heatStep_mul` (`heatStep (P * Q) u = heatStep P (heatStep Q u)`).

A **finite-grid heat kernel satisfying the stated bounds** is the structure

```lean
structure FiniteGridHeatKernel (step : Matrix X X ℝ) (d : X → X → ℝ)
    (dim C_up c_up C_lo c_lo : ℝ) where
  K : ℕ → Matrix X X ℝ
  initial : K 0 = 1
  generator : K 1 = step
  semigroup : ∀ m n : ℕ, K (m + n) = K m * K n
  upperBound : ∀ n : ℕ, 0 < n → ∀ x y : X,
    K n x y ≤ C_up * (n : ℝ) ^ (-(dim / 2)) * Real.exp (-(d x y) ^ 2 / (c_up * n))
  lowerBound : ∀ n : ℕ, 0 < n → ∀ x y : X, d x y ≤ 1 →
    C_lo * (n : ℝ) ^ (-(dim / 2)) * Real.exp (-(d x y) ^ 2 / (c_lo * n)) ≤ K n x y
```

The two main results are

```lean
theorem FiniteGridHeatKernel.eq_pow (K : FiniteGridHeatKernel step d dim C_up c_up C_lo c_lo) :
    K.K = fun n => step ^ n

theorem FiniteGridHeatKernel.unique (K₁ K₂ : FiniteGridHeatKernel step d dim C_up c_up C_lo c_lo) :
    K₁.K = K₂.K
```

i.e. **uniqueness of a heat kernel satisfying the stated bounds on a finite grid**: the generator
`K 1 = step`, the initial condition `K 0 = 1`, and the semigroup law determine the kernel uniquely,
and the bounds are part of the datum. The proof is the induction
`K (n+1) = K n * K 1 = step^n * step = step^(n+1)`. `apply_unique` records `K.K n = step ^ n`, and
`gridKernel` is the canonical inhabitant `step ^ n` whose Gaussian bounds are supplied as explicit
hypotheses (so the structure is inhabited exactly when the bounds can be certified).

The same uniqueness is also available in **hypothesis form**, with the bounds explicit in the
statement rather than hidden in the structure:

```lean
def IsFiniteGridHeatKernel (step : Matrix X X ℝ) (d : X → X → ℝ)
    (dim C_up c_up C_lo c_lo : ℝ) (K : ℕ → Matrix X X ℝ) : Prop :=
  K 0 = 1 ∧ K 1 = step ∧ (∀ m n : ℕ, K (m + n) = K m * K n) ∧
  (∀ n, 0 < n → ∀ x y, K n x y ≤ C_up * n ^ (-(dim / 2)) * exp (-(d x y)^2 / (c_up * n))) ∧
  (∀ n, 0 < n → ∀ x y, d x y ≤ 1 →
    C_lo * n ^ (-(dim / 2)) * exp (-(d x y)^2 / (c_lo * n)) ≤ K n x y)

theorem finiteGrid_heatKernel_unique (h₁ : IsFiniteGridHeatKernel step d dim C_up c_up C_lo c_lo K₁)
    (h₂ : IsFiniteGridHeatKernel step d dim C_up c_up C_lo c_lo K₂) : K₁ = K₂
```

Both proofs share the generator-uniqueness lemma `FiniteGridHeatKernel.eq_pow_of`.

Uniqueness of a **bounded solution of the discrete heat equation** with prescribed initial data and
prescribed bounds is `GridHeatSolution.unique`:

```lean
structure GridHeatSolution (step : Matrix X X ℝ) (f : X → ℝ) (B : ℕ → X → ℝ) where
  u : ℕ → X → ℝ
  initial : u 0 = f
  step_eq : ∀ n : ℕ, u (n + 1) = heatStep step (u n)
  bounded : ∀ n x, |u n x| ≤ B n x

theorem GridHeatSolution.unique (u v : GridHeatSolution step f B) : u.u = v.u
```

Finally `gridFlow K f n = heatStep (K.K n) f` is the temperature field generated by the kernel;
`gridFlow_succ` proves it solves the discrete heat equation with generator `step`, and
`gridFlow_nonneg` proves nonnegativity is preserved.

---

## 4. Monotonicity of the discrete heat content (task item 2b)

`release/Poincare/D7/HeatKernel/Content.lean`. The two monotone quantities are

```lean
def heatContent (μ u : X → ℝ) : ℝ := ∑ x, μ x * u x      -- total heat with density μ
def l2Energy (u : X → ℝ) : ℝ := ∑ x, (u x) ^ 2           -- L² energy
```

The one-step and time-monotonicity theorems are

```lean
theorem heatContent_heatStep_le (P) (μ u) (hP : ∀ x y, 0 ≤ P x y) (hμ : ∀ x, 0 ≤ μ x)
    (hu : ∀ x, 0 ≤ u x) (hcol : ∀ y, ∑ x, μ x * P x y ≤ μ y) :
    heatContent μ (heatStep P u) ≤ heatContent μ u

theorem heatContent_antitone (P) (μ) (u : ℕ → X → ℝ) ... (hstep : ∀ n, u (n + 1) = heatStep P (u n)) :
    Antitone (fun n => heatContent μ (u n))

theorem l2Energy_heatStep_le (P) (u) (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y ≤ 1) (hcol : ∀ y, ∑ x, P x y ≤ 1) :
    l2Energy (heatStep P u) ≤ l2Energy u

theorem l2Energy_antitone (P) (u : ℕ → X → ℝ) ... :
    Antitone (fun n => l2Energy (u n))
```

The heat-content proof expands `∑ x, μ x * ∑ y, P x y * u y`, swaps the sums, factors
`(∑ x, μ x * P x y) * u y`, and applies the column contraction `hcol` against `u y ≥ 0`. The
`L²` energy proof uses the **weighted Cauchy–Schwarz inequality**

```lean
theorem weighted_cauchy_schwarz (a b : X → ℝ) (ha : ∀ x, 0 ≤ a x) :
    (∑ x, a x * b x) ^ 2 ≤ (∑ x, a x) * (∑ x, a x * (b x) ^ 2)
```

(proved from mathlib's `Finset.sum_mul_sq_le_sq_mul_sq` with `a = (√a)²`), then sums
`(P u x)² ≤ (∑ y, P x y) * (∑ y, P x y * u y²) ≤ ∑ y, P x y * u y²` over `x` and swaps sums using
the column bound. The kernel-flow instantiations `heatContent_gridFlow_antitone` and
`l2Energy_gridFlow_antitone` connect these results to `gridFlow`.

---

## 5. Concrete instances and numeric witnesses

`release/Poincare/D7/HeatKernel/Example.lean`, on the two-point grid `Fin 2`.

**A finite-grid heat kernel with non-trivial bounds.** With the constant matrix
`twoPointStep = fun _ _ => 1/2` and the trivial distance `twoPointDist = 0`:

* `twoPointStep_mul_self` and `twoPointStep_pow_succ : twoPointStep ^ (n+1) = twoPointStep`;
* `twoPointStep_pow_upper` / `twoPointStep_pow_lower` certify
  `1/4 ≤ (twoPointStep ^ n) x y ≤ 1` for every `n > 0` and every pair `x y`;
* `twoPointGridKernel : FiniteGridHeatKernel twoPointStep twoPointDist 0 1 1 (1/4) 1` is a genuine
  inhabitant of the uniqueness theorem's structure;
* `twoPointGridKernel_K_two : twoPointGridKernel.K 2 = twoPointStep` is the concrete instance of
  `eq_pow`, and `twoPointGridKernel_unique` is the concrete instance of `unique`.

**A substochastic flow.** With `stepSub = fun _ _ => 1/4`, the initial field `u0 = (1, 3)` evolves to
`u1 = (1, 1)` and `u2 = (1/2, 1/2)` (`heatStep_stepSub_u0`, `heatStep_stepSub_u1`, `uFlow_one`,
`uFlow_two`). The numeric values are kernel-checked:

| quantity | time 0 | time 1 | time 2 |
| --- | --- | --- | --- |
| field | `(1, 3)` | `(1, 1)` | `(1/2, 1/2)` |
| heat content `∑ x, u x` | `4` | `2` | `1` |
| `L²` energy `∑ x, (u x)^2` | `10` | `2` | `1/2` |

The monotonicity theorems are instantiated both abstractly (`heatContent_uFlow_antitone`,
`l2Energy_uFlow_antitone` via `Antitone`) and numerically
(`heatContent_two_le_zero : 1 ≤ 4`, `l2Energy_two_le_zero : 1/2 ≤ 10`).

---

## 6. Heat-kernel existence on closed manifolds: state-only `Prop` (task item 3)

`release/Poincare/D7/HeatKernel/Blocked.lean` records the theorem as an **explicit unproved `Prop`**
with named blockers; there is no `sorry`/`axiom`/`proof_wanted`.

The schematic analytic datum collects the blocked objects:

```lean
structure HeatSpacetime (M : Type*) [TopologicalSpace M] [MeasurableSpace M] where
  volume : Measure M                                  -- Riemannian volume
  laplacian : (M → ℝ) →ₗ[ℝ] (M → ℝ)                    -- Laplace–Beltrami operator
  timeDerivative : (M → ℝ) →ₗ[ℝ] (M → ℝ)               -- ∂_t
  dist : M → M → ℝ                                     -- Riemannian distance
  dim : ℝ                                              -- dimension
```

with `HeatSpacetime.heatOperator u = ∂_t u - Δ u`. The geometric requirements are the predicate
`IsClosedRiemannianManifold` (compactness, positive volume on nonempty open sets, finite volume on
compacts, and the metric axioms for `dist`); the kernel properties are `IsHeatKernel S K`:
positivity for `t > 0`, the heat equation `∂_t K = Δ K`, normalization `∫ K dV = 1`, and the initial
Dirac condition against continuous test functions. The blocked statement is

```lean
def HeatKernelExistenceStatement : Prop :=
  ∀ (M : Type*) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (S : HeatSpacetime M), IsClosedRiemannianManifold S →
      ∀ y₀ : M, ∃ K : M → M → ℝ → ℝ, IsHeatKernel S K
```

Consistency checks (no proof of the statement itself): `HeatSpacetime.not_isClosedRiemannian_zero`
(the zero datum is not closed Riemannian on a space with a nonempty open set),
`HeatSpacetime.isClosedRiemannian_zero_of_isEmpty` (it is Riemannian vacuously on an empty
manifold), and `not_isHeatKernel_zero` (the zero kernel is not a heat kernel on a nonempty
manifold).

Named blockers (`blockers_length = 7`):

| blocker | content |
| --- | --- |
| `B-D7-HEAT-KERNEL-EXISTENCE` | no parametrix/Levi method, no Duhamel principle, no short-time existence theorem for the heat equation on a manifold |
| `B-D7-PARABOLIC-REGULARITY` | no Schauder estimates, no Hölder spaces `C^{k,α}`, no smoothness of weak parabolic solutions |
| `B-D7-SOBOLEV-EMBEDDING` | no Sobolev spaces on manifolds, no Sobolev embedding, no Rellich–Kondrachov compactness |
| `B-D7-SPECTRAL-THEOREM` | no spectral theorem for the Laplace–Beltrami operator on a closed manifold, no heat semigroup generation (Hille–Yosida) |
| `B-D7-DIRAC-DELTA` | no distribution theory or Dirac delta; the initial condition is only stated against continuous test functions |
| `B-D7-GAUSSIAN-BOUNDS` | no Gaussian bounds, no Li–Yau differential Harnack inequality |
| `B-D7-MAXIMUM-PRINCIPLE` | no parabolic maximum principle, no positivity/uniqueness theory |

`MissingMathlibDependencies` (8 entries, `_length = 8`): fundamental-solution existence, parabolic
regularity (Schauder/Hölder), Sobolev spaces + embedding + Rellich–Kondrachov, spectral theorem and
heat semigroup, Dirac delta/distributions, Gaussian bounds, parabolic maximum principle, and the
Riemannian metric/geodesic distance/volume measure.
`PresentMathlibDependencies` (4 entries) lists the reused pieces (measure and Bochner integral,
`Tendsto`/filters, `LinearMap`, matrix powers and finite-grid monotonicity).

---

## 7. Compile gate and `#print axioms` audit

### 7.1 Authored files (`lake env lean` from the worktree root)

| file | exit |
| --- | --- |
| `release/Poincare/D7/HeatKernel/Basic.lean` | 0 |
| `release/Poincare/D7/HeatKernel/Grid.lean` | 0 |
| `release/Poincare/D7/HeatKernel/Content.lean` | 0 |
| `release/Poincare/D7/HeatKernel/Instance.lean` | 0 |
| `release/Poincare/D7/HeatKernel/Example.lean` | 0 |
| `release/Poincare/D7/HeatKernel/Blocked.lean` | 0 |
| `release/Poincare/D7/HeatKernel/All.lean` | 0 |
| `release/Poincare/D7/HeatKernel/Probe.lean` | 0 |
| `release/Poincare/D7/HeatKernel/Audit.lean` | 0 |

(`longrun/d7hk-logs/exit_codes.txt`; per-file output in
`longrun/d7hk-logs/release_Poincare_D7_HeatKernel_*.log`.) The modules were built first with
`cd release && lake build Poincare.D7.HeatKernel.All Poincare.D7.HeatKernel.Probe
Poincare.D7.HeatKernel.Audit` (exit 0), which produces the oleans the per-file gate resolves.

### 7.2 Harness-gate replication

Every `.lean` file in the worktree (116 files: `negcontrol/`, the pre-existing `release/` modules,
and the 9 new heat-kernel files) was compiled with `lake env lean` from the worktree root:
**116/116 exit 0**, no failures (`longrun/d7hk-logs/gate_exit_codes.txt`; full output in
`longrun/d7hk-logs/gate.log`).

### 7.3 `#print axioms`

`release/Poincare/D7/HeatKernel/Audit.lean` runs 102 `#print axioms` commands, one per principal
declaration of the layer. Parsed cones (`longrun/d7hk-logs/axiom-summary.json`):

| cone | count |
| --- | --- |
| `{propext, Classical.choice, Quot.sound}` | 93 |
| no axioms | 8 |
| `{propext}` | 1 |

No `sorryAx`, no `native_decide`, no `proof_wanted`, and no other unapproved axiom appears. The
no-axiom declarations are the data-only ones (`TwoPoint`, `Blocker`, `blockers`,
`blockers_length`, `MissingMathlibDependencies`, `MissingMathlibDependencies_length`,
`PresentMathlibDependencies`, `PresentMathlibDependencies_length`); the `{propext}`-only one is
`blockers_ne_nil`.

---

## 8. Forbidden-token scan

A comment/string-aware scanner (nested `/- -/`, `--`, `"..."` stripped) searched for `sorry`,
`admit`, `native_decide`, `unsafe`, `proof_wanted`, and `axiom` (word-boundary; `#print axioms` does
not match):

| scope | files | hard hits |
| --- | --- | --- |
| `release/Poincare/D7/HeatKernel/*.lean` | 9 | **0** |
| `release/Poincare/D7/**/*.lean` (D7-wide) | 52 | **0** |

Report: `longrun/d7hk-logs/forbidden-scan.json`.

---

## 9. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-heat-kernel-existence
# 1. build the new modules (produces oleans used by the per-file gate)
(cd release && lake build Poincare.D7.HeatKernel.All Poincare.D7.HeatKernel.Probe \
  Poincare.D7.HeatKernel.Audit)
# 2. per-file compile gate
for f in release/Poincare/D7/HeatKernel/*.lean; do
  lake env lean "$f" || echo "FAIL $f"
done
# 3. axiom audit (the #print axioms output is the audit)
lake env lean release/Poincare/D7/HeatKernel/Audit.lean
# 4. source integrity
diff -rq ../D7-conjugate-heat-interface . -x .lake -x HeatKernel -x d7hk-logs \
  -x 'D7-heat-kernel-existence.md' -x 'D7-heat-kernel-existence.json'
```

Machine-readable card: `longrun/results/D7-heat-kernel-existence.json`.

TASK_DONE — longrun/results/D7-heat-kernel-existence.md
