# D7-discrete-continuous-limit — result card

**Task id:** `D7-discrete-continuous-limit`
**Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-discrete-continuous-limit`
**Generated (UTC):** 2026-09-09T18:59:40Z
**Verdict:** `TASK_DONE` — kernel-checked discrete-to-continuous consistency bridge: an explicit
`ConsistencyCertificate` between the D2 finite-grid heat evolution and the D2 continuous heat
interface; a kernel-checked local error recursion; its discrete stability under the stated CFL
condition `0 ≤ α ≤ 1/2` with the explicit, computable bound `ε₀ + Σ τ` (rate form
`ε₀ + (n Δt)(Δt/2·A + h²/12·B)`); the discrete maximum principle preserved under mesh refinement
(uniform in the mesh); the D4 `FiniteMeshConvergence` predicate discharged under explicit
stability/consistency hypotheses; the D2 `ContinuousHeatMaximumPrincipleInterface` recovered as a
corollary of mesh convergence; and the unconditional convergence theorem recorded state-only with
named blockers for compactness and parabolic regularity. No `sorry` / `axiom` / `unsafe` /
`native_decide` / `proof_wanted`.

---

## 0. Bottom line

| item | result |
| --- | --- |
| new files (only under `release/Poincare/D7/Limit/`) | **10 Lean files, 1827 lines, 89 audited declarations** |
| compiled with `lake env lean` from the worktree root | **10/10 authored files exit 0** (`longrun/d7-limit-logs/gate_exit_codes.txt`) |
| whole release package `lake build` | **exit 0** (9008 jobs; `longrun/d7-limit-logs/lake_build_full.log`) |
| `#print axioms` audit | **89 declarations**: cone `{propext, Classical.choice, Quot.sound}` (81), cone `{propext}` (1, `blockers_ne_nil`), no dependencies (7: the `Blocker`/dependency string lists and their length lemmas); **0 nonstandard cones, 0 `sorryAx`** |
| forbidden-token scan (comment/string aware) | **0 hard, 0 soft** in the 10 authored files; D7-wide scan (62 files) also **0 hard, 0 soft** |
| copied scaffold files modified | **0** (`diff -rq` against `../D7-heat-kernel-existence`, `.lake`/`Limit`/logs/cards excluded: **empty**) |
| consistency certificate | `ConsistencyCertificate u a b T N α`: mesh + `h>0`, `Δt>0`, `α = Δt/h²`, CFL `0 ≤ α ≤ 1/2`, discrete slab, boundary compatibility with `u`, initial error `ε₀`, truncation error `τ`, and `ContinuousHeatHypotheses u a b T` |
| local error recursion | `error_step : e (n+1) i ≤ α e n (i-1) + (1-2α) e n i + α e n (i+1) + τ n` |
| stability under CFL | `perturbed_recursion_stable : e n i ≤ max 0 (max_j e 0 j) + Σ_{k<n} τ k` |
| explicit global bound | `error_le_of_certificate : |u (x i) (t n) - v n i| ≤ ε₀ + Σ_{k<n} τ k`; rate form `error_le_order_rate : ≤ ε₀ + (n Δt)(Δt/2·A + h²/12·B)` |
| refinement | `GridMesh.Refines`, `RefinesEvolution.sup_initial_le`, `maxPrinciple_uniform_in_mesh`, `maxPrinciple_preserved_under_refinement` |
| convergence | `heatMeshConvergence_of_stability`, `finiteMeshConvergence_of_stability`, `continuousHeatMaximumPrincipleInterface_of_meshConvergence` |
| blocked items | `HeatMeshConvergenceTheorem` and `ContinuousHeatMaximumPrincipleConjecture` state-only `Prop`s; 5 named blockers; 7 exact missing mathlib dependencies |

**Not claimed:** no unconditional convergence theorem, no compactness extraction, no parabolic
regularity, no construction of the continuous heat solution, no proof of the D2
`ContinuousHeatMaximumPrincipleInterface`. Those are the state-only `Prop`s of Section 6.

---

## 1. Scaffold, environment, and source integrity

The worktree was scaffolded from `../D7-heat-kernel-existence/` as instructed.

| command | exit | note |
| --- | --- | --- |
| `cp -al ../D7-heat-kernel-existence/. .` | **1** | hard links rejected on this filesystem (`Invalid cross-device link`), matching every other D7 card |
| `cp -a ../D7-heat-kernel-existence/. .` | **0** | full copy including the prebuilt `.lake`; scaffold intact |
| `diff -rq ../D7-heat-kernel-existence . -x .lake -x Limit -x d7-limit-logs -x 'D7-discrete-continuous-limit.md' -x 'D7-discrete-continuous-limit.json'` | **0** | no output: **0 shared scaffold files changed**; the only additions are `release/Poincare/D7/Limit/`, `longrun/d7-limit-logs/` and this card |

Environment:

| key | value |
| --- | --- |
| Lean | `4.34.0-rc2` (commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`) |
| mathlib | `7974e751bece493b6ff508039423ca9fa2452fa8` |
| root package | `D7RiemannCurvatureTensorRoot` (re-exposes `release/.lake`, so `lake env lean` works from the worktree root) |
| release package | `PoincareRelease` (`release/lakefile.toml`, glob `Poincare.+`) |

New files:

| file | lines | declarations | role |
| --- | --- | --- | --- |
| `release/Poincare/D7/Limit/Basic.lean` | 227 | 21 | `GridMesh`, `GridMesh.Refines`, `TimeMesh`, `SlabGrid`, D2 bridges `SlabGrid.ofHeatGridEvolution` / `SlabGrid.toHeatGridEvolution` |
| `release/Poincare/D7/Limit/ErrorRecursion.lean` | 267 | 12 | `ConsistencyCertificate`, local recursion `error_step`, D2 bridge `ConsistencyCertificate.toHeatGridEvolution`, computable `truncationConstant` |
| `release/Poincare/D7/Limit/Stability.lean` | 217 | 6 | `perturbed_recursion_stable` under CFL, explicit global bounds, exactness |
| `release/Poincare/D7/Limit/Refinement.lean` | 155 | 9 | two-sided max principle, `RefinesEvolution.sup_initial_le`, mesh-uniform and refinement-preserved bounds |
| `release/Poincare/D7/Limit/Convergence.lean` | 315 | 16 | `HeatMeshSequence`, limit passage, `FiniteMeshConvergence`, interface recovery, state-only theorem |
| `release/Poincare/D7/Limit/Blocked.lean` | 156 | 11 | state-only `ContinuousHeatMaximumPrincipleConjecture`, 5 blockers, missing dependencies |
| `release/Poincare/D7/Limit/Example.lean` | 238 | 14 | quadratic exact certificate (`ε₀ = τ = 0`), inconsistency and CFL negative controls |
| `release/Poincare/D7/Limit/Probe.lean` | 101 | 0 | compilable mathlib/D7 API probe (`#check` / `#check_failure`) |
| `release/Poincare/D7/Limit/Audit.lean` | 132 | 0 | 89 `#print axioms` commands |
| `release/Poincare/D7/Limit/All.lean` | 19 | 0 | umbrella module |

Source hashes are recorded in the `.json` card (`files[].sha256`).

---

## 2. The consistency certificate (task item 1)

`release/Poincare/D7/Limit/ErrorRecursion.lean`:

```lean
structure ConsistencyCertificate (u : ℝ → ℝ → ℝ) (a b T : ℝ) (N : ℕ) (α : ℝ) where
  mesh : GridMesh a b N
  h : ℝ                    -- spatial step
  h_pos : 0 < h
  Δt : ℝ                   -- time step
  Δt_pos : 0 < Δt
  timeMesh : TimeMesh Δt
  alpha_eq : α = Δt / h ^ 2
  cfl_nonneg : 0 ≤ α
  cfl_le_half : α ≤ 1 / 2
  grid : SlabGrid N α
  boundary_left  : ∀ n, grid.v n 0 = u a (timeMesh.time n)
  boundary_right : ∀ n, grid.v n (N + 1) = u b (timeMesh.time n)
  ε₀ : ℝ
  ε₀_nonneg : 0 ≤ ε₀
  initial_error : ∀ i ≤ N + 1, |u (mesh.x i) (timeMesh.time 0) - grid.v 0 i| ≤ ε₀
  τ : ℕ → ℝ
  τ_nonneg : ∀ n, 0 ≤ τ n
  truncation : ∀ n i, 0 < i → i < N + 1 →
    |u (mesh.x i) (timeMesh.time (n + 1))
        - heatStep α (fun j => u (mesh.x j) (timeMesh.time n)) i| ≤ τ n
  continuous : ContinuousHeatHypotheses u a b T
```

The certificate connects the **D2 finite-grid evolution** and the **D2 continuous interface**:

* `SlabGrid N α` generalizes the D2 `Poincare.Longrun.PDE.HeatGridEvolution`: arbitrary boundary
  traces instead of the zero Dirichlet pinning, with the same explicit-Euler update
  `v (t+1) i = α v t (i-1) + (1-2α) v t i + α v t (i+1)`.  The D2 evolution is recovered by
  `SlabGrid.ofHeatGridEvolution`, and conversely `SlabGrid.toHeatGridEvolution` turns a slab with
  vanishing boundary traces into a D2 `HeatGridEvolution`; `SlabGrid.step_heatStep` rewrites the
  update in D2 `heatStep` form.
* `continuous : ContinuousHeatHypotheses u a b T` is exactly the D2 continuous heat interface
  (`∂ₜu = ∂ₓ²u`, continuity on the slab, nonpositive initial and lateral data).
* The boundary compatibility fields make the boundary error identically zero, so the error
  recursion is driven only by the initial error `ε₀` and the local truncation error `τ`.

When the continuous solution vanishes at both spatial endpoints, `ConsistencyCertificate.toHeatGridEvolution`
extracts a D2 zero-Dirichlet `HeatGridEvolution` from the certificate, so the D2 maximum principle
and energy theorems apply to it verbatim.  The certificate is inhabited by a genuine non-steady
solution: `quadCertificate` in `Example.lean` (Section 7).

---

## 3. The error recursion and its stability (task item 2)

### 3.1 Local recursion

`error_recursion_of_truncation` is pure algebra plus the triangle inequality: writing
`e n i = |u (x i) (t n) - v n i|`, splitting the defect into the truncation term and the
scheme's convex combination, and using `0 ≤ α`, `0 ≤ 1-2α`, one gets

```lean
theorem error_recursion_of_truncation ... :
    e (n + 1) i ≤ α * e n (i - 1) + (1 - 2 * α) * e n i + α * e n (i + 1) + τ n
```

and `ConsistencyCertificate.error_step` instantiates it for the certificate, with the boundary
values contributing `0` (`error_left`, `error_right`).

### 3.2 Stability under the CFL condition

`perturbed_recursion_stable` proves, by the convexity induction (`α + (1-2α) + α = 1`), that
under `0 ≤ α ≤ 1/2` and a nonnegative source `τ`,

```lean
theorem perturbed_recursion_stable ... :
    e n i ≤ max 0 (max_j e 0 j) + ∑ k ∈ Finset.range n, τ k
```

The CFL condition is essential: `1 - 2α < 0` breaks the convex combination; the explicit failure
is `cfl_essential` in `Example.lean` (Section 7).

### 3.3 Explicit computable constants

```lean
theorem ConsistencyCertificate.error_le_of_certificate ... :
    C.error n i ≤ C.ε₀ + ∑ k ∈ Finset.range n, C.τ k

theorem ConsistencyCertificate.error_le_order_rate ... :
    C.error n i ≤ C.ε₀ + ((n : ℝ) * C.Δt) * (C.Δt / 2 * A + C.h ^ 2 / 12 * B)
```

where `truncationConstant Δt α A B h = Δt²/2 * A + α h⁴/12 * B` is the Taylor-remainder constant
(`A` bounds `|∂ₜ²u|`, `B` bounds `|∂ₓ⁴u|`), and `truncationConstant_eq` factors it as
`Δt * (Δt/2 * A + h²/12 * B)` under the CFL relation `α h² = Δt`.  The rate form is therefore
first order in `Δt` and second order in `h` per unit of physical time.  The hypothesis that the
truncation error is bounded by this constant is the explicit consistency input; it is never an
axiom.

`error_eq_zero_of_exact` records the sharp case: `ε₀ = 0` and `τ ≡ 0` force error `0`.

---

## 4. The discrete maximum principle preserved under refinement

`release/Poincare/D7/Limit/Refinement.lean`:

* `negEvolution` and `abs_le_of_initial_abs_le` give the two-sided form
  `|u 0 i| ≤ M → |u t i| ≤ M` of the D2 maximum principle;
* `le_zero_of_initial_nonpos` is the nonpositive form matching the D2 interface;
* `GridMesh.Refines` is the mesh-refinement relation (every coarse node is a fine node), with
  `Refines.refl`, `Refines.trans`, and `RefinesEvolution.sup_initial_le`: under a refinement the
  coarse initial supremum is at most the fine one, so the D2 bound `max 0 (sup initial)` is
  monotone along refinements;
* `maxPrinciple_uniform_in_mesh` is the key mesh-independence statement: for an initial datum
  sampled from a continuous `f` with `|f x| ≤ M` on `[a,b]`, the bound `M` holds for **every**
  mesh, uniformly in the number of cells;
* `maxPrinciple_preserved_under_refinement` packages the coarse and fine bounds.

---

## 5. Convergence and recovery of the continuous interface

`release/Poincare/D7/Limit/Convergence.lean`:

* `HeatMeshSequence u a b T` is a sequence of slabs with per-level mesh, time step, CFL relation,
  boundary compatibility, initial error `ε n`, truncation error `τ n k`, and the D2 continuous
  interface.
* `HeatMeshSequence.tendsto_value` is the checked limit passage: if sampled grid points converge
  to `(x,t)` in the slab and the explicit error bound `ε n + Σ τ` tends to `0`, then the discrete
  values converge to `u x t`.  It uses continuity of the slab solution
  (`ContinuousHeatHypotheses.continuous_on_slab`), not compactness.
* `heatMeshConvergence_of_stability` lifts this to `HeatMeshConvergence S` under
  `IsRefiningMesh S` (mesh density) and `HasVanishingError S` (error-vanishing).
* `finiteMeshConvergence_of_stability` discharges the D4 statement-only predicate
  `Poincare.Longrun.Evolution.FiniteMeshConvergence` for the heat mesh.
* `continuousHeatMaxPrinciple_of_meshConvergence` and
  `continuousHeatMaximumPrincipleInterface_of_meshConvergence` recover the D2
  `ContinuousHeatMaximumPrincipleInterface u a b T` as a corollary of the discrete maximum
  principle plus mesh convergence:

```lean
theorem continuousHeatMaximumPrincipleInterface_of_meshConvergence
    (S : HeatMeshSequence u a b T) (hconv : HeatMeshConvergence S)
    (hdiscrete : ∀ n k i, i ≤ S.N n + 1 → (S.grid n).v k i ≤ 0)
    (hdense : ∀ x ∈ Icc a b, ∀ t ∈ Icc 0 T, ∃ (i k : ℕ → ℕ),
      (∀ n, i n ≤ S.N n + 1) ∧
      Tendsto (fun n => (S.mesh n).x (i n)) atTop (𝓝 x) ∧
      Tendsto (fun n => (S.timeMesh n).time (k n)) atTop (𝓝 t)) :
    ContinuousHeatMaximumPrincipleInterface u a b T
```

---

## 6. State-only convergence theorem and exact missing dependencies (task item 3)

`release/Poincare/D7/Limit/Convergence.lean` and `Blocked.lean`:

```lean
def HeatMeshConvergenceTheorem (a b T : ℝ) : Prop :=
  ∀ (u : ℝ → ℝ → ℝ), ContinuousHeatHypotheses u a b T →
    ∀ S : HeatMeshSequence u a b T, IsRefiningMesh S → HeatMeshConvergence S

def ContinuousHeatMaximumPrincipleConjecture (a b T : ℝ) : Prop :=
  ∀ (u : ℝ → ℝ → ℝ), ContinuousHeatHypotheses u a b T →
    ContinuousHeatMaximumPrincipleInterface u a b T
```

Both are `def … : Prop` (consistency checked by `…_isProp`), with no proof attempt.  The checked
reduction `heatMeshConvergenceTheorem_of_vanishingError` adds `HasVanishingError S` as an explicit
hypothesis; the conditional recovery
`continuousHeatMaximumPrincipleConjecture_of_meshConvergence` shows exactly which input is missing
(a convergent nonpositive mesh sequence).

Named blockers (each list checked nonempty by `blockers_ne_nil`):

| blocker | missing input |
| --- | --- |
| `B-D7-LIMIT-COMPACTNESS` | compactness of the family of discrete solutions; mathlib has `Equicontinuous` and `IsCompact` but **no Arzelà–Ascoli theorem** (`#check_failure @ArzelaAscoli` in `Probe.lean`) |
| `B-D7-LIMIT-REGULARITY` | parabolic regularity: Schauder estimates, Hölder spaces, uniform `C²`/`C⁴` a priori bounds |
| `B-D7-LIMIT-CONSISTENCY` | uniform a priori bounds turning the Taylor remainder into the truncation estimate (`taylor_mean_remainder` is present; the uniform estimate is not) |
| `B-D7-LIMIT-WELLPOSED` | existence/uniqueness of the continuous heat solution (the D2 `ContinuousHeatHypotheses` is statement-only) |
| `B-D7-LIMIT-MESH-DENSITY` | construction of refining mesh sequences with the density property |

Exact missing mathlib dependencies (`MissingMathlibDependencies`, 7 entries): Arzelà–Ascoli
compactness; sequential compactness/closedness of the limit; parabolic regularity; uniform
`C²`/`C⁴` bounds; existence/uniqueness of the continuous solution; the uniform Taylor-remainder
estimate; a constructive refining mesh sequence.  Present dependencies
(`PresentMathlibDependencies`, 6 entries): `ContinuousOn`/`ContinuousWithinAt`, filter limits
(`Tendsto`, `le_of_tendsto'`, `Metric.tendsto_atTop`), the D2 finite-grid evolution and maximum
principle, the D2 continuous interface, the D4 `FiniteMeshConvergence` predicate, and
`Finset.sum`/`Finset.sup'`.

---

## 7. Non-vacuity and negative controls

`release/Poincare/D7/Limit/Example.lean`:

* **Exact quadratic certificate.**  On `[-1,1]`, the genuine non-steady heat solution
  `u x t = -x² - 2t` (`quadSolution_continuousHeatHypotheses`) is reproduced **exactly** by the
  forward-Euler/centered-difference scheme whenever `α h² = Δt` (`quad_step`: the centered second
  difference of a quadratic is exactly `-2h²` and the forward time step of a linear-in-time
  function is exactly `-2Δt`).  `quadCertificate` inhabits `ConsistencyCertificate` with
  `ε₀ = 0`, `τ ≡ 0`, and `quad_error_zero` proves the error bound is attained:
  the discrete values equal the sampled continuous solution at every node and time.
* **Inconsistency control.**  `quad_truncation_eq_of_alpha_zero` shows that with `α = 0` (so
  `α h² ≠ Δt`) the local truncation error is exactly `-2Δt`; `quad_truncation_abs_pos` gives
  `|τ| = 2Δt > 0`, so no certificate with `τ = 0` exists for the wrong CFL ratio.
* **CFL control.**  `cfl_essential` exhibits a signed recursion satisfying the perturbed
  inequality with `α = 1` whose values violate the stability bound at `n = 1`; the failure is
  caused by `1 - 2α = -1 < 0`.

---

## 8. Verification

### 8.1 Compile gate

Every authored file compiled with `lake env lean <file>` from the worktree root:

```
release/Poincare/D7/Limit/All.lean 0
release/Poincare/D7/Limit/Audit.lean 0
release/Poincare/D7/Limit/Basic.lean 0
release/Poincare/D7/Limit/Blocked.lean 0
release/Poincare/D7/Limit/Convergence.lean 0
release/Poincare/D7/Limit/ErrorRecursion.lean 0
release/Poincare/D7/Limit/Example.lean 0
release/Poincare/D7/Limit/Probe.lean 0
release/Poincare/D7/Limit/Refinement.lean 0
release/Poincare/D7/Limit/Stability.lean 0
```

(`longrun/d7-limit-logs/gate_exit_codes.txt`, full output `gate.log`.)  The whole release package
also builds: `cd release && lake build` exit 0 (9008 jobs).

### 8.2 `#print axioms` audit

`release/Poincare/D7/Limit/Audit.lean` runs `#print axioms` on all **85** principal declarations
(89 commands, 89 output records).  Cone summary:

| cone | count |
| --- | --- |
| no dependencies | 7 (`Blocker`, `blockers`, `blockers_length`, `MissingMathlibDependencies`, `MissingMathlibDependencies_length`, `PresentMathlibDependencies`, `PresentMathlibDependencies_length`) |
| `{propext}` | 1 (`blockers_ne_nil`) |
| `{propext, Classical.choice, Quot.sound}` | 77 |

**0** nonstandard cones, **0** `sorryAx`, **0** `native_decide`, **0** `proof_wanted`.  Full
output: `longrun/d7-limit-logs/audit_build.log`; machine-readable records:
`longrun/d7-limit-logs/axiom-records.json`.

### 8.3 Forbidden-token scan

`input/d5-tools/scan_forbidden.py` (comment/string aware) reports:

| scope | files | hard | soft |
| --- | --- | --- | --- |
| `release/Poincare/D7/Limit` | 10 | **0** | 0 |
| `release/Poincare/D7` | 62 | **0** | 0 |

### 8.4 Source integrity

`diff -rq ../D7-heat-kernel-existence . -x .lake -x Limit -x d7-limit-logs
-x 'D7-discrete-continuous-limit.md' -x 'D7-discrete-continuous-limit.json'` exits 0 with no
output: **0 shared scaffold files changed**.

---

## 9. Honest boundary

This card claims exactly what the kernel checked:

* a consistency certificate between the D2 finite-grid heat evolution and the D2 continuous heat
  interface;
* the local error recursion and its stability under the CFL condition `0 ≤ α ≤ 1/2`, with the
  explicit computable bounds `ε₀ + Σ τ` and `ε₀ + (n Δt)(Δt/2·A + h²/12·B)`;
* the discrete maximum principle preserved under mesh refinement (uniform in the mesh);
* mesh convergence under the explicit `IsRefiningMesh` and `HasVanishingError` hypotheses, the
  D4 `FiniteMeshConvergence` predicate discharged for the heat mesh, and the D2
  `ContinuousHeatMaximumPrincipleInterface` recovered as a corollary;
* a non-vacuous exact certificate for `u x t = -x² - 2t`, plus inconsistency and CFL negative
  controls;
* the unconditional convergence theorem and the unconditional continuous interface recorded as
  state-only `Prop`s with named blockers and exact missing dependencies.

It does **not** claim the unconditional convergence theorem, compactness extraction, parabolic
regularity, the construction of the continuous heat solution, or the D2
`ContinuousHeatMaximumPrincipleInterface`.  Those are the blocked `Prop`s of Section 6.

---

## 10. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-discrete-continuous-limit
cd release && lake build && cd ..
for f in release/Poincare/D7/Limit/*.lean; do lake env lean "$f" || exit 1; done
lake env lean release/Poincare/D7/Limit/Audit.lean | tee longrun/d7-limit-logs/audit_build.log
python3 input/d5-tools/scan_forbidden.py release/Poincare/D7/Limit
```

Logs: `longrun/d7-limit-logs/` (`gate_exit_codes.txt`, `gate.log`, `lake_build_full.log`,
`audit_build.log`, `axiom-records.json`, `probe.log`, `forbidden-scan-limit.json`,
`forbidden-scan-d7-wide.json`, `source_integrity_diff.txt`).

---

TASK_DONE — `longrun/results/D7-discrete-continuous-limit.md`
