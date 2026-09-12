# D2-ricci-ode-cluster — result card

> **Delivery note (sandbox).** The canonical shared path
> `/data3/guoshaoyang/workdir/lean_poincare/longrun/results/D2-ricci-ode-cluster.md`
> is outside the `workspace-write` sandbox (session workspace =
> `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D2_ricci_ode_cluster`).
> A direct `cp` was denied (`exit code 1`, `Permission denied`), and the sanctioned
> escalation to `danger-full-access` was rejected (`requires approval, but no approval
> channel is available`). This card and its JSON twin are therefore mirrored at
> `<worktree>/longrun/results/`. **Integrator action:** copy the two mirrored files to the
> shared `longrun/results/` directory, or grant the worker write access to it. (Same
> delivery pattern as `D2-geometry-foundation` and `D2-pde-foundation`.)
>
> **Path note.** The task prompt names the worktree `…/worktrees/D2_ode`; the current
> runtime snapshot assigns `…/worktrees/D2_ricci_ode_cluster` (the `D2_ode` name does not
> exist on disk). All work was done in `D2_ricci_ode_cluster`.

- **Task id:** `D2-ricci-ode-cluster`
- **Stage / lane:** D2 / builder (`requires_lean: true`)
- **Model:** `deepseek-v4.1-flash-expires-on-0910`
- **Session:** `session-2cf48c9d-9221-43ce-8596-8df3035668de`
- **Started:** `2026-09-09T00:00:00+08:00`
- **Finished:** `2026-09-09T00:35:00+08:00`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D2_ricci_ode_cluster`
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (commit `6a10ac8c22be`)
- **mathlib:** revision `7974e751bece493b6ff508039423ca9fa2452fa8`
- **Status:** `done`. All required deliverables are checked; the only unresolved item is the
  sandbox denial of the shared `longrun/results/` path (delivery note above).

## 1. Consumed input

The accepted `D2-geometry-foundation` result card and its checked cluster
`Poincare.Longrun.Geometry` were read and imported unmodified:

- `Poincare/Longrun/Geometry/MetricData.lean` — `MetricData V ι` (symmetric positive-definite
  form + chosen orthonormal basis), `raiseIndex`, `toScalarContractionData`,
  `scalarCurvature_eq_sum_basis` (`scalarCurvature K d = ∑ i, ricci K eᵢ eᵢ`);
- `Poincare/Longrun/Geometry/Contraction.lean` — `curvatureForm` (metric-lowered (0,4)
  tensor), `ricci_add`/`ricci_smul`, `scalarCurvature_add`/`scalarCurvature_smul`;
- `Poincare/Longrun/Geometry/ConnectionAdapter.lean` — `LieBracketData`,
  `AbstractConnection`, `toCurvatureOperator`, `meanConnection`;
- `Poincare/Longrun/Geometry/LeviCivitaBlocked.lean` —
  `CovariantDerivativeCurvatureStatement` (the BLOCKED manifold curvature API),
  `LeviCivitaExistenceStatement`, `LeviCivitaData`;
- `Poincare/Stage1/CurvatureAlgebra.lean` and `Poincare/Stage1/RiemannAdapter.lean` —
  `CurvatureOperator`, `ricci`, `scalarCurvature`, `PointwiseCurvature`,
  `RiemannianCurvatureData`.

The worktree contains **private byte-identical copies** of the Stage1 and geometry sources;
the shared `poincare-lab/` sources were never written. Integrity hashes are in §7.

## 2. What was built

A compilable Stage 2 / curvature-ODE cluster under `Poincare/Longrun/CurvatureODE/`:

| File | Lines | sha256 |
| --- | --- | --- |
| `Poincare/Longrun/CurvatureODE.lean` (umbrella) | 37 | `b930b7a533cdb62358a25020e2fd0a1a66a555c0d5097ee17f935e76b77c737b` |
| `Poincare/Longrun/CurvatureODE/State.lean` | 166 | `6e6ccb0192580304cd565761b4107d7b3fe5d2a2a710e4c2bcd32a291d0f94b6` |
| `Poincare/Longrun/CurvatureODE/Evolution.lean` | 136 | `d54e51c9ce01389d3a3273fb27f71fff2bf54e2e0821305a3b6c643581fa91e0` |
| `Poincare/Longrun/CurvatureODE/ScalarODE.lean` | 86 | `4e9d72724224ac1d2e42e116b82b099577541a4e17a7ce07bdbea077e875b8a4` |
| `Poincare/Longrun/CurvatureODE/Invariant.lean` | 104 | `b173a7363ec0b1e99cde510bf2ecb43565bd3a0a06008e47a270053baa56f4d0` |
| `Poincare/Longrun/CurvatureODE/Monotonicity.lean` | 151 | `466f7c713859f57a8670426e051b0f0685e0f6405254db1f7b80363ff889db0c` |
| `Poincare/Longrun/CurvatureODE/Bridge.lean` | 226 | `8baeff93d0b3808ec293c29edccea5263b899036d834b44b32e31badae841645` |
| `Audit/CurvatureODEAudit.lean` (axiom audit driver) | 78 | `bfe0e1d3e8363b571ec6b0160690a8e80e897e18508d1ae9926f604268abcbc0` |

Total authored: **984 Lean lines**, 37 audited declarations.

## 3. Requirement mapping

### 3.1 Finite state (`State.lean`)

```lean
abbrev CurvatureState (ι : Type w) := ι → ℝ
```

A finite tuple (`ι` is `Fintype` at every use site). It is tied to the geometry cluster by:

```lean
noncomputable def diagonalEndomorphism (m : MetricData V ι) (lam : CurvatureState ι) : V →ₗ[ℝ] V
noncomputable def stateOfCurvature (m : MetricData V ι) (K : CurvatureOperator ℝ V) : CurvatureState ι :=
  fun i => ricci K (m.basis i) (m.basis i)
noncomputable def scalarOfState (lam : CurvatureState ι) : ℝ := ∑ i, lam i
```

with the checked consumption of the accepted geometry result

```lean
theorem scalarOfState_stateOfCurvature (m : MetricData V ι) (K : CurvatureOperator ℝ V) :
    scalarOfState (stateOfCurvature m K) = scalarCurvature K m.toScalarContractionData
```

(proof: the geometry cluster's `MetricData.scalarCurvature_eq_sum_basis`). Additional checked
API: `diagonalEndomorphism_basis` (`eᵢ ↦ lamᵢ • eᵢ`), `trace_diagonalEndomorphism`
(`trace = ∑ i, lamᵢ`), `form_diagonalEndomorphism`, `diagonalEndomorphism_selfAdjoint`
(the diagonal endomorphism is metric-self-adjoint).

### 3.2 Evolution relation (`Evolution.lean`)

The finite reaction field and the continuous/discrete evolution relations:

```lean
structure ReactionField (ι : Type w) [Fintype ι] where
  a : ι → ℝ
  g : (ι → ℝ) → ι → ℝ
  a_nonneg : ∀ i, 0 ≤ a i
  g_nonneg : ∀ lam i, 0 ≤ g lam i

def ReactionField.eval (F : ReactionField ι) (lam : ι → ℝ) (i : ι) : ℝ :=
  F.a i * (lam i) ^ 2 + F.g lam i

structure EvolutionRelation (F : ReactionField ι) (T : ℝ) (traj : ℝ → ι → ℝ) : Prop where
  continuous : ∀ i, ContinuousOn (fun t => traj t i) (Icc 0 T)
  hasDeriv : ∀ i, ∀ t ∈ Ico 0 T,
    HasDerivWithinAt (fun s => traj s i) (F.eval (traj t) i) (Ici t) t

structure DiscreteEvolution (F : ReactionField ι) (h : ℝ) (traj : ℕ → ι → ℝ) : Prop where
  step : ∀ n i, traj (n + 1) i = traj n i + h * F.eval (traj n) i
```

The canonical Ricci-flow-inspired field is `ReactionField.hamilton`
(`lamᵢ' = lamᵢ² + ∑ⱼ lamⱼ²`, the diagonal model of the reaction `Rm² + Rm#`). The relation is
witnessed non-vacuous by `zero_evolutionRelation` and `zero_discreteEvolution`.

### 3.3 Invariant-region / sign-preservation theorem (`Invariant.lean`)

```lean
theorem component_monotone (F : ReactionField ι) {T : ℝ} {traj : ℝ → ι → ℝ}
    (ev : EvolutionRelation F T traj) (i : ι) :
    ∀ t ∈ Icc 0 T, traj 0 i ≤ traj t i

theorem nonneg_orthant_invariant (F : ReactionField ι) {T : ℝ} {traj : ℝ → ι → ℝ}
    (ev : EvolutionRelation F T traj) (h0 : ∀ i, 0 ≤ traj 0 i) :
    ∀ t ∈ Icc 0 T, ∀ i, 0 ≤ traj t i

theorem nonneg_orthant_invariant_discrete (F : ReactionField ι) {h : ℝ} (hh : 0 ≤ h)
    {traj : ℕ → ι → ℝ} (ev : DiscreteEvolution F h traj) (h0 : ∀ i, 0 ≤ traj 0 i) :
    ∀ n i, 0 ≤ traj n i
```

Proof engine (`ScalarODE.lean`): the mathlib fencing theorem
`image_le_of_deriv_right_le_deriv_boundary` (`le_left_of_hasDerivWithinAt_nonpos`) applied to
`-trajᵢ`; the reaction is `≥ 0` in **every** state, so no a priori region restriction is
needed. `zero_orthant_invariant` is a consistency witness.

### 3.4 Scalar monotonicity theorem (`Monotonicity.lean`)

```lean
theorem scalarFunctional_monotone (F : ReactionField ι) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    {T : ℝ} {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj) :
    ∀ t ∈ Icc 0 T, scalarFunctional w (traj 0) ≤ scalarFunctional w (traj t)

theorem scalarOfState_monotone (F : ReactionField ι) {T : ℝ} {traj : ℝ → ι → ℝ}
    (ev : EvolutionRelation F T traj) :
    ∀ t ∈ Icc 0 T, scalarOfState (traj 0) ≤ scalarOfState (traj t)
```

with the explicit-Euler analogues `scalarFunctional_monotone_discrete` /
`scalarOfState_monotone_discrete`. The derivative of `S_w = ∑ i, wᵢ lamᵢ` along the flow is
`∑ i, wᵢ Fᵢ(lam) ≥ 0` (`hasDerivWithinAt_scalarFunctional`). Sign-convention audit:
`ReactionField.hamilton_eval_pos` (nonzero component ⟹ strictly positive reaction) and the
`Fin 1` computations `eval 1 = 2`, `0 < eval (-1)`. The sign matches the reaction part of
`∂ₜ R = ΔR + 2|Ric|²`.

### 3.5 The exact missing bridge (`Bridge.lean`) — explicit interface, not an axiom

Four missing pieces are exposed as named `Prop`-valued `def`s (no proof, no `axiom`):

```lean
def ManifoldCurvatureRealization (I) (M) (cov) : Prop :=
  CovariantDerivativeCurvatureStatement I M cov          -- geometry cluster, BLOCKED

def MetricFamilySolvesRicciFlow (metric) (curvature) (T) : Prop :=
  ∀ t ∈ Icc 0 T, ∀ X : V,
    HasDerivWithinAt (fun s => (metric s).form X X)
      (-2 * ricci (curvature t) X X) (Icc 0 T) t

def MetricCurvatureShadow (metric) (curvature) (T) : Prop :=
  (second-pair antisymmetry of curvatureForm) ∧ (pair symmetry of curvatureForm)

def TensorRicciFlowODERealization (I) (M) (cov) (metric) (curvature) (T)
    (DiffusionVanishes : Prop) : Prop :=
  ManifoldCurvatureRealization I M cov ∧
    MetricFamilySolvesRicciFlow metric curvature T ∧
    MetricCurvatureShadow metric curvature T ∧
    DiffusionVanishes
```

`DiffusionVanishes` is an explicit `Prop` parameter: the finite ODE is the **reaction** part
of `∂ₜ Rm = ΔRm + Rm² + Rm#`; the Laplacian is not modeled (mathlib has no Laplacian on
tensor fields).

The bridge itself is a `Type`-valued `structure` (the geometry cluster's
`RiemannianCurvatureData` is the precedent), with data fields `metric`, `curvature`,
`basis_fixed`, `state_eq` and hypothesis fields `realization`, `evolves`, `continuous`. **No
inhabitant is constructed anywhere in the repository.** Conditional transfer theorems:

```lean
theorem evolutionRelation_of_bridge (B : TensorRicciFlowODEBridge …) : EvolutionRelation F T traj

theorem ricciDiagonal_nonneg_of_bridge (B : …) (h0 : ∀ i, 0 ≤ traj 0 i) :
    ∀ t ∈ Icc 0 T, ∀ i,
      0 ≤ ricci (B.curvature t) ((B.metric t).basis i) ((B.metric t).basis i)

theorem scalarCurvature_monotone_of_bridge (B : …) (hT : 0 ≤ T) :
    ∀ t ∈ Icc 0 T,
      scalarCurvature (B.curvature 0) (B.metric 0).toScalarContractionData ≤
        scalarCurvature (B.curvature t) (B.metric t).toScalarContractionData
```

These show the checked invariant-region and monotonicity theorems transfer to the tensor
level **once** the missing hypotheses are supplied — and never before.

## 4. Worktree bootstrap (reproducible)

The assigned worktree was empty, so it was bootstrapped as an isolated Lake workspace that
reuses the prebuilt pinned mathlib read-only (same pattern as `D2-geometry-foundation`):

```text
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D2_ricci_ode_cluster
cp /data3/guoshaoyang/workdir/lean_poincare/poincare-lab/{lakefile.toml,lake-manifest.json,lean-toolchain} .
mkdir -p .lake
ln -s /data3/guoshaoyang/workdir/lean_poincare/poincare-lab/.lake/packages .lake/packages
mkdir -p Poincare/Stage1 Poincare/Longrun/Geometry
cp /data3/guoshaoyang/workdir/lean_poincare/poincare-lab/Poincare/Basic.lean Poincare/
cp /data3/guoshaoyang/workdir/lean_poincare/poincare-lab/Poincare/Stage1/{CurvatureAlgebra,RiemannAdapter}.lean Poincare/Stage1/
cp /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D2_geometry_foundation/Poincare/Longrun/Geometry.lean Poincare/Longrun/
cp /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D2_geometry_foundation/Poincare/Longrun/Geometry/*.lean Poincare/Longrun/Geometry/
```

## 5. Exact commands and exit codes

All commands run with:

```text
export PATH=/data3/guoshaoyang/workdir/lean_poincare/elan/bin:$PATH
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
```

### 5.1 Bootstrap build of the consumed dependency

```text
lake build Poincare.Longrun.Geometry
exit code: 0
# Build completed successfully (3221 jobs).
```

### 5.2 Clean rebuild of the authored cluster from source

`.lake/build/lib/lean/Poincare/Longrun/CurvatureODE{,.olean}` was deleted first, so this is a
from-source build (`longrun/logs/cluster.build.log`):

```text
lake build Poincare.Longrun.CurvatureODE
exit code: 0
# ✔ [3245/3251] Built Poincare.Longrun.CurvatureODE.ScalarODE (2.7s)
# ✔ [3246/3251] Built Poincare.Longrun.CurvatureODE.State (3.5s)
# ✔ [3247/3251] Built Poincare.Longrun.CurvatureODE.Evolution (3.2s)
# ✔ [3248/3251] Built Poincare.Longrun.CurvatureODE.Invariant (2.9s)
# ✔ [3249/3251] Built Poincare.Longrun.CurvatureODE.Monotonicity (3.4s)
# ✔ [3250/3251] Built Poincare.Longrun.CurvatureODE.Bridge (2.4s)
# ✔ [3251/3251] Built Poincare.Longrun.CurvatureODE (1.8s)
# Build completed successfully (3251 jobs).
```

Full-library build (`longrun/logs/Poincare.build.log`):

```text
lake build Poincare
exit code: 0
# Build completed successfully (3253 jobs).
```

### 5.3 `lake env lean` on every authored file

```text
lake env lean Poincare/Longrun/CurvatureODE/State.lean        exit code: 0   (0 bytes output)
lake env lean Poincare/Longrun/CurvatureODE/Evolution.lean    exit code: 0   (0 bytes output)
lake env lean Poincare/Longrun/CurvatureODE/ScalarODE.lean    exit code: 0   (0 bytes output)
lake env lean Poincare/Longrun/CurvatureODE/Invariant.lean    exit code: 0   (0 bytes output)
lake env lean Poincare/Longrun/CurvatureODE/Monotonicity.lean exit code: 0   (0 bytes output)
lake env lean Poincare/Longrun/CurvatureODE/Bridge.lean       exit code: 0   (0 bytes output)
lake env lean Poincare/Longrun/CurvatureODE.lean              exit code: 0   (0 bytes output)
lake env lean Audit/CurvatureODEAudit.lean                    exit code: 0   (63 output lines)
```

Per-file compiler output was captured verbatim in `longrun/logs/*.compile.log` (all empty
except the audit).

### 5.4 `#print axioms`

```text
lake env lean Audit/CurvatureODEAudit.lean > Audit/CurvatureODEAudit.out 2>&1
exit code: 0
grep -c "sorryAx" Audit/CurvatureODEAudit.out   →  0
grep -c "depends on axioms" Audit/CurvatureODEAudit.out   →  37
grep -o "depends on axioms: \[[^]]*\]" Audit/CurvatureODEAudit.out | sort -u
  → depends on axioms: [propext, Classical.choice, Quot.sound]
```

37 principal declarations were audited (every `#print axioms` directive produced exactly one
output line; names verified to match). Exactly **one** axiom set occurs:
`[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no project axiom. Representative
lines:

```text
'Poincare.Longrun.CurvatureODE.scalarOfState_stateOfCurvature' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.CurvatureODE.le_left_of_hasDerivWithinAt_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.CurvatureODE.nonneg_orthant_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.CurvatureODE.scalarFunctional_monotone' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.CurvatureODE.TensorRicciFlowODEBridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.CurvatureODE.scalarCurvature_monotone_of_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The full 63-line output is `Audit/CurvatureODEAudit.out` (also
`longrun/logs/CurvatureODEAudit.compile.log`).

## 6. Hygiene checks

```text
# actual declarations only (comments/docstrings excluded by the ^[[:space:]]* anchor)
grep -rnE "^[[:space:]]*(sorry|axiom|unsafe|native_decide|proof_wanted)\b" \
  Poincare/Longrun/CurvatureODE.lean Poincare/Longrun/CurvatureODE/ Audit/CurvatureODEAudit.lean
→ no matches (exit 1)

# textual occurrences are only the honesty docstrings ("no sorry, axiom, unsafe, ...")
# and the audit file's `#print axioms` directives.
```

The authored files contain no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted`.

## 7. Shared-tree integrity

Private copies are byte-identical to their accepted sources:

```text
sha256 Poincare/Stage1/CurvatureAlgebra.lean  = d2295c744bdabacf48fe2734b0e989b8d09bda651c7b61aa05b0729ded11b988  (== shared original)
sha256 Poincare/Stage1/RiemannAdapter.lean    = a19c67087666e5fcca9d226972b4eaa5baf94822a11cd49f6a7385088aefd20b  (== shared original)
sha256 Poincare/Longrun/Geometry.lean         = 136065c47e12130a9368cee1bb2f21a43949df701410930c245d03eaecf344fa  (== D2-geometry-foundation)
sha256 Poincare/Longrun/Geometry/MetricData.lean         (== D2-geometry-foundation)
sha256 Poincare/Longrun/Geometry/ConnectionAdapter.lean  (== D2-geometry-foundation)
sha256 Poincare/Longrun/Geometry/Contraction.lean        (== D2-geometry-foundation)
sha256 Poincare/Longrun/Geometry/LeviCivitaBlocked.lean  (== D2-geometry-foundation)
```

`find poincare-lab -type f -mmin -60` (excluding `.lake`) → no files modified. All new oleans
go to the worktree-local `.lake/build/`; the shared `.lake/packages` tree is used read-only
through a symlink.

## 8. Mathematical statement and assumptions (summary)

- The cluster is a **finite-dimensional diagonal reaction model** of Hamilton's curvature
  ODE. The state is a finite tuple `lam : ι → ℝ`; the field is
  `Fᵢ(lam) = aᵢ lamᵢ² + gᵢ(lam)` with `aᵢ ≥ 0` and `gᵢ(lam) ≥ 0` in every state.
- **Invariant region (checked):** the nonnegative orthant is forward-invariant, and every
  component is nondecreasing, for the continuous reaction ODE on `[0,T]` and for its
  explicit-Euler analogue with `h ≥ 0`.
- **Scalar monotonicity (checked):** the weighted scalar functional `∑ i, wᵢ lamᵢ`
  (`wᵢ ≥ 0`), in particular the unweighted `∑ i, lamᵢ`, is nondecreasing.
- **Geometry tie-in (checked):** the unweighted scalar functional of the state induced by a
  `CurvatureOperator` is exactly the geometry cluster's scalar-curvature contraction
  `scalarCurvature K m.toScalarContractionData`.
- **Missing bridge (explicit, unproved, not axiomatized):** the manifold curvature API
  (geometry cluster `CovariantDerivativeCurvatureStatement`), the diagonal Ricci-flow
  equation, the metric-curvature symmetry shadow, and the vanishing of the spatial
  diffusion. Conditional transfer theorems connect the checked ODE theorems to the tensor
  level under these hypotheses.

## 9. Honest boundaries and hand-off

| Boundary | Evidence | Follow-up |
| --- | --- | --- |
| Not Hamilton's ODE: exact `Rm#` coefficients depend on the Lie-algebra structure and are replaced by abstract nonnegative `g` | `ReactionField`, module docstrings | instantiate for a concrete Lie algebra; prove the quadratic reaction of `Rm#` is nonnegative (Böhm–Wilking cone invariance is research-level) |
| Spatial Laplacian `ΔRm` not modeled | `DiffusionVanishes : Prop` hypothesis of the bridge; mathlib has no tensor Laplacian | D3/D4 PDE lane; parabolic theory is a known D1 blocker |
| Manifold curvature API missing | `ManifoldCurvatureRealization := CovariantDerivativeCurvatureStatement` (geometry cluster, BLOCKED) | track upstream mathlib |
| The bridge has no inhabitant | `TensorRicciFlowODEBridge` is a `structure`; no instance/def constructed | a future task proves `TensorRicciFlowODERealization` for a concrete homogeneous model |
| The reaction model is one-sided: the nonpositive orthant is **not** invariant | checked `Fin 1` computation `0 < hamilton.eval (-1) 0` | sign-convention audit for D4 |

**Hand-off to D4-evolution-theorem.** Available now: a fully checked finite reaction ODE with
an invariant-region theorem, a scalar monotonicity theorem (continuous and explicit-Euler),
the geometry tie-in `scalarOfState_stateOfCurvature`, and an explicit bridge interface with
conditional tensor-level transfer theorems. Suggested D4 use: instantiate
`ReactionField.hamilton` on a concrete `Fin n` state, or use
`scalarCurvature_monotone_of_bridge` as the approximation-boundary-explicit template; the
counterexample/sign audit can start from `hamilton_eval_pos` and the `Fin 1` computations.

## 10. Files changed (all under the worktree; no shared source modified)

Authored:

- `Poincare/Longrun/CurvatureODE.lean`
- `Poincare/Longrun/CurvatureODE/State.lean`
- `Poincare/Longrun/CurvatureODE/Evolution.lean`
- `Poincare/Longrun/CurvatureODE/ScalarODE.lean`
- `Poincare/Longrun/CurvatureODE/Invariant.lean`
- `Poincare/Longrun/CurvatureODE/Monotonicity.lean`
- `Poincare/Longrun/CurvatureODE/Bridge.lean`
- `Audit/CurvatureODEAudit.lean`, `Audit/CurvatureODEAudit.out`
- `longrun/logs/*.log`

Bootstrap (copied/symlinked, byte-identical or read-only):

- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`
- `.lake/packages` → shared prebuilt mathlib packages
- `Poincare/Basic.lean`, `Poincare/Stage1/CurvatureAlgebra.lean`,
  `Poincare/Stage1/RiemannAdapter.lean`
- `Poincare/Longrun/Geometry.lean`, `Poincare/Longrun/Geometry/*.lean`

Mirrored result card (intended shared destination, outside the sandbox workspace):

- `longrun/results/D2-ricci-ode-cluster.md`
- `longrun/results/D2-ricci-ode-cluster.json`
