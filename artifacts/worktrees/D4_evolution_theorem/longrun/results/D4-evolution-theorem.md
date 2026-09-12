# D4-evolution-theorem — result card

> **Delivery note (sandbox).** The canonical shared path
> `/data3/guoshaoyang/workdir/lean_poincare/longrun/results/D4-evolution-theorem.md`
> is outside this session's `workspace-write` sandbox (workspace =
> `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D4_evolution_theorem`).
> This card and its JSON twin are mirrored at `<worktree>/longrun/results/`.
> **Integrator action:** copy the two mirrored files to the shared `longrun/results/`
> directory, or grant the worker write access to it. (Same delivery pattern as the
> accepted D2/D3 cards.)
>
> **Path note.** The task prompt names the worktree `…/worktrees/D4_evolution`; the
> current runtime snapshot assigns `…/worktrees/D4_evolution_theorem` (the `D4_evolution`
> name does not exist on disk). All work was done in `D4_evolution_theorem`.

- **Task id:** `D4-evolution-theorem`
- **Stage / lane:** D4 / builder (`requires_lean: true`)
- **Model:** `deepseek-v4.1-flash-expires-on-0910`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D4_evolution_theorem`
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2`
- **mathlib:** revision `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned prebuilt, reused read-only)
- **Status:** `done` — clean build exit 0, every authored file checks with empty output, the
  independent axiom probe reports 68/68 declarations with the single axiom set
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. One external delivery caveat (§10).

## 1. Consumed input

Both accepted predecessor cards were read in full. Their checked Lean sources were copied
**byte-identically** into this worktree (hashes match the cards exactly) and imported
unmodified.

| Consumed card | Lean module consumed | sha256 (== accepted card) |
| --- | --- | --- |
| `D2-ricci-ode-cluster` | `Poincare.Longrun.CurvatureODE.Evolution` | `d54e51c9ce01389d3a3273fb27f71fff2bf54e2e0821305a3b6c643581fa91e0` |
| `D2-ricci-ode-cluster` | `Poincare.Longrun.CurvatureODE.Monotonicity` | `466f7c713859f57a8670426e051b0f0685e0f6405254db1f7b80363ff889db0c` |
| `D2-ricci-ode-cluster` | `Poincare.Longrun.CurvatureODE.Bridge` | `8baeff93d0b3808ec293c29edccea5263b899036d834b44b32e31badae841645` |
| `D3-entropy-interface` | `Poincare.Longrun.Entropy.Functional` | `3128733f2fe542e528f407ee76b44cf4c06cb464eacf7297afa30ad89ef7c99f` |
| `D3-entropy-interface` | `Poincare.Longrun.Entropy.Certificate` | `c12f810405380e7b3c92b10d794df328885514bcbfab9f3e487644fd4ff50d3f` |
| `D3-entropy-interface` | `Poincare.Longrun.Entropy.Bridge` | `0d482a78b13c5ed190d75189b62b895ed1be5823ed12fb2a682b4d0162ddd471` |

The D2 cluster (`ReactionField`, `EvolutionRelation`, `DiscreteEvolution`, `eulerStep`,
`eval_nonneg`, `scalarOfState_monotone`, `le_left_of_hasDerivWithinAt_nonpos`,
`TensorRicciFlowODEBridge`) and the D3 cluster (`EntropyData`, `EntropyData.F`,
`HasConjugateWeight`, `AntitoneCertificate`, `ContinuousAntitoneCertificate`,
`WeightedCalculus`, `EntropyRegularityBridge`) are used directly; nothing in the consumed
sources was modified.

## 2. What was built

A new cluster `Poincare/Longrun/Evolution/` (7 modules + umbrella + independent audit):

| File | Lines | Declarations | sha256 |
| --- | --- | --- | --- |
| `Poincare/Longrun/Evolution/Gibbs.lean` | 177 | 10 | `dac3205e2e719ce5de17a46a4c2c25bf271098e96b8be88f5f438111ffc3d491` |
| `Poincare/Longrun/Evolution/Functional.lean` | 146 | 9 | `26b91bca6cbee6cfe79055e42188da284ab705218ffee37e239abd06336afd2c` |
| `Poincare/Longrun/Evolution/Continuous.lean` | 361 | 23 | `4ce14eda87aec4e4ad7519c37ccb8179a918e840521753f0c8541ac5e47841a1` |
| `Poincare/Longrun/Evolution/Discrete.lean` | 137 | 9 | `bf1beea5683d3b1d1318e633ca9f0fb50ea46b02d9dca3f9ce96168a38bdc6c8` |
| `Poincare/Longrun/Evolution/Counterexample.lean` | 222 | 13 | `2dd69ac0f7dc8021f1d5354f5683faaaf64702e99891602288101e830dabd394` |
| `Poincare/Longrun/Evolution/Bridge.lean` | 181 | 9 | `aa565d97d1b987631718d8e9f46d5b6d13aaf1d5f744938d320ae6413e7e7759` |
| `Poincare/Longrun/Evolution.lean` (umbrella) | 70 | — | `358dd1ada4daf0fcc9e5e9266e13720429509dbf1a8694ddb7a1b6e5d56c6e9a` |
| `Audit/EvolutionAudit.lean` (independent probe) | 105 | 68 audited | `255077bec4e293c672bb3dbfd14c3eebf8eb4e60bdc3eddbc7ce9d19f872c2d4` |

Total authored Lean: **1399 lines** (1294 cluster + 105 audit).

## 3. The main theorem

### 3.1 The finite functional

```lean
noncomputable def perelmanF (c lam : ι → ℝ) : ℝ :=
  ∑ i : ι, (c i + (lam i) ^ 2) * Real.exp (-(lam i))
```

`perelmanF c lam` is the finite-sum analogue of Perelman's `F`-functional
`∫ (R + |∇f|²) e^{-f} dV`: `c i` plays the role of the scalar-curvature density `R`,
`(lam i)²` the gradient-squared density `|∇f|²`, `lam i` the potential `f`, and
`exp (-(lam i))` the conjugate weight. It is **exactly** the `F`-functional of a finite
counting-measure D3 `EntropyData`:

```lean
theorem finiteReactionEntropyData_F (c lam : ι → ℝ) :
    EntropyData.F (finiteReactionEntropyData c lam) = perelmanF c lam
```

with `HasConjugateWeight` holding by construction and `EntropyData.FDissipation = 0`
(the finite model carries no Bochner/Ricci-Hessian dissipation; that is part of the
missing bridge). The D2 tie-in `perelmanF c 0 = scalarOfState c` holds at the zero state.

### 3.2 Exact dissipation identity (continuous time)

```lean
theorem hasDerivWithinAt_perelmanF (F : ReactionField ι) (c : ι → ℝ) {T : ℝ}
    {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj) {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun s => perelmanF c (traj s))
      (-∑ i : ι, F.eval (traj t) i * ((traj t i - 1) ^ 2 + (c i - 1)) *
        Real.exp (-(traj t i))) (Ici t) t
```

i.e. `d/dt perelmanF c (traj t) = -∑ i Fᵢ(lam) · ((lamᵢ - 1)² + (cᵢ - 1)) · e^{-lamᵢ}`.
The bracket `(lamᵢ - 1)² + (cᵢ - 1)` is exactly the finite analogue of the integrand
`R + |∇f|²` of the dissipation density.

### 3.3 Main monotonicity theorem (continuous time)

```lean
theorem perelmanF_antitone (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {T : ℝ} {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj) :
    ∀ ⦃s t : ℝ⦄, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t →
      perelmanF c (traj t) ≤ perelmanF c (traj s)
```

Proof: D2 `ReactionField.eval_nonneg` makes every reaction term `≥ 0`; `1 ≤ c i` makes the
bracket `≥ 0`; `exp > 0`; so the dissipation is `≤ 0`, and the D2 sign-preservation engine
`le_left_of_hasDerivWithinAt_nonpos` (mean value theorem) gives the comparison on `[s,t]`.
Consequences: `perelmanF_le_initial`, flat-spot rigidity `perelmanF_eq_on_Icc_of_eq_at`,
the D3 `EntropyData.F` form `finiteReactionEntropyData_F_antitone`, and the two-sided
statement `two_sided_monotonicity` (D4 functional nonincreasing while the D2 scalar
functional `scalarOfState` is nondecreasing).

### 3.4 Main monotonicity theorem (discrete / explicit Euler)

```lean
theorem perelmanF_antitone_discrete (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {h : ℝ} (hh : 0 ≤ h) {traj : ℕ → ι → ℝ} (ev : DiscreteEvolution F h traj) :
    ∀ ⦃m n : ℕ⦄, m ≤ n → perelmanF c (traj n) ≤ perelmanF c (traj m)
```

The one-step inequality is the monotonicity `gibbsTerm_step_le` of the one-variable Gibbs
term `(c + x²) e^{-x}` for `c ≥ 1`, so **no CFL restriction** beyond `h ≥ 0` is needed. The
strict version `perelmanF_step_lt` requires `1 < c i` and `0 < F.eval (traj n) i`.

### 3.5 D3 certificate consumption

Both theorems are packaged as genuine inhabitants of the accepted D3 structures:

| Declaration | D3 structure inhabited |
| --- | --- |
| `perelmanAntitoneCertificate` | `AntitoneCertificate {t // t ∈ Icc 0 T}` (continuous, interval) |
| `perelmanAntitoneCertificate_discrete` | `AntitoneCertificate ℕ` (discrete) |
| `continuousPerelmanCertificate` | `ContinuousAntitoneCertificate` (global flow) |

The D3 consequences `F_le_of_le`/`F_le_at`, `lower_le_value`, `eq_of_le_of_eq`,
`antitoneOn`, `F_le_initial`, `lower_le_initial` are re-derived for `perelmanF` in
`perelmanF_certificate_compare`, `perelmanF_certificate_lower`,
`perelmanF_certificate_compare_discrete`, `continuousPerelmanCertificate_antitoneOn`,
`continuousPerelmanCertificate_le_initial`. Non-vacuity witnesses:
`unitReactionField` + `unitGlobalFlow` (`traj t = t`, a nontrivial global flow) and
`unitDiscreteEvolution` (`traj n = n`).

## 4. Approximation boundary (explicit)

The cluster is a **finite-dimensional model**, not Perelman's monotonicity theorem. The
boundary is a named, unproved hypothesis interface in `Poincare.Longrun.Evolution.Bridge`:

```lean
def ContinuousPerelmanFMonotonicity (E : ℝ → EntropyData X μ) (T : ℝ) : Prop :=
  ∀ t ∈ Icc 0 T, (E t).F ≤ (E 0).F

def FiniteRepresentsContinuousPerelman (E) (c) (traj) (T) : Prop :=
  ∀ t ∈ Icc 0 T, (E t).F = perelmanF c (traj t)        -- the identification boundary

def FiniteMeshConvergence (mesh : ℕ → ℝ) (state : ℕ → ι → ℝ) (limit : ι → ℝ) : Prop :=
  Tendsto mesh atTop (𝓝 0) ∧ ∀ i, Tendsto (fun n => state n i) atTop (𝓝 (limit i))

structure PerelmanApproximation (E) (F) (T) (traj) (c) where
  hc : ∀ i, 1 ≤ c i
  evolves : EvolutionRelation F T traj
  identification : FiniteRepresentsContinuousPerelman E c traj T
```

Checked transfer statements (no inhabitant of the identification is constructed):

```lean
theorem continuousPerelmanFMonotone_of_approximation (A : PerelmanApproximation …) :
    ContinuousPerelmanFMonotonicity E T

theorem perelmanF_limit_le_of_discrete
    (hmono : ∀ n, perelmanF c (state n) ≤ perelmanF c (state 0))
    (hlim : Tendsto state atTop (𝓝 limit)) :
    perelmanF c limit ≤ perelmanF c (state 0)

theorem perelmanF_monotone_of_tensorBridge
    (B : TensorRicciFlowODEBridge …) (hc : ∀ i, 1 ≤ c i) :
    ∀ t ∈ Icc 0 T, perelmanF c (traj t) ≤ perelmanF c (traj 0)
```

`PerelmanEvolutionBoundary` bundles the identification, the D2
`TensorRicciFlowODERealization` and the D3 `EntropyRegularityBridge` as an explicit
statement-only interface; it has no inhabitant in the repository. What is **not** modeled:
the spatial Laplacian `ΔRm`/Bochner term, the manifold curvature API, the geometric
identification of `c` with scalar curvature, and the mesh-to-continuum identification.

## 5. Exact commands and exit codes

Environment for every command:

```text
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D4_evolution_theorem
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
```

### 5.1 Worktree bootstrap (reproducible)

```text
cp <poincare-lab>/{lakefile.toml,lake-manifest.json,lean-toolchain} .
mkdir -p .lake && ln -s <poincare-lab>/.lake/packages .lake/packages
cp -r <D3_entropy_interface>/Poincare .                  # Entropy, PDE, Geometry, Stage1, Basic
cp -r <D2_ricci_ode_cluster>/Poincare/Longrun/CurvatureODE Poincare/Longrun/
```

### 5.2 Clean build from an empty local build tree

`.lake/build` was deleted first (the local project oleans were rebuilt from source; the
pinned prebuilt mathlib in `.lake/packages` was reused read-only):

```text
rm -rf .lake/build
lake build Poincare
exit code: 0
# ✔ [8912/8913] Built Poincare.Longrun.Evolution (3.4s)
# Build completed successfully (8913 jobs).
```

Log: `longrun/logs/Poincare.clean.build.log` (zero `error`/`warning` lines).

### 5.3 `lake env lean` on every authored file

```text
lake env lean Poincare/Longrun/Evolution/Gibbs.lean          exit code: 0   (0 bytes output)
lake env lean Poincare/Longrun/Evolution/Functional.lean     exit code: 0   (0 bytes output)
lake env lean Poincare/Longrun/Evolution/Continuous.lean     exit code: 0   (0 bytes output)
lake env lean Poincare/Longrun/Evolution/Discrete.lean       exit code: 0   (0 bytes output)
lake env lean Poincare/Longrun/Evolution/Counterexample.lean exit code: 0   (0 bytes output)
lake env lean Poincare/Longrun/Evolution/Bridge.lean         exit code: 0   (0 bytes output)
lake env lean Poincare/Longrun/Evolution.lean                exit code: 0   (0 bytes output)
```

Per-file transcripts: `longrun/logs/*.compile.log` (all empty).

### 5.4 Independent `#print axioms` probe

```text
lake env lean Audit/EvolutionAudit.lean > Audit/EvolutionAudit.out 2>&1
exit code: 0
```

- `Audit/EvolutionAudit.lean` is **outside** the `Poincare/` library tree (it is not part of
  the umbrella import) and audits **68 principal declarations**.
- `grep -c "depends on axioms" Audit/EvolutionAudit.out` → **68**
- `grep -c "sorryAx" Audit/EvolutionAudit.out` → **0**
- The complete normalized parse (joining wrapped lines) gives exactly **one** axiom set for
  all 68 declarations: `[propext, Classical.choice, Quot.sound]`. No project axiom.

Representative lines:

```text
'Poincare.Longrun.Evolution.perelmanF_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Evolution.perelmanF_antitone_discrete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Evolution.hasDerivWithinAt_perelmanF' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Evolution.finiteReactionEntropyData_F' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Evolution.continuousPerelmanCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Evolution.squareTraj_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Evolution.continuousPerelmanFMonotone_of_approximation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Evolution.perelmanF_monotone_of_tensorBridge' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 6. Hygiene checks

```text
grep -rnE "^[[:space:]]*(sorry|axiom|unsafe|native_decide|proof_wanted)\b" \
  Poincare/Longrun/Evolution.lean Poincare/Longrun/Evolution/ Audit/EvolutionAudit.lean
→ no matches (exit 1)
```

The only textual occurrences of the forbidden words are the honesty docstrings that state
their absence (and the `#print axioms` directives of the audit). The consumed D2/D3 sources
are byte-identical copies (§1); no shared source was modified. `poincare-lab` was not
written; all new oleans are under the worktree-local `.lake/build/`.

## 7. Counterexample search and sign-convention audit

Every hypothesis of the main theorems is attacked by an explicit **checked** counterexample
in `Poincare/Longrun/Evolution/Counterexample.lean` (13 declarations).

### 7.1 `1 ≤ c i` cannot be weakened to `0 ≤ c i` — discrete one-step

`squareField : ReactionField (Fin 1)` is the D2 quadratic reaction `F(lam) = lam²`
(`a = 1`, `g = 0`). With `c = 0` and one explicit-Euler step `h = 1` from `lam = 1` to
`lam = 2`:

```lean
theorem perelmanF_step_increases_of_c_zero :
    perelmanF (fun _ : Fin 1 => 0) (fun _ => 1) <
      perelmanF (fun _ : Fin 1 => 0) (eulerStep squareField 1 (fun _ => 1))
```

i.e. `e^{-1} < 4 e^{-2}` (`exp_neg_one_lt_four_exp_neg_two`). The functional **increases**
by a factor `4/e > 1`, so the one-step inequality (and hence the discrete theorem) fails
without `1 ≤ c`.

### 7.2 `1 ≤ c i` cannot be weakened — full continuous trajectory

`squareTraj t = 1/(1-t)` is a genuine `EvolutionRelation squareField (1/2)` (checked
`squareTraj_evolution`), and along it

```lean
theorem squareTraj_counterexample :
    perelmanF (fun _ : Fin 1 => 0) (squareTraj 0) <
      perelmanF (fun _ : Fin 1 => 0) (squareTraj (1/2))
```

i.e. the `c = 0` functional increases from `e^{-1}` to `4 e^{-2}` on `[0, 1/2]`. This is a
full continuous-time counterexample to `perelmanF_antitone` with `c = 0`. The pointwise
form is `perelmanF_dissipation_pos_at_c_zero`: the exact dissipation at `c = 0`,
`lam = 1` equals `e^{-1} > 0`.

### 7.3 `0 ≤ h` and nonnegative reactions are necessary

With a negative step `h = -1` (the discrete shadow of a negative reaction, which the D2
`ReactionField` structure forbids via `g_nonneg`):

```lean
theorem perelmanF_step_increases_of_negative_step :
    perelmanF (fun _ : Fin 1 => 1) (fun _ => 1) <
      perelmanF (fun _ : Fin 1 => 1) (eulerStep squareField (-1) (fun _ => 1))
```

i.e. `2 e^{-1} < 1`. So both `0 ≤ h` and the D2 nonnegativity `F.eval ≥ 0` are needed.

### 7.4 The threshold `c = 1` is sharp, and the flat spot is real

```lean
theorem gibbsTerm_deriv_at_one_zero : deriv (gibbsTerm 1) 1 = 0
theorem gibbsTerm_one_two_lt : gibbsTerm 1 2 < gibbsTerm 1 1   -- 5 e^{-2} < 2 e^{-1}
theorem perelmanF_one_two_le : perelmanF (fun _ => 1) (fun _ => 2) ≤ perelmanF (fun _ => 1) (fun _ => 1)
```

At `c = 1` the derivative vanishes at the flat spot `x = 1`, but the function still strictly
decreases through it; the theorem still applies at the threshold (`perelmanF_one_two_le`),
so the counterexamples above are exactly at the boundary.

### 7.5 Sign convention vs. Perelman's `F`

Perelman's `F` is nondecreasing, with `dF/dt = 2∫|Ric + ∇²f|² e^{-f} ≥ 0`. The D4
functional is **nonincreasing**: the finite model couples the Gibbs weight `e^{-lam}` to
the curvature state itself, so growth of curvature shrinks the weight. The two directions
are displayed side by side in `two_sided_monotonicity` (D4 decreasing, D2 `scalarOfState`
increasing). This is a genuine sign-convention difference, documented in the module
docstrings and the umbrella; **nothing in this cluster is claimed to be Perelman's
monotonicity theorem**.

## 8. Honest boundaries and hand-off

| Boundary | Evidence | Follow-up |
| --- | --- | --- |
| Finite sum, not an integral over a manifold | `perelmanF`; `FiniteRepresentsContinuousPerelman` (unproved `Prop`) | prove the discretization identification for a concrete manifold/grid |
| `c` is abstract data, not scalar curvature | `finiteReactionEntropyData` takes `c` as data | instantiate `c i = ricci K eᵢ eᵢ` via the D2 geometry cluster and evolve it |
| No spatial Laplacian / Bochner dissipation | `FDissipation = 0`; `PerelmanEvolutionBoundary` re-exports the D3 `EntropyRegularityBridge` unproved | D3/D4 PDE lane; parabolic theory is a known blocker |
| Functional is nonincreasing, opposite to Perelman's `F` | `two_sided_monotonicity`; §7.5 | a future model with the conjugate measure evolution and Bochner identity |
| Identification/mesh limit unproved | `FiniteRepresentsContinuousPerelman`, `FiniteMeshConvergence` have no inhabitant | construct a convergent discretization |
| Tensor bridge has no inhabitant | `perelmanF_monotone_of_tensorBridge` is conditional on the D2 `TensorRicciFlowODEBridge` | D2 card's own hand-off |

**Hand-off to `D4-counterexample-audit`.** The verifier should attack: (i) the exact
dissipation identity `hasDerivWithinAt_perelmanF` (try a state with `c i < 1` and a
trajectory through it — §7.1/§7.2 are the intended witnesses); (ii) the D3 certificate
inhabitants `perelmanAntitoneCertificate` / `continuousPerelmanCertificate` (check the
`lower_le` bound `0` and the `dissipation_nonpos` field); (iii) the limit passage
`perelmanF_limit_le_of_discrete` (check the `NeBot atTop` instance and the `le_of_tendsto'`
orientation); (iv) the strict-decrease hypotheses `perelmanF_step_lt` (`1 < c i`, `h > 0`,
`0 < F.eval` — all three are needed). The independent probe `Audit/EvolutionAudit.lean`
can be rerun verbatim.

## 9. Files changed (all under the worktree; no shared source modified)

Authored:

- `Poincare/Longrun/Evolution/Gibbs.lean`
- `Poincare/Longrun/Evolution/Functional.lean`
- `Poincare/Longrun/Evolution/Continuous.lean`
- `Poincare/Longrun/Evolution/Discrete.lean`
- `Poincare/Longrun/Evolution/Counterexample.lean`
- `Poincare/Longrun/Evolution/Bridge.lean`
- `Poincare/Longrun/Evolution.lean`
- `Audit/EvolutionAudit.lean`, `Audit/EvolutionAudit.out`
- `longrun/logs/*.log`, `longrun/results/D4-evolution-theorem.{md,json}`

Bootstrap (copied/symlinked, byte-identical or read-only):

- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`
- `.lake/packages` → shared prebuilt mathlib packages (symlink)
- `Poincare/Basic.lean`, `Poincare/Stage1/{CurvatureAlgebra,RiemannAdapter}.lean`
- `Poincare/Longrun/Geometry.lean`, `Poincare/Longrun/Geometry/*.lean`
- `Poincare/Longrun/PDE/*.lean`, `Poincare/Longrun/Entropy/*.lean` (D3)
- `Poincare/Longrun/CurvatureODE.lean`, `Poincare/Longrun/CurvatureODE/*.lean` (D2)

## 10. Sandbox / delivery note

The canonical shared control-plane directory
`/data3/guoshaoyang/workdir/lean_poincare/longrun/results/` is outside this session's
`workspace-write` sandbox. This card and its JSON twin are therefore written at
`longrun/results/D4-evolution-theorem.{md,json}` inside the worktree. **Integrator action:**
copy the two mirrored files to the shared `longrun/results/` directory, or grant the worker
write access to it.
