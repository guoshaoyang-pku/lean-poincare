# D4-counterexample-audit — result card

> **Delivery note (sandbox).** The canonical shared path
> `/data3/guoshaoyang/workdir/lean_poincare/longrun/results/D4-counterexample-audit.md`
> is outside this session's `workspace-write` sandbox (workspace =
> `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D4_counterexample_audit`).
> This card and its JSON twin are mirrored at `<worktree>/longrun/results/`.
> **Integrator action:** copy the two mirrored files to the shared `longrun/results/`
> directory (same delivery pattern as the accepted D2/D3/D4 cards).

- **Task id:** `D4-counterexample-audit`
- **Stage / lane:** D4 / verifier (`requires_lean: true`)
- **Model:** `deepseek-v4.1-flash-expires-on-0910`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D4_counterexample_audit`
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (lake 5.0.0-src+6a10ac8)
- **mathlib:** pinned prebuilt packages reused read-only via `.lake/packages` symlink
  (revision `7974e751bece493b6ff508039423ca9fa2452fa8`, same as the D4 card)
- **Status:** `done` — independent verifier compiles with exit 0; 58/58 audited declarations
  have the single axiom set `[propext, Classical.choice, Quot.sound]`; no `sorryAx`; the
  promoted 68-declaration audit is reproduced independently. **One overstrong hypothesis
  family found and corrected; no false statement found.**

## 1. Consumed input (promoted D4 interfaces)

The verifier imports **only** `Poincare.Longrun.Evolution` (the promoted umbrella). The
whole `Poincare/` source tree was copied byte-identically from
`worktrees/D4_evolution_theorem`, and the promoted D4 sources match the D4 card's hashes
exactly:

| Promoted module | sha256 (matches D4 card) |
| --- | --- |
| `Poincare/Longrun/Evolution/Gibbs.lean` | `dac3205e2e719ce5de17a46a4c2c25bf271098e96b8be88f5f438111ffc3d491` |
| `Poincare/Longrun/Evolution/Functional.lean` | `26b91bca6cbee6cfe79055e42188da284ab705218ffee37e239abd06336afd2c` |
| `Poincare/Longrun/Evolution/Continuous.lean` | `4ce14eda87aec4e4ad7519c37ccb8179a918e840521753f0c8541ac5e47841a1` |
| `Poincare/Longrun/Evolution/Discrete.lean` | `bf1beea5683d3b1d1318e633ca9f0fb50ea46b02d9dca3f9ce96168a38bdc6c8` |
| `Poincare/Longrun/Evolution/Counterexample.lean` | `2dd69ac0f7dc8021f1d5354f5683faaaf64702e99891602288101e830dabd394` |
| `Poincare/Longrun/Evolution/Bridge.lean` | `aa565d97d1b987631718d8e9f46d5b6d13aaf1d5f744938d320ae6413e7e7759` |
| `Poincare/Longrun/Evolution.lean` (umbrella) | `358dd1ada4daf0fcc9e5e9266e13720429509dbf1a8694ddb7a1b6e5d56c6e9a` |

The consumed D2 (`CurvatureODE/{Evolution,Monotonicity,Bridge}.lean`) and D3
(`Entropy/{Functional,Certificate,Bridge}.lean`) copies inside the D4 worktree were also
hash-checked against the accepted D2/D3 worktrees and are byte-identical.

## 2. What the verifier contains

`Audit/CounterexampleAudit.lean` (565 lines, sha256
`816650d3da8c913e82df63062a25943b19162c88678b82277e68d54efc27819c`), single import
`Poincare.Longrun.Evolution`, fresh namespace `D4Audit`:

1. fresh-namespace restatements of `perelmanF_antitone`, `perelmanF_antitone_discrete`,
   `hasDerivWithinAt_perelmanF`, `two_sided_monotonicity`, with non-vacuity and strictness
   witnesses;
2. independent counterexamples to weakened hypotheses (below);
3. a **corrected theorem** weakening `1 < c i` to `1 ≤ c i` in the strict-decrease chain;
4. non-vacuity witnesses for the statement-only approximation boundary;
5. `#print axioms` for 46 audit declarations and 12 promoted declarations.

`Audit/PromotedEvolutionAudit.lean` is a byte-identical copy of the D4 cluster's own
68-declaration probe (`sha256 255077bec4e293c672bb3dbfd14c3eebf8eb4e60bdc3eddbc7ce9d19f872c2d4`),
rerun independently in this worktree.

## 3. Verdict

**No false statement was found.** Every promoted declaration audited is kernel-checked, and
its axiom cone is exactly `[propext, Classical.choice, Quot.sound]` (no project axiom, no
`sorryAx`). The audit found **one overstrong hypothesis family** (not a falsity), and
confirmed that the remaining hypotheses are sharp.

| # | Statement | Verdict | Evidence |
| --- | --- | --- | --- |
| 1 | `perelmanF_antitone` (`1 ≤ c i`) | TRUE, hypothesis sharp | re-checked; fails at `c = 1/2 ≥ 0` |
| 2 | `perelmanF_antitone_discrete` (`1 ≤ c i`, `0 ≤ h`) | TRUE, hypotheses sharp | re-checked; fails at `c = 1/2`, and at `h = -1` |
| 3 | `hasDerivWithinAt_perelmanF` | TRUE | re-checked; concrete derivative value `-1` at `t=0` reproduced |
| 4 | `perelmanF_nonneg` (`0 ≤ c i`) | TRUE, hypothesis sharp | fails at `c = -1`, `lam = 0` (value `-1`) |
| 5 | `perelmanF_step_lt` (`1 < c i`) | TRUE but **OVERSTRONG** | `1 ≤ c i` suffices; corrected theorem proved |
| 6 | `gibbsTerm_strictAnti` (`1 < c`) | TRUE but **OVERSTRONG** | `1 ≤ c` suffices; `gibbsTerm_strictAnti_of_one_le` proved |
| 7 | `gibbsTerm_step_lt` (`1 < c`) | TRUE but **OVERSTRONG** | `1 ≤ c` suffices; `gibbsTerm_step_lt_of_one_le` proved |
| 8 | `0 ≤ h` in the discrete theorem | NECESSARY | `counterexample_negative_step` |
| 9 | D2 reaction nonnegativity `F.eval ≥ 0` | NECESSARY | `weak_discrete_monotonicity_false`, `no_sign_continuous_monotonicity_false` |
| 10 | `0 < h` and `0 < F.eval` in `perelmanF_step_lt` | NECESSARY | `strict_step_needs_pos_step`, `strict_step_needs_pos_reaction` |
| 11 | `ContinuousPerelmanFMonotonicity` transfer | non-vacuous but content-free | `PerelmanApproximation` inhabited by the finite datum itself |
| 12 | `FiniteMeshConvergence`, `PerelmanEvolutionBoundary`, `TensorRicciFlowODEBridge` | statement-only interfaces | honest boundary, no inhabitant claimed; not false |
| 13 | Sign convention (functional nonincreasing, opposite to Perelman's `F`) | documented, not a defect | cluster explicitly disclaims Perelman's theorem |

## 4. The overstrong statement and its correction

`perelmanF_step_lt` assumes `∀ i, 1 < c i`, and its proof goes through
`gibbsTerm_step_lt`/`gibbsTerm_strictAnti`, which assume `1 < c`. This is **stronger than
necessary**: for `c = 1` the one-variable term is still strictly antitone, because

```text
deriv (gibbsTerm 1) x = -((x - 1)^2) * exp(-x),
```

which vanishes only at the isolated point `x = 1`. Hence `gibbsTerm c` is `StrictAnti`
already for `1 ≤ c`, and the whole strict-decrease chain works with `1 ≤ c i`.

Corrected statements, all proved in `D4Audit` (no new axiom):

```lean
theorem gibbsTerm_strictAnti_of_one_le (c : ℝ) (hc : 1 ≤ c) : StrictAnti (gibbsTerm c)

theorem gibbsTerm_step_lt_of_one_le {c x u : ℝ} (hc : 1 ≤ c) (hu : 0 < u) :
    gibbsTerm c (x + u) < gibbsTerm c x

theorem perelmanF_step_lt_of_one_le (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {h : ℝ} (hh : 0 < h) {traj : ℕ → ι → ℝ} (ev : DiscreteEvolution F h traj) {n : ℕ}
    {i : ι} (hi : 0 < F.eval (traj n) i) :
    perelmanF c (traj (n + 1)) < perelmanF c (traj n)
```

The correction is not vacuous: `strict_step_positive_control` applies it at `c = 1`, where
the original `perelmanF_step_lt` is inapplicable (`1 < 1` is false), and obtains strict
decrease for the explicit-Euler trajectory `sqTraj` of the square reaction field.

## 5. Counterexamples (all kernel-checked)

| Finding | Lean declaration | Content |
| --- | --- | --- |
| `1 ≤ c` cannot be weakened to `0 ≤ c` (discrete) | `counterexample_discrete_c_half` | `c = 1/2`, square reaction, one step `h=1` from `lam=1` to `lam=2`: `(3/2)e^{-1} < (9/2)e^{-2}` |
| `1 ≤ c` cannot be weakened to `0 ≤ c` (continuous) | `counterexample_continuous_c_half` | along the genuine ODE solution `squareTraj t = 1/(1-t)` on `[0,1/2]` (`counterexample_continuous_c_half_is_evolution`), the `c=1/2` functional increases |
| `0 ≤ h` necessary | `counterexample_negative_step` | `c=1`, `lam=2`, `h=-1` sends the state to `-2`; `5e^{-2} < 5e^{2}` |
| reaction nonnegativity necessary (discrete) | `weak_discrete_monotonicity_false` | `G ≡ -1`, `h=1`, `c=1`: functional increases `2e^{-1} → 1` |
| reaction nonnegativity necessary (continuous) | `no_sign_continuous_monotonicity_false` | `lam(t)=1-t` with reaction `-1`, `c=1`: functional increases `2e^{-1} → 1` |
| `0 < h` necessary for strict decrease | `strict_step_needs_pos_step` | `h=0` makes the Euler step the identity, so the strict inequality is impossible |
| `0 < F.eval` necessary for strict decrease | `strict_step_needs_pos_reaction` | canonical field at the zero state has `F.eval = 0`; the functional is constant |
| `0 ≤ c` necessary for nonnegativity | `perelmanF_nonneg_sharp` | `c=-1`, `lam=0` gives `perelmanF = -1 < 0` |

The builder's own witnesses used `c = 0`; the `c = 1/2` witnesses above are strictly
stronger: the threshold `1 ≤ c` already fails for a **positive** sub-threshold `c`, so
`0 ≤ c` is not merely insufficient at the boundary but on an open region below it.

## 6. Non-vacuity and limit-passage checks

- `perelmanApproximation_nonvacuous`: `PerelmanApproximation` is inhabited by taking the
  continuous family `E t := finiteReactionEntropyData c (traj t)`; the identification field
  is `finiteReactionEntropyData_F`. Hence
  `continuousPerelmanFMonotone_of_approximation` is not vacuous.
- `transfer_nonvacuous`: the transfer theorem is applied to the constant reaction field and
  the nontrivial global flow `t ↦ t`, producing a genuine
  `ContinuousPerelmanFMonotonicity` conclusion. **Caveat:** this canonical inhabitant
  identifies the continuous functional with the finite sum, so it carries no manifold
  content — exactly the boundary the D4 card documents.
- `finiteMeshConvergence_nonvacuous`: `FiniteMeshConvergence` is inhabited by mesh
  `1/(n+1) → 0` and a constant state.
- `limit_passage_sanity`: `perelmanF_limit_le_of_discrete` is exercised with the nontrivial
  convergent sequence `state n = 1 - 1/(n+1) → 1` (finite comparison proved for every `n`),
  confirming the `le_of_tendsto'` orientation.
- `certificate_lower_bound_zero`, `audit_certificate_compare`,
  `audit_continuous_certificate`: the D3 certificate inhabitants have the advertised lower
  bound `0` and produce the advertised comparison/initial-bound consequences.
- `dissipation_sanity`: along `t ↦ t` with `c=1`, the exact dissipation identity gives
  derivative `-1` at `t = 0`.

## 7. Axiom audit (exact commands and exit codes)

Environment for every command:

```text
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D4_counterexample_audit
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
```

### 7.1 Clean library build in this worktree

```text
lake build Poincare
exit code: 0
# Build completed successfully (8913 jobs).
```

Log: `longrun/logs/audit.build.log`. The local `.lake/build` was created from scratch in
this worktree; the shared prebuilt mathlib in `.lake/packages` was reused read-only.

### 7.2 Independent verifier

```text
lake env lean Audit/CounterexampleAudit.lean > longrun/logs/CounterexampleAudit.out 2>&1
exit code: 0
grep -c "depends on axioms" longrun/logs/CounterexampleAudit.out   -> 58
grep -c "sorryAx"           longrun/logs/CounterexampleAudit.out   -> 0
```

Normalized parse (joining wrapped lines): all **58** declarations report exactly one axiom
set, `[propext, Classical.choice, Quot.sound]`.

### 7.3 Promoted 68-declaration probe rerun

```text
lake env lean Audit/PromotedEvolutionAudit.lean > longrun/logs/PromotedEvolutionAudit.out 2>&1
exit code: 0
grep -c "depends on axioms" longrun/logs/PromotedEvolutionAudit.out -> 68
grep -c "sorryAx"           longrun/logs/PromotedEvolutionAudit.out -> 0
```

All **68** declarations report exactly `[propext, Classical.choice, Quot.sound]`.

Representative lines from `CounterexampleAudit.out`:

```text
'D4Audit.perelmanF_step_lt_of_one_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'D4Audit.counterexample_continuous_c_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Evolution.perelmanF_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Evolution.perelmanF_step_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Evolution.perelmanF_monotone_of_tensorBridge' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 8. Hygiene

```text
grep -rnE "^[[:space:]]*(sorry|axiom|unsafe|native_decide|proof_wanted)\b" \
  Audit/CounterexampleAudit.lean Poincare/
-> no matches (exit 1)
```

The verifier uses no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`; it
imports only the promoted umbrella module.

## 9. Residual boundaries (not defects; hand-off)

1. **Overstrong hypotheses to fix upstream.** `perelmanF_step_lt`, `gibbsTerm_strictAnti`
   and `gibbsTerm_step_lt` should be restated with `1 ≤ c` (or the corrected declarations
   here promoted). No downstream result breaks; this is a strengthening.
2. **Tensor bridge has no inhabitant.** `perelmanF_monotone_of_tensorBridge` is conditional
   on the D2 `TensorRicciFlowODEBridge`; no inhabitant was constructed (it needs manifold
   data). The transfer is therefore conditional, not vacuous.
3. **Approximation boundary.** `FiniteRepresentsContinuousPerelman` is satisfiable only by
   the trivial finite identification here; a genuine discretization theorem remains open.
4. **No Bochner/Laplacian content.** `FDissipation = 0` for the finite datum; the spatial
   Laplacian/Bochner term is not modeled.
5. **Sign convention.** The functional is nonincreasing, opposite to Perelman's
   `F`-monotonicity; the cluster documents this and does not claim Perelman's theorem.

## 10. Files produced (all under the worktree)

- `Audit/CounterexampleAudit.lean` — independent verifier (565 lines)
- `Audit/PromotedEvolutionAudit.lean` — verbatim rerun of the promoted probe
- `longrun/logs/audit.build.log` — clean library build log
- `longrun/logs/CounterexampleAudit.out` — verifier output (58 axiom lines)
- `longrun/logs/PromotedEvolutionAudit.out` — promoted probe output (68 axiom lines)
- `longrun/results/D4-counterexample-audit.md`, `.json` — this card (mirror)
- `Poincare/` — byte-identical copy of the promoted library sources
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.lake/packages` symlink
