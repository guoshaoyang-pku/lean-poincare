# D8-verifier-evolution-sharp — result card

- **Task id:** `D8-verifier-evolution-sharp`
- **Stage / lane:** D8 / verifier (`requires_lean: true`)
- **Model:** `deepseek-v4.1-flash-expires-on-0910`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D8-verifier-evolution-sharp`
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (lake `5.0.0-src+6a10ac8`,
  commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`)
- **mathlib:** pinned prebuilt packages reused read-only via `.lake -> release/.lake`
  (revision `7974e751bece493b6ff508039423ca9fa2452fa8`, the D6/D7 pin)
- **Scaffold:** `cp -a ../D7-evolution-sharp-restatement/. .` — the prescribed
  `cp -al` fails in this sandbox with `Invalid cross-device link` (`link(2)` is emulated
  across the workspace overlay boundary; verified with a minimal `ln` test, exactly as the
  D7 card and the sibling `VERIFIER-D7-adversarial-audit-d2d3` report). This is a process
  deviation only: `diff -rq --exclude=.lake --exclude=AuditSharp . ../D7-evolution-sharp-restatement`
  reports **0 differences**, and every file added by this task lives under `AuditSharp/`
  (plus this card).
- **Status:** `done`
- **Verdict summary:** **2 CONFIRMED, 1 STILL_OVERSTRONG, 0 VACUOUS, 0 COUNTEREXAMPLE.**

## 1. Scope

The consumed artefact is `D7-evolution-sharp-restatement`, which restated the three
overstrong D4 strict-decrease theorems at the audit's sharp bound `1 ≤ c` (finding #5–#7):

| # | D7 sharpened theorem | sharpened hypothesis | promoted original |
|---|---|---|---|
| T1 | `Poincare.D7.EvolutionSharp.gibbsTerm_strictAnti_of_one_le` | `1 ≤ c` | `Poincare.Longrun.Evolution.gibbsTerm_strictAnti` (`1 < c`) |
| T2 | `Poincare.D7.EvolutionSharp.gibbsTerm_step_lt_of_one_le` | `1 ≤ c`, `0 < u` | `Poincare.Longrun.Evolution.gibbsTerm_step_lt` (`1 < c`) |
| T3 | `Poincare.D7.EvolutionSharp.perelmanF_step_lt_of_one_le` | `∀ i, 1 ≤ c i`, `0 < h`, `0 < F.eval (traj n) i` | `Poincare.Longrun.Evolution.perelmanF_step_lt` (`∀ i, 1 < c i`) |

All verifier files are new and live under `AuditSharp/`. Nothing in the D7/D6 scaffold was
modified (hash/diff check in §6.5).

## 2. Goal 1 — fresh-namespace re-derivation from the release interfaces

`AuditSharp/ReDerive.lean` imports **only** `Poincare.Longrun.Evolution` (the promoted D4
release interface) and `Lean.Util.CollectAxioms`; it does **not** import any `Poincare.D7.*`
module. The three sharpened statements are re-proved in the fresh namespace `AuditSharp`:

| fresh re-derivation | D7 artefact | type match | exit |
|---|---|---|---|
| `AuditSharp.audit_gibbsTerm_strictAnti_one` | `Poincare.D7.EvolutionSharp.gibbsTerm_strictAnti_one` | `StrictAnti (gibbsTerm 1)` | 0 |
| `AuditSharp.audit_gibbsTerm_strictAnti_of_one_le` | `…gibbsTerm_strictAnti_of_one_le` | `∀ c, 1 ≤ c → StrictAnti (gibbsTerm c)` | 0 |
| `AuditSharp.audit_gibbsTerm_step_lt_of_one_le` | `…gibbsTerm_step_lt_of_one_le` | `∀ {c x u}, 1 ≤ c → 0 < u → gibbsTerm c (x+u) < gibbsTerm c x` | 0 |
| `AuditSharp.audit_perelmanF_step_lt_of_one_le` | `…perelmanF_step_lt_of_one_le` | `∀ {ι} [Fintype ι] (F) {c}, (∀ i, 1 ≤ c i) → 0 < h → DiscreteEvolution F h traj → 0 < F.eval (traj n) i → perelmanF c (traj (n+1)) < perelmanF c (traj n)` | 0 |

The threshold case `c = 1` is re-proved from scratch: the derivative
`deriv (gibbsTerm 1) x = -((x-1)²) e^{-x}` is strictly negative off the isolated flat spot
`x = 1`, `strictAntiOn_of_deriv_neg` gives strict antitonicity on `(-∞,1]` and `[1,∞)`, and
the two one-sided results glue at `x = 1`. The `1 < c` case consumes the promoted release
theorem `Poincare.Longrun.Evolution.gibbsTerm_strictAnti`. T3 reuses the promoted non-strict
`gibbsTerm_step_le` for all non-strict components and the fresh one-variable theorem for the
strict component (`Finset.sum_lt_sum`).

The old statements are also pinned and recovered:

- closed `Prop`s `AuditGibbsStrictAntiSharp/Old`, `AuditGibbsStepLtSharp/Old`,
  `AuditPerelmanFStepLtSharp/Old`;
- implications `audit_gibbsStrictAnti_old_of_sharp`, `audit_gibbsStepLt_old_of_sharp`,
  `audit_perelmanFStepLt_old_of_sharp` (the discarded strictness enters only through
  `le_of_lt`);
- `audit_*_promoted` pin the promoted declarations to the old statements, and
  `audit_*_old_recovered` re-derive the promoted statements from the fresh sharpened ones.

Non-vacuity is witnessed in the same file: `audit_gibbsTerm_strict_decrease_at_one`
(`2 e^{-1} < 1`), `audit_gibbsTerm_step_lt_at_one`, and
`audit_perelmanF_strict_decrease_at_one` with `audit_perelmanF_witness_values`
(`5 e^{-2}` at time 1, `2 e^{-1}` at time 0) plus the independent numerical check
`audit_perelmanF_strict_decrease_by_values`.

**Result: all three D7 statements are true exactly as stated; the fresh proofs are
independent of the D7 artefact.**

## 3. Goal 3 — the sharpened hypotheses are strictly weaker than the originals

`AuditSharp/StrictlyWeaker.lean` imports `Poincare.D7.EvolutionSharp.FunctionalSharp` (the
object under verification) and exhibits, for each theorem, a compiling witness where the
sharpened hypothesis holds, the promoted hypothesis fails, and the sharpened conclusion is a
genuine non-vacuous instance — computed **by values** (independent of the D7 proof) *and*
produced by the D7 theorem itself.

| theorem | witness | new hypothesis | old hypothesis | non-vacuous conclusion |
|---|---|---|---|---|
| T1 | `c = 1` | `new_hyp_one_le_one : 1 ≤ 1` | `old_hyp_not_one_lt_one : ¬ 1 < 1` | `strictAnti_witness_by_values : gibbsTerm 1 1 < gibbsTerm 1 0` (`2 e^{-1} < 1`); D7 applies: `gibbsTerm_strictAnti_strictly_weaker` |
| T2 | `c = 1, x = 0, u = 1` | same | same | `gibbsTerm_step_lt_witness_by_values`; D7 applies: `gibbsTerm_step_lt_strictly_weaker` |
| T3 | `c ≡ 1` on `Fin 1`, `squareField`, trajectory `1 → 2`, `h = 1` | `weakWitness_c_new` | `weakWitness_c_old_fails` | `weakWitness_values` (`5 e^{-2} < 2 e^{-1}`), `weakWitness_strict_decrease_by_values`; D7 applies: `weakWitness_strict_decrease`, `perelmanF_step_lt_strictly_weaker(_by_values)` |

The hypothesis sets are strictly nested, not merely non-equal pointwise:
`scalar_hypothesis_strictly_weaker` (`∃ c, 1 ≤ c ∧ ¬ 1 < c`),
`family_hypothesis_strictly_weaker` (`Fin 1`, `c ≡ 1`),
`family_hypothesis_strictly_weaker_two` (`Fin 2`, `c = (1,2)`). The D7 theorem recovers the
promoted statements whenever the promoted hypothesis holds
(`gibbsTerm_strictAnti_promoted_recovered`, `gibbsTerm_step_lt_promoted_recovered`,
`perelmanF_step_lt_promoted_recovered`).

## 4. Goal 2 — further-weakening attacks

`AuditSharp/Sharpness.lean` imports **only** `Poincare.Longrun.Evolution` (plus the audit
runtime) and attacks every hypothesis.

### 4.1 Refuted weakenings (compiling counterexamples)

| attacked hypothesis | attempted weakening | verdict | evidence declaration |
|---|---|---|---|
| T1/T2 `1 ≤ c` | `0 ≤ c` | **refuted** | `audit_gibbsTerm_half_one_lt_two` (`3 e^{-1} < 9 e^{-2}` at `c = 1/2`), `audit_strictAnti_c_nonneg_false` |
| T1/T2 `1 ≤ c` | any relaxation (all `c < 1`) | **refuted** | `audit_not_strictAnti_of_lt_one : ∀ c, c < 1 → ¬ StrictAnti (gibbsTerm c)` — the hypothesis set is exactly `{c \| 1 ≤ c}`; `audit_not_step_lt_of_lt_one` gives the corresponding `x, u` witness for the step form |
| T2 `0 < u` | `0 ≤ u` | **refuted** | `audit_step_lt_u_nonneg_false` (`u = 0`) |
| T3 `∀ i, 1 ≤ c i` | `∀ i, 0 ≤ c i` | **refuted** | `auditTwoTraj_increases`, `audit_perelmanF_c_nonneg_false`: `c = (1,0)`, both components stepped `1 → 2`, functional **increases** (`3 e^{-1} < 9 e^{-2}`) |
| T3 `∀ i, 1 ≤ c i` | only the reacting component (pointwise) | **refuted** | `audit_perelmanF_c_pointwise_false` (same two-component counterexample) |
| T3 `0 < h` | `0 ≤ h` | **refuted** | `audit_perelmanF_h_nonneg_false` (`h = 0`, constant trajectory) |
| T3 `0 < F.eval (traj n) i` | `0 ≤ F.eval (traj n) i` | **refuted** | `audit_perelmanF_reaction_nonneg_false` (zero state of the canonical reaction field) |
| T3 D2 reaction sign | drop `F.eval ≥ 0` | **refuted** | `audit_perelmanF_needs_reaction_sign`: `G = (1,-1)`, trajectory `n ↦ (n,-n)`, `c ≡ 1`, `h = 1`; functional increases (`2 < 2 e^{-1} + 2 e`) |

The general `c < 1` failure is the strongest possible sharpness statement for T1/T2: no
state-independent condition weaker than `1 ≤ c` can imply either conclusion.

### 4.2 Successful weakenings (the residual overstrength of T3)

The following strictly more general statements compile, so the D7 hypotheses are **not** the
weakest sufficient conditions:

| successful weakening | theorem | strictness witness |
|---|---|---|
| curvature bound only on the **active support** `∀ j, 0 < F.eval (traj n) j → 1 ≤ c j` | `audit_perelmanF_step_lt_of_active_support` | `audit_active_support_strictly_weaker`: `auditSupportField` has `eval = (0,1)`, `auditSupportC = (-100,1)`; the uniform D7 hypothesis fails (`auditSupportC_uniform_fails`), the active-support hypothesis holds (`auditSupportC_active`), and the conclusion is the genuine strict decrease `-100 + 2 e^{-1} < -99` (also recomputed by values: `audit_support_value_zero/one`, `audit_active_support_by_values`) |
| recurrence only at the single step `n` | `audit_perelmanF_step_lt_of_single_step` | the D7 theorem is the instance `y := traj (n+1)`; the full `DiscreteEvolution` is used only at `n` |
| strictly reacting component need only exist | `audit_perelmanF_step_lt_of_exists_reaction` | `∃ i, 0 < F.eval (traj n) i` replaces the fixed `i`; the conclusion does not mention `i` |

The active-support witness is non-vacuous: the uniform bound fails at the inactive
component, yet the conclusion holds. This is a genuine strict generalization, not a
re-encoding: `∀ i, 1 ≤ c i` implies the active-support hypothesis, and the witness instance
shows the converse fails.

## 5. Verdicts per theorem

| theorem | verdict | rationale |
|---|---|---|
| **T1** `gibbsTerm_strictAnti_of_one_le` | **CONFIRMED** | Re-derived independently from the release interface (`AuditSharp.ReDerive.audit_gibbsTerm_strictAnti_of_one_le`); `1 ≤ c` is **exactly** sharp (`audit_not_strictAnti_of_lt_one` refutes every `c < 1`); the conclusion is non-vacuous at `c = 1` (`2 e^{-1} < 1`); the hypothesis is strictly weaker than `1 < c` (`gibbsTerm_strictAnti_strictly_weaker`). |
| **T2** `gibbsTerm_step_lt_of_one_le` | **CONFIRMED** | Re-derived (`audit_gibbsTerm_step_lt_of_one_le`); `1 ≤ c` exactly sharp (`audit_not_step_lt_of_lt_one`); `0 < u` necessary (`audit_step_lt_u_nonneg_false`); non-vacuous (`gibbsTerm_step_lt_at_one`); strictly weaker than the promoted statement. |
| **T3** `perelmanF_step_lt_of_one_le` | **STILL_OVERSTRONG** | The statement is **correct** and strictly weaker than the promoted one, and the positivity hypotheses `0 < h`, `0 < F.eval (traj n) i` and the D2 reaction sign are all necessary. But the hypotheses are not the weakest sufficient ones: (i) the uniform curvature bound can be replaced by the strictly weaker state-dependent **active-support** hypothesis (`audit_perelmanF_step_lt_of_active_support`, strictness witness `audit_active_support_strictly_weaker`); (ii) the trajectory hypothesis is used only at step `n` (`audit_perelmanF_step_lt_of_single_step`); (iii) the fixed reacting component can be made existential (`audit_perelmanF_step_lt_of_exists_reaction`). The D7 card's claim that "`1 ≤ c` cannot be weakened further" is true for **state-independent bound families** (the counterexamples above) but false for the state-dependent active-support family. |

## 6. Kernel audit and gates

### 6.1 Per-file compilation (`lake env lean`, cwd = worktree root)

| verifier file | lines | top-level decls | `#print axioms` entries | exit | log |
|---|---|---|---|---|---|
| `AuditSharp/ReDerive.lean` | 337 | 30 | 20 | 0 | `AuditSharp/logs/lean_ReDerive.log` |
| `AuditSharp/StrictlyWeaker.lean` | 274 | 25 | 21 | 0 | `AuditSharp/logs/lean_StrictlyWeaker.log` |
| `AuditSharp/Sharpness.lean` | 661 | 51 | 47 | 0 | `AuditSharp/logs/lean_Sharpness.log` |
| `AuditSharp/D7CrossCheck.lean` | 174 | 13 | 20 | 0 | `AuditSharp/logs/lean_D7CrossCheck.log` |

### 6.2 Full-worktree gate replay

`AuditSharp/gate_replay.py` reproduces the harness gate exactly (`cwd = worktree root`,
`ELAN_HOME = <longrun>/elan`, `lake env lean <abs file>`) over **every** `.lean` file:

```text
75/75 files: `lake env lean <abs file>` exit 0
AuditSharp/logs/gate_replay.json, AuditSharp/logs/gate_replay.out, per-file logs AuditSharp/logs/gate_*.log
```

This includes the 71 scaffold files (unchanged) and the four new verifier files. The D7
environment-wide gate re-runs inside the replay and still passes:

```text
D7SharpReleaseAudit: project declarations audited: 876
D7SharpReleaseAudit: project axiom declarations: 0
D7SharpReleaseAudit: unsafe declarations: 0
D7SharpReleaseAudit: declarations depending on sorryAx: 0
D7SharpReleaseAudit: declarations depending on native_decide/ofReduceBool: 0
D7SharpReleaseAudit: declarations with unapproved axioms: 0
D7SharpReleaseAudit: declaration names containing 'proof_wanted': 0
D7SharpReleaseAudit: PASS
```
(`AuditSharp/logs/gate_release__Poincare__D7__EvolutionSharp__ReleaseAudit.lean.log`.)

### 6.3 Per-module environment audits

Each verifier module ends with a `run_cmd` that walks every `AuditSharp.*` constant in its
own environment and checks the dependency cones:

| module | declarations audited | project axioms | unsafe | unapproved cones | `proof_wanted` |
|---|---|---|---|---|---|
| `AuditSharp.ReDerive` | 37 | 0 | 0 | 0 | 0 |
| `AuditSharp.Sharpness` | 72 | 0 | 0 | 0 | 0 |
| `AuditSharp.StrictlyWeaker` | 32 | 0 | 0 | 0 | 0 |
| `AuditSharp.D7CrossCheck` | 1 | 0 | 0 | 0 | 0 |

All 108 explicit `#print axioms` entries across the four files report the single cone
`[propext, Classical.choice, Quot.sound]` (or a subset); no `sorryAx`, no project `axiom`, no
`unsafe`, no `native_decide`, no unapproved axiom.

### 6.4 Forbidden-token scan

`python3 input/d5-tools/scan_forbidden.py AuditSharp` (the accepted comment/string-aware
scanner): **4 files scanned, 0 hard matches, 0 soft flags** for
`sorry`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`, `sorryAx`, `admit`
(`AuditSharp/logs/forbidden_scan.json`). The audit blocks mention these tokens only inside
strings/escaped identifiers, which the scanner removes.

### 6.5 Scaffold integrity

`diff -rq --exclude=.lake --exclude=AuditSharp --exclude=.dshpkg . ../D7-evolution-sharp-restatement`
→ exit 0, no output: every scaffold file is byte-identical to the D7 source; the only new
files are under `AuditSharp/` plus this card.

## 7. Headline findings

| # | finding | class | evidence |
|---|---|---|---|
| F1 | `perelmanF_step_lt_of_one_le`'s uniform curvature hypothesis `∀ i, 1 ≤ c i` is still overstrong: the state-dependent active-support condition `∀ j, 0 < F.eval (traj n) j → 1 ≤ c j` suffices, and there is a non-vacuous instance where it holds while the uniform hypothesis fails. | **STILL_OVERSTRONG** | `Sharpness.audit_perelmanF_step_lt_of_active_support`, `Sharpness.audit_active_support_strictly_weaker`, `Sharpness.audit_support_value_zero/one`, `Sharpness.audit_active_support_by_values` |
| F2 | The `DiscreteEvolution` hypothesis is consumed only at index `n`; the one-step recurrence suffices. | residual generality | `Sharpness.audit_perelmanF_step_lt_of_single_step` |
| F3 | The fixed strictly reacting component can be replaced by an existential. | residual generality | `Sharpness.audit_perelmanF_step_lt_of_exists_reaction` |
| F4 | No state-independent relaxation of `1 ≤ c` works for T1/T2; `0 < u`, `0 < h`, `0 < F.eval`, and the D2 reaction sign are all necessary for T2/T3. | positive (sharpness confirmed) | `Sharpness.audit_not_strictAnti_of_lt_one`, `audit_not_step_lt_of_lt_one`, `audit_step_lt_u_nonneg_false`, `audit_perelmanF_c_nonneg_false`, `audit_perelmanF_c_pointwise_false`, `audit_perelmanF_h_nonneg_false`, `audit_perelmanF_reaction_nonneg_false`, `audit_perelmanF_needs_reaction_sign` |
| F5 | The D7 statements are exactly the D4 audit's corrected statements (same types), and every D7 sharpened declaration has an approved axiom cone. | positive | `D7CrossCheck` type ascriptions + `#print axioms` |

## 8. Analytic boundaries (explicit)

- The verifier adds no geometric or manifold-level claim. `perelmanF` is the finite sum
  `∑ i, (c i + (lam i)²) e^{-lam i}` along the finite explicit-Euler recurrence; the D2
  `ReactionField` and the D3 bridge boundaries are unchanged.
- The active-support finding is a statement about the **one-step** strict-decrease lemma at
  the state `traj n`, not about the certificate layer, whose `perelmanF_nonneg` lower bound
  still needs `0 ≤ c i` everywhere.
- The counterexamples are finite and explicit (`Fin 1`/`Fin 2`, rational/exponential data);
  no `native_decide` or computational reflection is used, and all conclusions are
  kernel-checked.

## 9. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D8-verifier-evolution-sharp
cd "$WT"

# exact harness gate command on the four verifier modules
lake env lean AuditSharp/ReDerive.lean
lake env lean AuditSharp/StrictlyWeaker.lean
lake env lean AuditSharp/Sharpness.lean
lake env lean AuditSharp/D7CrossCheck.lean

# full gate replay over every .lean file + forbidden scan (writes AuditSharp/logs/)
bash AuditSharp/verify.sh
```

## 10. Deliverables

| Artifact | Path |
|---|---|
| Fresh-namespace re-derivation (goal 1) | `AuditSharp/ReDerive.lean` |
| Strictly-weaker hypothesis witnesses (goal 3) | `AuditSharp/StrictlyWeaker.lean` |
| Further-weakening counterexamples + successful weakenings (goal 2) | `AuditSharp/Sharpness.lean` |
| D7 statement-shape / axiom cross-check | `AuditSharp/D7CrossCheck.lean` |
| Gate replay + forbidden scan tooling | `AuditSharp/gate_replay.py`, `AuditSharp/verify.sh` |
| Compilation / audit logs | `AuditSharp/logs/lean_*.log`, `AuditSharp/logs/gate_*.log`, `AuditSharp/logs/gate_replay.json`, `AuditSharp/logs/forbidden_scan.json` |
| This card | `longrun/results/D8-verifier-evolution-sharp.md` / `.json` |

**Verdict: DONE.** The three D7 sharpened restatements are kernel-correct, non-vacuous, and
strictly weaker than the promoted statements; their state-independent bound/positivity
hypotheses are individually necessary; and one of them (T3) is still overstrong because a
strictly weaker state-dependent active-support hypothesis suffices.

TASK_DONE — longrun/results/D8-verifier-evolution-sharp.md
