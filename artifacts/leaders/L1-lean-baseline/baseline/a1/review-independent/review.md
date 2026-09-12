# Independent semantic review — L1-lean-baseline, blocker A1

Reviewer: independent semantic reviewer (verifier lane), did not author the patch.
Worktree: `.../worktrees/leaders/L1-lean-baseline` (WT). Read-only outside `WT/baseline/a1/review-independent/`.
Scope: the finite reaction-ODE / finite-sum restatement in `Poincare.Longrun.Evolution.{gibbsTerm_strictAnti, gibbsTerm_step_lt, perelmanF_step_lt}` — **not** Perelman's theorem.

## VERDICT: INDEPENDENT-REVIEW-PASS

The patch restates the three promoted theorems from `1 < c` (resp. `∀ i, 1 < c i`) to `1 ≤ c`
(resp. `∀ i, 1 ≤ c i`) with **identical conclusions, no added hypotheses, no renamed or removed
declarations, and no proof escapes**, and the sharp case `c = 1` is mathematically correct.
The pass does **not** extend to the whole-package audit logs, which are author-produced and were
not re-run (see §7).

## 1. Patch integrity and scope — verified myself

- Fresh byte-copy of `release/` under `review-independent/fresh-release`; `patch -p1 --dry-run`
  → **exit 0**, all 8 files checked. (First attempt failed only because the sandbox denies the
  default temp dir; rerun with `TMPDIR` under `review-independent` succeeded. Not a patch defect.)
- Real apply → **exit 0**; `diff -r -x .lake fresh-release patched-release` → **empty (0 lines)**:
  the patched tree is exactly `release + patch`.
- `diff -rq release patched-release` (excluding `.lake`): exactly the 7 files named in the patch
  changed + the 1 new file `Poincare/D7/EvolutionSharp/SharpOnlyConsumers.lean`; 462 → 463 files;
  no deletions.
- Patch sha256 `c58333…2ac8a` matches `a1-evidence.json`.

## 2. Declaration-level semantics — verified myself

- **Names unchanged**: declaration-name sets of all 7 changed files are identical release vs
  patched (`removed=[]`, `added=[]`). Nothing was replaced by a weaker/renamed restatement.
- **Conclusions unchanged**, hypothesis strictly narrowed (raw-source comparison):

  | declaration | release | patched |
  |---|---|---|
  | `gibbsTerm_strictAnti` | `(c) (hc : 1 < c) : StrictAnti (gibbsTerm c)` | `(c) (hc : 1 ≤ c) : StrictAnti (gibbsTerm c)` |
  | `gibbsTerm_step_lt` | `(hc : 1 < c) (hu : 0 < u) : gibbsTerm c (x+u) < gibbsTerm c x` | `(hc : 1 ≤ c) …` |
  | `perelmanF_step_lt` | `(hc : ∀ i, 1 < c i) … : perelmanF c (traj (n+1)) < perelmanF c (traj n)` | `(hc : ∀ i, 1 ≤ c i) …` |

  All other binders and the whole conclusion are textually identical; no hypothesis added.
- **No escapes**: stripped-comment scan of every added patch line and of every changed/new file
  finds no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`. Raw whole-tree
  token deltas (+1 for sorry/unsafe/native_decide/proof_wanted, +4 for `axiom`) are fully explained
  by the new file's docstring sentence and its three `#print axioms` commands.
- All in-tree call sites were converted (`CounterexampleAudit:332`, `GibbsSharp:101`,
  `Implications:67/96/146`, internal use in `Discrete:88`). A grep of **every** `.lean` file in the
  tree finds no remaining application of the three theorems to a `1 < c` proof: Lean has no
  `<`→`≤` proof coercion, so any survivor would fail to compile.

## 3. Mathematics of the `c = 1` case — verified myself

`gibbsTerm c x = (c + x²) e^{-x}` (`Poincare/Longrun/Evolution/Gibbs.lean:50`), with
`gibbsTerm_hasDerivAt` giving `deriv = -((x-1)² + (c-1)) e^{-x}`.

- `1 < c` branch: unchanged from release (`strictAnti_of_deriv_neg`, bracket `> 0`).
- `c = 1` branch: `deriv (gibbsTerm 1) x = -((x-1)²) e^{-x}` (ring from `gibbsTerm_hasDerivAt 1 x`);
  `sq_pos_of_ne_zero (sub_ne_zero.mpr hx)` gives `(x-1)² > 0` for `x ≠ 1`, so the derivative is
  **strictly negative off the isolated point `x = 1`**. `strictAntiOn_of_deriv_neg` on the convex
  sets `Iic 1` and `Ici 1` (negativity on their interiors, via `interior_Iic`/`interior_Ici`) gives
  strict antitonicity on each side. The gluing case split is exhaustive:
  `y ≤ 1`; `1 < y ∧ 1 ≤ x`; `1 < y ∧ x < 1` (then `gibbsTerm 1 1 < gibbsTerm 1 x` and
  `gibbsTerm 1 y < gibbsTerm 1 1`, chained by `trans`). No flat interval, no sign error, no hidden
  use of `gibbsTerm_strictAnti` inside its own proof, no hypothesis equivalent to the conclusion,
  no unproved lemma beyond Mathlib.
- **Sharpness is genuine, not merely sufficient**: for `c < 1`, `deriv (gibbsTerm c) 1 = (1-c)e^{-1} > 0`,
  so `gibbsTerm c` is not even antitone. The pre-existing `D4Audit.antitone_discrete_fails_at_c_half`
  kernel-checks failure at `c = 1/2`. Thus `1 ≤ c` is exactly the threshold for the *unchanged*
  conclusion.

## 4. `perelmanF_step_lt`: the `Finset.sum_lt_sum` argument — verified myself

`perelmanF c lam = ∑ i, gibbsTerm (c i) (lam i)` and
`DiscreteEvolution.step n i : traj (n+1) i = traj n i + h * F.eval (traj n) i`. The proof gives
pointwise `≤` at every index via `gibbsTerm_step_le (hc j) (mul_nonneg hh.pos.le (F.eval_nonneg …))`
and one strict index `i` via the **sharp** `gibbsTerm_step_lt (hc i) (mul_pos hh hi)`. That is a
valid strict-sum argument: the single strict component comes exactly from the sharp one-variable
step, and all other components are non-strict. No call site needs `1 < c`. The pre-existing
`D4Audit.perelmanF_step_lt_of_one_le` uses the identical argument, independently corroborating it.

## 5. `SharpOnlyConsumers.lean` — consumer analysis

- `gibbsTerm_strictAnti_at_threshold_one` is literally `…gibbsTerm_strictAnti 1 le_rfl`. Against
  the **old** type `(c : ℝ) → 1 < c → StrictAnti (gibbsTerm c)`, the argument `le_rfl : 1 ≤ 1` is
  checked against `1 < 1`: `LE.le` and `LT.lt` are distinct constants with no coercion between
  proofs, so elaboration fails. This is not merely a syntactic mismatch — `1 < 1` is refutable.
- `perelmanF_step_lt_at_threshold_one` supplies `fun i => le_of_eq (hc i).symm : ∀ i, 1 ≤ c i`
  against the old expected `∀ i, 1 < c i`. With `hc : ∀ i, c i = 1` and inhabited `ι`, the old
  hypothesis type is **empty**; I proved this independently:
  `IndepReview.old_hyp_refuted : (∀ i, c i = 1) → ¬ (∀ i, 1 < c i)` (my own probe, exit 0).
- **No smuggling**: hypotheses are `hc : ∀ i, c i = 1`, `hh : 0 < h`, `ev : DiscreteEvolution F h traj`,
  `hi : 0 < F.eval (traj n) i`; none is the conclusion or an instance of it.
- **Non-vacuous**: my probe instantiates the consumer at `squareField : ReactionField (Fin 1)`,
  `sqTraj`, `n = 0`, `i = 0`, proves the reaction positivity, and cross-checks the same
  proposition against the independently written `D4Audit.strict_step_positive_control`.

## 6. Independent runs (my own; outputs under `review-independent/`)

| command (cwd `patched-release`, `lake env lean`) | exit | note |
|---|---|---|
| `Poincare/D7/EvolutionSharp/SharpOnlyConsumers.lean` | **0** | three `#print axioms` rows: `{propext, Classical.choice, Quot.sound}` |
| `../../../baseline/a1/verify/A1Probe.lean` | **0** | `#check`s show `1 ≤ c`, `∀ i, 1 ≤ c i`; sharp consumers' cones clean |
| `../../../baseline/a1/review-independent/IndepReviewProbe.lean` (mine) | **0** | old-hypothesis refutation, consumer non-vacuity, `le_rfl` applications |

Olean-freshness check: every changed module's `.olean` in `.lake/build` is newer than its patched
`.lean` source, so these runs elaborated artifacts of the patched sources. My runs wrote no
`.olean`/`.ilean` into the source tree.

## 7. Author-produced evidence (NOT independently re-run)

- `logs/a1-axiom-audit-G1.log` — trailing `L1AXVERDICT PASS`; `L1SUM` declarations 12072, sorry 0,
  native 0, unexpected_violations 0, collect_failures 0; the three promoted declarations show cones
  `{propext, Classical.choice, Quot.sound}`. **Author-produced; I did not re-run this whole-package audit.**
- `logs/a1-axiom-audit-G2.log` — `L1SUM` axioms 0, sorry 0, native 0, unexpected_violations 0,
  collect_failures 0; trailing `L1AXVERDICT PASS`; no FAIL/VIOLATION rows. **Not re-run.**
- `logs/a1-d7-release-audit.log` — 880 declarations audited, sorryAx-dependent 0, unapproved axioms 0,
  unsafe 0, proof_wanted 0, `PASS`. Its 1 `partial` declaration is pre-existing
  (`TriangulationTopology.segChain._unsafe_rec`), not introduced here. **Not re-run.**
- `logs-patched-build.log` — tail `Build completed successfully (9340 jobs)` + `D13FULLVERDICT PASS`;
  0 error lines / 0 sorry warnings by my grep. **Not re-run** (author's from-scratch build).
- Consumer-cone extraction (`a1-consumer-cone.log`) — **not re-run**; I reproduced only the probe.

## 8. Strongest objection found (documentation, not soundness)

The new module frames `c ≡ 1` as a consumer “that the *old* `1 < c` statements could not serve”.
That is literally true for a term applying the promoted declaration itself, and the per-consumer
wording (“This application is impossible against the old statement”) is precise. **But the same
propositions were already kernel-checked in the frozen release** via
`D7.EvolutionSharp.gibbsTerm_strictAnti_one` (the identical flat-spot gluing proof),
`D4Audit.gibbsTerm_strictAnti_of_one_le` / `gibbsTerm_step_lt_of_one_le` /
`perelmanF_step_lt_of_one_le`, `D4Audit.strict_step_positive_control` (c = 1 positive control), and
`Witnesses.sharpWitness_strict_decrease` with the independent numerical check
`sharpWitness_strict_decrease_by_values`. So this patch adds **no new mathematical content**: its
value is aligning the promoted upstream declarations with the already-known sharp form — which is
exactly what A1 asked for. Also, the new `c = 1` proof branch duplicates the pre-existing D7 proof
(now in 3–4 places). This does not affect the verdict; the ledger should describe the consumer as a
consumer of the *restated declaration*, not as new mathematical power.

Other observations:
- `a1-evidence.json` records `p5_gate_patched.verdict = FAIL` with 22 drift items. This is expected
  source-hash drift against frozen manifests, resolving to exactly the 7 intended files across
  4 manifests (7+7+4+4 = 22) plus the 1 added file — not an unresolved gate. It should be labelled
  “expected drift” in the card.
- `Discrete.lean`'s sentence “the flat spot is bypassed because the step increment … is strictly
  positive” is loose but not false: the actual mechanism is the one-sided gluing making
  `gibbsTerm 1` globally `StrictAnti`.
- The two added Mathlib imports cannot create a package cycle; no `Longrun`/`CurvatureODE` module
  imports `D7`/`Audit`, and `SharpOnlyConsumers` is imported only by `AxiomAudit`.

## 9. Residual uncertainty

1. I did not re-run the full 9340-job build. Instead: author log (labelled), olean-freshness, and my
   own elaboration of **every changed module** via the probe import cones. A failure confined to a
   module that neither imports the three declarations nor is imported by my probes is not excluded,
   but cannot be caused by a hypothesis weakening.
2. Modules that only `#check`/`#print axioms` the three declarations (`D6LedgerProbe`,
   `D12/SemanticLedger/LedgerProbe`, `ReleaseClaims`, `Audit/EvolutionAudit`,
   `Audit/PromotedEvolutionAudit`) were not re-elaborated; those commands are signature-agnostic.
3. G1/G2/D7 whole-package audit verdicts and the consumer-cone extraction are taken from
   author-produced logs only.

## 10. Evidence index (`review-independent/`)

`IndepReviewProbe.lean`, `indep-reviewprobe.out`, `indep-sharponlyconsumers.out`, `indep-a1probe.out`,
`indep_scan.py`, `indep_scan.out`, `apply.log`, `diff-fresh-vs-patched.txt` (empty),
`review.json`, `review.md`.
