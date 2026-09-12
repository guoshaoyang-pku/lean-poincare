# L4-child-conjugate-point-bound — invocation-5 independent re-verification

- **Task:** `L4-child-conjugate-point-bound`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-child-conjugate-point-bound`
- **Performed (UTC):** 2026-09-12T02:26Z–02:34Z (invocation 5)
- **Reason:** continuation invocation on a checkpoint marked `complete`; fresh-session
  independent re-verification. No prior work was restarted; no authored source was modified.
- **Model handling:** configured host model only. No subagent, workflow, Ralph loop or external
  model was invoked; all checks are local `lake`/`lean`/`python3`/`sha256sum`/`cmp` runs.
  The controller's `queue.json` `controller_note` (updated 2026-09-12T10:29:43+0800) records
  provider recovery with this task as the live probe, i.e. quota recovery is recorded.
- **Verdict:** **TASK_DONE maintained.** No mathematical change and no new claim. One *new*
  piece of positive evidence was produced (an independent from-scratch reproof, §5).

## 1. Frozen-artifact hash check (against `checkpoint.json`)

All match the checkpoint exactly; nothing authored was touched.

| file | sha256 | checkpoint |
| --- | --- | --- |
| `release/Poincare/L4/GeodesicComparison/ConjugatePointEndpoint.lean` | `6b6ddac2db2f7ea72a5088c65e4b215282875f5e1bd8661185ae5dc0400d8a5b` | match |
| `release/Poincare/L4/GeodesicComparison/ConjugatePointAxiomAudit.lean` | `de3f9489b9a1e664afea59d05e933e801c9465be023f521429fe6ba54981fd90` | match |
| `tools/l4cp_verify.py` | `ea18db80453ed4413645623d3e8c6ae9d309ecc611bd61231a312ad1d0be3b24` | match |
| `negcontrol/EndpointNegativeControl.lean` | `fa4f3bcd0e138182273ed2db2abb70dec1a762aa7c13adb56fd3a98a5767055d` | match |
| `longrun/results/L4-child-conjugate-point-bound.md` | `6e9d0cca9862d8b4f8461686c7835b23ab0cf3d67daf95d1f120510d99d53114` | match (frozen) |
| `longrun/results/L4-child-conjugate-point-bound.json` | `351d3ea6dee4e7b53cd3a149a8e94b36e50365ce61867efbb19ac956d2852aa0` | match (frozen) |

## 2. Clean rebuild from a deleted build cache

```
cd release
rm -rf .lake/build
lake build Poincare.L4.GeodesicComparison.ConjugatePointEndpoint \
           Poincare.L4.GeodesicComparison.ConjugatePointAxiomAudit
```

- exit **0**; wall time 22.3 s; 0 errors.
- log `logs/l4cp-clean-build-inv5.log`, sha256
  `272cb560e7271d2601b2a5a24af3ca9c891c70b7854ed694c719790bd805be9d`.

## 3. Eleven-gate fail-closed verification

```
python3 tools/l4cp_verify.py        # exit 0
```

- `ok: true`, gates **11/11** true, `failures: []`.
- Final console log `logs/l4cp-verify-inv5-final.log`, sha256
  `fa62246b815d3c0df88128a85fb05702d9204276e02900a3937e532b69676b65` — **byte-identical**
  to the invocation-3 and invocation-4 final logs (deterministic reproduction).
- `manifest/l4cp-verification.json`, sha256
  `7c91fb33122a8a117d32d77025771167818a1a4e367dd48d6f18a4350f097dc9`; differs from the
  invocation-4 snapshot (`manifest/l4cp-verification-inv4.json`) **only** in `generated_at`
  (verified by key-wise JSON comparison; all other keys, including the 27 cones, identical).
- Raw audit log `logs/l4cp-verify-axioms.log`, sha256
  `0111234953e5d744d23cd17d169f98054d872888bd601ce3d21dc2a204d54978` — byte-identical to
  invocations 2, 3 and 4. 27/27 audited declarations found, every cone exactly
  `[propext, Classical.choice, Quot.sound]`, **0** occurrences of `sorryAx`.
- Real negative control `logs/l4cp-negative-control.log`, sha256
  `4af5d1e31b05ce346c6c702505f7e3ac0ce3038bd3ead2bde41dde19ab3ba95f`: `negControl_sorry`
  ↦ `[sorryAx]`, `negControl_axiom` ↦ `[negControl_axiom]`, both rejected. Synthetic control
  rejected as well.
- Compile log `logs/l4cp-verify-build.log`, exit 0.
- Gate 6 independently reproduced: the endpoint module declares exactly **13**
  `theorem`s (listed by an independent `grep`), all on the audit list; the audit module adds
  the acceptance lock, giving the 14 authored queries.

## 4. Fresh independent probe (`tmp/l4cp_probe_inv5.lean`, compiled exit 0)

sha256 `2c4ae7f890d7b3d741624a2e8a531fe579a48d0cfb9b6d563cd2291f6fb88276`;
log `logs/l4cp-probe-inv5.log`, sha256
`17e735296c709f04819d84ab9ecb814ded53a593feef1d7bb6adf40c44018ee8`.

1. **Statement fidelity (defeq).** `inv5_HeadlineType` restates the acceptance sentence
   independently; both `conjugate_point_bound` **and** `endpoint_bound_acceptance_lock` were
   elaborated against it (`example : inv5_HeadlineType := …`). Exact hypothesis-for-hypothesis
   match, including `0 < K` (the imported `rauch_upper_of_jacobi_constCurv` has `0 ≤ K` plus
   `hzero`; the deliverable removes `hzero` and strengthens `K`).
2. **Fresh near-threshold witness.** `k ≡ 5`, `K = 5`, `T = 7/5` (threshold
   `π/√5 ≈ 1.40496`, so `T` is within 0.005 of it), `B = 7`, `t₀ = 1/14`, `u = jacobiSol 5`:
   `inv5_witness_k5_near_threshold_strict : 7/5 < π/√5` proved through
   `conjugate_point_bound_strict` with every one of the 14 arguments discharged; the non-strict
   acceptance instance follows by `le_of_lt`. This is a new non-vacuity witness at numbers not
   used anywhere in the artifact (which uses `k=2,K=1`, `k=2,K=2`; invocation 4 used
   `k=3,K=3`).
3. **Sharpness at the new numbers.** `inv5_jacobiSol_five_firstZero :
   jacobiSol 5 (π/√5) = 0` and `inv5_jacobiSol_five_pos_fails_beyond :
   ¬ (∀ t ∈ Ioc 0 (π/√5 + 1/10), 0 < jacobiSol 5 t)` — positivity already fails arbitrarily
   close past the threshold, so no larger `T` satisfies the hypotheses.
4. **Hypothesis necessity (falsification).** `inv5_K_zero_variant_false` proves that the same
   sentence with `0 < K` replaced by `0 ≤ K` is **false** (at `K = 0` the model threshold
   degenerates to `0 ≤ 1/2` while `T ≤ π/√0 = 0` fails for `T = 1`). The positive-curvature
   hypothesis is essential; the acceptance statement is not a degenerate consequence of a
   vacuous hypothesis set.
5. All five probe declarations have cone exactly `[propext, Classical.choice, Quot.sound]`.

## 5. Independent from-scratch reproof (`tmp/l4cp_independent_reproof_inv5.lean`)

sha256 `414795886dde5cf5e52df69dc0d72ba0cadf9d0c360463c4ccb4580cd302e349`;
log `logs/l4cp-independent-reproof-inv5.log`, sha256
`e640f54da2bf6fda85f3a57e43a0511ebb85bf59b765387887ddbfe821a5cb6f`; compiled **exit 0**.

This file imports **only** `Poincare.L4.GeodesicComparison.ConstantCurvatureRauch` (it does
*not* import `ConjugatePointEndpoint.lean`) and re-derives the acceptance statement from
`jacobi_le_constCurvModel` with an independently written proof:

- local restriction lemma `inv5_mono` (the artifact's `JacobiSolutionOn.mono` is not used);
- local normalisation bound `inv5_basePoint_lt_firstZero` with a different proof route
  (`K·max (1/√K) T ≥ √K`, then `t₀·√K ≤ 1/2 < π`);
- comparison interval `T'' = (max t t₀ + x)/2` taken directly from `x = π/√K` (the artifact
  uses `min T (π/√K)`);
- endpoint limit by the **sequence** `x − 2/(n+1) → x` along `atTop` with
  `le_of_tendsto_of_tendsto`, instead of the artifact's one-sided filter `𝓝[<] x`.

`inv5_independent_endpoint_bound` has the acceptance type (checked by an in-file
`example : inv5_HeadlineType' := …`) and cone exactly
`[propext, Classical.choice, Quot.sound]`. The endpoint passage is therefore confirmed by a
second, independently written proof term.

Note: the first draft of the independent proof failed to compile because it treated
`Ioo 0 x` as a neighbourhood of `x` (`x ∉ Ioo 0 x`); the fix uses the one-sided limit
`x − 2/(n+1) → x` with eventual positivity from `Ioi_mem_nhds`. This is recorded because it
shows the endpoint subtlety is real and that the artifact's `𝓝[<] x` handling is the correct
mechanism rather than an accident.

## 6. Proof-term non-circularity of the artifact

`tmp/l4cp_print_inv5.lean` (sha256
`14abe7f4d7f118fed8f0edbe8e4d065f740248ebdfee842c381998c563a8b69d`) prints the proof term of
`conjugate_point_bound_strict` (log `logs/l4cp-print-inv5.log`, sha256
`fb0ca3fd137e20716e0588e68750c7f98d05cb09f6ce30a9da96a236d03fa4d9`, exit 0). The term
mentions `jacobi_le_constCurvModel`, `basePoint_lt_firstZero`, `JacobiSolutionOn.mono`,
`ContinuousWithinAt.mono_of_mem_nhdsWithin`, `le_of_tendsto_of_tendsto` and
`jacobiSolSphere_firstZero` — the endpoint-limit ingredients — and contains **no** use of the
non-strict `conjugate_point_bound`, so the strict theorem is primitive and the derivation is
not circular.

## 7. Provenance and import closure

- `cmp` against canonical origins: **11/11** imported files byte-identical (8 from
  `leaders/L1-lean-baseline/release`, 3 from `leaders/L4-geometric-critical-path/release`).
- Import closure of the endpoint module: exactly the 11 pinned modules plus `Mathlib`; the
  only `Poincare.*` imports are `D10.{Basic,ODE,Comparison}`, `D12.ComparisonGeodesics.*` and
  the three `L4.GeodesicComparison` dependencies. No `ConjugatePointBound` or
  `SturmZeroCount` module appears anywhere in the closure.
- `negcontrol/EndpointNegativeControl.lean` inspected: genuinely tainted (`by sorry` and a
  declared `axiom`), and it lives outside `release/` so it cannot enter the build.
- Queue/checkpoints untouched: no file under `manifest/` (D6 release records), `input/`,
  `third_party/`, `docs/` or `reference/` was modified; the controller's
  `state/L4-child-conjugate-point-bound/` was only read.

## 8. Residual uncertainty

No mathematical or mechanical uncertainty found. The result remains *conditional analytic*
(scalar Jacobi comparison), exactly as the result card states; the manifold-level
conjugate-point theorem is not claimed. The frozen result card
(`longrun/results/L4-child-conjugate-point-bound.md`) was deliberately **not** modified, so its
hash and the reviewed revision are preserved; this evidence file and `checkpoint.json` carry
the invocation-5 record instead.

**Verdict: TASK_DONE maintained.**
