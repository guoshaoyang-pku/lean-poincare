# L4-child-conjugate-point-bound — continuation-invocation 3 re-verification

- **Task id:** `L4-child-conjugate-point-bound`
- **Invocation:** 3 (continuation of the completed round-1 artifact set; fresh session)
- **Performed (UTC):** 2026-09-12T02:22Z
- **Prior state:** `checkpoint.json` on arrival: `status = complete`, verdict `TASK_DONE`,
  `continuation_reverification` recorded for invocation 2; all authored sources on disk with
  hashes equal to the recorded ones.
- **Scope of this invocation:** independent mechanical re-verification of the frozen
  deliverable and a fresh compile-checked checkpoint. **No Lean source, audit source, tool,
  or result card was modified.**
- **Result:** every check reproduces byte-for-byte where the tool is deterministic;
  `TASK_DONE` maintained; classification unchanged (conditional analytic scalar
  Jacobi/Riccati comparison; no manifold-level and no Poincaré claim).
- **Model use:** configured host model only. No external model was invoked.

## 1. Frozen revisions checked (unchanged)

| artifact | sha256 (this invocation) | equal to checkpoint |
| --- | --- | --- |
| `release/Poincare/L4/GeodesicComparison/ConjugatePointEndpoint.lean` | `6b6ddac2db2f7ea72a5088c65e4b215282875f5e1bd8661185ae5dc0400d8a5b` | yes |
| `release/Poincare/L4/GeodesicComparison/ConjugatePointAxiomAudit.lean` | `de3f9489b9a1e664afea59d05e933e801c9465be023f521429fe6ba54981fd90` | yes |
| `tools/l4cp_verify.py` | `ea18db80453ed4413645623d3e8c6ae9d309ecc611bd61231a312ad1d0be3b24` | yes |
| `negcontrol/EndpointNegativeControl.lean` | `fa4f3bcd0e138182273ed2db2abb70dec1a762aa7c13adb56fd3a98a5767055d` | yes |
| `longrun/results/L4-child-conjugate-point-bound.md` | `6e9d0cca9862d8b4f8461686c7835b23ab0cf3d67daf95d1f120510d99d53114` | yes (not edited) |
| `longrun/results/L4-child-conjugate-point-bound.json` | `351d3ea6dee4e7b53cd3a149a8e94b36e50365ce61867efbb19ac956d2852aa0` | yes (not edited) |

Provenance: the verification suite re-hashed all 11 imported modules against their canonical
origins (`release/Poincare/D10/*` 3 files, `release/Poincare/D12/*` 5 files against
`leaders/L1-lean-baseline/release`; the three `L4/GeodesicComparison` files against
`leaders/L4-geometric-critical-path/release`). Gate `provenance_unchanged` = true.

## 2. Clean rebuild from a deleted build cache

```
cd release
rm -rf .lake/build
time lake build Poincare.L4.GeodesicComparison.ConjugatePointEndpoint \
                Poincare.L4.GeodesicComparison.ConjugatePointAxiomAudit
```

* exit **0**; wall time 31.5 s (`user 33.1 s`, `sys 26.6 s`).
* 2771/2771 jobs; 0 occurrences of `error` in the log; the 13 project modules (11 imported
  + 2 authored) rebuilt from source on top of the hash-pinned mathlib cache.
* log: `logs/l4cp-clean-build-inv3.log`,
  sha256 `b9b4b222d13111258c799251ffb07844ce015af80bcd247c3404fbb342c64fbb`.
* The prior invocation's log `logs/l4cp-clean-build-rerun.log` was left intact; this is a
  third independent reproduction of the compile claim, not a re-read.

## 3. Independent statement probe (against the fresh oleans)

`tmp/l4cp_probe.lean` (unchanged, sha256
`410a990c826fa651b662528aa426acd024f08901cb45e4eb9d65e86c1c96bd06`) was re-elaborated with
`cd release && lake env lean ../tmp/l4cp_probe.lean`:

* exit **0**; log `logs/l4cp-probe-inv3.log`,
  sha256 `db95fa8ad11e1634b500f0ed165d5af73aa9db7d522de1600c5246503f51498f`.
* This hash is **byte-identical to the invocation-2 probe log** recorded in `checkpoint.json`
  (`db95fa8a…`): elaboration output is deterministic and the oleans are semantically the same
  revision.
* The elaborated head line is hypothesis-for-hypothesis the acceptance sentence:
  `0 < T → 0 ≤ B → 0 < t₀ → t₀ ≤ T → B t₀ ≤ 1/2 → JacobiSolutionOn k u du ddu 0 T →
  ContinuousOn ddu (Icc 0 T) → (∀ t ∈ Ioo 0 T, |ddu t| ≤ B) → u 0 = 0 → du 0 = 1 →
  (∀ t ∈ Ioc 0 T, 0 < u t) → 0 < K → (∀ t ∈ Ioo 0 T, K ≤ k t) →
  K * max (1/√K) T * t₀ ≤ 1/2 → T ≤ π/√K`,
  and the proof term is `le_of_lt (conjugate_point_bound_strict …)` — i.e. the endpoint bound
  is derived from the strict form, not postulated.
* The probe's independent `example`s (both witnesses, the `K = 2` sharp-threshold iff, the
  explicit first zero, and the near-threshold instance `T = 11/5`, `B = 22/5`, `t₀ = 1/10`
  giving `11/5 ≤ π/√2`) all elaborate, and its `#print axioms` lines report
  `[propext, Classical.choice, Quot.sound]` for the headline, strict, both witnesses,
  `jacobiSol_pos_iff` and the acceptance lock; 0 occurrences of `sorryAx`.

## 4. Fail-closed verification suite

```
python3 tools/l4cp_verify.py
```

* exit **0**; `manifest/l4cp-verification.json` regenerated with `ok: true`,
  **11/11 gates true**, `failures: []`. Manifest sha256
  `3265bd80cdfba480405f54987ec30f1c2e004faa0cd4ecc262b793e53b5c6fb0`; runner log
  `logs/l4cp-verify-inv3-final.log` sha256
  `fa62246b815d3c0df88128a85fb05702d9204276e02900a3937e532b69676b65`.
* Axiom audit: 27 expected = 27 found, `bad_cones: {}`, `missing: []`, every cone exactly
  `[propext, Classical.choice, Quot.sound]` (allowed set `{propext, Classical.choice,
  Quot.sound}`), 0 `sorryAx`. Raw audit log `logs/l4cp-verify-axioms.log` sha256
  `0111234953e5d744d23cd17d169f98054d872888bd601ce3d21dc2a204d54978` — again
  **byte-identical to the invocation-2 record**, another deterministic reproduction.
* Negative controls re-run: real control (`negControl_sorry ↦ [sorryAx]`,
  `negControl_axiom ↦ [negControl_axiom]`) rejected; synthetic mixed/empty-cone parser test
  rejected. Logs `logs/l4cp-negative-control.log` (sha256 `4af5d1e3…`) and
  `logs/l4cp-negative-control-synthetic.log` (sha256 `f9929649…`).
* Gates `authored_declarations_all_audited` and `no_unscanned_declaration_forms` confirm the
  13 authored declarations are exactly the audited non-lock set and that no
  `instance`/`structure`/`class`/`opaque`/`example`/`mutual` can escape the audit.

## 5. Mathematical spot-check (line-level re-read, no source change)

The endpoint-limit argument in `ConjugatePointEndpoint.lean` (lines 125–190) was re-read and
is genuinely formalized: for `t < π/√K` it constructs `T''` with
`max t t₀ < T'' < min T (π/√K)`, discharges the model-zero hypothesis
`√K·T'' < π` by construction, applies the imported `jacobi_le_constCurvModel`, obtains
`u t ≤ j_K t` on `Ioo 0 (π/√K)`, then uses one-sided continuity at the endpoint
(`ContinuousWithinAt.mono_of_mem_nhdsWithin` from `ContinuousOn u (Icc 0 T)`), continuity of
`jacobiSol K`, `le_of_tendsto_of_tendsto`, and the D10 first zero
`jacobiSolSphere_firstZero : jacobiSol K (π/√K) = 0` to contradict `u (π/√K) > 0`. The
hypothesis list of `conjugate_point_bound` is the hypothesis list of the imported
`rauch_upper_of_jacobi_constCurv` with `hzero` removed and `0 ≤ K` strengthened to `0 < K`;
no other hypothesis was weakened and the conclusion is not assumed. Sharpness is proved, not
asserted: `jacobiSol_pos_iff` (both directions) and `jacobiSol_two_firstZero`.

## 6. Verdict

All mechanical checks reproduce on the frozen revision; the deliverable is unchanged and
still meets the acceptance criterion.

**TASK_DONE maintained.** Classification unchanged: conditional analytic scalar
Jacobi/Riccati comparison (`T ≤ π/√K`, strict form `T < π/√K`, non-vacuous `k = 2`
witnesses, sharp threshold `π/√K`); not a manifold-level conjugate-point theorem and not a
Poincaré proof. This invocation contributes no new mathematical claim — it is independent
re-verification plus a checkpoint refresh.
