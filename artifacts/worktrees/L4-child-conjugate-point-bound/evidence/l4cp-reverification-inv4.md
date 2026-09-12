# L4-child-conjugate-point-bound — continuation-invocation 4 re-verification

- **Task id:** `L4-child-conjugate-point-bound`
- **Invocation:** 4 (continuation of the completed round-1 artifact set; fresh session)
- **Performed (UTC):** 2026-09-12T02:26Z
- **Prior state:** `checkpoint.json` on arrival: `status = complete`, verdict `TASK_DONE`,
  re-verification records for invocations 2 and 3; all authored sources on disk with hashes
  equal to the recorded ones.
- **Scope of this invocation:** independent re-verification with **new** checks (a fresh
  non-vacuity witness at a different curvature, an independently written audit parser, direct
  provenance hashing with pins read from `checkpoint.json`) plus a compile-checked checkpoint
  refresh. **No Lean source, audit source, tool, or result card was modified.**
- **Result:** every check passes; on the deterministic paths the outputs are byte-identical
  to the invocation-2/3 records; `TASK_DONE` maintained; classification unchanged
  (conditional analytic scalar Jacobi/Riccati comparison; no manifold-level and no Poincaré
  claim).
- **Model use:** configured host model only. No other model was invoked.

## 1. Frozen revisions checked (unchanged)

| artifact | sha256 (this invocation) | equal to checkpoint |
| --- | --- | --- |
| `release/Poincare/L4/GeodesicComparison/ConjugatePointEndpoint.lean` | `6b6ddac2db2f7ea72a5088c65e4b215282875f5e1bd8661185ae5dc0400d8a5b` | yes |
| `release/Poincare/L4/GeodesicComparison/ConjugatePointAxiomAudit.lean` | `de3f9489b9a1e664afea59d05e933e801c9465be023f521429fe6ba54981fd90` | yes |
| `tools/l4cp_verify.py` | `ea18db80453ed4413645623d3e8c6ae9d309ecc611bd61231a312ad1d0be3b24` | yes |
| `negcontrol/EndpointNegativeControl.lean` | `fa4f3bcd0e138182273ed2db2abb70dec1a762aa7c13adb56fd3a98a5767055d` | yes |
| `longrun/results/L4-child-conjugate-point-bound.md` | `6e9d0cca9862d8b4f8461686c7835b23ab0cf3d67daf95d1f120510d99d53114` | yes (not edited) |
| `longrun/results/L4-child-conjugate-point-bound.json` | `351d3ea6dee4e7b53cd3a149a8e94b36e50365ce61867efbb19ac956d2852aa0` | yes (not edited) |

## 2. Clean rebuild from a deleted build cache

```
cd release
rm -rf .lake/build
lake build Poincare.L4.GeodesicComparison.ConjugatePointEndpoint \
           Poincare.L4.GeodesicComparison.ConjugatePointAxiomAudit
```

* exit **0**; 2771/2771 jobs; `Build completed successfully (2771 jobs)`; 0 occurrences of
  `error` in the log.
* log: `logs/l4cp-clean-build-inv4.log`,
  sha256 `390f2d1b03309277278bbc8d8f4792859b59a63e7b69de49f7d46e36de8f93a4`.
* This is a fourth independent reproduction of the compile claim (invocations 1–3 each
  performed one), not a re-read of a cached build; the authored oleans were re-created from
  source on top of the hash-pinned mathlib cache.

## 3. New independent statement + non-vacuity probe

A **new** probe `tmp/l4cp_probe_inv4.lean` (sha256
`5167c41de9a653ef20fe656e871f8d66ed6cec23459c46c7b599a03f1d3e7a1a`) was compiled against
the freshly built oleans with `cd release && lake env lean ../tmp/l4cp_probe_inv4.lean`:

* exit **0**; log `logs/l4cp-probe-inv4.log`,
  sha256 `433df9e6ec3df3c0ce68982e44c7afa4d1a1599569c42fccfacd891d3fbd2ec1`;
  0 occurrences of `sorryAx`.

What it establishes beyond the invocation-2/3 probe:

1. **Type ascription check (statement fidelity).** The probe *ascribes* the full acceptance
   type to `conjugate_point_bound` (`#check (conjugate_point_bound : ∀ {k u du ddu} {T B t₀
   K}, 0 < T → … → T ≤ π/√K)`). Elaboration succeeds, so the elaborated type is
   definitionally the acceptance sentence; if the `hzero` hypothesis `K = 0 ∨ √K·T < π` were
   still present the ascription would fail. The log lines 701–716 print
   `rauch_upper_of_jacobi_constCurv` *with* `0 ≤ K` and `K = 0 ∨ √K * T < Real.pi`, while the
   headline print (lines 1–13) has `0 < K` and **no** `hzero` disjunct — the removal is
   visible in the elaborated types, not merely asserted.
2. **Fresh witness at a different curvature.** `inv4_witness_k3_K3_both` runs the theorem at
   `k ≡ 3`, `K = 3`, `u = jacobiSol 3`, `T = 3/2`, `B = 9/2`, `t₀ = 1/9` (no such instance
   exists in the shipped module) and discharges every hypothesis explicitly:
   `max (1/√3) (3/2) = 3/2`, `√3·(3/2) < 3 < π`, `B·t₀ = (9/2)·(1/9) = 1/2`. It applies
   **both** `conjugate_point_bound_strict` (`3/2 < π/√3`) and `conjugate_point_bound`
   (`3/2 ≤ π/√3`) to the same data.
3. **Independent numerics.** `inv4_numeric_k3` proves `3/2 ≤ π/√3` directly
   (`3√3/2 = 2.598… ≤ π`) from `Real.sqrt_lt'`, `Real.sq_sqrt` and `Real.pi_gt_three`,
   without using the theorem.
4. **Sharpness at `K = 3`.** `inv4_k3_firstZero : jacobiSol 3 (π/√3) = 0` and
   `inv4_k3_not_pos_at_threshold : ¬ (∀ t ∈ Ioc 0 (π/√3), 0 < jacobiSol 3 t)`, so the
   threshold is attained and positivity genuinely fails there; `inv4_k2_not_pos_beyond`
   proves the analogous failure strictly beyond the `K = 2` threshold
   (`T = π/√2 + 1`).
5. **Kernel cones of the new declarations** are exactly
   `[propext, Classical.choice, Quot.sound]` (five `#print axioms` lines, 0 `sorryAx`).

## 4. Independently written fail-closed audit

`tmp/l4cp_independent_audit_inv4.py` (sha256
`30df4ec14342f8fa3b19da8c1141567346182371347aeff8830dbcc10cefd9db`) is a from-scratch
checker that does **not** import or shell out to `tools/l4cp_verify.py`. It reads the
provenance pins out of `checkpoint.json` and re-hashes both sides, parses
`logs/l4cp-axioms-inv4-own.log` (produced by this invocation's own
`lake env lean Poincare/L4/GeodesicComparison/ConjugatePointAxiomAudit.lean`, exit 0) with
its own regex, scans the endpoint module with its own declaration regex, and re-checks the
negative control from `logs/l4cp-negctl-inv4-own.log`.

Result: **exit 0, `ok: true`, `failures: []`**; log
`logs/l4cp-independent-audit-inv4.log`, sha256
`36718c8fb4d0d9bca113c8989adc8efdde0bf57ed3a6c3ff0fa1370d674d600e`. Checks:

| independent check | result |
| --- | --- |
| 11/11 imported files byte-identical to their canonical origins (L1 for D10/D12, L4 leader for the three comparison files) and to the checkpoint pin | true |
| 27 `#print axioms` queries present in the audit source, unique, and all 27 found in the log | true |
| every cone exactly `[propext, Classical.choice, Quot.sound]`, none containing `sorryAx` | true |
| 13 endpoint-module declarations scanned, all 13 on the audit list | true |
| no `sorry`/`axiom`/`admit`/`unsafe`/`native_decide`/`proof_wanted` survives comment stripping in either authored file | true |
| real negative control yields `negControl_sorry ↦ [sorryAx]`, `negControl_axiom ↦ [negControl_axiom]`, both outside the allowed set (rejected) | true |
| elaborated type of `endpoint_bound_acceptance_lock` equals the elaborated type of `conjugate_point_bound` (textual `#print` comparison) | true |
| headline type contains **no** `hzero`; `rauch_upper_of_jacobi_constCurv` type **does** | true |

## 5. Shipped fail-closed verification suite (re-run on the rebuilt tree)

```
python3 tools/l4cp_verify.py
```

* exit **0**; `manifest/l4cp-verification.json` regenerated with `ok: true`, **11/11 gates
  true**, `failures: []`; manifest sha256
  `a6baece0b910b60fc95069c8e543ebe5e328bd76369b8b22796b7a2cc0228b81` (snapshot:
  `manifest/l4cp-verification-inv4.json`, identical hash); console log
  `logs/l4cp-verify-inv4-final.log`, sha256
  `fa62246b815d3c0df88128a85fb05702d9204276e02900a3937e532b69676b65` — **byte-identical to
  the invocation-3 final console log**, a deterministic reproduction.
* Raw audit log `logs/l4cp-verify-axioms.log`, sha256
  `0111234953e5d744d23cd17d169f98054d872888bd601ce3d21dc2a204d54978` — byte-identical to the
  invocation-2 and invocation-3 records; 27 expected = 27 found, `bad_cones: {}`,
  `missing: []`, every cone exactly the allowed triple, 0 `sorryAx`.
* Real negative control log `logs/l4cp-negative-control.log` sha256 `4af5d1e3…` and synthetic
  parser control `logs/l4cp-negative-control-synthetic.log` sha256 `f9929649…`, both
  byte-identical to the invocation-3 records and both rejected.

## 6. Mathematical spot-check (no source change)

The endpoint-limit proof was re-walked: for `t < π/√K` the proof constructs
`T'' = (max t t₀ + min T (π/√K))/2`, so `max t t₀ < T'' < min T (π/√K)`; this gives
`√K·T'' < π` (the model-zero hypothesis of `jacobi_le_constCurvModel`, supplied as
`Or.inr hT''pi`), `T'' ≤ T` and the restricted normalization threshold. The comparison then
yields `u t ≤ j_K t` on `Ioo 0 (π/√K)`. At the endpoint it uses
`ContinuousWithinAt.mono_of_mem_nhdsWithin` (from `ContinuousOn u (Icc 0 T)` and
`Icc 0 T ∈ 𝓝[Iio x] x`), continuity of `jacobiSol K`,
`le_of_tendsto_of_tendsto`, and D10 `jacobiSolSphere_firstZero` to get
`u (π/√K) ≤ j_K (π/√K) = 0`, contradicting `hpos` at `x = π/√K ∈ Ioc 0 T` under the
`by_contra` assumption `π/√K ≤ T`. The proof term printed by this invocation's probe
(`#print conjugate_point_bound_strict`, log line 15 ff.) shows exactly this
`Decidable.byContradiction` structure with `basePoint_lt_firstZero` and the `T''`
construction; `conjugate_point_bound` is `le_of_lt (conjugate_point_bound_strict …)`. The
fresh `k = 3` instance of §3 is an end-to-end exercise of the same machinery at a curvature
and horizon not present in the artifact, so the result is non-vacuous beyond the shipped
`k = 2` witnesses.

## 7. Verdict

All mechanical and mathematical checks pass on the frozen revision; the deterministic paths
reproduce byte-for-byte, and the new `k = 3` witness independently confirms non-vacuity and
both theorem forms.

**TASK_DONE maintained.** Classification unchanged: conditional analytic scalar
Jacobi/Riccati comparison (`T ≤ π/√K`, strict form `T < π/√K`, non-vacuous `k = 2`
witnesses, sharp threshold `π/√K`); not a manifold-level conjugate-point theorem and not a
Poincaré proof. This invocation adds no new mathematical claim to the deliverable — it is
independent re-verification plus a checkpoint refresh.
