# L4-child-conjugate-point-bound — invocation-7 independent re-verification

- **Task:** `L4-child-conjugate-point-bound` (worktree `worktrees/L4-child-conjugate-point-bound`)
- **Invocation:** 7 (continuation on a completed checkpoint; live provider probe)
- **Performed (UTC):** 2026-09-12T02:43Z–02:52Z
- **Model use:** configured host model only; no subagent, workflow or external model invoked
- **Quota recovery:** recorded — `longrun/queue.json` `controller_note`: *"2026-09-12 10:0x
  operator: provider recovered (probe L4-child-conjugate-point-bound running with live
  inference)"*; live inference this invocation confirms recovery
- **Verdict:** **TASK_DONE maintained** — no source change, no mathematical change, no new
  claim; two genuinely new independent checks added (non-constant-coefficient witness;
  numerical ODE falsification cross-check)

## 1. Source drift check

All checkpoint-pinned authored artifacts are byte-identical to disk:

| artifact | sha256 | matches checkpoint |
| --- | --- | --- |
| `release/Poincare/L4/GeodesicComparison/ConjugatePointEndpoint.lean` | `6b6ddac2db2f7ea72a5088c65e4b215282875f5e1bd8661185ae5dc0400d8a5b` | yes |
| `release/Poincare/L4/GeodesicComparison/ConjugatePointAxiomAudit.lean` | `de3f9489b9a1e664afea59d05e933e801c9465be023f521429fe6ba54981fd90` | yes |
| `tools/l4cp_verify.py` | `ea18db80453ed4413645623d3e8c6ae9d309ecc611bd61231a312ad1d0be3b24` | yes |
| `negcontrol/EndpointNegativeControl.lean` | `fa4f3bcd0e138182273ed2db2abb70dec1a762aa7c13adb56fd3a98a5767055d` | yes |
| `longrun/results/L4-child-conjugate-point-bound.md` | `6e9d0cca9862d8b4f8461686c7835b23ab0cf3d67daf95d1f120510d99d53114` | yes |
| `longrun/results/L4-child-conjugate-point-bound.json` | `351d3ea6dee4e7b53cd3a149a8e94b36e50365ce61867efbb19ac956d2852aa0` | yes |

The result card is unchanged; this file is additional acceptance evidence only.

## 2. Clean rebuild (deleted build cache)

```
rm -rf release/.lake/build
cd release && lake build Poincare.L4.GeodesicComparison.ConjugatePointEndpoint \
                         Poincare.L4.GeodesicComparison.ConjugatePointAxiomAudit
```

**exit 0**, 2771/2771 jobs, wall 31.87 s, log `logs/l4cp-clean-build-inv7.log`
sha256 `574ccca42e40edc106375b6c62d2cf72aa75c0599f07142b5cc254533a9fab8c`.
Fresh oleans: `ConjugatePointEndpoint.olean` sha256
`34d30ca741024f275032ab3dbcad3d98ca2d085b62c70fda60c0f9e29529c307`,
`ConjugatePointAxiomAudit.olean` sha256
`8ee613eaa99a012b786ad35a68080fca9a09c512d7d28fde375046ad8378cd53`.

## 3. Fail-closed verification suite (11 gates)

`python3 tools/l4cp_verify.py` — **exit 0, 11/11 gates true, failures []**.
Console log `logs/l4cp-verify-inv7-final.log` sha256
`fa62246b815d3c0df88128a85fb05702d9204276e02900a3937e532b69676b65` (byte-identical to the
invocation-3/4/5 final logs). Manifest `manifest/l4cp-verification.json` sha256
`88115ce496ccae5b1d3c46d349aac4d38e471eedb6e9660aba4f54df5e20112f`; diff against the
invocation-4 snapshot `manifest/l4cp-verification-inv4.json` is **empty after removing
`generated_at`** (all gates, all 27 cones and all source hashes identical). Raw axiom log
`logs/l4cp-verify-axioms.log` sha256
`0111234953e5d744d23cd17d169f98054d872888bd601ce3d21dc2a204d54978`, byte-identical to
invocations 2–6.

## 4. Fresh independent audit parser (`tmp/l4cp_independent_audit_inv7.py`, new)

Written from scratch this invocation, does **not** import `tools/l4cp_verify.py`:

- parses the `#print axioms` query list out of the audit **source** (27 queries) and the
  declarations out of the raw **log** — sets equal, 0 missing, 0 extra;
- every cone is exactly `{propext, Classical.choice, Quot.sound}` (single distinct cone);
  no `sorryAx`;
- the 15 invocation-7 probe declarations are all found with allowed cones;
- the real negative control yields `[sorryAx]` and `[negControl_axiom]` and the synthetic
  control yields `[sorryAx]` — both **rejected** by the same predicate;
- forbidden-token scan of both authored sources with comments stripped: 0 hits.

**exit 0**, `ok: true`, log `logs/l4cp-independent-audit-inv7.log` sha256
`b27bc7ca03d21a3d1e8af2c2089b346b8a37422404f1c77bbff07acad8859618`.

## 5. New check A — first non-constant-coefficient witness (`tmp/l4cp_probe_inv7.lean`)

sha256 `500fd70767a3d85176364411b926631360070204b177007afade355f96b1b6b5`; compiled against
the frozen oleans with **exit 0**, log `logs/l4cp-probe-inv7.log` sha256
`68418ff0a1e274a8f3c4354d03527cfb5997cfe0a039bd921fb48129c61a633a`. 15 new declarations,
each with cone exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

Content:

1. **Statement fidelity.** `inv7_statement_fidelity : Inv7HeadlineType :=
   conjugate_point_bound`, where `Inv7HeadlineType` is the acceptance sentence written out
   independently (implicit binders, `hzero` removed, `0 < K` assumed). The ascription
   elaborates only because the deliverable's type is definitionally equal to it.
2. **Non-constant coefficient.** `inv7k t = 2/(t·(4−t))`, `inv7u t = t − t²/4`,
   `inv7du t = 1 − t/2`, `inv7ddu t = −1/2`, on `(0,2)`. Proved: `inv7_k_nonconstant`
   (`inv7k 1 = 2/3 ≠ 1/2 = inv7k 2`), the three derivative identities (using the D12
   pinned-instance combinators `hasDerivAtR_id/const/pow` — an instance-sensitivity trap
   that a naive `HasDerivAt.pow` composition in this import context does *not* pass),
   `inv7_eq_secondDeriv : inv7ddu t = −(inv7k t)·inv7u t` (i.e. `u'' = −k·u` for a
   genuinely rational, non-constant `k`), continuity, `inv7_u_pos` on `(0,2]`,
   `inv7_k_ge : 1/2 ≤ inv7k t` on `(0,2)`, `inv7_ddu_bound : |inv7ddu| ≤ 1`.
   `inv7_jacobiSolution : JacobiSolutionOn inv7k inv7u inv7du inv7ddu 0 2`.
3. **Instantiation.** `inv7_nonconstant_witness : 2 ≤ π/√(1/2) = π√2` and
   `inv7_nonconstant_witness_strict : 2 < π√2` by applying `conjugate_point_bound` /
   `conjugate_point_bound_strict` with `T = 2`, `B = 1`, `t₀ = 1/2`, `K = 1/2`;
   `inv7_bound_is_nontrivial : 2 < π√2` as a numeric sanity statement.

This is the **first** instantiation in the whole task (all invocations 1–6) that is not a
constant-curvature model: it exercises the non-constant branch of `JacobiSolutionOn`, the
domination hypothesis `K ≤ k` as a strict pointwise inequality, and the ODE identity with a
non-trivial coefficient. The bound `π√2 ≈ 4.4429 ≥ 2` is non-trivially satisfied; the exact
solution's next zero is at `t = 4 > 2`, consistent with the theorem.

### 5b. Acceptance-wording probe, part B (`tmp/l4cp_probe_inv7b.lean`)

sha256 `3be6d78de0d9e7bab1f9894ea254e43ea12c16e03536338994f514076e24bbec`; **exit 0**,
log `logs/l4cp-probe-inv7b.log` sha256
`4dacc29386f2c21afbdd1eecdd6cc449c406392b1a3e6d5462bbe48c77b4ff91`.
Seven fresh consumer-side declarations re-elaborating the deliverable sentence
"non-vacuous witness (k = 2, K = 1 giving `T ≤ π/√1 = π`, sharpened by `π/√2` for the k=2
solution)" and the sharpness claims:

- `inv7b_witness_k2_K1 : 2 ≤ π/√1`, `inv7b_witness_k2_K2 : 2 ≤ π/√2`,
  `inv7b_witness_k2_K1_strict : 2 < π/√1`;
- `inv7b_sharpening_strict : π/√2 < π` (the `K = 2` bound is strictly sharper);
- `inv7b_k2_threshold (T) : (∀ t ∈ Ioc 0 T, 0 < jacobiSol 2 t) ↔ T < π/√2`;
- `inv7b_k2_first_zero : jacobiSol 2 (π/√2) = 0`;
- `inv7b_k2_not_pos_at_endpoint : ¬ (0 < jacobiSol 2 (π/√2))`.

All seven cones are exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

## 6. New check B — numerical ODE falsification cross-check (`tmp/l4cp_numeric_inv7.py`, new)

sha256 `6a5cb7a01b4958aa15e589677bec427be8d2d02ba1431d4d1117fb1ed0f5b523`; `scipy`
`solve_ivp` (rtol 1e-12, atol 1e-14, event detection + Brent refinement), **exit 0**
(`ok: true`, 13 rows), log `logs/l4cp-numeric-inv7.log` sha256
`58f07e13c522b615c098deadac8509a7917d3782a006dfa13030485a461b5223`, JSON
`logs/l4cp-numeric-inv7.json` sha256 `3c34a8008fd9b4b215aa978eabdc8a9059cb637c7e79f3d521da343b33f5e4b0`.

| case | first zero `t*` | bound `π/√K` | `t* − bound` |
| --- | --- | --- | --- |
| `k ≡ K = 1` | 3.141592653589782 | 3.141592653589793 | −1.1e-14 (sharp threshold, rel. err 3.5e-15) |
| `k ≡ K = 2` | 2.221441469079177 | 2.221441469079183 | rel. err 2.8e-15 |
| `k ≡ K = 1/2` | 4.442882938158346 | 4.442882938158366 | rel. err 4.6e-15 |
| `k ≡ K = 5` | 1.4049629462081403 | 1.4049629462081452 | rel. err 3.5e-15 |
| `k = K(1+0.02 sin²t)`, `K=1` | 3.1182041708422097 | 3.141592653589793 | −0.023388 |
| `k = K(1+0.2 sin²t)`, `K=1` | 2.9242379343711122 | 3.141592653589793 | −0.217355 |
| `k = K(1+0.05 cos²2t)`, `K=2` | 2.196021491436973 | 2.221441469079183 | −0.025420 |
| `k = K(1+t/10)`, `K=1/2` | 4.049150255663689 | 4.442882938158366 | −0.393733 |
| `k = K(1+0.5 sin²t)`, `K=5` | 1.2877226450661443 | 1.4049629462081452 | −0.117240 |
| near-threshold `k = 1+1e-4 sin²t` | 3.1414748481606343 | π | −0.000118 |
| **adversarial** `k = 0.8K`, `K=1` | 3.512407365520353 | 3.141592653589793 | **+0.370815 (bound violated)** |
| **adversarial** `k = 0.8K`, `K=2` | 2.483647066449014 | 2.221441469079183 | **+0.262206 (bound violated)** |
| inv7 exact witness `k = 2/(t(4−t))`, `K=1/2`, `T=2` | 3.999999999999998 (analytic 4) | 4.442882938158366 | bound holds with margin 2.442883 |

No counterexample to the acceptance statement was found: for every non-constant `k ≥ K` the
first zero is strictly below `π/√K` (as Sturm comparison requires), the constant-`k` sharp
threshold is reproduced to ~4e-15 relative error, and the adversarial `k = 0.8K` cases show
the numerical pipeline *does* detect a violation when the domination hypothesis is dropped,
so the negative results above have detection power. The exact inv7 witness satisfies the ODE
on `(0,2]` with max residual `5.6e-17`, `u > 0` on `(0,2]`, `u 2 = 1`, and its first zero is
at `4` as predicted analytically.

## 7. Kernel re-check and provenance

- `lake env leanchecker Poincare.L4.GeodesicComparison.ConjugatePointEndpoint` → **exit 0**
  (`logs/l4cp-leanchecker-inv7.log`, empty, sha256 `e3b0c442…b855`);
  `…ConjugatePointAxiomAudit` → **exit 0** (`logs/l4cp-leanchecker-audit-inv7.log`, empty,
  same hash). Not a no-op: the same command on a nonexistent module exits 1 with
  *"Could not find any oleans"*.
- Provenance: all 11 imported sources are byte-identical (`cmp`) to their canonical origins
  — 8 files against `leaders/L1-lean-baseline/release` (D10 ×3, D12 ×5) and 3 against
  `leaders/L4-geometric-critical-path/release` (RauchBridge, DownstreamComparison,
  ConstantCurvatureRauch). The leader's live `ConstantCurvatureRauch.lean` hash is
  `93cb411e25f19079d39c36202bdf61a23e3b23a5939694fb668583d6c6e96048`, matching the recorded
  pin. The import closure contains no `ConjugatePointBound`/`SturmZeroCount` module; the
  leader artifact is reference material only.
- The endpoint-limit proof was re-walked line by line: `basePoint_lt_firstZero` gives
  `t₀ < π/√K`; for `x := π/√K ≤ T` the comparison is obtained on all of `(0,x)` via
  `T'' = (max t t₀ + min T x)/2` and `jacobi_le_constCurvModel` with `√K·T'' < π`; one-sided
  continuity at `x` follows from `ContinuousOn` by
  `ContinuousWithinAt.mono_of_mem_nhdsWithin`; `le_of_tendsto_of_tendsto` and
  `jacobiSolSphere_firstZero` yield `u x ≤ 0`, contradicting `hpos`. The limit is genuinely
  formalized; no goal is assumed.

## 8. Disposition

Reproduced from scratch this invocation: source-hash pins, clean rebuild, 11-gate
fail-closed verification, 27/27 axiom cones, negative controls, provenance. Added three
independent checks not present in invocations 1–6: a **non-constant-coefficient witness**
(first in the task), a **numerical ODE falsification cross-check** that independently
reproduces the sharp threshold and finds no counterexample, and a **part-B
acceptance-wording probe** re-elaborating the exact `k = 2`, `K = 1` / `K = 2` sharpened
witness and sharpness sentences. No blocker, no weakened statement, no forbidden construct,
no source change, no new claim. **TASK_DONE maintained**; the result card remains the
accepted deliverable. This is independent acceptance evidence for a conditional-analytic
scalar ODE milestone — not a Poincaré proof.
