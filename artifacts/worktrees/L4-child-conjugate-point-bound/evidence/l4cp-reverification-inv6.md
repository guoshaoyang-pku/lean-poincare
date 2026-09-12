# L4-child-conjugate-point-bound — invocation-6 (quota-recovery live probe) re-verification

- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-child-conjugate-point-bound`
- **Invocation:** 6 · **Performed:** 2026-09-12 ≈02:36–02:55 UTC (10:36–10:55 +0800)
- **Reason:** continuation invocation on the completed checkpoint, run as the operator's provider
  recovery probe. Controller queue `queue.json` note:
  `2026-09-12 10:0x operator: provider recovered (probe L4-child-conjugate-point-bound running
  with live inference)`. Model use: configured host model only; no subagent, workflow or
  external model invoked.
- **Authored sources changed:** no · **Result card changed:** no
- **Verdict:** **TASK_DONE maintained** — no mathematical change and no new claim.

## 1. Frozen artifact hashes (re-hashed this invocation, match checkpoint)

| file | sha256 |
| --- | --- |
| `release/Poincare/L4/GeodesicComparison/ConjugatePointEndpoint.lean` | `6b6ddac2db2f7ea72a5088c65e4b215282875f5e1bd8661185ae5dc0400d8a5b` |
| `release/Poincare/L4/GeodesicComparison/ConjugatePointAxiomAudit.lean` | `de3f9489b9a1e664afea59d05e933e801c9465be023f521429fe6ba54981fd90` |
| `tools/l4cp_verify.py` | `ea18db80453ed4413645623d3e8c6ae9d309ecc611bd61231a312ad1d0be3b24` |
| `negcontrol/EndpointNegativeControl.lean` | `fa4f3bcd0e138182273ed2db2abb70dec1a762aa7c13adb56fd3a98a5767055d` |
| `longrun/results/L4-child-conjugate-point-bound.md` | `6e9d0cca9862d8b4f8461686c7835b23ab0cf3d67daf95d1f120510d99d53114` (unchanged) |
| `longrun/results/L4-child-conjugate-point-bound.json` | `351d3ea6dee4e7b53cd3a149a8e94b36e50365ce61867efbb19ac956d2852aa0` (unchanged) |

## 2. Clean rebuild from a deleted build cache

```
rm -rf release/.lake/build
lcd release && lake build Poincare.L4.GeodesicComparison.ConjugatePointEndpoint \
    Poincare.L4.GeodesicComparison.ConjugatePointAxiomAudit
```

- **exit 0**, `Build completed successfully (2771 jobs)`, 13 project modules, 0 errors.
- wall 27.262 s real / 33.250 s user / 17.626 s sys.
- log `logs/l4cp-clean-build-inv6.log`, sha256 `116439375e67ea9dcafc1951b09733cbda66cb114b6037c1c3aec9f9274fdc85`.

## 3. Eleven-gate fail-closed verification

```
python3 tools/l4cp_verify.py      # exit 0
```

- `ok: true`, **11/11 gates true**, `failures: []`.
- manifest `manifest/l4cp-verification.json`, sha256 `7168a7be7cd139524b88048f2bee8a8205862809876346cec1d69ef1faf293f5`.
- console log `logs/l4cp-verify-inv6-final.log`, sha256 `909346a132560c293e631050bc0c9e64314814049e3cfe15f6088cc3637e59df`.
- gates: `provenance_unchanged`, `forbidden_tokens_clean`, `compile_exit_zero`,
  `axiom_run_exit_zero`, `audit_query_list_exact`, `authored_declarations_all_audited`,
  `no_unscanned_declaration_forms`, `axiom_audit_all_expected_found`, `axiom_cones_allowed`,
  `negative_control_real_rejected`, `negative_control_synthetic_rejected`.

## 4. Axiom audit, parsed by an independently written parser

The raw kernel output was produced afresh this invocation
(`logs/l4cp-verify-axioms.log`, sha256 `0111234953e5d744d23cd17d169f98054d872888bd601ce3d21dc2a204d54978`,
byte-identical to invocations 2–5) and re-parsed with a parser written from scratch for this
invocation (not importing `tools/l4cp_verify.py`):

- 27/27 expected declarations found, 0 missing, 0 extra;
- every axiom cone **exactly** `[propext, Classical.choice, Quot.sound]`;
- 0 occurrences of `sorryAx`; no bad cones.
- parser log `logs/l4cp-independent-audit-inv6.log`, sha256
  `93f08fc868bcb345f363edea42671cff666efa24d7136c77466134978be6c45d`.

Real negative control `negcontrol/EndpointNegativeControl.lean` yields `[sorryAx]` and
`[negControl_axiom]` (log sha `4af5d1e31b05ce346c6c702505f7e3ac0ce3038bd3ead2bde41dde19ab3ba95f`);
the synthetic control log is also rejected (sha `f99296493e03f221a362f0a4e55227a0945b481e2ba988e62bba48f57ba1ad53`).

## 5. Kernel re-check of the oleans (new this invocation)

```
cd release && lake env leanchecker Poincare.L4.GeodesicComparison.ConjugatePointEndpoint   # exit 0
cd release && lake env leanchecker Poincare.L4.GeodesicComparison.ConjugatePointAxiomAudit # exit 0
```

`leanchecker` re-type-checks the compiled `.olean` with the kernel independently of the
elaborator; both modules re-check with **no diagnostics and exit 0**
(`logs/l4cp-leanchecker-inv6.log`, `logs/l4cp-leanchecker-audit-inv6.log`). Passing a module
without oleans errors (`Could not find any oleans for: …`), so the checks were not no-ops.

## 6. Provenance

Fresh hashing this invocation: **11/11** imported sources are byte-identical to their canonical
origins — 8 to `leaders/L1-lean-baseline/release` (D10 ×3, D12 ×5) and 3 to
`leaders/L4-geometric-critical-path/release` (`RauchBridge`, `DownstreamComparison`,
`ConstantCurvatureRauch`, the last at
`93cb411e25f19079d39c36202bdf61a23e3b23a5939694fb668583d6c6e96048`). The import closure of the
deliverable contains no `ConjugatePointBound`/`SturmZeroCount` module; the leader artifact
remains read-only reference material only.

## 7. New independent probe `tmp/l4cp_probe_inv6.lean`

sha256 `0f16f30124ec4a87a53d1ffa346ed4cb0ae6d91b5ef4c6ca4401b4f6a8e434fb`;
compiled against the frozen oleans: **exit 0**, no `sorryAx`, log
`logs/l4cp-probe-inv6.log` sha256 `57bcfa36e9fbb9b3fd8e723a7dd5be0cbdde3f4237ff82f8306d0f25432ff086`.
Thirteen declarations, each with axiom cone exactly `[propext, Classical.choice, Quot.sound]`.

Content new relative to inv2–inv5 probes:

1. **Statement ascription.** `inv6_statement_fidelity : Inv6HeadlineType := conjugate_point_bound`
   where `Inv6HeadlineType` is the acceptance sentence written out independently. The term
   elaborates only because the deliverable's type is definitionally equal to the independently
   written type, so the acceptance sentence is hypothesis-for-hypothesis locked by a second,
   independently authored statement.
2. **Necessity of `u > 0` on `(0,T]`.** `inv6_hpos_necessary` proves that the variant of the
   acceptance sentence with `hpos` dropped is **false**: for `k ≡ 2`, `K = 2`,
   `u = jacobiSol 2`, `T = 3`, `B = √2`, `t₀ = 1/12` every remaining hypothesis holds
   (including `|u''| ≤ √2` across the whole interval, i.e. past the conjugate point) while
   `3 > π/√2`.
3. **Necessity of the domination `K ≤ k`.** `inv6_hk_necessary` proves that the variant with
   `hk` dropped is **false**: `k ≡ 1`, `K = 2`, `u = jacobiSol 1 = sin`, `T = 3`, `B = 1`,
   `t₀ = 1/12` satisfies every remaining hypothesis (positivity holds since `3 < π`) while
   `3 > π/√2`.
4. **New near-threshold witness at `k ≡ K = 4`.** `inv6_near_threshold_witness_strict` and
   `inv6_near_threshold_witness` instantiate `conjugate_point_bound_strict` /
   `conjugate_point_bound` with `u = jacobiSol 4`, `T = 314159/200000 = 1.570795`,
   `B = 2`, `t₀ = 1/13`, giving `T < π/√4 = π/2`; `inv6_threshold_gap` proves
   `π/√4 − T > 0`. Since `2T = 3.14159 < π`, the instance sits within `2.65·10⁻⁶` of the
   sharp threshold (ratio `3.14159/π > 0.999999`). Prior probes used only `K = 1, 2, 3, 5`.

## 8. Endpoint-limit proof re-walked

`conjugate_point_bound_strict` was re-read line by line. For `¬ T < π/√K`, i.e.
`x := π/√K ≤ T`, the comparison `u t ≤ jacobiSol K t` is obtained on every `t ∈ (0,x)` by
restricting to `T'' = (max t t₀ + min T x)/2` (so `√K·T'' < π` holds by construction and
`jacobi_le_constCurvModel` applies), and the one-sided limit `t → x⁻` via
`ContinuousWithinAt.mono_of_mem_nhdsWithin` + `le_of_tendsto_of_tendsto` yields
`u x ≤ jacobiSol K x = 0` (`jacobiSolSphere_firstZero`), contradicting `hpos` at `x`. The new
near-threshold witness exercises exactly this strict theorem at a point `2.65·10⁻⁶` below the
threshold, where a bounding or off-by-one error in the limit would show up. The limit is
formalized; no goal is assumed.

## 9. Disposition

All mechanical checks of invocations 2–5 reproduced from scratch this invocation, with two
additional independent checks (kernel `leanchecker` re-check of both oleans; the fresh
statement-ascription and hypothesis-necessity probe). No blocker, no weakened statement, no
source change. **TASK_DONE maintained**; the result card is unchanged and still records the
accepted verdict. This is independent acceptance evidence for a conditional-analytic scalar
ODE milestone — not a Poincaré proof.
