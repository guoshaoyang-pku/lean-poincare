# L4-child-conjugate-point-bound — continuation-invocation re-verification

- **Task id:** `L4-child-conjugate-point-bound`
- **Invocation:** 2 (continuation of the completed round-1 artifact set; fresh session)
- **Performed (UTC):** 2026-09-12T02:18Z
- **Prior state:** `checkpoint.json` on arrival: `status = complete`, verdict `TASK_DONE`,
  authored sources on disk with hashes equal to the recorded ones.
- **Scope of this invocation:** independent re-verification of the frozen deliverable and a
  fresh checkpoint. **No Lean source, audit source or result card was modified.**
- **Result:** all checks reproduce; `TASK_DONE` maintained; classification unchanged
  (conditional analytic scalar Jacobi/Riccati comparison; no manifold-level or Poincaré
  claim).

## 1. Frozen revisions checked (unchanged)

| artifact | sha256 (this invocation) | equal to checkpoint |
| --- | --- | --- |
| `release/Poincare/L4/GeodesicComparison/ConjugatePointEndpoint.lean` | `6b6ddac2db2f7ea72a5088c65e4b215282875f5e1bd8661185ae5dc0400d8a5b` | yes |
| `release/Poincare/L4/GeodesicComparison/ConjugatePointAxiomAudit.lean` | `de3f9489b9a1e664afea59d05e933e801c9465be023f521429fe6ba54981fd90` | yes |
| `tools/l4cp_verify.py` | `ea18db80453ed4413645623d3e8c6ae9d309ecc611bd61231a312ad1d0be3b24` | yes |
| `negcontrol/EndpointNegativeControl.lean` | `fa4f3bcd0e138182273ed2db2abb70dec1a762aa7c13adb56fd3a98a5767055d` | yes |
| `longrun/results/L4-child-conjugate-point-bound.md` | `6e9d0cca9862d8b4f8461686c7835b23ab0cf3d67daf95d1f120510d99d53114` | yes (not edited) |

All 11 imported dependency modules were re-hashed against their canonical origins by the
verification suite (gate 1): `release/Poincare/D10/*` (3), `release/Poincare/D12/*` (5) and
`release/Poincare/L4/GeodesicComparison/{RauchBridge,DownstreamComparison,ConstantCurvatureRauch}.lean`
against `leaders/L1-lean-baseline/release` and
`leaders/L4-geometric-critical-path/release` respectively. Additionally, the leader's live
`ConstantCurvatureRauch.lean` was hashed directly in this session and equals the imported
copy `93cb411e25f19079d39c36202bdf61a23e3b23a5939694fb668583d6c6e96048`. All provenance
gates pass.

**Minor observation (process only).** The arriving `checkpoint.json` recorded
`updated_at = 2026-09-12T02:30:00Z`, which is 16 minutes *later* than the modification time
of the artifacts it describes and of this invocation's arrival; the field was evidently
pre-dated/rounded. It has been replaced with the actual re-verification timestamp (a
bookkeeping nit only: no hash, statement or evidence was affected).

## 2. Clean rebuild from a deleted build cache

```
cd release
rm -rf .lake/build
lake build Poincare.L4.GeodesicComparison.ConjugatePointEndpoint \
           Poincare.L4.GeodesicComparison.ConjugatePointAxiomAudit
```

* exit **0**; wall time 23.6 s (`user 32.9 s`, `sys 12.2 s`).
* 13 project modules rebuilt (`2759/2771` … `2771/2771`): the 11 imported modules plus the
  2 authored modules; 2758 mathlib jobs were already cached from the hash-pinned package
  (`release/.lake/packages` → D6 weekly-release package, `lake-manifest.json`
  `7974e751bece493b6ff508039423ca9fa2452fa8`).
* 0 occurrences of `error` in the log.
* log: `logs/l4cp-clean-build-rerun.log`,
  sha256 `ecc56f763db1c064a2d232f8144dc641ebf4aff345c4c74faccdc7fab1018b35`.

Note: this re-run replaced `release/.lake/build`; the earlier log
`logs/l4cp-clean-build.log` was left intact and the new log is a separate file. The earlier
clean-build claim is therefore reproduced, not merely re-read.

## 3. Full fail-closed verification suite re-run

`python3 tools/l4cp_verify.py` → exit **0**, `ok = true`, `failures = []`, **11/11 gates
true**: `provenance_unchanged`, `forbidden_tokens_clean`, `compile_exit_zero`,
`axiom_run_exit_zero`, `audit_query_list_exact`, `authored_declarations_all_audited`,
`no_unscanned_declaration_forms`, `axiom_audit_all_expected_found`, `axiom_cones_allowed`,
`negative_control_real_rejected`, `negative_control_synthetic_rejected`.

* `manifest/l4cp-verification.json` (rewritten by the suite; the final run at
  `2026-09-12T02:20:03Z` post-dates the clean rebuild and the probe),
  sha256 `4b36faae0c20c628a0e3381d478fe15a3f6fd46a570245932d22f8400e0b8b68`.
* Raw audit log `logs/l4cp-verify-axioms.log`,
  sha256 `0111234953e5d744d23cd17d169f98054d872888bd601ce3d21dc2a204d54978`:
  **27/27** expected declarations found; every axiom cone is exactly
  `[propext, Classical.choice, Quot.sound]`; **0** `sorryAx`.
* Real negative control `negcontrol/EndpointNegativeControl.lean` recompiled; its two
  declarations are rejected (`negControl_sorry ↦ [sorryAx]`,
  `negControl_axiom ↦ [negControl_axiom]`), and the synthetic multi-line/empty-cone control
  is rejected.

## 4. Independent elaborated-statement probe

`tmp/l4cp_probe.lean` (not part of the build; new in this invocation,
sha256 `410a990c826fa651b662528aa426acd024f08901cb45e4eb9d65e86c1c96bd06`) imports
`ConjugatePointAxiomAudit` and is compiled with `lake env lean` against the **oleans**
(`logs/l4cp-probe.log`, exit 0, sha256
`db95fa8ad11e1634b500f0ed165d5af73aa9db7d522de1600c5246503f51498f`). It prints the
elaborated types: `conjugate_point_bound` elaborates to

```
∀ {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ},
  0 < T → 0 ≤ B → 0 < t₀ → t₀ ≤ T → B * t₀ ≤ 1/2 →
  JacobiSolutionOn k u du ddu 0 T → ContinuousOn ddu (Icc 0 T) →
  (∀ t ∈ Ioo 0 T, |ddu t| ≤ B) → u 0 = 0 → du 0 = 1 →
  (∀ t ∈ Ioc 0 T, 0 < u t) → 0 < K → (∀ t ∈ Ioo 0 T, K ≤ k t) →
  K * max (1/√K) T * t₀ ≤ 1/2 → T ≤ Real.pi / √K
```

i.e. the acceptance sentence with exactly the `hzero : K = 0 ∨ √K·T < π` hypothesis of
`rauch_upper_of_jacobi_constCurv` removed and `0 ≤ K` strengthened to `0 < K`; no hidden
binder, no typeclass argument and no weakened conclusion. The probe additionally re-proves,
as independent `example`s against the olean, the witness inequalities
`2 ≤ π/√1` and `2 ≤ π/√2`, the sharp-threshold equivalence
`(∀ t ∈ Ioc 0 T, 0 < jacobiSol 2 t) ↔ T < π/√2`, and `jacobiSol 2 (π/√2) = 0`; it re-queries
the kernel cones of the headline, strict, witness and lock declarations. All exit 0.

As a stronger non-vacuity check the probe also applies the theorem at
`T = 11/5 = 2.2`, which is *closer to the sharp threshold* `π/√2 ≈ 2.22144` than the shipped
`T = 2` witness, with the different normalization data `B = 22/5`, `t₀ = 1/10`: all
hypotheses are discharged and the conclusion yields `11/5 ≤ π/√2`. Positivity of the model
on `(0, 11/5]` is established from the sharper mathlib bound `Real.pi_gt_d4 : 3.1415 < π`
(since `√2·11/5 ≈ 3.1113 < 3.1415`). This shows the theorem's constants are not
accidentally loose at the shipped instance and that the bound is exercised practically up to
the first zero `π/√2`.

## 5. Manual walkthrough of the endpoint-limit proof (independent of the prior review)

Read line by line in this session:

1. `JacobiSolutionOn.mono` restricts the structure to `(0,T'')`, `T'' ≤ T`, including
   `continuousOn_u`/`continuousOn_du` via `Icc_subset_Icc_right`.
2. `basePoint_lt_firstZero`: from `(K·max (1/√K) T)·t₀ ≤ 1/2` and `K > 0` it derives
   `√K·t₀ ≤ 1/2` and hence `t₀ < π/√K`; correct.
3. `conjugate_point_bound_strict`: assumes `¬ T < π/√K`, i.e. `x := π/√K ≤ T` (the
   `by_contra` is on the *negation of the conclusion*, not an assumption of the conclusion).
   For `t ∈ Ioo 0 x` it sets `T'' = (max t t₀ + min T x)/2`, so
   `t < T'' < min T x ≤ T`, `t₀ ≤ T''`, `√K·T'' < π`, and
   `max (1/√K) T'' ≤ max (1/√K) T`, hence the model threshold holds on `T''`. It then applies
   the imported `jacobi_le_constCurvModel` with `Or.inr hT''pi`, obtaining `u t ≤ j_K t`.
4. One-sided continuity at `x`: `Icc 0 T ∈ 𝓝[Iio x] x` is proved from `x ∈ Icc 0 T` and
   `0 < x`; `ContinuousWithinAt.mono_of_mem_nhdsWithin` turns
   `ContinuousOn u (Icc 0 T)` into `ContinuousWithinAt u (Iio x) x`, i.e.
   `Tendsto u (𝓝[<] x) (𝓝 (u x))`; `jacobiSol K` is continuous everywhere, so its limit is
   `jacobiSol K x`. `le_of_tendsto_of_tendsto` upgrades the eventual inequality to
   `u x ≤ jacobiSol K x = jacobiSolSphere K x = 0`, contradicting `0 < u x` from
   `hpos x ⟨hxpos, hxT⟩`.
5. `conjugate_point_bound` is `le_of_lt` of the strict form, so both deliverables are the
   same proof.
6. `jacobiSol_pos_iff`: forward direction applies step 5 to `jacobiSol K` itself with
   `B = K·max (1/√K) T`, `t₀ = min T (1/(2B))`, then excludes equality `T = π/√K` by
   `jacobiSolSphere_firstZero`; reverse direction uses `jacobiSolSphere_pos`. Consistent.

No step assumes the conclusion, and no goal is left as `sorry`/`admit` (kernel-checked, and
the forbidden-token gate is clean). The endpoint limit requested by the task **is**
formalized; the "if the endpoint limit cannot be formalized" branch does not apply.

## 6. Falsification attempts (none succeeded)

* Raw `grep` (comments included) for `sorry`, `admit`, `native_decide`, `proof_wanted`,
  `unsafe`, `axiom`, `opaque` in the two authored files: only the word "sorry" inside a
  documentation comment of the audit module (the gate strips comments); no construct.
* `grep` for `set_option`, `macro`, `elab`, `syntax`, `notation`, `attribute`, `instance`,
  `deriving`, `local ` in the authored files: no hits outside doc-comment prose ("instance"
  as an English word).
* Adversarial parser test: the suite's acceptance predicate was driven with a synthetic log
  containing a mixed cone `[propext, MyEvilAxiom]`, a `[sorryAx]` cone, a multi-line allowed
  cone, an empty cone (`does not depend on any axioms`) and a single allowed axiom. Result:
  only the clean cones are accepted; `MyEvilAxiom` and `sorryAx` are rejected
  (`ADVERSARIAL PARSER TEST: PASS`). The predicate is fail-closed, not allow-listed by name.
* Non-vacuity: both witnesses instantiate all 14 explicit arguments with concrete data
  (`k ≡ 2`, `u = jacobiSol 2`, `T = 2`, `B = 4`, `t₀ = 1/8`, `K ∈ {1,2}`) and compile.
  The probe's near-threshold instance adds the same theorem at `T = 11/5 > 2` with
  `B = 22/5`, `t₀ = 1/10`, reaching `11/5 ≤ π/√2`. Hence no hypothesis set is
  contradictory and the conclusion is non-trivial at points approaching the first zero.
* Sharpness: `jacobiSol_two_pos_iff` gives positivity on `(0,T]` iff `T < π/√2`, with
  `jacobiSol_two_firstZero` showing the endpoint is a genuine zero, so the `K = 2` bound
  cannot be improved for the `k = 2` solution; `pi_div_sqrt_two_lt_pi` separates it from the
  `K = 1` bound. Numeric sanity: `2 ≤ π/√2 ⟺ 2√2 ≤ π` (2.828 ≤ 3.1416), and `π/√2 < π`.

## 7. Classification and trusted base (unchanged)

* **Class:** conditional analytic scalar Jacobi/Riccati comparison; **not** a manifold-level
  conjugate-point theorem and not a Poincaré proof.
* **Trusted base for this re-verification:** (i) the hash-pinned imported D10/D12/L4 modules
  (their mathematical content was not re-proved here; their provenance and axiom cones were
  re-checked); (ii) mathlib oleans from the pinned revision
  `7974e751bece493b6ff508039423ca9fa2452fa8`; (iii) the Lean 4.34.0-rc2 kernel.
* **Not modified:** authored Lean sources, audit module, negative control, verify tool and
  the result card `longrun/results/L4-child-conjugate-point-bound.md` are byte-identical to
  the reviewed round-1 revision.
* **Verdict:** `TASK_DONE` maintained. Independent acceptance of the conditional-analytic
  milestone is still requested from the controller; this file records only that a fresh
  session reproduced every mechanical check and hand-checked the endpoint-limit proof.

## 8. Evidence index (this invocation)

| evidence | path | sha256 |
| --- | --- | --- |
| clean rebuild log | `logs/l4cp-clean-build-rerun.log` | `ecc56f76…18b35` |
| verification manifest | `manifest/l4cp-verification.json` | `4b36faae…b8b68` |
| raw axiom-audit log | `logs/l4cp-verify-axioms.log` | `01112349…54978` |
| statement probe source | `tmp/l4cp_probe.lean` | `410a990c…6bd06` |
| statement probe log | `logs/l4cp-probe.log` | `db95fa8a…498f` |
| this file | `evidence/l4cp-reverification.md` | recorded in `checkpoint.json` |

Generated by the continuation invocation on 2026-09-12T02:18Z.
